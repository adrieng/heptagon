(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Format
open List
open Misc
open Names
open Idents
open Obc
open Obc_utils
open Types

open Modules
open Signature
open C
open Location
open Format

module Error =
struct
  type error =
    | Evar of string
    | Enode of string
    | Eno_unnamed_output
    | Ederef_not_pointer
    | Estatic_exp_compute_failed
    | Eunknown_method of string

  let message loc kind = (match kind with
    | Evar name ->
        eprintf "%aCode generation : The variable name '%s' is unbound.@."
          print_location loc name
    | Enode name ->
        eprintf "%aCode generation : The node name '%s' is unbound.@."
          print_location loc name
    | Eno_unnamed_output ->
        eprintf "%aCode generation : Unnamed outputs are not supported.@."
          print_location loc
    | Ederef_not_pointer ->
        eprintf "%aCode generation : Trying to deference a non pointer type.@."
          print_location loc
    | Estatic_exp_compute_failed ->
        eprintf "%aCode generation : Computation of the value of the static \
                 expression failed.@."
          print_location loc
    | Eunknown_method s ->
        eprintf "%aCode generation : Methods other than step and \
                    reset are not supported (found '%s').@."
          print_location loc
          s);
    raise Errors.Error
end

let rec struct_name ty =
  match ty with
  | Cty_id n -> n
  | _ -> assert false

let int_of_static_exp se =
  Static.int_of_static_exp QualEnv.empty se


let output_names_list sig_info =
  let remove_option ad = match ad.a_name with
    | Some n -> n
    | None -> Error.message no_location Error.Eno_unnamed_output
  in
  List.map remove_option sig_info.node_outputs

let is_stateful n =
  try
    let sig_info = find_value n in
      sig_info.node_stateful
  with
      Not_found -> Error.message no_location (Error.Enode (fullname n))

(******************************)

(** {2 Translation from Obc to C using our AST.} *)

(** [fold_stm_list] is an utility function that transforms a list of statements
    into one statements using Cseq constructors. *)

(** [ctype_of_type mods oty] translates the Obc type [oty] to a C
    type. We assume that identified types have already been defined
    before use. [mods] is an accumulator for modules to be opened for
    each function (i.e., not opened by an "open" declaration).
    We have to make a difference between function args and local vars
    because of arrays (when used as args, we use a pointer).
*)
let rec ctype_of_otype oty =
  match oty with
    | Types.Tid id when id = Initial.pint -> Cty_int
    | Types.Tid id when id = Initial.pfloat -> Cty_float
    | Types.Tid id when id = Initial.pbool -> Cty_int
    | Tid id -> Cty_id id
    | Tarray(ty, n) -> Cty_arr(int_of_static_exp n, ctype_of_otype ty)
    | Tprod _ -> assert false
    | Tinvalid -> assert false

let cvarlist_of_ovarlist vl =
  let cvar_of_ovar vd =
    let ty = ctype_of_otype vd.v_type in
    let ty = if Linearity.is_linear vd.v_linearity then pointer_to ty else ty in
    name vd.v_ident, ty
  in
  List.map cvar_of_ovar vl

let copname = function
  | "="  -> "==" | "<>" -> "!=" | "&"  -> "&&" | "or" -> "||" | "+" -> "+"
  | "-" -> "-" | "*" -> "*" | "/" -> "/" | "*." -> "*" | "/." -> "/"
  | "+." -> "+" | "-." -> "-" | "<"  -> "<" | ">"  -> ">" | "<=" -> "<="
  | ">=" -> ">="
  | "~-" -> "-" | "not" -> "!" | "%" -> "%"
  | op   -> op

(** Translates an Obc var_dec to a tuple (name, cty). *)
let cvar_of_vd vd =
  name vd.v_ident, ctype_of_otype vd.v_type

(** If idx_list = [e1;..;ep], returns the lhs e[e1]...[ep] *)
let rec csubscript_of_e_list e idx_list =
  match idx_list with
    | [] -> e
    | idx::idx_list ->
        Carray (csubscript_of_e_list e idx_list, idx)

(** If idx_list = [i1;..;ip], returns the lhs e[i1]...[ip] *)
let csubscript_of_idx_list e idx_list =
  csubscript_of_e_list e (List.map (fun i -> Cconst (Ccint i)) idx_list)

(** Generate the expression to copy [src] into [dest], where bounds
    represents the bounds of these two arrays. *)
let rec copy_array src dest bounds =
  match bounds with
    | [] -> [Caffect (dest, Clhs src)]
    | n::bounds ->
        let x = gen_symbol () in
        [Cfor(x, Cconst (Ccint 0), n,
              copy_array (Carray (src, Clhs (Cvar x)))
                (Carray (dest, Clhs (Cvar x))) bounds)]

(** Returns the type associated with the name [n]
    in the environnement [var_env] (which is an association list
    mapping strings to cty). *)
let rec assoc_type n var_env =
  match var_env with
    | [] -> Error.message no_location (Error.Evar n)
    | (vn,ty)::var_env ->
        if vn = n then
          ty
        else
          assoc_type n var_env

(** @return the unaliased version of a type. *)
let rec unalias_ctype = function
  | Cty_id ty_name ->
      (try
         match find_type ty_name with
           | Talias ty -> unalias_ctype (ctype_of_otype ty)
           | _ -> Cty_id ty_name
      with Not_found -> Cty_id ty_name)
  | Cty_arr (n, cty) -> Cty_arr (n, unalias_ctype cty)
  | Cty_ptr cty -> Cty_ptr (unalias_ctype cty)
  | cty -> cty

(** Returns the type associated with the lhs [lhs]
    in the environnement [var_env] (which is an association list
    mapping strings to cty).*)
let rec assoc_type_lhs lhs var_env =
  match lhs with
    | Cvar x -> unalias_ctype (assoc_type x var_env)
    | Carray (lhs, _) ->
        let ty = assoc_type_lhs lhs var_env in
        array_base_ctype ty [1]
    | Cderef lhs ->
        (match assoc_type_lhs lhs var_env with
         | Cty_ptr ty -> ty
         | _ -> Error.message no_location Error.Ederef_not_pointer)
    | Cfield(Cderef (Cvar "self"), { name = x }) -> assoc_type x var_env
    | Cfield(x, f) ->
        let ty = assoc_type_lhs x var_env in
        let n = struct_name ty in
        let fields = find_struct n in
        ctype_of_otype (field_assoc f fields)

(** Creates the statement a = [e_1, e_2, ..], which gives a list
    a[i] = e_i.*)
let rec create_affect_lit dest l ty =
  let rec _create_affect_lit dest i = function
    | [] -> []
    | v::l ->
        let stm = create_affect_stm (Carray (dest, Cconst (Ccint i))) v ty in
        stm@(_create_affect_lit dest (i+1) l)
  in
  _create_affect_lit dest 0 l

(** Creates the expression dest <- src (copying arrays if necessary). *)
and create_affect_stm dest src ty =
  match ty with
    | Cty_arr (n, bty) ->
        (match src with
           | Carraylit l -> create_affect_lit dest l bty
           | Clhs src ->
               let x = gen_symbol () in
               [Cfor(x, Cconst (Ccint 0), Cconst (Ccint n),
                     create_affect_stm (Carray (dest, Clhs (Cvar x)))
                       (Clhs (Carray (src, Clhs (Cvar x)))) bty)]
           | _ -> assert false (** TODO: add missing cases eg for records *)
        )
    | Cty_id ln ->
        (match src with
          | Cstructlit (_, ce_list) ->
              let create_affect { f_name = f_name;
                                  Signature.f_type = f_type; } e stm_list =
                let cty = ctype_of_otype f_type in
                create_affect_stm (Cfield (dest, f_name)) e cty @ stm_list in
              List.fold_right2 create_affect (find_struct ln) ce_list []
          | _ -> [Caffect (dest, src)])
    | _ -> [Caffect (dest, src)]

(** Returns the expression to use e as an argument of
    a function expecting a pointer as argument. *)
let address_of e =
(*  try *)
    let lhs = lhs_of_exp e in
    match lhs with
      | Carray _ -> Clhs lhs
      | Cderef lhs -> Clhs lhs
      | _ -> Caddrof lhs
(*  with _ ->
    e  *)

let rec cexpr_of_static_exp se =
  match se.se_desc with
    | Sint i -> Cconst (Ccint i)
    | Sfloat f -> Cconst (Ccfloat f)
    | Sbool b -> Cconst (Ctag (if b then "true" else "false"))
    | Sstring s -> Cconst (Cstrlit s)
    | Sfield _ -> assert false
    | Sconstructor c -> Cconst (Ctag (cname_of_qn c))
    | Sarray sl -> Carraylit (List.map cexpr_of_static_exp sl)
    | Srecord fl ->
        let ty_name =
          match Modules.unalias_type se.se_ty with
            | Types.Tid n -> cname_of_qn n
            | _ -> assert false
        in
          Cstructlit (ty_name,
                     List.map (fun (_, se) -> cexpr_of_static_exp se) fl)
    | Sarray_power(c,n) ->
        let cc = cexpr_of_static_exp c in
          Carraylit (repeat_list cc (int_of_static_exp n)) (* TODO should be recursive *)
    | Svar ln ->
        (try
          let cd = find_const ln in
          cexpr_of_static_exp (Static.simplify QualEnv.empty cd.c_value)
        with Not_found -> assert false)
    | Sop _ ->
        let se' = Static.simplify QualEnv.empty se in
          if se = se' then
            Error.message se.se_loc Error.Estatic_exp_compute_failed
          else
            cexpr_of_static_exp se'
    | Stuple _ -> assert false (** TODO *)


(** [cexpr_of_exp exp] translates the Obj action [exp] to a C expression. *)
let rec cexpr_of_exp var_env exp =
  match exp.e_desc with
    (** Obj expressions that form valid C lhs are translated via clhs_of_exp. *)
    | Epattern _  ->
        Clhs (clhs_of_exp var_env exp)
          (** Constants, the easiest translation. *)
    | Econst lit ->
        cexpr_of_static_exp lit
          (** Operators *)
    | Eop(op, exps) ->
        cop_of_op var_env op exps
          (** Structure literals. *)
    | Estruct (tyn, fl) ->
        let cexps = List.map (fun (_,e) -> cexpr_of_exp var_env e) fl in
        let ctyn = cname_of_qn tyn in
        Cstructlit (ctyn, cexps)
    | Earray e_list ->
        Carraylit (cexprs_of_exps var_env e_list)

and cexprs_of_exps var_env exps =
  List.map (cexpr_of_exp var_env) exps

and cop_of_op_aux op_name cexps = match op_name with
    | { qual = Pervasives; name = op } ->
        begin match op,cexps with
          | "~-", [e] -> Cuop ("-", e)
          | "not", [e] -> Cuop ("!", e)
          | (
              "=" | "<>"
            | "&" | "or"
            | "+" | "-" | "*" | "/"
            | "*." | "/." | "+." | "-." | "%"
            | "<" | ">" | "<=" | ">="), [el;er] ->
              Cbop (copname op, el, er)
          | _ -> Cfun_call(op, cexps)
        end
    | {qual = m; name = op} -> Cfun_call(op,cexps)

and cop_of_op var_env op_name exps =
  let cexps = cexprs_of_exps var_env exps in
  cop_of_op_aux op_name cexps

and clhs_of_lhs var_env l = match l.pat_desc with
  (** Each Obc variable corresponds to a real local C variable. *)
  | Lvar v ->
      let n = name v in
      if List.mem_assoc n var_env then
        let ty = assoc_type n var_env in
        (match ty with
           | Cty_ptr _ -> Cderef (Cvar n)
           | _ -> Cvar n
        )
      else
        Cvar n
  (** Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> Cfield(clhs_of_lhs var_env l, fn)
  | Larray (l, idx) ->
      Carray(clhs_of_lhs var_env l, cexpr_of_exp var_env idx)

and clhss_of_lhss var_env lhss =
  List.map (clhs_of_lhs var_env) lhss

and clhs_of_exp var_env exp = match exp.e_desc with
  | Epattern l -> clhs_of_lhs var_env l
  (** We were passed an expression that is not translatable to a valid C lhs?!*)
  | _ -> invalid_arg "clhs_of_exp: argument not a Var, Mem or Field"

let rec assoc_obj instance obj_env =
  match obj_env with
    | [] -> raise Not_found
    | od :: t ->
        if od.o_ident = instance
        then od
        else assoc_obj instance t

let assoc_cn instance obj_env =
  (assoc_obj (obj_ref_name instance) obj_env).o_class

let is_op = function
  | { qual = Pervasives; name = _ } -> true
  | _ -> false

let out_var_name_of_objn o =
   o ^"_out_st"

(** Creates the list of arguments to call a node. [targeting] is the targeting
    of the called node, [mem] represents the node context and [args] the
    argument list.*)
let step_fun_call var_env sig_info objn out args =
  let rec add_targeting l ads = match l, ads with
    | [], [] -> []
    | e::l, ad::ads ->
        (*this arg is targeted, use a pointer*)
        let e = if Linearity.is_linear ad.a_linearity then address_of e else e in
          e::(add_targeting l ads)
    | _, _ -> assert false
  in
  let args = (add_targeting args sig_info.node_inputs) in
  if sig_info.node_stateful then (
    let mem =
      (match objn with
         | Oobj o -> Cfield (Cderef (Cvar "self"), local_qn (name o))
         | Oarray (o, l) ->
             let l = clhs_of_lhs var_env l in
               Carray (Cfield (Cderef (Cvar "self"), local_qn (name o)), Clhs l)
      ) in
      args@[Caddrof out; Caddrof mem]
  ) else
    args@[Caddrof out]

(** Generate the statement to call [objn].
    [outvl] is a list of lhs where to put the results.
    [args] is the list of expressions to use as arguments.
    [mem] is the lhs where is stored the node's context.*)
let generate_function_call var_env obj_env outvl objn args =
  (** Class name for the object to step. *)
  let classln = assoc_cn objn obj_env in
  let classn = cname_of_qn classln in
  let sig_info = find_value classln in
  let out = Cvar (out_var_name_of_objn classn) in

  let fun_call =
    if is_op classln then
      cop_of_op_aux classln args
    else
      (** The step function takes scalar arguments and its own internal memory
          holding structure. *)
      let args = step_fun_call var_env sig_info objn out args in
      (** Our C expression for the function call. *)
      Cfun_call (classn ^ "_step", args)
  in

  (** Act according to the length of our list. Step functions with
      multiple return values will return a structure, and we care of
      assigning each field to the corresponding local variable. *)
  match outvl with
    | [] -> [Csexpr fun_call]
    | [outv] when is_op classln ->
        let ty = assoc_type_lhs outv var_env in
          create_affect_stm outv fun_call ty
    | _ ->
        (* Remove options *)
        let out_sig = output_names_list sig_info in
        let create_affect outv out_name =
          let ty = assoc_type_lhs outv var_env in
            create_affect_stm outv (Clhs (Cfield (out, local_qn out_name))) ty
        in
          (Csexpr fun_call)::(List.flatten (map2 create_affect outvl out_sig))

(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const var_env dest c =
  match c.se_desc with
    | Svar ln ->
        let se = Static.simplify QualEnv.empty (find_const ln).c_value in
        create_affect_const var_env dest se
    | Sarray_power(c, n) ->
        let x = gen_symbol () in
        [Cfor(x, Cconst (Ccint 0), cexpr_of_static_exp n,
              create_affect_const var_env (Carray (dest, Clhs (Cvar x))) c)]
    | Sarray cl ->
        let create_affect_idx c (i, affl) =
          let dest = Carray (dest, Cconst (Ccint i)) in
            (i - 1, create_affect_const var_env dest c @ affl)
        in
          snd (List.fold_right create_affect_idx cl (List.length cl - 1, []))
    | Srecord f_se_list ->
        let affect_field affl (f, se) =
          let dest_f = Cfield (dest, f) in
            (create_affect_const var_env dest_f se) @ affl
        in
          List.fold_left affect_field [] f_se_list
    | _ -> [Caffect (dest, cexpr_of_static_exp c)]

(** [cstm_of_act obj_env mods act] translates the Obj action [act] to a list of
    C statements, using the association list [obj_env] to map object names to
    class names.  *)
let rec cstm_of_act var_env obj_env act =
  match act with
      (** Cosmetic : cases on boolean values are converted to if statements. *)
    | Acase (c, [({name = "true"}, te); ({ name = "false" }, fe)])
    | Acase (c, [({name = "false"}, fe); ({ name = "true"}, te)]) ->
        let cc = cexpr_of_exp var_env c in
        let cte = cstm_of_act_list var_env obj_env te in
        let cfe = cstm_of_act_list var_env obj_env fe in
        [Cif (cc, cte, cfe)]
    | Acase (c, [({name = "true"}, te)]) ->
        let cc = cexpr_of_exp var_env c in
        let cte = cstm_of_act_list var_env obj_env te in
        let cfe = [] in
        [Cif (cc, cte, cfe)]
    | Acase (c, [({name = "false"}, fe)]) ->
        let cc = Cuop ("!", (cexpr_of_exp var_env c)) in
        let cte = cstm_of_act_list var_env obj_env fe in
        let cfe = [] in
        [Cif (cc, cte, cfe)]


    (** Translation of case into a C switch statement is simple enough: we
        just recursively translate obj expressions and statements to
        corresponding C constructs, and cautiously "shortnamize"
        constructor names. *)
    | Acase (e, cl) ->
        (** [ccl_of_obccl] translates an Obc clause to a C clause. *)
        let ccl =
          List.map
            (fun (c,act) -> cname_of_qn c,
               cstm_of_act_list var_env obj_env act) cl in
        [Cswitch (cexpr_of_exp var_env e, ccl)]

    | Ablock b ->
        cstm_of_act_list var_env obj_env b

    (** For composition of statements, just recursively apply our
        translation function on sub-statements. *)
    | Afor ({ v_ident = x }, i1, i2, act) ->
        [Cfor(name x, cexpr_of_exp var_env i1,
              cexpr_of_exp var_env i2, cstm_of_act_list var_env obj_env act)]

    (** Special case for x = 0^n^n...*)
    | Aassgn (vn, { e_desc = Econst c }) ->
        let vn = clhs_of_lhs var_env vn in
        create_affect_const var_env vn c

    (** Purely syntactic translation from an Obc local variable to a C
        local one, with recursive translation of the rhs expression. *)
    | Aassgn (vn, e) ->
        let vn = clhs_of_lhs var_env vn in
        let ty = assoc_type_lhs vn var_env in
        let ce = cexpr_of_exp var_env e in
        create_affect_stm vn ce ty

    (** Our Aop marks an operator invocation that will perform side effects. Just
        translate to a simple C statement. *)
    | Aop (op_name, args) ->
        [Csexpr (cop_of_op var_env op_name args)]

    (** Reinitialization of an object variable, extracting the reset
        function's name from our environment [obj_env]. *)
    | Acall (name_list, o, Mreset, args) ->
        assert_empty name_list;
        assert_empty args;
        let on = obj_ref_name o in
        let obj = assoc_obj on obj_env in
        let classn = cname_of_qn obj.o_class in
        (match obj.o_size with
           | None ->
             [Csexpr (Cfun_call (classn ^ "_reset",
                [Caddrof (Cfield (Cderef (Cvar "self"), local_qn (name on)))]))]
           | Some size ->
               let x = gen_symbol () in
               let field = Cfield (Cderef (Cvar "self"), local_qn (name on)) in
               let elt = [Caddrof( Carray(field, Clhs (Cvar x)) )] in
                 [Cfor(x, Cconst (Ccint 0), cexpr_of_static_exp size,
                       [Csexpr (Cfun_call (classn ^ "_reset", elt ))] )]
        )

    (** Step functions applications can return multiple values, so we use a
        local structure to hold the results, before allocating to our
        variables. *)
    | Acall (outvl, objn, Mstep, el) ->
        let args = cexprs_of_exps var_env el in
        let outvl = clhss_of_lhss var_env outvl in
        generate_function_call var_env obj_env outvl objn args


and cstm_of_act_list var_env obj_env b =
  let l = List.map cvar_of_vd b.b_locals in
  let var_env = l @ var_env in
  let cstm = List.flatten (List.map (cstm_of_act var_env obj_env) b.b_body) in
    match l with
      | [] -> cstm
      | _ ->
            [Csblock { var_decls = l; block_body = cstm }]

(* TODO needed only because of renaming phase *)
let global_name = ref "";;



(** {2 step() and reset() functions generation *)

let qn_append q suffix =
  { qual = q.qual; name = q.name ^ suffix }

(** Builds the argument list of step function*)
let step_fun_args n md =
  let args = cvarlist_of_ovarlist md.m_inputs in
  let out_arg = [("out", Cty_ptr (Cty_id (qn_append n "_out")))] in
  let context_arg =
    if is_stateful n then
      [("self", Cty_ptr (Cty_id (qn_append n "_mem")))]
    else
      []
  in
    args @ out_arg @ context_arg


(** [fun_def_of_step_fun name obj_env mods sf] returns a C function definition
    [name ^ "_out"] corresponding to the Obc step function [sf]. The object name
    <-> class name mapping [obj_env] is needed to translate internal steps and
    reset calls. A step function can have multiple return values, whereas C does
    not allow such functions. When it is the case, we declare a structure with a
    field by return value. *)
let fun_def_of_step_fun n obj_env mem objs md =
  let fun_name = (cname_of_qn n) ^ "_step" in
  (** Its arguments, translating Obc types to C types and adding our internal
      memory structure. *)
  let args = step_fun_args n md in

  (** Out vars for function calls *)
  let out_vars =
    unique
      (List.map (fun obj -> out_var_name_of_objn (cname_of_qn obj.o_class),
                   Cty_id (qn_append obj.o_class "_out"))
         (List.filter (fun obj -> not (is_op obj.o_class)) objs)) in

  (** The body *)
  let mems = List.map cvar_of_vd (mem@md.m_outputs) in
  let var_env = args @ mems @ out_vars in
  let body = cstm_of_act_list var_env obj_env md.m_body in

  (** Substitute the return value variables with the corresponding
      context field*)
  let map = Csubst.assoc_map_for_fun md in
  let body = List.map (Csubst.subst_stm map) body in

  Cfundef {
    f_name = fun_name;
    f_retty = Cty_void;
    f_args = args;
    f_body = {
      var_decls = out_vars;
      block_body = body
    }
  }

(** [mem_decl_of_class_def cd] returns a declaration for a C structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decl_of_class_def cd =
  (** This one just translates the class name to a struct name following the
      convention we described above. *)
  let struct_field_of_obj_dec l od =
    if is_stateful od.o_class then
      let ty = Cty_id (qn_append od.o_class "_mem") in
      let ty = match od.o_size with
        | Some se -> Cty_arr (int_of_static_exp se, ty)
        | None -> ty in
        (name od.o_ident, ty)::l
    else
      l
  in
    if is_stateful cd.cd_name then (
      (** Fields corresponding to normal memory variables. *)
      let mem_fields = List.map cvar_of_vd cd.cd_mems in
      (** Fields corresponding to object variables. *)
      let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.cd_objs in
        [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_mem",
                       mem_fields @ obj_fields)]
    ) else
      []

let out_decl_of_class_def cd =
  (** Fields corresponding to output variables. *)
  let step_m = find_step_method cd in
  let out_fields = List.map cvar_of_vd step_m.m_outputs in
    [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_out", out_fields)]

(** [reset_fun_def_of_class_def cd] returns the defintion of the C function
    tasked to reset the class [cd]. *)
let reset_fun_def_of_class_def cd =
  let body =
    try
      let var_env = List.map cvar_of_vd cd.cd_mems in
      let reset = find_reset_method cd in
      cstm_of_act_list var_env cd.cd_objs reset.m_body
    with Not_found -> [] (* TODO C : nicely deal with stateless objects *)
  in
  Cfundef {
    f_name = (cname_of_qn cd.cd_name) ^ "_reset";
    f_retty = Cty_void;
    f_args = [("self", Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")))];
    f_body = {
      var_decls = [];
      block_body = body;
    }
  }


(** [cdecl_and_cfun_of_class_def cd] translates the class definition [cd] to
    a C program. *)
let cdefs_and_cdecls_of_class_def cd =
  (** We keep the state of our class in a structure, holding both internal
      variables and the state of other nodes. For a class named ["cname"], the
      structure will be called ["cname_mem"]. *)
  let step_m = find_step_method cd in
  let memory_struct_decl = mem_decl_of_class_def cd in
  let out_struct_decl = out_decl_of_class_def cd in
  let step_fun_def = fun_def_of_step_fun cd.cd_name
    cd.cd_objs cd.cd_mems cd.cd_objs step_m in
  (** C function for resetting our memory structure. *)
  let reset_fun_def = reset_fun_def_of_class_def cd in
  let res_fun_decl = cdecl_of_cfundef reset_fun_def in
  let step_fun_decl = cdecl_of_cfundef step_fun_def in
  let (decls, defs) =
    if is_stateful cd.cd_name then
      ([res_fun_decl; step_fun_decl], [reset_fun_def; step_fun_def])
    else
      ([step_fun_decl], [step_fun_def]) in

  memory_struct_decl @ out_struct_decl @ decls,
  defs

(** {2 Type translation} *)


let decls_of_type_decl otd =
  let name = cname_of_qn otd.t_name in
  match otd.t_desc with
    | Type_abs -> [] (*assert false*)
    | Type_alias ty -> [Cdecl_typedef (ctype_of_otype ty, name)]
    | Type_enum nl ->
        let name = !global_name ^ "_" ^ name in
        [Cdecl_enum (name, List.map cname_of_qn nl);
         Cdecl_function (name ^ "_of_string",
                         Cty_id otd.t_name,
                         [("s", Cty_ptr Cty_char)]);
         Cdecl_function ("string_of_" ^ name,
                         Cty_ptr Cty_char,
                         [("x", Cty_id otd.t_name); ("buf", Cty_ptr Cty_char)])]
    | Type_struct fl ->
        let decls = List.map (fun f -> cname_of_qn f.Signature.f_name,
                                ctype_of_otype f.Signature.f_type) fl in
        [Cdecl_struct (name, decls)];;

(** Translates an Obc type declaration to its C counterpart. *)
let cdefs_and_cdecls_of_type_decl otd =
  let name = cname_of_qn otd.t_name in
  match otd.t_desc with
    | Type_abs -> [], [] (*assert false*)
    | Type_alias ty ->
      [], [Cdecl_typedef (ctype_of_otype ty, name)]
    | Type_enum nl ->
        let of_string_fun = Cfundef
          { f_name = name ^ "_of_string";
            f_retty = Cty_id otd.t_name;
            f_args = [("s", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_if t =
                    let t = cname_of_qn t in
                    let funcall = Cfun_call ("strcmp", [Clhs (Cvar "s");
                                                        Cconst (Cstrlit t)]) in
                    let cond = Cbop ("==", funcall, Cconst (Ccint 0)) in
                    Cif (cond, [Creturn (Cconst (Ctag t))], []) in
                  map gen_if nl; }
          }
        and to_string_fun = Cfundef
          { f_name = "string_of_" ^ name;
            f_retty = Cty_ptr Cty_char;
            f_args = [("x", Cty_id otd.t_name); ("buf", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_clause t =
                    let t = cname_of_qn t in
                    let fun_call =
                      Cfun_call ("strcpy", [Clhs (Cvar "buf");
                                            Cconst (Cstrlit t)]) in
                    (t, [Csexpr fun_call]) in
                  [Cswitch (Clhs (Cvar "x"), map gen_clause nl);
                   Creturn (Clhs (Cvar "buf"))]; }
          } in
        ([of_string_fun; to_string_fun],
         [Cdecl_enum (name, List.map cname_of_qn nl);
          cdecl_of_cfundef of_string_fun;
          cdecl_of_cfundef to_string_fun])
    | Type_struct fl ->
        let decls = List.map (fun f -> cname_of_qn f.Signature.f_name,
                                ctype_of_otype f.Signature.f_type) fl in
        let decl = Cdecl_struct (name, decls) in
        ([], [decl])

(** [cfile_list_of_oprog oprog] translates the Obc program [oprog] to a list of
    C source and header files. *)
let cfile_list_of_oprog_ty_decls name oprog =
  let types = Obc_utils.program_types oprog in
  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_type_decl types in

  let (cty_defs, cty_decls) = List.split cdefs_and_cdecls in
  let filename_types = name ^ "_types" in
  let types_h = (filename_types ^ ".h",
                 Cheader (["stdbool"; "assert"; "pervasives"],
                          List.concat cty_decls)) in
  let types_c = (filename_types ^ ".c", Csource (concat cty_defs)) in

  filename_types, [types_h; types_c]

let global_file_header name prog =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_program prog) in
  let dependencies = List.map (fun m -> String.uncapitalize (modul_to_string m)) dependencies in

  let classes = program_classes prog in
  let (decls, defs) =
    List.split (List.map cdefs_and_cdecls_of_class_def classes) in
  let decls = List.concat decls
  and defs = List.concat defs in

  let (ty_fname, ty_files) = cfile_list_of_oprog_ty_decls name prog in

  let header =
    (name ^ ".h", Cheader (ty_fname :: dependencies, decls))
  and source =
    (name ^ ".c", Csource defs) in
  [header; source] @ ty_files
