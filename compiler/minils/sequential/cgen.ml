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
open Ident
open Obc
open Modules
open Signature
open C
open Location
open Printf

module Error =
struct
  type error =
    | Evar of string
    | Enode of string
    | Eno_unnamed_output
    | Ederef_not_pointer

  let message loc kind = (match kind with
    | Evar name ->
        eprintf "%aCode generation : The variable name '%s' is unbound.\n"
          output_location loc name
    | Enode name ->
        eprintf "%aCode generation : The node name '%s' is unbound.\n"
          output_location loc name
    | Eno_unnamed_output ->
        eprintf "%aCode generation : Unnamed outputs are not supported.\n"
          output_location loc
    | Ederef_not_pointer ->
        eprintf "%aCode generation : Trying to deference a non pointer type.\n"
          output_location loc );
    raise Misc.Error
end

let rec struct_name ty =
  match ty with
  | Cty_id n -> n
  | _ -> assert false

let cname_of_name' name = match name with
  | Name n -> Name (cname_of_name n)
  | _ -> name

(* Functions to deal with opened modules set. *)
type world = { mutable opened_modules : S.t }
let world = { opened_modules = S.empty }

let add_opened_module (m:string) =
  world.opened_modules <-
    S.add (String.uncapitalize (cname_of_name m)) world.opened_modules
let get_opened_modules () =
  S.elements  world.opened_modules
let remove_opened_module (m:string) =
  world.opened_modules <- S.remove m world.opened_modules
let reset_opened_modules () =
  world.opened_modules <- S.empty

let shortname = function
  | Name(n) -> n
  | Modname(q) ->
      if q.qual <> "Pervasives" then
        add_opened_module q.qual;
      q.id

(** Returns the information concerning a node given by name. *)
let node_info classln =
  match classln with
    | Modname {qual = modname; id = modname_name } ->
        begin try
          modname, find_value (Modname({qual = modname;
                                        id = modname_name }))
        with Not_found ->
          (* name might be of the form Module.name, remove the module name*)
          let ind_name = (String.length modname) + 1 in
          let name = String.sub modname_name ind_name
            ((String.length modname_name)-ind_name) in
          begin try
            modname, find_value (Modname({qual = modname;
                                          id = name }))
          with Not_found ->
            Error.message no_location (Error.Enode name)
          end
        end
    | Name n ->
        Error.message no_location (Error.Enode n)

let output_names_list sig_info =
  let remove_option ad = match ad.a_name with
    | Some n -> n
    | None -> Error.message no_location Error.Eno_unnamed_output
  in
  List.map remove_option sig_info.info.node_outputs

let is_statefull n =
  try
    let _, sig_info = node_info n in
      sig_info.info.node_statefull
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
    | Tint -> Cty_int
    | Tfloat -> Cty_float
    | Tbool -> Cty_int
    | Tid id ->
        begin match shortname id with
            (* standard C practice: use int as boolean type. *)
          | "bool" -> Cty_int
          | "int" -> Cty_int
          | "float" -> Cty_float
          | id -> Cty_id id
        end
    | Tarray(ty, n) ->
        Cty_arr(n, ctype_of_otype ty)

let ctype_of_heptty ty =
  let ty = Mls2obc.translate_type NamesEnv.empty ty in
  ctype_of_otype ty

let cvarlist_of_ovarlist vl =
  let cvar_of_ovar vd =
    let ty = ctype_of_otype vd.v_type in
    name vd.v_ident, ty
  in
  List.map cvar_of_ovar vl

let copname = function
  | "="  -> "==" | "<>" -> "!=" | "&"  -> "&&" | "or" -> "||" | "+" -> "+"
  | "-" -> "-" | "*" -> "*" | "/" -> "/" | "*." -> "*" | "/." -> "/"
  | "+." -> "+" | "-." -> "-" | "<"  -> "<" | ">"  -> ">" | "<=" -> "<="
  | ">=" -> ">="
  | "~-" -> "-" | "not" -> "!"
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
        [Cfor(x, 0, n,
              copy_array (Carray (src, Clhs (Cvar x)))
                (Carray (dest, Clhs (Cvar x))) bounds)]

(** Returns the type associated with the name [n]
    in the environnement [var_env] (which is an association list
    mapping strings to cty). *)
let rec assoc_type n var_env =
  match var_env with
    | [] -> (*Error.message no_location (Error.Evar n)*)assert false
    | (vn,ty)::var_env ->
        if vn = n then
          ty
        else
          assoc_type n var_env

(** Returns the type associated with the lhs [lhs]
    in the environnement [var_env] (which is an association list
    mapping strings to cty).*)
let rec assoc_type_lhs lhs var_env =
  match lhs with
    | Cvar x -> assoc_type x var_env
    | Carray (lhs, _) ->
        let ty = assoc_type_lhs lhs var_env in
        array_base_ctype ty [1]
    | Cderef lhs ->
        (match assoc_type_lhs lhs var_env with
         | Cty_ptr ty -> ty
         | _ -> Error.message no_location Error.Ederef_not_pointer)
    | Cfield(Cderef (Cvar "self"), x) -> assoc_type x var_env
    | Cfield(x, f) ->
        let ty = assoc_type_lhs x var_env in
        let n = struct_name ty in
        let { info = fields } = find_struct (longname n) in
        ctype_of_heptty (field_assoc (Name f) fields)

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
  match ty  with
    | Cty_arr (n, bty) ->
        (match src with
           | Carraylit l -> create_affect_lit dest l bty
           | Clhs src ->
               let x = gen_symbol () in
               [Cfor(x, 0, n,
                     create_affect_stm (Carray (dest, Clhs (Cvar x)))
                       (Clhs (Carray (src, Clhs (Cvar x)))) bty)]
        )
    | _ -> [Caffect (dest, src)]

(** Returns the expression to use e as an argument of
    a function expecting a pointer as argument. *)
let address_of e =
  try
    let lhs = lhs_of_exp e in
    match lhs with
      | Carray _ -> Clhs lhs
      | Cderef lhs -> Clhs lhs
      | _ -> Caddrof lhs
  with _ ->
    e

(** [cexpr_of_exp exp] translates the Obj action [exp] to a C expression. *)
let rec cexpr_of_exp var_env exp =
  match exp with
    (** Obj expressions that form valid C lhs are translated via clhs_of_exp. *)
    | Lhs _  ->
        Clhs (clhs_of_exp var_env exp)
          (** Constants, the easiest translation. *)
    | Const lit ->
        (match lit with
          | Cint i -> Cconst (Ccint i)
          | Cfloat f -> Cconst (Ccfloat f)
          | Cconstr c -> Cconst (Ctag (shortname c))
          | Obc.Carray(n,c) ->
              let cc = cexpr_of_exp var_env (Const c) in
              Carraylit (repeat_list cc n)
        )
          (** Operators *)
    | Op(op, exps) ->
        cop_of_op var_env op exps
          (** Structure literals. *)
    | Struct_lit (tyn, fl) ->
        let cexps = List.map (fun (_,e) -> cexpr_of_exp var_env e) fl in
        let ctyn = shortname tyn in
        Cstructlit (ctyn, cexps)
    | Array_lit e_list ->
        Carraylit (cexprs_of_exps var_env e_list)

and cexprs_of_exps var_env exps =
  List.map (cexpr_of_exp var_env) exps

and cop_of_op_aux var_env op_name cexps =
  match op_name with
    | Modname { qual = "Pervasives"; id = op } ->
        begin match op,cexps with
          | "~-", [e] -> Cuop ("-", e)
          | "not", [e] -> Cuop ("!", e)
          | (
              "=" | "<>"
            | "&" | "or"
            | "+" | "-" | "*" | "/"
            | "*." | "/." | "+." | "-."
            | "<" | ">" | "<=" | ">="), [el;er] ->
              Cbop (copname op, el, er)
          | _ -> Cfun_call(op, cexps)
        end
    | Modname {qual = m; id = op} ->
        add_opened_module m;
        Cfun_call(op,cexps)
    | Name(op) ->
        Cfun_call(op,cexps)

and cop_of_op var_env op_name exps =
  let cexps = cexprs_of_exps var_env exps in
  cop_of_op_aux var_env op_name cexps

and clhs_of_lhs var_env = function
  (** Each Obc variable corresponds to a real local C variable. *)
  | Var v ->
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
  | Mem v -> Cfield (Cderef (Cvar "self"), name v)
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Field (l, fn) -> Cfield(clhs_of_lhs var_env l, shortname fn)
  | Array (l, idx) ->
      Carray(clhs_of_lhs var_env l, cexpr_of_exp var_env idx)

and clhss_of_lhss var_env lhss =
  List.map (clhs_of_lhs var_env) lhss

and clhs_of_exp var_env exp = match exp with
  | Lhs l -> clhs_of_lhs var_env l
  (** We were passed an expression that is not translatable to a valid C lhs?!*)
  | _ -> invalid_arg "clhs_of_exp: argument not a Var, Mem or Field"

let rec assoc_obj instance obj_env =
  match obj_env with
    | [] -> raise Not_found
    | od :: t ->
        if od.obj = instance
        then od
        else assoc_obj instance t

let assoc_cn instance obj_env =
  match instance with
    | Context obj
    | Array_context (obj, _) -> (assoc_obj obj obj_env).cls

let is_op = function
  | Modname { qual = "Pervasives"; id = _ } -> true
  | _ -> false

let out_var_name_of_objn o =
   o ^"_out_st"

(** Creates the list of arguments to call a node. [targeting] is the targeting
    of the called node, [mem] represents the node context and [args] the
    argument list.*)
let step_fun_call var_env sig_info objn out args =
  if sig_info.node_statefull then (
    let mem =
      (match objn with
         | Context o -> Cfield (Cderef (Cvar "self"), o)
         | Array_context (o, l) ->
             let l = clhs_of_lhs var_env l in
               Carray (Cfield (Cderef (Cvar "self"), o), Clhs l)
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
  let classn = shortname classln in
  let mod_classn, sig_info = node_info classln in
  let out = Cvar (out_var_name_of_objn classn) in

  let fun_call =
    if is_op classln then
      cop_of_op_aux var_env classln args
    else
      (** The step function takes scalar arguments and its own internal memory
          holding structure. *)
      let args = step_fun_call var_env sig_info.info objn out args in
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
            create_affect_stm outv (Clhs (Cfield (out, out_name))) ty
        in
          (Csexpr fun_call)::(List.flatten (map2 create_affect outvl out_sig))

(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const var_env dest c =
  match c with
    | Obc.Carray(n,c) ->
        let x = gen_symbol () in
        [ Cfor(x, 0, n,
               create_affect_const var_env (Carray (dest, Clhs (Cvar x))) c) ]
    | _ -> [Caffect (dest, cexpr_of_exp var_env (Const c))]

(** [cstm_of_act obj_env mods act] translates the Obj action [act] to a list of
    C statements, using the association list [obj_env] to map object names to
    class names.  *)
let rec cstm_of_act var_env obj_env act =
  match act with
      (** Case on boolean values are converted to if instead of switch! *)
    | Case (c, [(Name "true", te); (Name "false", fe)])
    | Case (c, [(Name "false", fe); (Name "true", te)]) ->
        let cc = cexpr_of_exp var_env c in
        let cte = cstm_of_act var_env obj_env te in
        let cfe = cstm_of_act var_env obj_env fe in
        [Cif (cc, cte, cfe)]

    (** Translation of case into a C switch statement is simple enough: we
        just recursively translate obj expressions and statements to
        corresponding C constructs, and cautiously "shortnamize"
        constructor names. *)
    | Case (e, cl) ->
        (** [ccl_of_obccl] translates an Obc clause to a C clause. *)
        let ccl =
          List.map
            (fun (c,act) -> shortname c, cstm_of_act var_env obj_env act) cl in
        [Cswitch (cexpr_of_exp var_env e, ccl)]

    (** For composition of statements, just recursively apply our
        translation function on sub-statements. *)
    | For (x, i1, i2, act) ->
        [Cfor(name x, i1, i2, cstm_of_act var_env obj_env act)]

    | Comp (s1, s2) ->
        let cstm1 = cstm_of_act var_env obj_env s1 in
        let cstm2 = cstm_of_act var_env obj_env s2 in
        cstm1@cstm2

    (** Reinitialization of an object variable, extracting the reset
        function's name from our environment [obj_env]. *)
    | Reinit on ->
        let obj = assoc_obj on obj_env in
        let classn = shortname obj.cls in
        if obj.size = 1 then
          [Csexpr (Cfun_call (classn ^ "_reset",
                              [Caddrof (Cfield (Cderef (Cvar "self"), on))]))]
        else
          let x = gen_symbol () in
          let field = Cfield (Cderef (Cvar "self"), on) in
          let elt = [Caddrof( Carray(field, Clhs (Cvar x)) )] in
          [Cfor(x, 0, obj.size,
                [Csexpr (Cfun_call (classn ^ "_reset", elt ))] )]

    (** Special case for x = 0^n^n...*)
    | Assgn (vn, Const c) ->
        let vn = clhs_of_lhs var_env vn in
        create_affect_const var_env vn c

    (** Purely syntactic translation from an Obc local variable to a C
        local one, with recursive translation of the rhs expression. *)
    | Assgn (vn, e) ->
        let vn = clhs_of_lhs var_env vn in
        let ty = assoc_type_lhs vn var_env in
        let ce = cexpr_of_exp var_env e in
        create_affect_stm vn ce ty

    (** Step functions applications can return multiple values, so we use a
        local structure to hold the results, before allocating to our
        variables. *)
    | Step_ap (outvl, objn, el) ->
        let args = cexprs_of_exps var_env el in
        let outvl = clhss_of_lhss var_env outvl in
        generate_function_call var_env obj_env outvl objn args

    (** Well, Nothing translates to no instruction. *)
    | Nothing -> []

(* TODO needed only because of renaming phase *)
let global_name = ref "";;



(** {2 step() and reset() functions generation *)



(** Builds the argument list of step function*)
let step_fun_args n sf =
  let args = cvarlist_of_ovarlist sf.inp in
  let out_arg =
    (match sf.out with
       | [] -> []
       | _ -> [("out", Cty_ptr (Cty_id (n ^ "_out")))]
    ) in
  let context_arg =
    if is_statefull (longname n) then
      [("self", Cty_ptr (Cty_id (n ^ "_mem")))]
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
let fun_def_of_step_fun name obj_env mem objs sf =
  let fun_name = name ^ "_step" in
  (** Its arguments, translating Obc types to C types and adding our internal
      memory structure. *)
  let args = step_fun_args name sf in
  (** Its normal local variables. *)
  let local_vars = List.map cvar_of_vd sf.local in

  (** Out vars for function calls *)
  let out_vars =
    List.map (fun obj -> out_var_name_of_objn (shortname obj.cls),
                Cty_id ((cname_of_name (shortname obj.cls)) ^ "_out"))
      (List.filter (fun obj -> not (is_op obj.cls)) objs) in

  (** Controllable variables valuations *)
  let use_ctrlr, ctrlr_calls =
    match sf.controllables with
      | [] -> false, []
      | c_list ->
          let args_inputs_state =
            List.map (fun (arg_name,_) -> Clhs(Cvar(arg_name))) args in
          let addr_controllables =
            let addrof { v_ident = c_name } =
              Caddrof (Cvar (Ident.name c_name)) in
            List.map addrof c_list in
          let args_ctrlr =
            args_inputs_state @ addr_controllables in
          let funname = name ^ "_controller" in
          let funcall = Cfun_call(funname,args_ctrlr) in
          true,
          [Csexpr(funcall)] in
  (** The body *)
  let mems = List.map cvar_of_vd (mem@sf.out) in
  let var_env = args @ mems @ local_vars @ out_vars in
  let body = cstm_of_act var_env obj_env sf.bd in

  (** Substitute the return value variables with the corresponding
      context field*)
  let map = Csubst.assoc_map_for_fun sf in
  let body = List.map (Csubst.subst_stm map) body in

  use_ctrlr,
  Cfundef {
    f_name = fun_name;
    f_retty = Cty_void;
    f_args = args;
    f_body = {
      var_decls = local_vars @ out_vars;
      block_body = ctrlr_calls @ body
    }
  }

(** [mem_decl_of_class_def cd] returns a declaration for a C structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decl_of_class_def cd =
  (** This one just translates the class name to a struct name following the
      convention we described above. *)
  let struct_field_of_obj_dec l od =
    if is_statefull od.cls then
      let clsname = shortname od.cls in
      let ty = Cty_id ((cname_of_name clsname) ^ "_mem") in
      let ty = if od.size <> 1 then Cty_arr (od.size, ty) else ty in
        (od.obj, ty)::l
    else
      l
  in
    if is_statefull (longname cd.cl_id) then (
      (** Fields corresponding to normal memory variables. *)
      let mem_fields = List.map cvar_of_vd cd.mem in
      (** Fields corresponding to object variables. *)
      let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.objs in
        [Cdecl_struct (cd.cl_id ^ "_mem", mem_fields @ obj_fields)]
    ) else
      []

let out_decl_of_class_def cd =
  match cd.step.out with
    | [] -> []
    | out ->
        (** Fields corresponding to output variables. *)
        let out_fields = List.map cvar_of_vd out in
          [Cdecl_struct (cd.cl_id ^ "_out", out_fields)]

(** [reset_fun_def_of_class_def cd] returns the defintion of the C function
    tasked to reset the class [cd]. *)
let reset_fun_def_of_class_def cd =
  let var_env = List.map cvar_of_vd cd.mem in
  let body = cstm_of_act var_env cd.objs cd.reset in
  Cfundef {
    f_name = (cd.cl_id ^ "_reset");
    f_retty = Cty_void;
    f_args = [("self", Cty_ptr (Cty_id (cd.cl_id ^ "_mem")))];
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
  let memory_struct_decl = mem_decl_of_class_def cd in
  let out_struct_decl = out_decl_of_class_def cd in
  let obj_env =
    List.map (fun od -> { od with cls = cname_of_name' od.cls }) cd.objs in
  let use_ctrlr,step_fun_def
    = fun_def_of_step_fun cd.cl_id obj_env cd.mem cd.objs cd.step in
  (** C function for resetting our memory structure. *)
  let reset_fun_def = reset_fun_def_of_class_def cd in
  let res_fun_decl = cdecl_of_cfundef reset_fun_def in
  let step_fun_decl = cdecl_of_cfundef step_fun_def in
  let fun_defs =
    if is_statefull (longname cd.cl_id) then
      ([res_fun_decl; step_fun_decl], [reset_fun_def; step_fun_def])
    else
      ([step_fun_decl], [step_fun_def]) in

  memory_struct_decl @ out_struct_decl,
  use_ctrlr,
  fun_defs



(** {2 Main function generation} *)

(* Unique names for C variables handling step counts. *)
let step_counter = Ident.fresh "step_c"
and max_step = Ident.fresh "step_max"

let assert_node_res cd =
  if List.length cd.step.inp > 0 then
    (Printf.eprintf "Cannot generate run-time check for node %s with inputs.\n"
       cd.cl_id;
     exit 1);
  if (match cd.step.out with
        | [{ v_type = Tbool; }] -> false
        | _ -> true) then
    (Printf.eprintf
       "Cannot generate run-time check for node %s with non-boolean output.\n"
       cd.cl_id;
     exit 1);
  let mem = (name (Ident.fresh ("mem_for_" ^ cd.cl_id)),
             Cty_id (cd.cl_id ^ "_mem")) in
  let reset_i =
    Cfun_call (cd.cl_id ^ "_reset", [Caddrof (Cvar (fst mem))]) in
  let step_i =
    (*
      if (!step()) {
        printf("Node $node failed at step %d.\n", step_count);
        return 1;
      }
    *)
    Cif (Cuop ("!", Cfun_call (cd.cl_id ^ "_step", [Caddrof (Cvar (fst mem))])),
         [Csexpr (Cfun_call ("printf",
                             [Cconst (Cstrlit ("Node \\\"" ^ cd.cl_id
                                               ^ "\\\" failed at step %d.\\n"));
                              Clhs (Cvar (name step_counter))]));
          Creturn (Cconst (Ccint 1))],
         []) in
  (mem, Csexpr reset_i, step_i);;

(** [main_def_of_class_def cd] returns a [(var_list, rst_i, step_i)] where
    [var_list] (resp. [rst_i] and [step_i]) is a list of variables (resp. of
    statements) needed for a main() function calling [cd]. *)
(* TODO: refactor into something more readable. *)
let main_def_of_class_def cd =
  let format_for_type ty = match ty with
    | Tarray _ -> assert false
    | Tint | Tbool -> "%d"
    | Tfloat -> "%f"
    | Tid ((Name sid) | Modname { id = sid }) -> "%s" in

  (** Does reading type [ty] need a buffer? When it is the case,
      [need_buf_for_ty] also returns the type's name. *)
  let need_buf_for_ty ty = match ty with
    | Tarray _ -> assert false
    | Tint | Tfloat | Tbool -> None
    | Tid (Name sid | Modname { id = sid; }) -> Some sid in

  (** Generates scanf statements. *)
  let rec read_lhs_of_ty lhs ty = match ty with
    | Tarray (ty, n) ->
        let iter_var = Ident.name (Ident.fresh "i") in
        let lhs = Carray (lhs, Clhs (Cvar iter_var)) in
        let (reads, bufs) = read_lhs_of_ty lhs ty in
        ([Cfor (iter_var, 0, n, reads)], bufs)
    | _ ->
        let rec mk_prompt lhs = match lhs with
          | Cvar vn -> (vn, [])
          | Carray (lhs, cvn) ->
              let (vn, args) = mk_prompt lhs in
              (vn ^ "[%d]", cvn :: args)
          | _ -> assert false in
        let (prompt, args_format_s) = mk_prompt lhs in
        let scan_exp =
          let printf_s = Printf.sprintf "%s ? " prompt in
          let format_s = format_for_type ty in
          Csblock { var_decls = [];
                    block_body = [
                      Csexpr (Cfun_call ("printf",
                                         Cconst (Cstrlit printf_s)
                                         :: args_format_s));
                      Csexpr (Cfun_call ("scanf",
                                         [Cconst (Cstrlit format_s);
                                          Caddrof lhs])); ]; } in
        match need_buf_for_ty ty with
          | None -> ([scan_exp], [])
          | Some tyn ->
              let varn = Ident.name (Ident.fresh "buf") in
              ([scan_exp;
                Csexpr (Cfun_call (tyn ^ "_of_string",
                                   [Clhs (Cvar varn)]))],
               [(varn, Cty_arr (20, Cty_char))]) in

  (** Generates printf statements and buffer declarations needed for printing
      resulting values of enum types. *)
  let rec write_lhs_of_ty lhs ty = match ty with
    | Tarray (ty, n) ->
        let iter_var = Ident.name (Ident.fresh "i") in
        let lhs = Carray (lhs, Clhs (Cvar iter_var)) in
        let (reads, bufs) = write_lhs_of_ty lhs ty in
        (Cfor (iter_var, 0, n, [reads]), bufs)
    | _ ->
        let varn = Ident.name (Ident.fresh "buf") in
        let format_s = format_for_type ty in
        let nbuf_opt = need_buf_for_ty ty in
        let ep = match nbuf_opt with
          | None -> [Clhs lhs]
          | Some sid -> [Cfun_call ("string_of_" ^ sid,
                                    [Clhs lhs;
                                     Clhs (Cvar varn)])] in
        (Csexpr (Cfun_call ("printf",
                            Cconst (Cstrlit ("=> " ^format_s ^ "\\t"))
                            :: ep)),
         match nbuf_opt with
           | None -> []
           | Some id -> [(varn, Cty_arr (20, Cty_char))]) in

  let (scanf_calls, scanf_decls) =
    let read_lhs_of_ty_for_vd vd =
      read_lhs_of_ty (Cvar (Ident.name vd.v_ident)) vd.v_type in
    split (map read_lhs_of_ty_for_vd cd.step.inp) in

  let (printf_calls, printf_decls) =
    let write_lhs_of_ty_for_vd vd = match cd.step.out with
      | [{ v_type = Tarray _; }] ->
          write_lhs_of_ty (Cfield (Cvar "mem", name vd.v_ident)) vd.v_type
      | [_] -> write_lhs_of_ty (Cvar "res") vd.v_type
      | _ ->
          write_lhs_of_ty (Cfield (Cvar "mem", name vd.v_ident)) vd.v_type in
    split (map write_lhs_of_ty_for_vd cd.step.out) in

  let cinp = cvarlist_of_ovarlist cd.step.inp in
  let cout = match cd.step.out with
    | [{ v_type = Tarray _; }] -> []
    | [vd] -> let vty = ctype_of_otype vd.v_type in [("res", vty)]
    | _ -> [] in
  let varlist =
    ("mem", Cty_id (cd.cl_id ^ "_mem"))
    :: cinp
    @ cout
    @ concat scanf_decls
    @ concat printf_decls in

  (** The main function loops (while (1) { ... }) reading arguments for our node
      and prints the results. *)
  let step_l =
    let funcall =
      let args =
        map (fun vd -> Clhs (Cvar (name vd.v_ident))) cd.step.inp
        @ [Caddrof (Cvar "mem")] in
      Cfun_call (cd.cl_id ^ "_step", args) in
    concat scanf_calls
      (* Our function returns something only when the node has exactly one
         scalar output. *)
    @ ([match cd.step.out with
          | [{ v_type = Tarray _; }] -> Csexpr funcall
          | [_] -> Caffect (Cvar "res", funcall)
          | _ -> Csexpr funcall])
    @ printf_calls
    @ [Csexpr (Cfun_call ("puts", [Cconst (Cstrlit "")]));
       Csexpr (Cfun_call ("fflush", [Clhs (Cvar "stdout")]))] in

  (** Do not forget to initialize memory via reset. *)
  let rst_i =
    Csexpr (Cfun_call (cd.cl_id ^ "_reset", [Caddrof (Cvar "mem")])) in

  (varlist, rst_i, step_l)

(** [main_skel var_list prologue body] generates a C main() function using the
    variable list [var_list], prologue [prologue] and loop body [body]. *)
let main_skel var_list prologue body =
  Cfundef {
    f_name = "main";
    f_retty = Cty_int;
    f_args = [("argc", Cty_int); ("argv", Cty_ptr (Cty_ptr Cty_char))];
    f_body = {
      var_decls =
        (name step_counter, Cty_int) :: (name max_step, Cty_int) :: var_list;
      block_body =
        [
          (*
            step_count = 0;
            max_step = 0;
            if (argc == 2)
              max_step = atoi(argv[1]);
          *)
          Caffect (Cvar (name step_counter), Cconst (Ccint 0));
          Caffect (Cvar (name max_step), Cconst (Ccint 0));
          Cif (Cbop ("==", Clhs (Cvar "argc"), Cconst (Ccint 2)),
               [Caffect (Cvar (name max_step),
                         Cfun_call ("atoi",
                                    [Clhs (Carray (Cvar "argv",
                                                   Cconst (Ccint 1)))]))], []);
        ]
        @ prologue
          (* while (!max_step || step_c < max_step) *)
        @ [
          Cwhile (Cbop ("||",
                        Cuop ("!", Clhs (Cvar (name max_step))),
                        Cbop ("<",
                              Clhs (Cvar (name step_counter)),
                              Clhs (Cvar (name max_step)))),
                  (* step_counter = step_counter + 1; *)
                  Caffect (Cvar (name step_counter),
                           Cbop ("+",
                                 Clhs (Cvar (name step_counter)),
                                 Cconst (Ccint 1)))
                  :: body)
        ];
    }
  }

let mk_main p = match (!Misc.simulation_node, !Misc.assert_nodes) with
  | (None, []) -> []
  | (_, n_names) ->
      let find_class n =
        try List.find (fun cd -> cd.cl_id = n) p.o_defs
        with Not_found ->
          Printf.eprintf "Unknown node %s.\n" n;
          exit 1 in

      let a_classes = List.map find_class n_names in

      let (var_l, res_l, step_l) =
        let add cd (var_l, res_l, step_l) =
          let (var, res, step) = assert_node_res cd in
          (var :: var_l, res :: res_l, step :: step_l) in
        List.fold_right add a_classes ([], [], []) in

      let (deps, var_l, res_l, step_l) =
        (match !Misc.simulation_node with
           | None -> (n_names, var_l, res_l, step_l)
           | Some n ->
               let (nvar_l, res, nstep_l) =
                 main_def_of_class_def (find_class n) in
               (n :: n_names, nvar_l @ var_l,
                res :: res_l, nstep_l @ step_l)) in

      [("_main.c", Csource [main_skel var_l res_l step_l]);
       ("_main.h", Cheader (deps, []))];
;;

(** {2 Type translation} *)


let decls_of_type_decl otd =
  let name = otd.t_name in
  match otd.t_desc with
    | Type_abs -> [] (*assert false*)
    | Type_enum nl ->
        let name = !global_name ^ "_" ^ name in
        [Cdecl_enum (otd.t_name, nl);
         Cdecl_function (name ^ "_of_string",
                         Cty_id name,
                         [("s", Cty_ptr Cty_char)]);
         Cdecl_function ("string_of_" ^ name,
                         Cty_ptr Cty_char,
                         [("x", Cty_id name); ("buf", Cty_ptr Cty_char)])]
    | Type_struct fl ->
        let decls = List.map (fun (n,ty) -> n, ctype_of_otype ty) fl in
        [Cdecl_struct (otd.t_name, decls)];;

(** Translates an Obc type declaration to its C counterpart. *)
let cdefs_and_cdecls_of_type_decl otd =
  let name = otd.t_name in
  match otd.t_desc with
    | Type_abs -> [], [] (*assert false*)
    | Type_enum nl ->
        let of_string_fun = Cfundef
          { f_name = name ^ "_of_string";
            f_retty = Cty_id name;
            f_args = [("s", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_if t =
                    let funcall = Cfun_call ("strcmp", [Clhs (Cvar "s");
                                                        Cconst (Cstrlit t)]) in
                    let cond = Cbop ("==", funcall, Cconst (Ccint 0)) in
                    Cif (cond, [Creturn (Cconst (Ctag t))], []) in
                  map gen_if nl; }
          }
        and to_string_fun = Cfundef
          { f_name = "string_of_" ^ name;
            f_retty = Cty_ptr Cty_char;
            f_args = [("x", Cty_id name); ("buf", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_clause t =
                    let fun_call =
                      Cfun_call ("strcpy", [Clhs (Cvar "buf");
                                            Cconst (Cstrlit t)]) in
                    (t, [Csexpr fun_call]) in
                  [Cswitch (Clhs (Cvar "x"), map gen_clause nl);
                   Creturn (Clhs (Cvar "buf"))]; }
          } in
        ([of_string_fun; to_string_fun],
         [Cdecl_enum (otd.t_name, nl); cdecl_of_cfundef of_string_fun;
          cdecl_of_cfundef to_string_fun])
    | Type_struct fl ->
        let decls = List.map (fun (n,ty) -> n, ctype_of_otype ty) fl in
        let decl = Cdecl_struct (otd.t_name, decls) in
        ([], [decl])

(** [cfile_list_of_oprog oprog] translates the Obc program [oprog] to a list of
    C source and header files. *)
let cfile_list_of_oprog name oprog =
  let opened_modules = oprog.o_opened in

  let header_and_source_of_class_def (deps,acc_cfiles) cd =
    reset_opened_modules ();
    List.iter add_opened_module opened_modules;
    List.iter add_opened_module deps;

    let cfile_name = String.uncapitalize cd.cl_id in
    let struct_decl,use_ctrlr,(cdecls, cdefs) =
      cdefs_and_cdecls_of_class_def cd in

    let cfile_mem = cfile_name ^ "_mem" in
    add_opened_module cfile_mem;
    if use_ctrlr then
      add_opened_module (cfile_name ^ "_controller");
    remove_opened_module name;

    let acc_cfiles = acc_cfiles @
      [ (cfile_mem ^ ".h", Cheader (get_opened_modules (), struct_decl));
        (cfile_name ^ ".h", Cheader (get_opened_modules (), cdecls));
        (cfile_name ^ ".c", Csource cdefs)] in
    deps@[cfile_name],acc_cfiles in

  reset_opened_modules ();
  List.iter add_opened_module opened_modules;
  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_type_decl oprog.o_types in
  remove_opened_module name;

  let (cty_defs, cty_decls) = List.split (List.rev cdefs_and_cdecls) in
  let filename_types = name ^ "_types" in
  let types_h = (filename_types ^ ".h",
                 Cheader (get_opened_modules (), concat cty_decls)) in
  let types_c = (filename_types ^ ".c", Csource (concat cty_defs)) in
  let _,cfiles =
    List.fold_left
      header_and_source_of_class_def
      ([filename_types],[types_h;types_c])
      oprog.o_defs in
  cfiles

let global_file_header name prog =
  let step_fun_decl cd =
    let _,s = fun_def_of_step_fun cd.cl_id cd.objs cd.mem cd.objs cd.step in
    cdecl_of_cfundef s
  in
  reset_opened_modules ();
  List.iter add_opened_module prog.o_opened;

  let ty_decls = List.map decls_of_type_decl prog.o_types in
  let ty_decls = List.concat ty_decls in
  let mem_step_fun_decls = List.flatten (List.map mem_decl_of_class_def
                                           prog.o_defs) in
  let reset_fun_decls =
    let cdecl_of_reset_fun cd =
      cdecl_of_cfundef (reset_fun_def_of_class_def cd) in
    List.map cdecl_of_reset_fun prog.o_defs in
  let step_fun_decls = List.map step_fun_decl prog.o_defs in

  (name ^ ".h", Cheader (get_opened_modules (),
                         ty_decls
                         @ mem_step_fun_decls
                         @ reset_fun_decls
                         @ step_fun_decls))

(******************************)

let translate name prog =
  let modname = (Filename.basename name) in
  global_name := String.capitalize modname;
  (global_file_header modname prog) :: (mk_main prog)
  @ (cfile_list_of_oprog modname prog)
