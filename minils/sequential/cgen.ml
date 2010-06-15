(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id$ *)

open Format
open List
open Misc
open Names
open Ident
open Obc
open Modules
open Global
open C
open Location
open Printf

module Error =
struct
  type error =
    | Evar of string
    | Enode of string
    | Eno_unnamed_output

  let message loc kind =
    begin match kind with
      | Evar name ->
          eprintf "%aCode generation : The variable name '%s' is unbound.\n"
            output_location loc 
	    name
      | Enode name ->
          eprintf "%aCode generation : The node name '%s' is unbound.\n"
            output_location loc 
	    name
      | Eno_unnamed_output ->
          eprintf "%aCode generation : Unnamed outputs are not supported. \n"
            output_location loc 	  
    end;
    raise Misc.Error
end

let struct_name = function
  | Heptagon.Tid n -> n
  | _ -> assert false

let cname_of_name' name = match name with
  | Name n -> Name (cname_of_name n)
  | _ -> name

let rec print_list ff print sep l =
  match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
        print ff x;
        fprintf ff "%s@ " sep;
        print_list ff print sep l

(* Function to deal with opened modules set. *)
type world = { mutable opened_modules : S.t }
let world = { opened_modules = S.empty }

let add_opened_module (m:string) = 
  world.opened_modules <- S.add (String.uncapitalize (cname_of_name m)) world.opened_modules
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
    | None -> Error.message no_location Error.Eno_unnamed_output (*TODO fresh*)
  in
    List.map remove_option sig_info.info.outputs

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
  let ty = Merge.translate_btype ty in
  let ty = Translate.translate_type NamesEnv.empty ty in
    ctype_of_otype ty

let cvarlist_of_ovarlist vl =
  let cvar_of_ovar vd =
    let ty = ctype_of_otype vd.v_type in
    let ty = if vd.v_pass_by_ref then pointer_to ty else ty in
      name vd.v_name, ty 
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
  name vd.v_name, ctype_of_otype vd.v_type

(** If idx_list = [e1;..;ep], returns the lhs e[e1]...[ep] *)
let rec csubscript_of_e_list e idx_list = 
  match idx_list with
    | [] -> e
    | idx::idx_list ->
	Carray (csubscript_of_e_list e idx_list, idx)

(** If idx_list = [i1;..;ip], returns the lhs e[i1]...[ip] *)
let csubscript_of_idx_list e idx_list = 
  csubscript_of_e_list e (List.map (fun i -> Cconst (Ccint i)) idx_list)

(** Creates the expression that checks that the indices 
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns 
    e1 <= n1 && .. && ep <= np *)
let rec bound_check_expr idx_list bounds = 
  match idx_list, bounds with
    | [idx], [n] ->
	Cbop ("<", idx, Cconst (Ccint n))
    | idx::idx_list, n::bounds ->
	Cbop ("&", Cbop ("<", idx, Cconst (Ccint n)), 
	      bound_check_expr idx_list bounds)
    | _, _ -> assert false

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
    | [] -> Error.message no_location (Error.Evar n)
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
    | Carray (lhs, idx) -> 
	let ty = assoc_type_lhs lhs var_env in
	  array_base_ctype ty [1]
    | Cderef lhs -> assoc_type_lhs lhs var_env
    | Cfield(Cderef (Cvar "self"), x) -> assoc_type x var_env
    | Cfield(x, f) ->
	let ty = assoc_type_lhs x var_env in
	let { info = { arg = ty_arg; } } = find_field (longname f) in
	let n = struct_name ty_arg in
	let { info = { fields = fields } } = find_struct n in
	  ctype_of_heptty (List.assoc f fields)
    | _ -> Cty_int (*TODO: add more cases*)

(** Creates the expression dest <- src (copying arrays if necessary). *)
let rec create_affect_stm dest src ty =
  match ty  with 
    | Cty_arr (n, bty) ->
	let src = lhs_of_exp src in
	let x = gen_symbol () in
	  [Cfor(x, 0, n, 
		create_affect_stm (Carray (dest, Clhs (Cvar x))) 
		  (Clhs (Carray (src, Clhs (Cvar x)))) bty)]
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
    | Lhs _ | Array_select _  ->
        Clhs (clhs_of_exp var_env exp)
	  (** Constants, the easiest translation. *)
    | Const lit ->
        begin match lit with
          | Cint i -> Cconst (Ccint i)
          | Cfloat f -> Cconst (Ccfloat f)
          | Cconstr c -> Cconst (Ctag (shortname c))
	  | Carray(n,c) -> 
	      let cc = cexpr_of_exp var_env (Const c) in
		Carraylit (repeat_list cc n)
        end
      (** Operators *)
    | Op(op, exps) ->
        cop_of_op var_env op exps
	  (** Structure literals. *)
    | Struct (tyn, fl) ->
        let cexps = List.map (fun (_,e) -> cexpr_of_exp var_env e) fl in
	let ctyn = shortname tyn in
	  Cstructlit (ctyn, cexps)
    | Array e_list ->
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
      let ty = assoc_type n var_env in
	(match ty with
	  | Cty_ptr _ -> Cderef (Cvar n)
	  | _ -> Cvar n
	)
      (** Dereference our [self] struct holding the node's memory. *)
  | Mem v -> Cfield (Cderef (Cvar "self"), name v)
      (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Field (l, fn) -> Cfield(clhs_of_lhs var_env l, shortname fn)
  | Array (l, idx) -> 
      Carray(clhs_of_lhs var_env e, cexpr_of_exp var_env idx)

and clhss_of_lhss var_env lhss =
  List.map (clhs_of_lhs var_env) lhss

and clhs_of_exp var_env exp = match exp with
  | Lhs l -> clhs_of_lhs var_env l
        (** We were passed an expression that is not translatable to a valid C lhs?! *)
  | _ -> invalid_arg "clhs_of_exp: argument not a Var, Mem or Field"

let rec assoc_obj instance obj_env =
  match obj_env with
    | [] -> raise Not_found
    | od :: t ->
        if od.obj = instance
        then od
        else assoc_obj instance t

let assoc_cn instance obj_env =
  (assoc_obj instance obj_env).cls

let is_op = function
  | Modname { qual = "Pervasives"; id = _ } -> true
  | _ -> false

(** Creates the list of arguments to call a node. [targeting] is the targeting of 
    the called node, [mem] represents the node context and [args] the argument list.*)
let step_fun_call sig_info args mem =
  let rec add_targeting i l ads = 
    match l, ads with
    | [] ,[] -> []
    | e::l, ad::ads -> 
	let e =
	  if ad.a_pass_by_ref then 
	    (*this arg is targeted, use a pointer*)
	    address_of e
	  else
	    e
	in
	  e::(add_targeting (i+1) l ads)
    | _ , _ -> assert false
  in 
    (add_targeting 0 args sig_info.inputs)@[Caddrof mem]

(** Generate the statement to call [objn]. 
    [outvl] is a list of lhs where to put the results. 
    [args] is the list of expressions to use as arguments.
    [mem] is the lhs where is stored the node's context.*)
let generate_function_call var_env obj_env outvl objn args mem =
 (** Class name for the object to step. *)
  let classln = assoc_cn objn obj_env in
  let classn = shortname classln in
  let mod_classn, sig_info = node_info classln in

  let fun_call = 
    if is_op classln then
      cop_of_op_aux var_env classln args
    else
      (** The step function takes scalar arguments and its own internal memory
        holding structure. *)
      let args = step_fun_call sig_info.info args mem in
	(** Our C expression for the function call. *)
        Cfun_call (classn ^ "_step", args)
  in

    (** Act according to the length of our list. Step functions with
        multiple return values will return a structure, and we care of
        assigning each field to the corresponding local variable. *)
    match outvl with
      | [] -> [Csexpr fun_call]
      | [vr] when Heptagon.is_scalar_type (List.hd sig_info.info.outputs).a_type ->
	  [Caffect (vr, fun_call)] 
      | _ ->
          (* Remove options *)
          let out_sig = output_names_list sig_info in
          let create_affect outv out_name =
	    let ty = 
	      match outv with 
	      | Cvar x -> assoc_type x var_env 
	      | Carray(Cvar x, _) -> array_base_ctype (assoc_type x var_env) [1]
	      | Carray(Cfield(Cderef (Cvar "self"), x), _) -> 
		  array_base_ctype (assoc_type x var_env) [1]
	      | _ -> Cty_void (*we don't care about the type*)
	    in
              create_affect_stm outv
		(Clhs (Cfield (mem,
                               mod_classn ^ "_" ^ out_name))) ty in
	    (Csexpr fun_call)::(List.flatten (map2 create_affect outvl out_sig))

(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const var_env dest c =
  match c with
    | Carray(n,c) -> 
	let x = gen_symbol () in
	  [ Cfor(x, 0, n, 
		create_affect_const var_env (Carray (dest, Clhs (Cvar x))) c) ]
    | _ -> [Caffect (dest, cexpr_of_exp var_env (Const c))]

let create_field_update x r f v (n,ty) =
  let ty = ctype_of_heptty ty in
  if n = f then 
    create_affect_stm (Cfield(x,n)) v ty
  else
    create_affect_stm (Cfield(x, n)) (Clhs (Cfield(r,n))) ty

(** [cstm_of_act obj_env mods act] translates the Obj action [act] to a list of C
    statements, using the association list [obj_env] to map object names to class
    names.  *)
let rec cstm_of_act var_env obj_env act =
  match act with
    (** Case on boolean values are converted to if instead of switch! *)
    | Case (c, [(Name "true", te); (Name "false", fe)])
    | Case (c, [(Name "false", fe); (Name "true", te)]) ->
        let cc = cexpr_of_exp var_env c in
        let cte = cstm_of_act var_env obj_env te in
        let cfe = cstm_of_act var_env obj_env fe in
        [Cif (cc, cte, cfe)]
    (** Translation of case into a C switch statement is simple enough: we just
        recursively translate obj expressions and statements to corresponding C
        constructs, and cautiously "shortnamize" constructor names. *)
    | Case (e, cl) ->
        (** [ccl_of_obccl] translates an Obc clause to a C clause. *)
        let ccl =
	  List.map (fun (c,act) -> shortname c, cstm_of_act var_env obj_env act) cl in
        [Cswitch (cexpr_of_exp var_env e, ccl)]
    (** For composition of statements, just recursively apply our translation
        function on sub-statements. *)
    | Comp (s1, s2) ->
        let cstm1 = cstm_of_act var_env obj_env s1 in
        let cstm2 = cstm_of_act var_env obj_env s2 in
          cstm1@cstm2
    (** Reinitialization of an object variable, extracting the reset function's
        name from our environment [obj_env]. *)
    | Reinit on ->
	let obj = assoc_obj on obj_env in
        let classn = shortname obj.cls in
	  if obj.n = 1 then
            [Csexpr (Cfun_call (classn ^ "_reset",
				[Caddrof (Cfield (Cderef (Cvar "self"), on))]))]
	  else 
	    let x = gen_symbol () in
	    let field = Cfield (Cderef (Cvar "self"), on) in
	    let elt = [Caddrof( Carray(field, Clhs (Cvar x)) )] in
	      [Cfor(x, 0, obj.n, 
		    [Csexpr (Cfun_call (classn ^ "_reset", elt ))] )]
    (** Special case for x = 0^n^n...*)
    | Assgn (vn, Const c) ->
	let vn = clhs_of_lhs var_env vn in
	  create_affect_const var_env vn c
    (** Purely syntactic translation from an Obc local variable to a C local
        one, with recursive translation of the rhs expression. *)
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
	let mem = Cfield (Cderef (Cvar "self"), objn) in
	  generate_function_call var_env obj_env outvl objn args mem

    | Array_select_dyn (x, e, idx_list, bounds, defv) -> 
	let x = clhs_of_lhs var_env x in
	let ty = assoc_type_lhs x var_env in
	let e = cexpr_of_exp var_env e in
	let cexps = cexprs_of_exps var_env idx_list in
	let defv = cexpr_of_exp var_env defv in
	let c = bound_check_expr cexps bounds in
	  [Cif (c, 
		create_affect_stm x 
		  (Clhs (csubscript_of_e_list (lhs_of_exp e) cexps)) ty,
		create_affect_stm x defv ty)]

    | Array_select_slice (x, e, idx1, idx2) ->
	let x = clhs_of_lhs var_env x in
	let ty = assoc_type_lhs x var_env in
	let e = clhs_of_exp var_env e in
	let y = gen_symbol () in
	let index = Cbop ("+", Cconst (Ccint idx1), Clhs (Cvar y)) in
	  [Cfor(y, 0, idx2 - idx1 + 1, 
		create_affect_stm (Carray(x, index)) 
		  (Clhs (Carray(e, Clhs (Cvar y))))
		  (array_base_ctype ty [1]) )]

    | Array_iterate (outvl, Imap, f, n, e_list) ->
	let x = gen_symbol () in
	let cexps = cexprs_of_exps var_env e_list in
	let cexps = List.map (fun e -> Clhs (Carray(lhs_of_exp e, Clhs (Cvar x)))) cexps in
	let outvl = clhss_of_lhss var_env outvl in
	let outvl = List.map (fun n -> Carray(n, Clhs (Cvar x))) outvl in
	let mem = Carray (Cfield (Cderef (Cvar "self"), f), Clhs (Cvar x)) in
	let fcall = generate_function_call var_env obj_env outvl f cexps mem in
	  [ Cfor (x, 0, n, fcall) ]

    | Array_iterate (outvl, Ifold, f, n, e_list) ->
	let x = gen_symbol () in
	let cexps = cexprs_of_exps var_env e_list in
	  (* Use the accumulator as the last arg *)
	let cexps, acc_init = split_last cexps in
	let cexps = List.map (fun e -> Clhs (Carray(lhs_of_exp e, Clhs (Cvar x)))) cexps in
	let outvl = clhss_of_lhss var_env outvl in
	let mem = Carray (Cfield (Cderef (Cvar "self"), f), Clhs (Cvar x)) in
	  (match outvl with
	     | [] -> 
		 (* the accumulator is targeted, so it does not appear in the result. *)
		 let cexps = cexps@[acc_init] in
		 let fcall = generate_function_call var_env obj_env outvl f cexps mem in
		   [Cfor (x, 0, n, fcall) ]
	     | outvl -> 
		 let cexps = cexps@[Clhs (List.hd outvl)] in 
		 let fcall = generate_function_call var_env obj_env outvl f cexps mem in
		 let ty = assoc_type_lhs (List.hd outvl) var_env in
		   (create_affect_stm (List.hd outvl) acc_init ty) @ [Cfor (x, 0, n, fcall) ]
	  )

   | Array_iterate (outvl, Imapfold, f, n, e_list) ->
	let x = gen_symbol () in
	let cexps = cexprs_of_exps var_env e_list in
	  (* Use the accumulator as the last arg *)
	let cexps, acc_init = split_last cexps in
	let cexps = List.map (fun e -> Clhs (Carray(lhs_of_exp e, Clhs (Cvar x)))) cexps in
	let outvl = clhss_of_lhss var_env outvl in
	let mem = Carray (Cfield (Cderef (Cvar "self"), f), Clhs (Cvar x)) in

	  (* Check if the accumulator is targeted and does not appear in the output. *)
	let _, sig_info = node_info (assoc_cn f obj_env) in	  
	let acc_is_targeted = (is_empty outvl) 
	  or (last_element sig_info.info.inputs).a_pass_by_ref in
	  if acc_is_targeted then (
	    (* no accumulator in output *)
	    let outvl = List.map (fun e -> Carray(e, Clhs (Cvar x))) outvl in
	    let cexps = cexps@[acc_init] in
	    let fcall = generate_function_call var_env obj_env outvl f cexps mem in
	      [Cfor (x, 0, n, fcall) ]
	  ) else (
	    (* use the last output as accumulator *)
	    let outvl = incomplete_map (fun e -> Carray(e, Clhs (Cvar x))) outvl in
	    let cexps = cexps@[(Clhs (last_element outvl))] in 
	    let ty = assoc_type_lhs (last_element outvl) var_env in
	    let fcall = generate_function_call var_env obj_env outvl f cexps mem in
	      (create_affect_stm (last_element outvl) acc_init ty)@[Cfor (x, 0, n, fcall) ] 
	  )

   | Array_concat (x, e1, e2) ->
       let x = clhs_of_lhs var_env x in
       let e1 = clhs_of_exp var_env e1 in
       let e2 = clhs_of_exp var_env e2 in
       let ty1 = assoc_type_lhs e1 var_env in
       let ty2 = assoc_type_lhs e2 var_env in
	 (match ty1, ty2 with
	    | Cty_arr(n1, t1), Cty_arr(n2, t2) ->
		let y1 = gen_symbol () in
		let y2 = gen_symbol () in
		let index = Cbop ("+", Cconst (Ccint n1), Clhs (Cvar y2)) in
		  [Cfor(y1, 0, n1, 
			create_affect_stm (Carray(x, Clhs (Cvar y1))) 
			  (Clhs (Carray(e1, Clhs (Cvar y1))))
			  t1 );
		   Cfor(y2, 0, n2, 
			create_affect_stm (Carray(x, index)) 
			  (Clhs (Carray(e2, Clhs (Cvar y2))))
			  t2 )] 
	    | _, _ -> assert false
	 )

   | Field_update(x, e1, f, e2) -> 
       (* Find the description of the struct type *)
       let { info = { arg = ty_arg; res = ty_res } } = find_field f in
       let n = struct_name ty_arg in
       let { info = { fields = fields } } = find_struct n in
	 (* Translate exps *)
       let f = shortname f in
       let x = clhs_of_lhs var_env x in
       let e1 = clhs_of_exp var_env e1 in
       let e2 = cexpr_of_exp var_env e2 in
	 (* create the final exp*)
	 if x = e1 then ( (* only modify one field *)
	   let ty = ctype_of_heptty (List.assoc f fields) in
	     create_affect_stm  (Cfield(x, f)) e2 ty
	 ) else
	   List.flatten (List.map (create_field_update x e1 f e2) fields)

          (** Well, Nothing translates to no instruction. *)
    | Nothing -> []
      
(** [main_def_of_class_def cd] generated a main() function that repeatedly reads
    data from standard input and then outputs result of [cd.step]. *)
(* TODO: refactor into something more readable. *)
let main_def_of_class_def cd =
  (** Generates scanf statements, conversion to enums and declarations of
      buffers needed for reading enum tags. *)
  let scanf_and_vardecl_of_param vd =
    let (formats, expr, need_buf) = match vd.v_type with
      | Tint -> ("%d", Caddrof (Cvar (name vd.v_name)), None)
      | Tid (Name "int"| Modname {qual="Pervasives";id="int"}) ->
          ("%d", Caddrof (Cvar (name vd.v_name)), None)
      | Tid (Name "bool"| Modname {qual="Pervasives";id="bool"}) ->
          ("%d", Caddrof (Cvar (name vd.v_name)), None)
      | Tfloat -> ("%f", Caddrof (Cvar (name vd.v_name)), None)
          (* TODO: distinguish struct and enums AND switch to sscanf *)
      | Tid ((Name sid) |
                 (Modname { id = sid })) -> ("%s",
                                             Clhs (Cvar ((name vd.v_name) ^ "_buf")),
                                             Some ((name vd.v_name) ^ "_buf", sid)) 
      | Tarray(ty, n) -> assert false
    in
    let scane =
      let puts_arg = Printf.sprintf "%s ? " (name vd.v_name) in
      Csblock { var_decls = [];
                block_body = [Csexpr (Cfun_call ("printf",
                                                 [Cconst (Cstrlit puts_arg)]));
                              Csexpr (Cfun_call ("scanf",
                                                 [Cconst (Cstrlit formats);
                                                  expr]));]; } in
    match need_buf with
      | None -> ([scane], [])
      | Some (bufn, tyn) -> ([scane;
                              Csexpr (Cfun_call (tyn ^ "_of_string",
                                                 [Clhs (Cvar bufn)]))],
                             [(bufn, Cty_arr (20, Cty_char))]) in
  let (scanf_calls, scanf_decls) =
    split (map scanf_and_vardecl_of_param cd.step.inp) in
  (** Generates printf statements and buffer declarations needed for printing
      resulting values of enum types. *)
  let printf_and_vardecl_of_result f vd =
    let (formats, expr, need_buf) = match vd.v_type with
      | Tint -> ("%d", f vd.v_name, None)
      | Tfloat -> ("%f", f vd.v_name, None)
      | Tid (Name "bool"| Modname {qual="Pervasives"; id="bool"}) ->
          ("%d", f vd.v_name, None)
      | Tid (Name "int"| Modname {qual="Pervasives"; id="int"}) ->
          ("%d", f vd.v_name, None)
      | Tid (Name sid | Modname {id = sid}) ->
          ("%s", Cfun_call ("string_of_" ^ sid,
                            [f vd.v_name;
                             Clhs (Cvar ((name vd.v_name) ^ "_buf"))]), Some (sid)) 
      | Tarray (ty, n) -> assert false
    in
    (Csexpr (Cfun_call ("printf",
                        [Cconst (Cstrlit ("=> " ^ formats ^ "\\t")); expr])),
     match need_buf with
       | None -> []
       | Some id -> [((name vd.v_name) ^ "_buf", Cty_arr (20, Cty_char))]) in
  let (printf_calls, printf_decls) =
    split (map (printf_and_vardecl_of_result
                  (fun n -> match cd.step.out with
                     | [vd] -> Clhs (Cvar "res")
                     | _ -> Clhs (Cfield (Cvar "res", name n)))) cd.step.out) in
  let cinp = cvarlist_of_ovarlist cd.step.inp in
  let cout =
    begin match cd.step.out with
      | [] -> []
      | [vd] -> [("res", ctype_of_otype vd.v_type)]
      | _ -> [("res", Cty_id (cd.cl_id ^ "_res"))]
    end in
  let varlist =
    ("mem", Cty_id (cd.cl_id ^ "_mem"))
    :: cinp
    @ cout
    @ concat scanf_decls
    @ concat printf_decls in
  (** The main function loops (while (1) { ... }) reading arguments for our node
      and prints the results. *)
  let body =
    let funcall =
      let args =
        map (fun vd -> Clhs (Cvar (name vd.v_name))) cd.step.inp
        @ [Caddrof (Cvar ("mem"))] in
      Cfun_call (cd.cl_id ^ "_step", args) in
    concat scanf_calls
    @ [Caffect (Cvar "res", funcall)]
    @ printf_calls
    @ [Csexpr (Cfun_call ("puts", [Cconst (Cstrlit "")]));
       Csexpr (Cfun_call ("fflush", [Clhs (Cvar "stdout")]))] in
  (** Do not forget to initialize memory via reset. *)
  let init_mem =
    Csexpr (Cfun_call (cd.cl_id ^ "_reset", [Caddrof (Cvar "mem")])) in
  Cfundef {
    f_name = "main";
    f_retty = Cty_int;
    f_args = [("argc", Cty_int); ("argv", Cty_ptr (Cty_ptr Cty_char))];
    f_body = {
      var_decls = varlist;
      block_body = [init_mem;
                    Cwhile (Cconst (Ccint 1), body)];
    }
  }

(** Builds the argument list of step function*)
let step_fun_args n sf = 
  let args = cvarlist_of_ovarlist sf.inp in
    args
      @[("self", Cty_ptr (Cty_id (n ^ "_mem")))]

(** [fun_def_of_step_fun name obj_env mods sf] returns a C function definition
    [name ^ "_out"] corresponding to the Obc step function [sf]. The object name
    <-> class name mapping [obj_env] is needed to translate internal steps and
    reset calls. A step function can have multiple return values, whereas C does
    not allow such functions. When it is the case, we declare a structure with a
    field by return value. A scalar result is directly returned. *)
let fun_def_of_step_fun name obj_env mem sf =
  let fun_name = name ^ "_step" in
  (** Its arguments, translating Obc types to C types and adding our internal
      memory structure. *)
  let args = step_fun_args name sf in
  (** Its normal local variables. *)
  let local_vars = List.map cvar_of_vd sf.local in
  (** Local variables containing return values. *)
  let ret_vars =
    if List.length sf.out = 1 && Obc.is_scalar_type (List.hd sf.out) then
      List.map cvar_of_vd sf.out
    else
      []
  in

  (** Return type, depending on the number of return values of our function. *)
  let retty =
    match sf.out with
      | [] -> Cty_void
      | [v] -> 
	  if Obc.is_scalar_type v then
	    ctype_of_otype v.v_type
	  else 
	    Cty_void
      | _ -> Cty_void in
  (** Controllable variables valuations *)
  let use_ctrlr, ctrlr_calls =
    match sf.controllables with
    | [] -> false, []
    | c_list ->
	let args_inputs_state =
	  List.map (fun (arg_name,_) -> Clhs(Cvar(arg_name))) args in
	let addr_controllables =
	  List.map (fun { v_name = c_name } -> Caddrof(Cvar(Ident.name c_name))) c_list in
	let args_ctrlr =
	  args_inputs_state @ addr_controllables in
	let funname = name ^ "_controller" in
	let funcall = Cfun_call(funname,args_ctrlr) in
	true,
	[Csexpr(funcall)] in
  (** The body *)
  let mems = List.map cvar_of_vd (mem@sf.out) in
  let var_env = args @ mems @ local_vars in
  let body = cstm_of_act var_env obj_env sf.bd in

  (** Our epilogue: affect each local variable holding a return value to
      the correct structure field. *)
  let epilogue = match sf.out with
    | [] -> []
    | [vd] when Obc.is_scalar_type (List.hd sf.out) -> 
	[Creturn (Clhs (Cvar (Ident.name vd.v_name)))] 
    | out -> [] in  

 (** Substitute the return value variables with the corresponding
  context field*)
  let map = Csubst.assoc_map_for_fun sf in
  let body = List.map (Csubst.subst_stm map) (body@epilogue) in

  use_ctrlr,
  Cfundef {
    f_name = fun_name;
    f_retty = retty;
    f_args = args;
    f_body = {
      var_decls = ret_vars @ local_vars;
      block_body = ctrlr_calls @ body
    }
  }

(** [mem_decl_of_class_def cd] returns a declaration for a C structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decl_of_class_def cd =
  (** This one just translates the class name to a struct name following the
      convention we described above. *)
  let struct_field_of_obj_dec l od =
    if is_op od.cls then
      l
    else
      let clsname = shortname od.cls in
      let ty = Cty_id ((cname_of_name clsname) ^ "_mem") in
      let ty = if od.n <> 1 then Cty_arr (od.n, ty) else ty in 
	(od.obj, ty)::l
  in
	
  (** Fields corresponding to normal memory variables. *)
  let mem_fields = List.map cvar_of_vd cd.mem in
  (** Fields corresponding to object variables. *)
  let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.objs in
  (** Fields corresponding to output variables. *) 
  let out_fields =
    if (List.length cd.step.out) <> 1 or
      not (Obc.is_scalar_type (List.hd cd.step.out)) then 
	List.map cvar_of_vd cd.step.out
    else
      []
  in
    Cdecl_struct (cd.cl_id ^ "_mem", mem_fields @ obj_fields @ out_fields)

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
  (** Our main() function will be generated only if the current class definition
      corresponds to the simulation_node. *)
  let main_def = match !simulation_node with
    | Some nn when nn = cd.cl_id -> [main_def_of_class_def cd]
    | _ -> [] in
  let obj_env =
    List.map (fun od -> { od with cls = cname_of_name' od.cls }) cd.objs in
  let use_ctrlr,step_fun_def
    = fun_def_of_step_fun cd.cl_id obj_env cd.mem cd.step in
  (** C function for resetting our memory structure. *)
  let reset_fun_def = reset_fun_def_of_class_def cd in
  let res_fun_decl = cdecl_of_cfundef reset_fun_def in
  let step_fun_decl = cdecl_of_cfundef step_fun_def in
  memory_struct_decl,
  use_ctrlr,
  ([res_fun_decl;step_fun_decl],
   reset_fun_def :: step_fun_def :: main_def)

let decls_of_type_decl otd =
  let name = otd.t_name in
  match otd.t_desc with
    | Type_abs -> [] (*assert false*)
    | Type_enum nl ->
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
    let mem_cdecl,use_ctrlr,(cdecls, cdefs) = cdefs_and_cdecls_of_class_def cd in
      
    let cfile_mem = cfile_name ^ "_mem" in
      add_opened_module cfile_mem;
      if use_ctrlr then 
	add_opened_module (cfile_name ^ "_controller");
      remove_opened_module name;
      
    let acc_cfiles = acc_cfiles @
      [ (cfile_mem ^ ".h", Cheader (get_opened_modules (),[mem_cdecl]));
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
    let _,s = fun_def_of_step_fun cd.cl_id cd.objs cd.mem cd.step in
	   cdecl_of_cfundef s 
  in
    reset_opened_modules ();
    List.iter add_opened_module prog.o_opened;
    
    let ty_decls = List.map decls_of_type_decl prog.o_types in
    let ty_decls = List.concat ty_decls in
    let mem_step_fun_decls = List.map mem_decl_of_class_def prog.o_defs in
    let reset_fun_decls = 
      List.map (fun cd -> cdecl_of_cfundef (reset_fun_def_of_class_def cd)) prog.o_defs in
    let step_fun_decls = List.map step_fun_decl prog.o_defs in
      
      (name ^ ".h", Cheader (get_opened_modules (),
                             ty_decls
                             @ mem_step_fun_decls
                             @ reset_fun_decls
                             @ step_fun_decls))
	
(******************************)

let sanitize_identifier modname id = match id with
  | "bool" -> "bool" | "int" -> "int" | "float" -> "float"
  | "true" -> "true" | "false" -> "false"
  | op   -> modname ^ "_" ^ cname_of_name op

let translate name prog =
  let modname = (Filename.basename name) in
  let prog =
    Rename.rename_program (sanitize_identifier (String.capitalize modname)) prog in
  begin match !simulation_node with
    | None -> ()
    | Some s -> simulation_node := Some (String.capitalize name ^ "_" ^ s)
  end;
  let res =
    (global_file_header modname prog) :: (cfile_list_of_oprog modname prog) in
  if !Misc.verbose then Printf.printf "Translation into C code done.\n";
  res
