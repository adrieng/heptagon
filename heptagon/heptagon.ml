(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the internal representation *)
(* $Id$ *)

open Location
open Misc
open Names
open Linearity
open Ident
open Interference_graph
open Static

type inlining_policy =
  | Ino
  | Ione
  | Irec

type ty =
  | Tbase of base_ty
  | Tprod of ty list

and base_ty =
  | Tint | Tfloat | Tbool
  | Tid of longname
  | Tarray of base_ty * size_exp

and exp =
    { e_desc: desc;
      mutable e_ty: ty;
      mutable e_linearity : linearity;
      e_loc: location }

and desc =
  | Econst of const
  | Evar of ident
  | Econstvar of name
  | Elast of ident
  | Etuple of exp list
  | Eapp of app * exp list
  | Efield of exp * longname
  | Estruct of (longname * exp) list
  | Earray of exp list
  | Ereset_mem of ident * exp * ident

and app =
    { mutable a_op : op; (* hange of global name after typing *)
      a_inlined : inlining_policy; (* node to inline or not *)
    }

and op =
  | Epre of const option
  | Efby | Earrow | Eifthenelse | Enode of longname * size_exp list
  | Eevery of longname * size_exp list | Eop of longname * size_exp list
  | Erepeat | Eselect of size_exp list | Eselect_dyn
  | Eupdate of size_exp list
  | Eselect_slice
  | Econcat | Ecopy
  | Eiterator of iterator_name * longname * size_exp list * exp option
  | Efield_update of longname
  | Eflatten of longname | Emake of longname

and const =
  | Cint of int
  | Cfloat of float
  | Cconstr of longname
  | Cconst_array of size_exp * const 

and pat =
  | Etuplepat of pat list
  | Evarpat of ident

type eq =
    { eq_desc : eqdesc;
      mutable eq_statefull : bool;
      eq_loc : location }

and eqdesc =
  | Eautomaton of state_handler list
  | Eswitch of exp * switch_handler list
  | Epresent of present_handler list * block
  | Ereset of eq list * exp
  | Eeq of pat * exp

and block =
    { b_local: var_dec list;
      b_equs: eq list;
      mutable b_defnames: ty Env.t;
      mutable b_statefull: bool;
      b_loc: location; }

and state_handler =
    { s_state : name;
      s_block : block;
      s_until : escape list;
      s_unless : escape list; }

and escape =
    { e_cond : exp;
      e_reset : bool;
      e_next_state : name; }

and switch_handler =
    { w_name : longname;
      w_block : block; }

and present_handler =
    { p_cond : exp;
      p_block : block; }

and var_dec =
    { v_name : ident;
      mutable v_type : base_ty;
      mutable v_linearity : linearity;
      v_last : last;
      v_loc  : location; }

and last = Var | Last of const option

type type_dec =
    { t_name : name;
      t_desc : type_desc;
      t_loc  : location }

and type_desc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of (name * base_ty) list

type contract =
    { c_assume : exp;
      c_enforce : exp;
      c_controllables : var_dec list;
      c_local : var_dec list;
      c_eq : eq list;
    }

type node_dec =
    { n_name      : name;
      n_statefull : bool;
      n_input     : var_dec list;
      n_output    : var_dec list;
      n_local     : var_dec list;
      n_contract  : contract option;
      n_equs      : eq list;
      n_loc       : location; 
      n_states_graph : (name,name) interf_graph; 
      n_params : name list;
      n_params_constraints : size_constr list;
    }

type const_dec =
    { c_name : name;
      c_type : base_ty;
      c_value : size_exp;
      c_loc : location; }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types  : type_dec list;
      p_nodes  : node_dec list;
      p_consts : const_dec list; }

type signature =
    { sig_name    : name;
      sig_inputs  : (name option * base_ty * linearity) list;
      sig_outputs : (name option * base_ty * linearity) list;
      sig_node    : bool;
      sig_safe    : bool;
      sig_params  : name list; }

type interface = interface_decl list

and interface_decl =
    { interf_desc : interface_desc;
      interf_loc  : location }

and interface_desc =
  | Iopen of name
  | Itypedef of type_dec
  | Isignature of signature

let tbool = Tbool

let edesc e = e.e_desc
let eqdesc eq = eq.eq_desc

(* Helper functions to create AST. *)
let pbool = Modname({ qual = "Pervasives"; id = "bool" })
let ptrue = Modname({ qual = "Pervasives"; id = "true" })
let pfalse = Modname({ qual = "Pervasives"; id = "false" })
let por = Modname({ qual = "Pervasives"; id = "or" })
let pint = Modname({ qual = "Pervasives"; id = "int" })
let pfloat = Modname({ qual = "Pervasives"; id = "float" })

let emake desc ty = { e_desc = desc; e_ty = ty; 
		      e_linearity = NotLinear; e_loc = no_location }
let eop op = { a_op = op; a_inlined = Ino }
let tmake name desc = { t_name = name; t_desc = desc; t_loc = no_location }
let eqmake desc = { eq_desc = desc; eq_statefull = true; eq_loc = no_location }

let tybool = Tbase(tbool)
let cfalse = Cconstr(pfalse)
let ctrue = Cconstr(ptrue)

let make_bool desc = emake desc tybool
let bool_var n = make_bool (Evar(n))
let bool_param n =
  { v_name = n; v_type = tbool; v_last = Var; 
    v_loc = no_location; v_linearity = NotLinear }

let dfalse = make_bool (Econst(Cconstr(pfalse)))
let dtrue = make_bool (Econst(Cconstr(ptrue)))

let var n ty = emake (Evar(n)) ty
let param n ty =
  { v_name = n; v_type = ty; v_linearity = NotLinear; 
    v_last = Var; v_loc = no_location }
let fby_state initial e =
  { e with e_desc = Eapp(eop (Epre(Some(Cconstr initial))), [e]) }
let fby_false e = emake (Eapp(eop (Epre(Some(cfalse))), [e])) tybool
let last_false x = emake (Elast(x)) tybool
let ifthenelse e1 e2 e3 = emake (Eapp(eop Eifthenelse, [e1;e2;e3])) e2.e_ty
let rec or_op e1 e2 = { e1 with e_desc = Eapp(eop (Eop(por, [])), [e1; e2]) }
let pair e1 e2 = emake (Etuple([e1;e2])) (Tprod [e1.e_ty;e2.e_ty])
let block defnames eqs =
  { b_local = []; b_equs = eqs; b_defnames = defnames;
    b_statefull = true; b_loc = no_location }
let eq pat e = eqmake (Eeq(pat, e))
let reset eq_list e = eqmake (Ereset(eq_list, e))
let switch e l = eqmake (Eswitch(e, l))

let varpat n = Evarpat(n)

(* Helper functions to work with type*)
let base_type ty =
  match ty with
    | Tbase ty -> ty
    | _ -> assert false

let is_scalar_type ty =
  let pint = Modname({ qual = "Pervasives"; id = "int" }) in
  let pfloat = Modname({ qual = "Pervasives"; id = "float" }) in
  let pbool = Modname({ qual = "Pervasives"; id = "bool" }) in
    match ty with
      | Tbase(Tint) | Tbase(Tfloat) | Tbase(Tbool) -> true
      | Tbase(Tid name_int) when name_int = pint -> true
      | Tbase(Tid name_float) when name_float = pfloat -> true
      | Tbase(Tid name_bool) when name_bool = pbool -> true	  
      | _ -> false 
	
let array_of ty exp =
  Tbase(Tarray (base_type ty, exp))

let const_array_of ty n =
  array_of ty (SConst n)

let op_from_app app =
  match app.a_op with
    | Eop (n,_) -> op_from_app_name n
    | _ -> raise Not_static

let rec size_exp_of_exp e =
  match e.e_desc with 
  | Econstvar n -> SVar n
  | Econst (Cint i) -> SConst i
  | Eapp(app, [e1;e2]) ->
      let op = op_from_app app in
	SOp(op, size_exp_of_exp e1, size_exp_of_exp e2)
  | _ -> raise Not_static

module Vars =
struct
  let rec vars_pat locals acc = function
    | Evarpat(x) ->
        if (IdentSet.mem x locals) or (IdentSet.mem x acc) then
	  acc 
	else 
	  IdentSet.add x acc
    | Etuplepat(pat_list) -> List.fold_left (vars_pat locals) acc pat_list

  let rec left locals acc e =
    match e.e_desc with
      | Eapp({a_op = Epre _},[e]) -> acc
      | Eapp({a_op = Efby}, [e1;e2]) -> left locals acc e1
      | Etuple(e_list) | Eapp({a_op = _}, e_list) | Earray(e_list)->
          List.fold_left (left locals) acc e_list
      | Evar(n) | Ereset_mem (_, _, n) ->
          if (IdentSet.mem n acc) or (IdentSet.mem n locals) then
	    acc 
	  else
	    IdentSet.add n acc
      | Efield(e, _) -> left locals acc e
      | Estruct(f_e_list) ->
          List.fold_left (fun acc (_, e) -> left locals acc e) acc f_e_list
      | Elast _ | Econst _ | Econstvar _  -> acc

  let rec read locals acc eq =
    match eq.eq_desc with
      | Eeq(pat, e) -> left locals acc e
      | Ereset(eq_list, e) ->
          List.fold_left (read locals) (left locals acc e) eq_list
      | Eautomaton(state_handlers) ->
          let escapes locals acc e_list =
            List.fold_left
              (fun acc { e_cond = e } -> left locals acc e) acc e_list in
          List.fold_left
            (fun acc {s_block = b; s_until = e_list1; s_unless = e_list2} ->
               let new_locals, acc = read_and_locals_block locals acc b in
               let acc = escapes new_locals acc e_list1 in
               escapes locals acc e_list2)
            acc state_handlers
      | Eswitch(e, switch_handlers) ->
          List.fold_left
            (fun acc { w_block = b } -> read_block locals acc b)
            (left locals acc e) switch_handlers
      | Epresent(present_handlers, b) ->
          List.fold_left
            (fun acc { p_cond = e; p_block = b } ->
               read_block locals (left locals acc e) b)
            (read_block locals acc b) present_handlers

  and read_and_locals_block locals acc { b_local = l; b_equs = eq_list } =
    let locals =
      List.fold_left
        (fun acc { v_name = n } -> if IdentSet.mem n acc then acc else IdentSet.add n acc)
        locals l in
    locals, List.fold_left (read locals) acc eq_list

  and read_block locals acc b =
    let _, acc = read_and_locals_block locals acc b in acc

  let rec def locals acc eq =
    match eq.eq_desc with
      | Eeq(pat, _) -> vars_pat locals acc pat
      | Eautomaton(state_handler) ->
          List.fold_left
            (fun acc { s_block = b } ->
               def_block locals acc b) acc state_handler
      | Eswitch(_, switch_handler) ->
          List.fold_left
            (fun acc { w_block = b } ->
               def_block locals acc b) acc switch_handler
      | Epresent(present_handler, b) ->
          List.fold_left
            (fun acc { p_block = b } -> def_block locals acc b)
            (def_block locals acc b) present_handler
      | Ereset(eq_list, _) -> def_list locals acc eq_list

  and def_block locals acc ({ b_local = l; b_equs = eq_list }) =
    let locals =
      List.fold_left
        (fun acc { v_name = n } -> if IdentSet.mem n acc then acc else IdentSet.add n acc)
        locals l in
    def_list locals acc eq_list

  and def_list locals acc def_list = List.fold_left (def locals) acc def_list

  let read eq = IdentSet.elements (read IdentSet.empty IdentSet.empty eq)
  let def eq = IdentSet.elements (def IdentSet.empty IdentSet.empty eq)
  let antidep eq = false
  let vars_list pat = IdentSet.elements (vars_pat IdentSet.empty IdentSet.empty pat)
end
