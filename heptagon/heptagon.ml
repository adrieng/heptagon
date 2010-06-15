(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the internal representation *)
open Location
open Misc
open Names
open Ident  
open Static
open Signature


type iterator_name = 
  | Imap
  | Ifold
  | Imapfold

type exp =
  { e_desc : desc; e_ty : ty; e_loc : location }

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

  and app =
  { a_op : op; }

  and op =
  | Epre of const option
  | Efby
  | Earrow
  | Eifthenelse
  | Earray_op of array_op
  | Ecall of op_desc * exp option (** [op_desc] is the function called
                                      [exp option] is the optional reset condition *)
    
  and array_op =
  | Erepeat
  | Eselect of size_exp list
  | Eselect_dyn
  | Eupdate of size_exp list
  | Eselect_slice
  | Econcat
  | Eiterator of iterator_name * op_desc * exp option
  
  and op_desc = longname * size_exp list * op_kind
  and op_kind = | Eop | Enode

  and const =
  | Cint of int
  | Cfloat of float
  | Cconstr of longname
  | Carray of size_exp * const

  and pat =
  | Etuplepat of pat list | Evarpat of ident

type eq =
  { eq_desc : eqdesc; eq_statefull : bool; eq_loc : location }

  and eqdesc =
  | Eautomaton of state_handler list
  | Eswitch of exp * switch_handler list
  | Epresent of present_handler list * block
  | Ereset of eq list * exp
  | Eeq of pat * exp

  and block =
  { b_local : var_dec list; b_equs : eq list; mutable b_defnames : ty Env.t;
    mutable b_statefull : bool; b_loc : location
  }

  and state_handler =
  { s_state : name; s_block : block; s_until : escape list;
    s_unless : escape list
  }

  and escape =
  { e_cond : exp; e_reset : bool; e_next_state : name
  }

  and switch_handler =
  { w_name : longname; w_block : block
  }

  and present_handler =
  { p_cond : exp; p_block : block
  }

  and var_dec =
  { v_name : ident; mutable v_type : ty; v_last : last; v_loc : location }

  and last =
  | Var | Last of const option

type type_dec =
  { t_name : name; t_desc : type_desc; t_loc : location }

  and type_desc =
  | Type_abs | Type_enum of name list | Type_struct of structure

type contract =
  { c_assume : exp; c_enforce : exp; c_controllables : var_dec list;
    c_local : var_dec list; c_eq : eq list
  }

type node_dec =
  { n_name : name; n_statefull : bool; n_input : var_dec list;
    n_output : var_dec list; n_local : var_dec list;
    n_contract : contract option; n_equs : eq list; n_loc : location;
    n_params : name list;
    n_params_constraints : size_constr list
  }

type const_dec =
  { c_name : name; c_type : ty; c_value : size_exp; c_loc : location }

type program =
  { p_pragmas : (name * string) list; p_opened : name list;
    p_types : type_dec list; p_nodes : node_dec list;
    p_consts : const_dec list
  }

type signature =
  { sig_name : name; sig_inputs : arg list;
    sig_outputs : arg list; sig_params : param list
  }

type interface =
  interface_decl list

  and interface_decl =
  { interf_desc : interface_desc; interf_loc : location
  }

  and interface_desc =
  | Iopen of name | Itypedef of type_dec | Isignature of signature
  
let edesc e = e.e_desc
  
let eqdesc eq = eq.eq_desc
  
(* Helper functions to create AST. *) (*TODO refactor en mk_*)

let emake desc ty =
  { e_desc = desc; e_ty = ty; e_linearity = NotLinear; e_loc = no_location; }
  
let eop op = { a_op = op; a_inlined = Ino; }
  
let tmake name desc = { t_name = name; t_desc = desc; t_loc = no_location; }
  
let eqmake desc =
  { eq_desc = desc; eq_statefull = true; eq_loc = no_location; }
  
let tybool = Tbase tbool
  
let cfalse = Cconstr pfalse
  
let ctrue = Cconstr ptrue
  
let make_bool desc = emake desc tybool
  
let bool_var n = make_bool (Evar n)
  
let bool_param n =
  {
    v_name = n;
    v_type = tbool;
    v_last = Var;
    v_loc = no_location;
    v_linearity = NotLinear;
  }
  
let dfalse = make_bool (Econst (Cconstr pfalse))
  
let dtrue = make_bool (Econst (Cconstr ptrue))
  
let var n ty = emake (Evar n) ty
  
let param n ty =
  {
    v_name = n;
    v_type = ty;
    v_linearity = NotLinear;
    v_last = Var;
    v_loc = no_location;
  }
  
let fby_state initial e =
  { (e) with e_desc = Eapp (eop (Epre (Some (Cconstr initial))), [ e ]); }
  
let fby_false e = emake (Eapp (eop (Epre (Some cfalse)), [ e ])) tybool
  
let last_false x = emake (Elast x) tybool
  
let ifthenelse e1 e2 e3 =
  emake (Eapp (eop Eifthenelse, [ e1; e2; e3 ])) e2.e_ty
  
let rec or_op e1 e2 =
  { (e1) with e_desc = Eapp (eop (Eop (por, [])), [ e1; e2 ]); }
  
let pair e1 e2 = emake (Etuple [ e1; e2 ]) (Tprod [ e1.e_ty; e2.e_ty ])
  
let block defnames eqs =
  {
    b_local = [];
    b_equs = eqs;
    b_defnames = defnames;
    b_statefull = true;
    b_loc = no_location;
  }
  
let eq pat e = eqmake (Eeq (pat, e))
  
let reset eq_list e = eqmake (Ereset (eq_list, e))
  
let switch e l = eqmake (Eswitch (e, l))
  
let varpat n = Evarpat n
  
let op_from_app app =
  match app.a_op with
  | Eop (n, _) -> op_from_app_name n
  | _ -> raise Not_static
  
let rec size_exp_of_exp e =
  match e.e_desc with
  | Econstvar n -> SVar n
  | Econst (Cint i) -> SConst i
  | Eapp (app, ([ e1; e2 ])) ->
      let op = op_from_app app
      in SOp (op, size_exp_of_exp e1, size_exp_of_exp e2)
  | _ -> raise Not_static

(** @return the set of variables defined in [pat]. *)
let vars_pat pat =
  let rec _vars_pat locals acc = function
      | Evarpat x ->
          if (IdentSet.mem x locals) or (IdentSet.mem x acc)
          then acc
          else IdentSet.add x acc
      | Etuplepat pat_list -> List.fold_left (_vars_pat locals) acc pat_list
  in _vars_pat IdentSet.empty IdentSet.empty pat

  
