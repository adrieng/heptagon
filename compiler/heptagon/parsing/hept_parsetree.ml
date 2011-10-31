(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


open Location
open Signature

(** var_names will be converted to idents *)
type var_name = Names.name

(** dec_names are locally declared qualified names *)
type dec_name = Names.name

type module_name = Names.modul

(** state_names, [automata] translate them in constructors with a fresh type. *)
type state_name = Names.name


type qualname =
  | Q of Names.qualname (* already qualified name *)
  | ToQ of Names.name (* name to qualify in the scoping process *)

type type_name = qualname
type fun_name = qualname
type field_name = qualname
type constructor_name = qualname
type constant_name = qualname

type static_exp = { se_desc: static_exp_desc; se_loc: location }

and static_exp_desc =
  | Svar of constant_name
  | Sint of int
  | Sfloat of float
  | Sbool of bool
  | Sstring of string
  | Sconstructor of constructor_name
  | Sfield of field_name
  | Stuple of static_exp list
  | Sarray_power of static_exp * (static_exp list) (** power : 0^n : [0,0,0,0,0,..] *)
  | Sarray of static_exp list (** [ e1, e2, e3 ] *)
  | Srecord of (field_name * static_exp) list (** { f1 = e1; f2 = e2; ... } *)
  | Sop of fun_name * static_exp list (** defined ops for now in pervasives *)
  | Sasync of static_exp

type iterator_type =
  | Imap
  | Imapi
  | Ifold
  | Ifoldi
  | Imapfold

type ty =
  | Tprod of ty list
  | Tid of qualname
  | Tarray of ty * exp
  | Tfuture of future_t * ty

and ck =
  | Cbase
  | Con of ck * constructor_name * var_name

and ct =
  | Ck of ck
  | Cprod of ct list

and exp =
  { e_desc     : edesc;
    e_ct_annot : ct option ;
    e_loc      : location }

and edesc =
  | Econst of static_exp
  | Evar of var_name (* can be a constant_name *)
  | Elast of var_name
  | Epre of exp option * exp
  | Efby of exp * exp
  | Estruct of (qualname * exp) list
  | Eapp of app * exp list
  | Eiterator of iterator_type * app * exp list * exp list * exp list
  | Ewhen of exp * constructor_name * var_name
  | Emerge of var_name * (constructor_name * exp) list
  | Esplit of var_name * exp

and app = { a_op: op; a_params: exp list; a_async : async_t option; a_inlined: bool }

and op =
  | Etuple
  | Enode of qualname
  | Efun of qualname
  | Eifthenelse
  | Earrow
  | Efield
  | Efield_update (* field name args would be [record ; value] *)
  | Earray
  | Earray_fill
  | Eselect
  | Eselect_dyn
  | Eselect_trunc
  | Eselect_slice
  | Eupdate
  | Econcat
  | Ebang
  | Ereinit

and pat =
  | Etuplepat of pat list
  | Evarpat of var_name

and async_t = exp list
and future_t = unit


type eq =
    { eq_desc : eqdesc;
      eq_loc  : location }

and eqdesc =
  | Eautomaton of state_handler list
  | Eswitch of exp * switch_handler list
  | Epresent of present_handler list * block
  | Ereset of block * exp
  | Eblock of block
  | Eeq of pat * Linearity.init * exp

and block =
  { b_local : var_dec list;
    b_equs  : eq list;
    b_loc   : location;
    b_async : async_t option; }

and state_handler =
  { s_state  : state_name;
    s_block  : block;
    s_until  : escape list;
    s_unless : escape list; }

and escape =
  { e_cond       : exp;
    e_reset      : bool;
    e_next_state : state_name; }

and switch_handler =
  { w_name  : constructor_name;
    w_block : block; }

and present_handler =
  { p_cond  : exp;
    p_block : block; }

and var_dec =
  { v_name  : var_name;
    v_type  : ty;
    v_linearity : Linearity.linearity;
    v_clock : ck option;
    v_last  : last;
    v_loc   : location; }

and last = Var | Last of exp option

type type_dec =
  { t_name : dec_name;
    t_desc : type_desc;
    t_loc  : location }

and type_desc =
  | Type_abs
  | Type_alias of ty
  | Type_enum of dec_name list
  | Type_struct of (dec_name * ty) list

type contract =
  { c_assume  : exp;
    c_enforce : exp;
    c_controllables : var_dec list;
    c_block   : block }

type node_dec =
  { n_name        : dec_name;
    n_stateful    : bool;
    n_input       : var_dec list;
    n_output      : var_dec list;
    n_contract    : contract option;
    n_block       : block;
    n_loc         : location;
    n_params      : var_dec list;
    n_constraints : exp list; }

type const_dec =
  { c_name  : dec_name;
    c_type  : ty;
    c_value : exp;
    c_loc   : location; }

type program =
  { p_modname : dec_name;
    p_opened : module_name list;
    p_desc : program_desc list }

and program_desc =
  | Ppragma of (var_name * string)
  | Ptype of type_dec
  | Pconst of const_dec
  | Pnode of node_dec


type arg =
  { a_type  : ty;
    a_clock : ck option;
    a_linearity : Linearity.linearity;
    a_name  : var_name option }

type signature =
  { sig_name        : dec_name;
    sig_inputs      : arg list;
    sig_stateful    : bool;
    sig_outputs     : arg list;
    sig_params      : var_dec list;
    sig_param_constraints : exp list;
    sig_loc         : location }

type interface =
    { i_modname : dec_name;
      i_opened : module_name list;
      i_desc : interface_desc list }

and interface_desc =
  | Itypedef of type_dec
  | Iconstdef of const_dec
  | Isignature of signature

(* {3 Helper functions to create AST} *)

let mk_exp desc ?(ct_annot = None) loc =
  { e_desc = desc; e_ct_annot = ct_annot; e_loc = loc }

let mk_app op async params inlined =
  { a_op = op; a_params = params; a_async = async; a_inlined = inlined }

let mk_call ?(async=None) ?(params=[]) ?(inlined=false) op exps =
  Eapp (mk_app op async params inlined, exps)

let mk_op_call ?(params=[]) s exps =
  mk_call ~params:params (Efun (Q (Names.pervasives_qn s))) exps

let mk_iterator_call it app n_list pexps exps =
  Eiterator (it, app, n_list, pexps, exps)

let mk_static_exp desc loc =
  { se_desc = desc; se_loc = loc }

let mk_static_exp_exp desc loc =
  mk_exp (Econst { se_desc = desc; se_loc = loc }) loc

let mk_constructor_exp f loc =
  mk_exp (Econst (mk_static_exp (Sconstructor f) loc)) loc

let mk_field_exp f loc =
  mk_exp (Econst (mk_static_exp (Sfield f) loc)) loc

let mk_type_dec name desc loc =
  { t_name = name; t_desc = desc; t_loc = loc }

let mk_equation desc loc =
  { eq_desc = desc; eq_loc = loc }

let mk_var_dec ?(linearity=Linearity.Ltop) name ty ck last loc =
  { v_name = name; v_type = ty; v_linearity = linearity;
    v_clock =ck; v_last = last; v_loc = loc }

let mk_block locals ?(async=None) eqs loc =
  { b_local = locals; b_equs = eqs;
    b_loc = loc; b_async = async }

let mk_const_dec id ty e loc =
  { c_name = id; c_type = ty; c_value = e; c_loc = loc }

let mk_arg name (ty,lin) ck =
  { a_type = ty; a_linearity = lin; a_name = name; a_clock = ck }

let ptrue = Q Initial.ptrue
let pfalse = Q Initial.pfalse
