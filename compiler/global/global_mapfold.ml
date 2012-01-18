open Misc
open Errors
open Signature
open Signature
open Clocks
open Idents

type 'a global_it_funs = {
  static_exp         : 'a global_it_funs -> 'a -> static_exp -> static_exp * 'a;
  static_exp_desc    : 'a global_it_funs -> 'a -> static_exp_desc -> static_exp_desc * 'a;
  async              : 'a global_it_funs -> 'a -> async_t -> async_t * 'a;
  ty                 : 'a global_it_funs -> 'a -> ty -> ty * 'a;
  ct                 : 'a global_it_funs -> 'a -> ct -> ct * 'a;
  ck                 : 'a global_it_funs -> 'a -> ck -> ck * 'a;
  link               : 'a global_it_funs -> 'a -> link -> link * 'a;
  var_ident          : 'a global_it_funs -> 'a -> var_ident -> var_ident * 'a;
  param              : 'a global_it_funs -> 'a -> param -> param * 'a;
  arg                : 'a global_it_funs -> 'a -> arg -> arg * 'a;
  param_ty           : 'a global_it_funs -> 'a -> param_ty -> param_ty * 'a;
  node               : 'a global_it_funs -> 'a -> node -> node * 'a;
  structure          : 'a global_it_funs -> 'a -> structure -> structure * 'a;
  field              : 'a global_it_funs -> 'a -> field -> field * 'a; }

let rec static_exp_it funs acc se = funs.static_exp funs acc se
and static_exp funs acc se =
  let se_ty, acc = ty_it funs acc se.se_ty in
  let se_desc, acc = static_exp_desc_it funs acc se.se_desc in
  { se with se_desc = se_desc; se_ty = se_ty }, acc

and static_exp_desc_it funs acc sd =
  try funs.static_exp_desc funs acc sd
  with Fallback -> static_exp_desc funs acc sd

and static_exp_desc funs acc sd = match sd with
  | Sfun _ | Svar _ | Sint _ | Sfloat _
  | Sbool _ | Sstring _ | Sconstructor _ | Sfield _ -> sd, acc
  | Stuple se_l ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Stuple se_l, acc
  | Sarray se_l ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sarray se_l, acc
  | Sop (n, se_l) ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sop (n, se_l), acc
  | Sarray_power (se1, se_l) ->
      let se1, acc = static_exp_it funs acc se1 in
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sarray_power(se1, se_l), acc
  | Srecord f_se_l ->
      let aux acc (f,se) = let se,acc = static_exp_it funs acc se in
        (f, se), acc in
      let f_se_l, acc = mapfold aux acc f_se_l in
      Srecord f_se_l, acc
  | Sasync se ->
      let se, acc = static_exp_it funs acc se in
      Sasync se, acc

and async_it funs acc a = funs.async funs acc a
and async funs acc a =
  Misc.optional_wacc (mapfold (static_exp_it funs)) acc a

and ty_it funs acc t = try funs.ty funs acc t with Fallback -> ty funs acc t
and ty funs acc t = match t with
  | Tid _ -> t, acc
  | Tprod t_l -> let t_l, acc = mapfold (ty_it funs) acc t_l in Tprod t_l, acc
  | Tarray (t, se) ->
      let t, acc = ty_it funs acc t in
      let se, acc = static_exp_it funs acc se in
      Tarray (t, se), acc
  | Tinvalid -> t, acc
  | Tfuture (a, t) -> let t, acc = ty_it funs acc t in Tfuture (a, t), acc

and ct_it funs acc c = try funs.ct funs acc c with Fallback -> ct funs acc c
and ct funs acc c = match c with
  | Ck(ck) -> let ck, acc = ck_it funs acc ck in Ck ck, acc
  | Cprod(ct_l) ->
      let ct_l, acc = mapfold (ct_it funs) acc ct_l in Cprod ct_l, acc

and ck_it funs acc c = try funs.ck funs acc c with Fallback -> ck funs acc c
and ck funs acc c = match c with
  | Cbase -> c, acc
  | Cvar(link_ref) ->
      let l, acc = link_it funs acc link_ref.contents in
      Cvar {link_ref with contents = l}, acc
  | Con(ck, constructor_name, v) ->
      let ck, acc = ck_it funs acc ck in
      let v, acc = var_ident_it funs acc v in
      Con (ck, constructor_name, v), acc

and link_it funs acc c =
  try funs.link funs acc c with Fallback -> link funs acc c
and link funs acc l = match l with
  | Cindex _ -> l, acc
  | Clink(ck) -> let ck, acc = ck_it funs acc ck in Clink ck, acc


and var_ident_it funs acc i = funs.var_ident funs acc i
and var_ident funs acc i = i, acc

and structure_it funs acc s = funs.structure funs acc s
and structure funs acc s =
  mapfold (field_it funs) acc s


and field_it funs acc f = funs.field funs acc f
and field funs acc f =
  let ty, acc = ty_it funs acc f.f_type in
    { f with f_type = ty }, acc


and param_it funs acc p = funs.param funs acc p
and param funs acc p =
  let p_type, acc = param_ty_it funs acc p.p_type in
  { p with p_type = p_type }, acc

and param_ty_it funs acc p =
  try funs.param_ty funs acc p with Fallback -> param_ty funs acc p
and param_ty funs acc p = match p with
  | Ttype t ->
      let t, acc = ty_it funs acc t in
      Ttype t, acc
  | Tsig node ->
      let node, acc = node_it funs acc node in
      Tsig node, acc


and arg_it funs acc a = funs.arg funs acc a
and arg funs acc a =
  let a_type, acc = ty_it funs acc a.a_type in
    { a with a_type = a_type }, acc


and node_it funs acc n = funs.node funs acc n
and node funs acc n =
  let node_params, acc = mapfold (param_it funs) acc n.node_params in
  let node_inputs, acc = mapfold (arg_it funs) acc n.node_inputs in
  let node_outputs, acc = mapfold (arg_it funs) acc n.node_outputs in
    { n with node_params = node_params;
        node_inputs = node_inputs;
        node_outputs = node_outputs }, acc


let defaults = {
  static_exp = static_exp;
  static_exp_desc = static_exp_desc;
  async = async;
  ty = ty;
  param_ty = param_ty;
  ct = ct;
  ck = ck;
  link = link;
  var_ident = var_ident;
  structure = structure;
  field = field;
  param = param;
  arg = arg;
  node = node;
}


(** Is used to stop the pass at this level *)
let stop _ acc x = x, acc

let defaults_stop = {
  static_exp = stop;
  static_exp_desc = stop;
  async = stop;
  ty = stop;
  param_ty = stop;
  ct = stop;
  ck = stop;
  link = stop;
  var_ident = stop;
  structure = stop;
  field = stop;
  param = stop;
  arg = stop;
  node = stop;
}



(** [it_gather gather f] will create a function to iterate
    over a type using [f] and then use [gather] to combine
    the value of the local accumulator with the one
    given as argument. *)
let it_gather gather f funs acc e =
  let e, new_acc = f funs acc e in
    e, gather acc new_acc
