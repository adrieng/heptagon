(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* The internal MiniLustre representation *)

open Location
open Dep
open Misc
open Names
open Ident
open Signature
open Static

type iterator_type = 
  | Imap
  | Ifold
  | Imapfold

type type_dec =
    { t_name: name;
      t_desc: tdesc;
      t_loc: location }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of structure

and exp =
    { e_desc: desc;        (* its descriptor *)
      mutable e_ck: ck;
      mutable e_ty: ty;
      e_loc: location }

and desc =
  | Econst of const
  | Evar of ident
  | Econstvar of name
  | Efby of const option * exp
  | Etuple of exp list
  | Ecall of op_desc * exp list * ident option (** [op_desc] is the function called
                              [exp list] is the passed arguments
                              [ident option] is the optional reset condition *)

  | Ewhen of exp * longname * ident
  | Emerge of ident * (longname * exp) list
  | Eifthenelse of exp * exp * exp
  | Efield of exp * longname
  | Efield_update of longname * exp * exp (*field, record, value*)
  | Estruct of (longname * exp) list
  | Earray of exp list
  | Earray_op of array_op

and array_op =
  | Erepeat of size_exp * exp
  | Eselect of size_exp list * exp (*indices, array*)
  | Eselect_dyn of exp list * size_exp list * exp * exp (*indices, bounds, array, default*)
  | Eupdate of size_exp list * exp * exp (*indices, array, value*)
  | Eselect_slice of size_exp * size_exp * exp (*lower bound, upper bound, array*)
  | Econcat of exp * exp
  | Eiterator of iterator_name * longname * size_exp list * size_exp * exp list * ident option
   
and op_desc = longname * size_exp list * op_kind
and op_kind = | Eop | Enode

and ct =
  | Ck of ck
  | Cprod of ct list

and ck =
  | Cbase
  | Cvar of link ref
  | Con of ck * longname * ident

and link =
  | Cindex of int
  | Clink of ck

and const =
  | Cint of int
  | Cfloat of float
  | Cconstr of longname
  | Carray of size_exp * const 

and pat =
  | Etuplepat of pat list
  | Evarpat of ident

type eq =
    { eq_lhs : pat;
      eq_rhs : exp;
      eq_loc : loc }

type var_dec =
    { v_name : ident;
      v_type : ty;
      v_clock : ck }

type contract =
    { c_assume : exp;
      c_enforce : exp;
      c_controllables : var_dec list;
      c_local : var_dec list;
      c_eq : eq list;
    }

type node_dec =
    { n_name   : name;
      n_input  : var_dec list;
      n_output : var_dec list;
      n_contract : contract option;
      n_local  : var_dec list;
      n_equs   : eq list;
      n_loc    : location;
      n_params : param list; 
      n_params_constraints : size_constr list;
      n_params_instances : (int list) list; }(*TODO commenter ou passer en env*)

type const_dec =
    { c_name : name;
      c_value : size_exp;
      c_loc : location; }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types  : type_dec list;
      p_nodes  : node_dec list;
      p_consts : const_dec list; }

(*Helper functions to build the AST*)
let make_exp desc ty l ck loc =
  { e_desc = desc; e_ty = ty; e_linearity = l; e_ck = ck; e_loc = loc }

let make_dummy_exp desc ty =
  { e_desc = desc; e_ty = ty; e_linearity = NotLinear; 
    e_ck = Cbase; e_loc = no_location }

let rec size_exp_of_exp e =
  match e.e_desc with 
  | Econstvar n -> SVar n
  | Econst (Cint i) -> SConst i
  | Eop(op, _, [e1;e2]) ->
      let sop = op_from_app_name op in
	SOp(sop, size_exp_of_exp e1, size_exp_of_exp e2)
  | _ -> raise Not_static

(*Returns the list of bounds of an array type*)
let rec bounds_list ty = 
  match ty with
    | Tarray(ty, n) -> n::(bounds_list ty)
    | _ -> []

(** Returns the var_dec object corresponding to the name n
    in a list of var_dec. *)
let rec vd_find n = function
  | [] -> Format.printf "Not found var %s\n" (name n); raise Not_found
  | vd::l -> 
      if vd.v_name = n then vd else vd_find n l

(** Returns whether an object of name n belongs to 
    a list of var_dec. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_name = n or (vd_mem n l)

(** [is_record_type ty] returns whether ty corresponds to a record type. *)
let is_record_type ty =
  match ty with
    | Tid n ->
	(try
	   ignore (Modules.find_struct n);
	   true
	 with 
	     Not_found -> false
	)
    | _ -> false


module Vars =
struct
  let rec vars_pat acc = function
    | Evarpat(x) -> x :: acc
    | Etuplepat(pat_list) -> List.fold_left vars_pat acc pat_list

  let rec vars_ck acc = function
    | Con(ck, c, n) -> if List.mem (IVar n) acc then acc else (IVar n) :: acc
    | Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck }         -> vars_ck acc ck

  let rec read is_left acc e =
    let add x acc = if List.mem (IVar x) acc then acc else (IVar x) :: acc in
    let acc =
      match e.e_desc with
        | Emerge(x, c_e_list) ->
            let acc = add x acc in
            List.fold_left (fun acc (_, e) -> read is_left acc e) acc c_e_list
        | Eifthenelse(e1, e2, e3) ->
            read is_left (read is_left (read is_left acc e1) e2) e3
        | Ewhen(e, c, x) ->
            let acc = add x acc in
            read is_left acc e
        | Eop(_, _, e_list)
        | Etuple(e_list) -> List.fold_left (read is_left) acc e_list
        | Eapp(_, _, e_list) -> List.fold_left (read is_left) acc e_list
        | Eevery(_, _, e_list, x) ->
            let acc = add x acc in
              List.fold_left (read is_left) acc e_list
        | Efby(_, e) ->
            if is_left then vars_ck acc e.e_ck else read is_left acc e
	| Ereset_mem (_, _,res) -> add res acc
        | Evar(n) -> add n acc
	| Efield({ e_desc = Evar x }, f) -> 
	    let acc = add x acc in
	    let x = IField(x,f) in
	      if List.mem x acc then acc else x::acc
        | Efield(e, _) -> read is_left acc e
        | Estruct(f_e_list) ->
            List.fold_left (fun acc (_, e) -> read is_left acc e) acc f_e_list
        | Econst _ | Econstvar _ -> acc 
    (*Array operators*)
	| Earray e_list -> List.fold_left (read is_left) acc e_list
	| Erepeat (_,e) -> read is_left acc e
	| Eselect (_,e) -> read is_left acc e
	| Eselect_dyn (e_list, _, e1, e2) -> 
	    let acc = List.fold_left (read is_left) acc e_list in 
	      read is_left (read is_left acc e1) e2
	| Eupdate (_, e1, e2) | Efield_update (_, e1, e2) ->
	    read is_left (read is_left acc e1) e2 
	| Eselect_slice (_ , _, e) -> read is_left acc e
	| Econcat (e1, e2) ->
	    read is_left (read is_left acc e1) e2 
	| Eiterator (_, _, _, _, e_list, _) ->  
	    List.fold_left (read is_left) acc e_list
    in
      vars_ck acc e.e_ck

  let rec remove x = function
    | [] -> []
    | y :: l -> if x = y then l else y :: remove x l

  let def acc { eq_lhs = pat } = vars_pat acc pat

  let read is_left { eq_lhs = pat; eq_rhs = e } =
    match pat, e.e_desc with
      |  Evarpat(n), Efby(_, e1) ->
           if is_left
           then remove (IVar n) (read is_left [] e1)
           else read is_left [] e1
      | _ -> read is_left [] e

  let rec remove_records = function
    | [] -> []
    | (IVar x)::l -> (IVar x)::(remove_records l)
    | (IField(x,f))::l -> 
	let l = remove (IVar x) l in
	  (IField(x,f))::(remove_records l)

  let read_ivars is_left eq =
    remove_records (read is_left eq)

  let read is_left eq =
    filter_vars (read is_left eq)

  let antidep { eq_rhs = e } =
    match e.e_desc with Efby _ -> true | _ -> false
  let clock { eq_rhs = e } =
    match e.e_desc with
      | Emerge(_, (_, e) :: _) -> e.e_ck
      | _ -> e.e_ck
  let head ck =
    let rec headrec ck l =
      match ck with
        | Cbase | Cvar { contents = Cindex _ } -> l
        | Con(ck, c, n) -> headrec ck (n :: l)
        | Cvar { contents = Clink ck } -> headrec ck l in
    headrec ck []

  let rec linear_use acc e =
      match e.e_desc with
        | Emerge(_, c_e_list) ->
            List.fold_left (fun acc (_, e) -> linear_use acc e) acc c_e_list
        | Eifthenelse(e1, e2, e3) ->
            linear_use (linear_use (linear_use acc e1) e2) e3
        | Ewhen(e, _, _) | Efield(e, _) | Efby(_, e) -> linear_use acc e
        | Eop(_,_, e_list)
        | Etuple(e_list) | Earray e_list
        | Eapp(_,_, e_list) | Eiterator (_, _, _, _, e_list, _)
        | Eevery(_,_, e_list, _) -> List.fold_left linear_use acc e_list
        | Evar(n) ->
	    (match e.e_linearity with
	       | At _ -> if List.mem n acc then acc else n :: acc
	       | _ -> acc
	    )
        | Estruct(f_e_list) ->
            List.fold_left (fun acc (_, e) -> linear_use acc e) acc f_e_list
        | Econst _ | Econstvar _ | Ereset_mem (_, _,_) -> acc 
    (*Array operators*)
	| Erepeat (_,e)
	| Eselect (_,e) | Eselect_slice (_ , _, e) -> linear_use acc e
	| Eselect_dyn (e_list, _, e1, e2) -> 
	    let acc = List.fold_left linear_use acc e_list in 
	      linear_use (linear_use acc e1) e2
	| Eupdate (_, e1, e2) | Efield_update (_, e1, e2) 
	| Econcat (e1, e2) ->
	    linear_use (linear_use acc e1) e2 

  let mem_reset { eq_rhs = e } =
    match e.e_desc with
      | Ereset_mem (y, _, _) -> [y]
      | _ -> []
end

(* data-flow dependences. pre-dependences are discarded *)
module DataFlowDep = Make
  (struct
     type equation = eq
     let read eq = Vars.read true eq
     let def = Vars.def
     let linear_read eq = Vars.linear_use [] eq.eq_rhs
     let mem_reset = Vars.mem_reset
     let antidep = Vars.antidep
   end)

(* all dependences between variables *)
module AllDep = Make
  (struct
     type equation = eq
     let read eq = Vars.read false eq
     let linear_read eq = Vars.linear_use [] eq.eq_rhs
     let mem_reset = Vars.mem_reset
     let def = Vars.def
     let antidep eq = false
   end)

module Printer =
struct
  open Format

  let is_infix =
    let module StrSet = Set.Make(String) in
    let set_infix = StrSet.singleton "or" in
    fun s ->
      if (StrSet.mem s set_infix) then true
      else begin
        match (String.get s 0) with
          | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' -> false
          | _ -> true
      end

  let rec print_list ff print sep l =
    match l with
      | [] -> ()
      | [x] -> print ff x
      | x :: l ->
          print ff x;
          fprintf ff "%s@ " sep;
          print_list ff print sep l

  let print_name ff n =
    let n = if is_infix n then
      match n with
        | "*" -> "( * )"
        | _ -> "(" ^ n ^ ")"
    else n
    in fprintf ff "%s" n

  let print_longname ff n =
    match n with
      | Name(m) -> print_name ff m
      | Modname({ qual = "Pervasives"; id = m }) ->
          print_name ff m
      | Modname({ qual = m1; id = m2 }) ->
          fprintf ff "%s." m1; print_name ff m2

  let print_ident ff id =
    fprintf ff "%s" (name id)

  let rec print_pat ff = function
    | Evarpat(n) -> print_ident ff n
    | Etuplepat(pat_list) ->
        fprintf ff "@[(";
        print_list ff print_pat "," pat_list;
        fprintf ff ")@]"

  let rec print_type ff = function
    | Tint -> fprintf ff  "int"
    | Tfloat -> fprintf ff  "float"
    | Tid(id) -> print_longname ff id
    | Tarray(ty, n) -> 
	print_type ff ty;
	fprintf ff "^";
	print_size_exp ff n

  let rec print_type ff = function
    | Tbase(ty) -> print_type ff ty
    | Tprod(ty_list) ->
        fprintf ff "@[(";
        print_list ff print_type " *" ty_list;
        fprintf ff ")@]"

  let rec print_ck ff = function
    | Cbase -> fprintf ff "base"
    | Con(ck, c, n) ->
        print_ck ff ck; fprintf ff " on ";
        print_longname ff c; fprintf ff "(";
        print_ident ff n; fprintf ff ")"
    | Cvar { contents = Cindex n } -> fprintf ff "base"
    | Cvar { contents = Clink ck } -> print_ck ff ck

  let rec print_clock ff = function
    | Ck(ck) -> print_ck ff ck
    | Cprod(ct_list) ->
        fprintf ff "@[(";
        print_list ff print_clock " *" ct_list;
        fprintf ff ")@]"

  let print_vd ff { v_name = n; v_type = ty; v_clock = ck } =
    fprintf ff "@[<v>";
    print_ident ff n;
    fprintf ff ":";
    print_type ff ty;
    fprintf ff " at ";
    print_ck ff ck;
    fprintf ff "@]"

  let rec print_c ff = function
    | Cint i -> fprintf ff "%d" i
    | Cfloat f -> fprintf ff "%f" f
    | Cconstr(tag) -> print_longname ff tag
    | Carray (n, c) ->
	print_c ff c;
	fprintf ff "^";
	print_size_exp ff n

  let print_call_params ff = function
    | [] -> ()
    | l -> 
	fprintf ff "<<";
	print_list ff print_size_exp "," l;
	fprintf ff ">>"

  let rec print_exps ff e_list =
    fprintf ff "@[(";print_list ff print_exp "," e_list; fprintf ff ")@]"

  and print_exp ff e =
    if !Misc.full_type_info then fprintf ff "(";
    begin match e.e_desc with
      | Evar x -> print_ident ff x
      | Econstvar x -> print_name ff x
      | Econst c -> print_c ff c
      | Efby(Some(c), e) ->
          print_c ff c; fprintf ff " fby "; print_exp ff e
      | Ereset_mem(y,v,res) ->
	  fprintf ff "@[reset_mem ";
	  print_ident ff y;
	  fprintf ff " = ";
	  print_c ff v;
	  fprintf ff " every ";
	  print_ident ff res;
	  fprintf ff "@]"
      | Efby(None, e) ->
          fprintf ff "pre "; print_exp ff e
      | Eop((Name(m) | Modname { qual = "Pervasives"; id = m }), params, [e1;e2])
          when is_infix m ->
          fprintf ff "(%a %s %a %a)"
            print_exp e1
            m
	    print_call_params params
            print_exp e2
      | Eop(op, params, e_list) ->
          print_longname ff op;
	  print_call_params ff params;
          print_exps ff e_list
      | Eapp({ a_op = f }, params, e_list) ->
          print_longname ff f;
	  print_call_params ff params;
          print_exps ff e_list
      | Eevery({ a_op = f }, params, e_list, x) ->
          print_longname ff f;
	  print_call_params ff params;
          print_exps ff e_list;
          fprintf ff " every "; print_ident ff x
      | Ewhen(e, c, n) ->
          fprintf ff "(";
          print_exp ff e;
          fprintf ff " when ";
          print_longname ff c; fprintf ff "(";
          print_ident ff n; fprintf ff ")";
          fprintf ff ")"
      | Eifthenelse(e1, e2, e3) ->
          fprintf ff "@[if ";print_exp ff e1;
          fprintf ff "@ then ";
          print_exp ff e2;
          fprintf ff "@ else ";
          print_exp ff e3;
          fprintf ff "@]"
      | Emerge(x, tag_e_list) ->
          fprintf ff "@[<hov 2>merge ";print_ident ff x;fprintf ff "@ ";
          fprintf ff "@[";
          print_tag_e_list ff tag_e_list;
          fprintf ff "@]@]"
      | Etuple(e_list) ->
          fprintf ff "@[(";
          print_list ff print_exp "," e_list;
          fprintf ff ")@]"
      | Efield(e, field) ->
          print_exp ff e;
          fprintf ff ".";
          print_longname ff field
      | Estruct(f_e_list) ->
          fprintf ff "@[<v 1>{";
          print_list ff
            (fun ff (field, e) -> print_longname ff field;fprintf ff " = ";
               print_exp ff e)
            ";" f_e_list;
          fprintf ff "}@]"
    (*Array operators*)
      | Earray e_list -> 
	  fprintf ff "@[[";
          print_list ff print_exp ";" e_list;
          fprintf ff "]@]"
      | Erepeat (n,e) -> 
	  print_exp ff e;
	  fprintf ff "^";
          print_size_exp ff n
      | Eselect (idx,e) -> 
	  print_exp ff e;
	  fprintf ff "[";
          print_list ff print_size_exp "][" idx;
          fprintf ff "]" 
      | Eselect_dyn (idx, _, e1, e2) ->
	  fprintf ff "@[";
	  print_exp ff e1;
	  fprintf ff "[";
          print_list ff print_exp "][" idx;
	  fprintf ff "] default ";
	  print_exp ff e2;
	    fprintf ff "@]"
      | Eupdate (idx, e1, e2) ->
	  fprintf ff "@[";
	  print_exp ff e1;
          fprintf ff " with [";
	  print_list ff print_size_exp "][" idx;
	  fprintf ff "] = ";
	  print_exp ff e2;
	  fprintf ff "@]"
      | Eselect_slice (idx1, idx2, e) -> 
	  print_exp ff e;
          fprintf ff "[";
	  print_size_exp ff idx1;
	  fprintf ff "..";
	  print_size_exp ff idx2;
	  fprintf ff "]"
      | Econcat (e1, e2) ->
	  print_exp ff e1;
	  fprintf ff " @@ ";
	  print_exp ff e2
      | Eiterator (it, f, params, n, e_list, reset) -> 
	  fprintf ff "("; 
	  fprintf ff "%s" (iterator_to_string it);
	  fprintf ff " ";
	  (match params with
	     | [] -> print_longname ff f
	     | l -> 
		 fprintf ff "(";
		 print_longname ff f;
		 print_call_params ff params;
		 fprintf ff ")"
	  );
	  fprintf ff " <<";
	  print_size_exp ff n;
	  fprintf ff ">>) (@[";
	  print_list ff print_exp "," e_list;
	  fprintf ff ")@]";
	  (match reset with 
	     | None -> ()
	     | Some r -> fprintf ff " every %s" (name r)
	  )
      | Efield_update (f, e1, e2) ->
	  fprintf ff "@[";
	  print_exp ff e1;
          fprintf ff " with .";
	  print_longname ff f;
	  fprintf ff " = ";
	  print_exp ff e2;
	  fprintf ff "@]"
    end;
    if !Misc.full_type_info
    then begin
      fprintf ff " : %a)" print_type e.e_ty;
      if e.e_loc = no_location then fprintf ff " (no loc)"
    end
  and print_tag_e_list ff tag_e_list =
    print_list ff
      (fun ff (tag, e) ->
         fprintf ff "@[(";
         print_longname ff tag;
         fprintf ff " -> ";
         print_exp ff e;
         fprintf ff ")@]@,") ""
      tag_e_list

  let print_eq ff { eq_lhs = p; eq_rhs = e } =
    fprintf ff "@[<hov 2>";
    print_pat ff p;
    (*     (\* DEBUG *\) *)
    (*     fprintf ff " : "; *)
    (*     print_ck ff e.e_ck; *)
    (*     (\* END DEBUG *\) *)
    fprintf ff " =@ ";
    print_exp ff e;
    if !Misc.full_type_info
    then begin fprintf ff "@ at "; print_ck ff e.e_ck end;
    fprintf ff ";@]"

  let print_eqs ff l =
    fprintf ff "@[<v>"; print_list ff print_eq "" l; fprintf ff "@]"

  let print_open_module ff name =
    fprintf ff "@[open ";
    print_name ff name;
    fprintf ff "@.@]"

  let print_type_def ff { t_name = name; t_desc = tdesc } =
    match tdesc with
      | Type_abs -> fprintf ff "@[type %s@\n@]" name
      | Type_enum(tag_name_list) ->
          fprintf ff "@[type %s = " name;
          print_list ff print_name "|" tag_name_list;
          fprintf ff "@\n@]"
      | Type_struct(f_ty_list) ->
          fprintf ff "@[type %s = " name;
          fprintf ff "@[<v 1>{";
          print_list ff
            (fun ff (field, ty) -> print_name ff field;
               fprintf ff ": ";
               print_type ff ty) ";" f_ty_list;
          fprintf ff "}@]@\n@]"

  let print_contract ff {c_local = l;
                         c_eq = eqs;
                         c_assume = e_a;
                         c_enforce = e_g;
                         c_controllables = cl } =
    if l <> [] then begin
      fprintf ff "contract\n";
      fprintf ff "@[<hov 4>var ";
      print_list ff print_vd ";" l;
      fprintf ff ";@]\n"
    end;
    if eqs <> [] then begin
      fprintf ff "@[<v 2>let @,";
      print_eqs ff eqs;
      fprintf ff "@]"; fprintf ff "tel\n"
    end;
    fprintf ff "assume@ %a@;enforce@ %a with ("
      print_exp e_a
      print_exp e_g;
    print_list ff print_vd ";" cl;
    fprintf ff ")"

  let print_node_params ff = function
    | [] -> ()
    | l -> 
	fprintf ff "<<";
	print_list ff print_name "," l;
	fprintf ff ">>"

  let print_node ff
      { n_name = n;n_input = ni;n_output = no;
        n_contract = contract;
        n_local = nl; n_equs = ne;
	n_params = params; } =
    fprintf ff "@[<v 2>node %s" n;
    print_node_params ff params;
    fprintf ff "(@["; 
    print_list ff print_vd ";" ni;
    fprintf ff "@]) returns (@[";
    print_list ff print_vd ";" no;
    fprintf ff "@])@,";
    optunit (print_contract ff) contract;
    if nl <> [] then begin
      fprintf ff "@[<hov 2>var ";
      print_list ff print_vd ";" nl;
      fprintf ff ";@]@,"
    end;
    fprintf ff "@[<v 2>let @,";
    print_eqs ff ne;
    fprintf ff "@]@;"; fprintf ff "tel";fprintf ff "@.@]"

  let print_exp oc e =
    let ff = formatter_of_out_channel oc in
    print_exp ff e;
    fprintf ff "@."

  let print_type oc ty =
    let ff = formatter_of_out_channel oc in
    print_type ff ty;
    fprintf ff "@?"

  let print_clock oc ct =
    let ff = formatter_of_out_channel oc in
    print_clock ff ct;
    fprintf ff "@?"

  let print oc { p_opened = pm; p_types = pt; p_nodes = pn } =
    let ff = formatter_of_out_channel oc in
    List.iter (print_open_module ff) pm;
    List.iter (print_type_def ff) pt;
    List.iter (print_node ff) pn;
    fprintf ff "@?"
end
