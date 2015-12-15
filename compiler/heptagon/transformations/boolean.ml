(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

(*
   Translate enumerated types (state variables) into boolean

   type t = A | B | C | D

   A --> 00
   B --> 01
   C --> 10
   D --> 11

   x : t --> x1,x2,x2_0,x2_1 : bool (x2_i for keeping correct clocks)

   x = B;
   -->
   (x1,x2) = (0,1);
   x2_0 = x2 when False(x1);
   x2_1 = x2 when True(x1);

   (e when A(x))
   -->
   (e when False(x1)) when False(x2_0)

   ck on A(x)
   -->
   ck on False(x1) on False(x2_0)

   merge x (A -> e0) (B -> e1) (C -> e2) (D -> e3)
   -->
   merge x1 (False -> merge x2_0 (False -> e0) (True -> e1))
            (True  -> merge x2_1 (False -> e2) (True -> e3))
*)

(* $Id: boolean.ml 833 2010-02-10 14:15:00Z delaval $ *)

open Names
open Location
open Idents
open Signature
open Types
open Clocks
open Heptagon
open Hept_utils

let fresh = Idents.gen_fresh "bool" (fun s -> s)

let ty_bool = Tid({ qual = Pervasives; name = "bool"})

let strue = mk_static_exp ty_bool (Sbool(true))
let sfalse = mk_static_exp ty_bool (Sbool(false))

let sbool = function
  | true -> strue
  | false -> sfalse

let ctrue = { qual = Pervasives; name = "true" }
let cfalse = { qual = Pervasives; name = "false" }

let mk_tuple e_l =
  Eapp((mk_app Etuple),e_l,None)

(* boolean decision tree ; left branch for true ; nodes are constructors *)
type btree = Node of constructor_name option | Tree of btree * btree

(* Debug
let print_indent n =
  for i = 1 to n do
    Printf.printf " "
  done

let rec print_btree indent bt =
  match bt with
  | Node(None) ->
      print_indent indent;
      Printf.printf "None\n"
  | Node(Some c) ->
      print_indent indent;
      Printf.printf "%s\n" (fullname c)
  | Tree(t1,t2) ->
      print_indent indent;
      Printf.printf "0\n";
      print_btree (indent+2) t1;
      print_indent indent;
      Printf.printf "1\n";
      print_btree (indent+2) t2
*)

(* info associated to each enum type *)
type enuminfo =
    {
      ty_nb_var : int; (* nb of boolean var representing this type *)
      ty_assoc : bool list QualEnv.t;
      ty_tree : btree
    }

(*
let rec print_bl bl =
  match bl with
  | [] -> ()
  | b::bl ->
      Printf.printf "%s" (if b then "1" else "0");
      print_bl bl

let print_enuminfo info =
  Printf.printf "{ ty_nb_var = %d;\n  ty_assoc = " info.ty_nb_var;
  QualEnv.fold
    (fun c l () ->
       Printf.printf "(%s : " (fullname c);
       print_bl l;
       Printf.printf "), ")
    info.ty_assoc ();
  Printf.printf ";\n  ty_tree =\n";
  print_btree 0 info.ty_tree
*)

(* ty_nb_var = n : var x of enum type will be represented by
   boolean variables x_1,...,x_n

   ty_assoc(A) = [b_1,...,b_n] : constant A will be represented by
   x_1,...,x_n where x_i = b_i

   assert length(ty_assoc(A)) = ty_nb_var
*)

(* Type var_tree : variable binary tree, each variable being of clock
   of its direct father (false clock for left son, true for right son).

   Then if x translates to (x1,x2)
   the corresponding var_tree is
       x1
      /  \
   x2_0  x2_1

   x2_0 being on clock False(x1)
   x2_1 being on clock True(x1)
 *)
type var_tree = Vempty | VNode of var_ident * var_tree * var_tree

(*
let rec print_var_tree indent t =
  match t with
  | Vempty ->
      print_indent indent;
      Printf.printf "Empty\n"
  | VNode(v,t1,t2) ->
      print_indent indent;
      Printf.printf "0 : %s\n" (name v);
      print_var_tree (indent+2) t1;
      print_var_tree (indent+2) t2
*)

type varinfo =
    {
      var_enum : enuminfo;
      var_list : var_ident list;
      clocked_var : var_tree;
    }

(*
let print_varinfo info =
  Printf.printf "{ var_enum = \n";
  print_enuminfo info.var_enum;
  Printf.printf ";\n  var_list = ";
  List.iter (fun v -> Printf.printf "%s, " (name v)) info.var_list;
  Printf.printf ";\n  clocked_var =\n";
  print_var_tree 0 info.clocked_var
*)

type type_info = Type of type_dec_desc | Enum of enuminfo

let enum_types : type_info QualEnv.t ref = ref QualEnv.empty

(*
let print_enum_types () =
  QualEnv.fold
    (fun t ti () ->
       match ti with
       | Enum info ->
           Printf.printf "type %s :\n" (fullname t);
           print_enuminfo info
       | _ -> ()
    ) !enum_types ()
*)

let get_enum name =
  QualEnv.find name !enum_types

(* split2 k [x1;...;xn] = ([x1;...;xk],[xk+1;...;xn]) *)
let split2 n l =
  let rec splitaux k acc l =
    if k = 0 then (acc,l) else
      begin
        match l with
        | x::t -> splitaux (k-1) (x::acc) t
        | _ -> assert false
      end in
  let (l1,l2) = splitaux n [] l in
  (List.rev l1,l2)



(* create an info from the elements of a name list *)
let rec var_list clist =
  match clist with
  | [] -> (0,QualEnv.empty,Node(None))
  | [c] -> (1, QualEnv.add c [false] QualEnv.empty, Tree(Node(Some c),Node(None)))
  | [c1;c2] -> (1,
                QualEnv.add c1 [false] (QualEnv.add c2 [true] QualEnv.empty),
                Tree(Node(Some c1),Node(Some c2)))
  | l ->
      let n = List.length l in
      let n1 = n asr 1 in
      let l1,l2 = split2 n1 l in
      let (nv1,vl1,t1) = var_list l1
      and (nv2,vl2,t2) = var_list l2 in
      (* test and debug *)
(*       assert ((nv1 = nv2) or (nv1 = nv2 - 1)); *)
(*       QualEnv.iter (fun _ l -> assert ((List.length l) = nv1)) vl1; *)
(*       QualEnv.iter (fun _ l -> assert ((List.length l) = nv2)) vl2; *)
(*       let nt1 =  *)
(*         begin *)
(*           match (count t1) with *)
(*             None -> assert false *)
(*           | Some n -> n *)
(*         end in *)
(*       assert (nt1 = nv1);  *)
(*       let nt2 = *)
(*         begin *)
(*           match (count t2) with *)
(*           | None -> assert false *)
(*           | Some n -> n *)
(*         end in *)
(*       assert (nt2 = nv2); *)
      let vl =
        QualEnv.fold (fun c l m -> QualEnv.add c (true::l) m) vl2
          (QualEnv.fold
             (if nv1 = nv2
              then (fun c l m -> QualEnv.add c (false::l) m)
              else (fun c l m -> QualEnv.add c (false::false::l) m))
             vl1
             QualEnv.empty) in
      let t1 = if nv1 = nv2 then t1 else Tree(t1,Node(None)) in
      let t = Tree(t1,t2) in
      nv2 + 1, vl, t

let nvar_list prefix n =
  let rec varl acc = function
    | 0 -> acc
    | n ->
        let acc = (prefix ^ "_" ^ (string_of_int n)) :: acc in
        varl acc (n-1) in
  varl [] n

let translate_pat env pat =
  let rec trans = function
    | Evarpat(name) ->
        begin
          try
            let info = Env.find name env in
            match info.var_enum.ty_nb_var with
            | 1 ->
                Evarpat(List.nth info.var_list 0)
            | _ ->
                let varpat_list = info.var_list in
                Etuplepat(List.map (fun v -> Evarpat(v)) varpat_list)
          with Not_found -> Evarpat(name)
        end
    | Etuplepat(pat_list) -> Etuplepat(List.map trans pat_list) in
  trans pat

let translate_ty ty =
  let rec trans ty =
    match ty with
    | Tid({ qual = Pervasives; name = "bool" }) -> ty
    | Tid(name) ->
        begin
          try
            let info = get_enum name in
            begin match info with
            | Type(_) -> ty
            | Enum { ty_nb_var = 1 } -> ty_bool
            | Enum { ty_nb_var = n } ->
                let strlist = nvar_list "" n in
                Tprod(List.map (fun _ -> ty_bool) strlist)
            end
          with Not_found -> ty
        end
    | Tprod(ty_list) -> Tprod(List.map trans ty_list)
    | Tarray(ty,se) -> Tarray(trans ty,se)
    | Tinvalid -> assert false
  in
  trans ty

let rec on_list ck bl vtree =
  match bl, vtree with
  | [], _ -> ck
  | b::bl', VNode(v,t0,t1) ->
      let (c,t) = if b then (ctrue,t1) else (cfalse,t0) in
      on_list (Clocks.Con(ck,c,v)) bl' t
  | _::_, Vempty -> failwith("on_list: non-coherent boolean list and tree")

let rec translate_ck env ck =
  match ck with
  | Clocks.Cbase -> Clocks.Cbase
  | Clocks.Cvar {contents = Clink(ck)} -> translate_ck env ck
  | Clocks.Cvar {contents = Cindex(_)} -> ck
  | Clocks.Con(ck,c,n) ->
      let ck = translate_ck env ck in
      begin
        try
          let info = Env.find n env in
          let bl = QualEnv.find c info.var_enum.ty_assoc in
          on_list ck bl info.clocked_var
        with Not_found ->
          (* Boolean clock *)
          Clocks.Con(ck,c,n)
      end

let rec translate_ct env ct =
  match ct with
  | Ck(ck) -> Ck(translate_ck env ck)
  | Cprod(l) -> Cprod(List.map (translate_ct env) l)

let translate_const c ty ct e =
  match c.se_desc,ty with
  | _, Tid({ qual = Pervasives; name = "bool" }) -> Econst(c)
  | Sconstructor(cname),Tid(tname) ->
      begin
        try
          begin
            match (get_enum tname) with
            | Type _ -> Econst(c)
            | Enum { ty_assoc = assoc } ->
                let bl = QualEnv.find cname assoc in
                let b_list = List.map (fun b -> Econst(sbool b)) bl in
                begin
                  match b_list with
                  | [] -> assert false
                  | [b] -> b
                  | _::_ ->
                      mk_tuple
                        (List.map
                           (fun b -> {e with
                                        e_desc = b;
                                        e_ct_annot = ct;
                                        e_ty = ty_bool })
                           b_list)
                end
          end
        with Not_found -> Econst(c)
      end
  | _ -> Econst(c)

let new_var_list d_list ty ck n =
  let rec varl acc d_list = function
    | 0 -> acc,d_list
    | n ->
        let v = fresh "bool" in
        let acc = v :: acc in
        let d_list = (mk_var_dec ~clock:ck v ty ~linearity:Linearity.Ltop) :: d_list in
        varl acc d_list (n-1) in
  varl [] d_list n

let assert_ck = function
    Some(Ck(ck)) -> ck
  | _ -> assert false

let intro_tuple context e =
  let n =
    match e.e_ty with
    | Tprod(l) -> List.length l
    | _ -> assert false in
  match e.e_desc with
    Eapp({a_op=Etuple},e_l,None) -> context,e_l
  | _ ->
      let (d_list,eq_list) = context in
      (* e is not a tuple, therefore e.e_ct_annot = Ck(ck) *)
      let ck = assert_ck e.e_ct_annot in
      let v_list,d_list = new_var_list d_list ty_bool ck n in
      let pat = Etuplepat(List.map (fun v -> Evarpat(v)) v_list) in
      let eq_list = (mk_equation (Eeq(pat,e))) :: eq_list in
      let e_list = List.map (fun v -> { e with e_ty = ty_bool; e_desc = Evar(v) }) v_list in
      (d_list,eq_list),e_list

let rec when_list e bl vtree =
  match bl, vtree with
  | [], _ -> e
  | b::bl', VNode(v,t0,t1) ->
      let (c,t) = if b then (ctrue,t1) else (cfalse,t0) in
      let ck = assert_ck e.e_ct_annot in
      (* let e_v = mk_exp (Evar v) ~ct_annot:(Some(Ck(ck))) ty_bool in *)
      let e_when = { e with
                       e_ct_annot = Some (Ck(Clocks.Con(ck,c,v)));
                       e_desc = Ewhen(e,c,v) } in
      when_list e_when bl' t
  | _::_, Vempty -> failwith("when_list: non-coherent boolean list and tree")

let rec when_ck desc li ty ck =
  match ck with
  | Clocks.Cbase | Clocks.Cvar _ ->
      { e_desc = desc;
        e_level_ck = ck;
        e_ct_annot = Some(Ck(ck));
        e_linearity = li;
        e_ty = ty;
        e_loc = no_location }
  | Clocks.Con(ck',c,v) ->
      let e = when_ck desc li ty ck' in
      (* let e_v = mk_exp (Evar v) ~ct_annot:(Some(Ck(ck'))) ty_bool in *)
      { e_desc = Ewhen(e,c,v);
        e_level_ck = ck;
        e_ct_annot = Some(Ck(ck));
        e_linearity = li;
        e_ty = ty;
        e_loc = no_location }

let rec base_value ck li ty =
  match ty with
  | Tid({qual = Pervasives; name = "int" }) ->
      when_ck (Econst(mk_static_exp ty (Sint(0)))) li ty ck
  | Tid({qual = Pervasives; name = "float"}) ->
      when_ck (Econst(mk_static_exp ty (Sfloat(0.)))) li ty ck
  | Tid({qual = Pervasives; name = "bool" }) ->
      when_ck (Econst(strue)) li ty ck
  | Tid(sname) ->
      begin
        try
          begin
            let info = get_enum sname in
            (* boolean tuple *)
            match info with
            | Type(Type_abs) -> failwith("Abstract types not implemented")
            | Type(Type_alias aty) -> base_value ck li aty
            | Type(Type_enum(l)) ->
                when_ck
                  (Econst(mk_static_exp ty (Sconstructor(List.hd l))))
                  li ty ck
            | Type(Type_struct(l)) ->
                let fields =
                  List.map
                    (fun {f_name = name; f_type = ty} ->
                       name,(base_value ck li ty))
                    l in
                when_ck (Estruct(fields)) li ty ck
            | Enum { ty_nb_var = 1 } ->
                when_ck (Econst(strue)) li ty_bool ck
            | Enum { ty_nb_var = n } ->
                let e = when_ck (Econst(strue)) li ty_bool ck in
                let rec aux acc = function
                  | 0 -> acc
                  | n -> aux (e::acc) (n-1) in
                let e_list = aux [] n in
                { e_desc = mk_tuple e_list;
                  e_ty = Tprod(List.map (fun _ -> ty_bool) e_list);
                  e_level_ck = Clocks.Cbase;
                  e_ct_annot = Some(Ck(ck));
                  e_linearity = li;
                  e_loc = no_location }
          end
        with Not_found ->
          Printf.printf "Name : %s\n" sname.name; assert false
      end
  | Tprod(ty_list) ->
      let e_list = List.map (base_value ck li) ty_list in
      { e_desc = mk_tuple e_list;
        e_ty = Tprod(List.map (fun e -> e.e_ty) e_list);
        e_level_ck = Clocks.Cbase;
        e_ct_annot = Some(Ck(ck));
        e_linearity = li;
        e_loc = no_location;
      }
  | Tarray(ty,se) ->
      let e = base_value ck li ty in
      { e_desc = Eapp((mk_app ~params:[se] Earray_fill), [e], None);
        e_ty = Tarray(e.e_ty,se);
        e_level_ck = Clocks.Cbase;
        e_ct_annot = Some(Ck(ck));
        e_linearity = li;
        e_loc = no_location;
      }
  | Tinvalid -> failwith("Boolean: invalid type")

let rec merge_tree ck ty li e_map btree vtree =
  match btree, vtree with
  | Node(None), _ -> base_value ck li ty
  | Node(Some name), _ ->
      let e = QualEnv.find name e_map in
      { e with e_ct_annot = Some(Ck(ck)) }
  | Tree(t1,t2), VNode(v,vt1,vt2) ->
      let e1 = merge_tree (Clocks.Con(ck,cfalse,v)) ty li e_map t1 vt1
      and e2 = merge_tree (Clocks.Con(ck,ctrue,v)) ty li e_map t2 vt2
      in
      (* let e_v = mk_exp (Evar v) ~ct_annot:(Some(Ck(ck))) ty_bool in *)
      { e_desc = Emerge(v,[(cfalse,e1);(ctrue,e2)]);
        e_ty = ty;
        e_level_ck = Clocks.Cbase;
        e_ct_annot = Some(Ck(ck));
        e_linearity = li;
        e_loc = no_location }
  | Tree (_,_), Vempty -> failwith("merge_tree: non-coherent trees")


let rec translate env context ({e_desc = desc; e_ty = ty; e_ct_annot = ct} as e) =
  let ct = Misc.optional (translate_ct env) ct in
  let context,desc =
    match desc with
    | Econst(c) ->
        context, translate_const c ty ct e
    | Evar(name) ->
        let desc = begin
          try
            let info = Env.find name env in
            if info.var_enum.ty_nb_var = 1 then
              Evar(List.nth info.var_list 0)
            else
              let ident_list = info.var_list in
              mk_tuple (List.map
                          (fun v -> { e with
                                        e_ty = ty_bool;
                                        e_ct_annot = ct;
                                        e_desc = Evar(v); })
                          ident_list)
          with Not_found -> Evar(name)
        end in
        context,desc
    | Efby(e1,e2) ->
        let context,e1 = translate env context e1 in
        let context,e2 = translate env context e2 in
        context,Efby(e1,e2)
    | Epre(None, e) ->
        let context,e = translate env context e in
        context,Epre(None,e)
    | Epre(Some c,e) ->
        let e_c = translate_const c ty ct e in
        let context,e = translate env context e in
        begin
          match e_c with
          | Econst(c) -> context,Epre(Some c,e)
          | Eapp({ a_op = Etuple },e_c_l,None) ->
              let context,e_l = intro_tuple context e in
              let c_l = List.map (function
                                    | { e_desc = Econst(c) } -> c
                                    | _ -> assert false) e_c_l in
              context,
              mk_tuple
                (List.map2
                   (fun c e -> { e with
                                   e_ty = ty_bool;
                                   e_desc = Epre(Some c,e)})
                   c_l e_l)
          | _ -> assert false
        end
    | Eapp(app, e_list, r) ->
        let context,e_list = translate_list env context e_list in
        context, Eapp(app, e_list, r)
    | Ewhen(e,c,ck) ->
        let context,e = translate env context e in
        begin
          try
            let info = Env.find ck env in
            let bl = QualEnv.find c info.var_enum.ty_assoc in
            let e_when = when_list e bl info.clocked_var in
            context,e_when.e_desc
          with Not_found ->
            (* Boolean clock *)
            context,Ewhen(e,c,ck)
        end
    | Emerge(ck,l) (* of name * (longname * exp) list *)
      ->
        begin
          try
            let info = Env.find ck env in
            let context,e_map = List.fold_left
              (fun (context,e_map) (n,e) ->
                 let context,e = translate env context e in
                 context,QualEnv.add n e e_map)
              (context,QualEnv.empty) l in
            let e_merge =
              merge_tree (assert_ck ct) ty e.e_linearity e_map
                info.var_enum.ty_tree
                info.clocked_var in
            context,e_merge.e_desc
          with Not_found ->
            (* Boolean clock *)
            let context, l =
              List.fold_left
                (fun (context,acc_l) (n,e) ->
                   let context,e = translate env context e in
                   context, (n,e)::acc_l)
                (context,[]) l in
            context,Emerge(ck,l)
        end
    | Esplit(e1,e2) ->
        let context,e1 = translate env context e1 in
        let context,e2 = translate env context e2 in
        context,Esplit(e1,e2)
    | Estruct(l) ->
        let context,acc =
          List.fold_left
            (fun (context,acc) (c,e) ->
               let context,e = translate env context e in
               (context,(c,e)::acc))
            (context,[]) l in
        context,Estruct(List.rev acc)
    | Eiterator(it,app,se,pe_list,e_list,r) ->
        let context,pe_list = translate_list env context pe_list in
        let context,e_list = translate_list env context e_list in
        context,Eiterator(it,app,se,pe_list,e_list,r)
    | Elast _ ->
        failwith("Boolean: not supported expression (abstract tree should be normalized)")
  in
  context,{ e with
              e_level_ck = translate_ck env e.e_level_ck;
              e_desc = desc;
              e_ty = translate_ty ty;
              e_ct_annot = ct}

and translate_list env context e_list =
  let context,acc_e =
    List.fold_left
      (fun (context,acc_e) e ->
         let context,e = translate env context e in
         (context,e::acc_e))
      (context,[]) e_list in
  context,List.rev acc_e

(* Tranlate variable declaration list : outputs
   - new declaration list
   - added local variables suffixed with "(_(1|0))*" for clock coherence
   - equations of these added variables
*)
let var_dec_list (acc_vd,acc_loc,acc_eq) var_from n =

  (* when_ck [v3_1_0;v2_1;v1] (ck on True(v1) on False(v2_1) on True(v3_1_0)) v4
     = ((v4 when True(v1)) when False(v2_1)) when True(v3_1_0)
     -> builds v4_1_0_1
  *)
  let rec when_ck ckvar_list ck var =
    match ckvar_list,ck with
    | [], _ ->
        { e_desc = Evar(var);
          e_level_ck = ck;
          e_ct_annot = Some(Ck(ck));
          e_ty = ty_bool;
          e_linearity = var_from.v_linearity;
          e_loc = no_location }
    | _ckvar::l, Clocks.Con(ck',c,v) ->
        (* assert v = _ckvar *)
        let e = when_ck l ck' var in
        (* let e_v = mk_exp (Evar v) ~ct_annot:(Some(Ck(ck'))) ty_bool in *)
        { e_desc = Ewhen(e,c,v);
          e_level_ck = ck;
          e_ct_annot = Some(Ck(ck));
          e_ty = ty_bool;
          e_linearity = var_from.v_linearity;
          e_loc = no_location }
    | _ -> failwith("when_ck: non coherent clock and var list")
  in

  let prefix = name var_from.v_ident in

  (* From v, build of v1...vn *)
  let rec varl acc_vd k =
    if k>n
    then acc_vd
    else
      begin
        let var_prefix = prefix ^ "_" ^ (string_of_int k) in
        let var = fresh var_prefix in
        (* addition of var_k *)
        let acc_vd = { var_from with
                         v_ident = var;
                         v_type = ty_bool } :: acc_vd in
        varl acc_vd (k+1)
      end in

  let vd_list = varl [] 1 in
  (* v_list = [vn;...;v1] *)
  let acc_vd = List.rev_append vd_list acc_vd in

  let v_list = List.rev_map (fun vd -> vd.v_ident) vd_list in

  (* From v1...vn, build clocked tree
     ( vi_(0|1)* on ... on (True|False) (v1) ) *)
  let rec clocked_tree (acc_loc,acc_eq) acc_var suffix v_list ck =
    begin match v_list, acc_var with
      [], _ ->
        (* Leafs *)
        acc_loc,acc_eq,Vempty
    | v1::v_list, [] ->
        (* Root : no new id, only rec calls for sons *)
        (* Build left son (ck on False(vi_...)) *)
        let ck_0 = Clocks.Con(ck,cfalse,v1) in
        let acc_loc,acc_eq,t0 =
          clocked_tree
            (acc_loc,acc_eq)
            ([v1])
            ("_0")
            v_list ck_0 in
        (* Build right son (ck on True(vi_...))*)
        let ck_1 = Clocks.Con(ck,ctrue,v1) in
        let acc_loc,acc_eq,t1 =
          clocked_tree
            (acc_loc,acc_eq)
            ([v1])
            ("_1")
            v_list ck_1 in
        acc_loc,acc_eq,VNode(v1,t0,t1)
    | vi::v_list, _ ->
        (* Build name vi_(0|1)* *)
        let v = (name vi) ^ suffix in
        (* Build ident from this name *)
        let id = fresh v in
        let acc_loc = { v_ident = id;
                        v_type = ty_bool;
                        v_linearity = var_from.v_linearity;
                        v_clock = ck;
                        v_last = Var;
                        v_loc = no_location } :: acc_loc in
        (* vi_... = vi when ... when (True|False)(v1) *)
        let acc_eq =
          (mk_equation (Eeq(Evarpat(id),(when_ck acc_var ck vi))))
          ::acc_eq in
        (* Build left son (ck on False(vi_...)) *)
        let ck_0 = Clocks.Con(ck,cfalse,id) in
        let acc_loc,acc_eq,t0 =
          clocked_tree
            (acc_loc,acc_eq)
            (id::acc_var)
            (suffix ^ "_0")
            v_list ck_0 in
        (* Build right son (ck on True(vi_...))*)
        let ck_1 = Clocks.Con(ck,ctrue,id) in
        let acc_loc,acc_eq,t1 =
          clocked_tree
            (acc_loc,acc_eq)
            (id::acc_var)
            (suffix ^ "_1")
            v_list ck_1 in
        acc_loc,acc_eq,VNode(id,t0,t1)
    end
  in

  let acc_loc,acc_eq,t =
    clocked_tree (acc_loc,acc_eq) [] "" v_list var_from.v_clock in

  (acc_vd,acc_loc,acc_eq,v_list,t)

let buildenv_var_dec (acc_vd,acc_loc,acc_eq,env) ({v_type = ty} as v) =
  match ty with
  | Tprod _ | Tarray _ ->
      v::acc_vd, acc_loc, acc_eq, env
  | Tid(tname) ->
      begin
        match tname with
        | { qual = Pervasives; name = ("bool" | "int" | "float") } ->
            v::acc_vd, acc_loc, acc_eq, env
        | _ ->
            begin
              try
                begin
                  match (get_enum tname) with
                  | Type _ -> v::acc_vd, acc_loc, acc_eq ,env
                  | Enum(info) ->
                      let (acc_vd,acc_loc,acc_eq,vl,t) =
                        var_dec_list
                          (acc_vd,acc_loc,acc_eq)
                          v info.ty_nb_var in
                      let env =
                        Env.add
                          v.v_ident
                          { var_enum = info;
                            var_list = vl;
                            clocked_var = t }
                          env in
                      acc_vd, acc_loc, acc_eq, env
                end
              with Not_found -> v::acc_vd, acc_loc, acc_eq, env
            end
      end
   | Tinvalid -> failwith("Boolean: invalid type")

let buildenv_var_dec_list env vlist =
  List.fold_left buildenv_var_dec ([],[],[],env) vlist

let translate_var_dec env ({ v_clock = ck } as v) =
  { v with v_clock = translate_ck env ck }

let translate_var_dec_list env vlist =
  List.map (translate_var_dec env) vlist

let rec translate_block env add_locals add_eqs ({ b_local = v;
                                              b_equs = eq_list; } as b) =
  let v, v',v_eq,env = buildenv_var_dec_list env v in
  let v = v@v'@add_locals in
  let v = translate_var_dec_list env v in
  let eq_list = eq_list@v_eq@add_eqs in
  let context = translate_eqs env eq_list in
  let d_list,eq_list = context in
  { b with
      b_local = v@d_list;
      b_equs = eq_list }, env

and translate_eq env context ({eq_desc = desc} as eq) =
  let desc,(d_list,eq_list) =
    match desc with
    | Eblock block ->
        let block, _ = translate_block env [] [] block in
        Eblock block,
        context
    | Eeq(pat,e) ->
        let pat = translate_pat env pat in
        let context,e = translate env context e in
        Eeq(pat,e),
        context
    | _ -> failwith("Boolean pass: control structures should be removed")
  in
  d_list,{ eq with eq_desc = desc }::eq_list

and translate_eqs env eq_list =
  List.fold_left
    (fun context eq ->
       translate_eq env context eq) ([],[]) eq_list

let translate_objectives env context objs =
  let context, objs =
    List.fold_left
      (fun (context,ol) o ->
       let context, e = translate env context o.o_exp in
       context, { o with o_exp = e } :: ol)
      (context, [])
      objs in
  context, List.rev objs

let translate_contract env contract =
  match contract with
  | None -> None, env
  | Some { c_assume = e_a;
           c_objectives = objs;
           c_assume_loc = e_a_loc;
           c_enforce_loc = e_g_loc;
           c_controllables = cl;
           c_block = b } ->
      let cl, cl_loc, cl_eq, env = buildenv_var_dec_list env cl in
      let cl = translate_var_dec_list env cl in
      let ({ b_local = v;
             b_equs = eqs } as b), env'
        = translate_block env cl_loc cl_eq b in
      let context, e_a = translate env' (v,eqs) e_a in
      let context, e_a_loc = translate env' context e_a_loc in
      let context, objs = translate_objectives env' context objs in
      let context, e_g_loc = translate env' context e_g_loc in
      let (d_list,eq_list) = context in
      Some { c_block = { b with
                           b_local = d_list;
                           b_equs = eq_list };
             c_assume = e_a;
             c_objectives = objs;
             c_assume_loc = e_a_loc;
             c_enforce_loc = e_g_loc;
             c_controllables = cl },
      env

let node ({ n_input = inputs;
            n_output = outputs;
            n_contract = contract;
            n_block = b } as n) =
  Idents.enter_node n.n_name;
  let inputs,in_loc,in_eq,env = buildenv_var_dec_list Env.empty inputs in
  let outputs,out_loc,out_eq,env = buildenv_var_dec_list env outputs in
  let contract, env = translate_contract env contract in
  let add_locals = in_loc@out_loc in
  let add_eqs = in_eq@out_eq in
  let b,_ = translate_block env add_locals add_eqs b in
  let b,_ = translate_block env [] [] b in
  { n with
      n_input = List.rev inputs;
      n_output = List.rev outputs;
      n_contract = contract;
      n_block = b }

let program_desc p_desc =
  match p_desc with
  | Pnode(n) -> Pnode(node n)
  | _ -> p_desc

let build p_desc =
  match p_desc with
  | Ptype(type_dec) ->
      begin
        let tenv =
          match type_dec.t_desc with
          | Type_enum clist ->
              let (n,env,t) = var_list clist in
              Enum({ ty_nb_var = n;
                     ty_assoc = env;
                     ty_tree = t})
          | tdesc -> Type(tdesc) in
        enum_types := QualEnv.add type_dec.t_name tenv !enum_types
      end
  | _ -> ()

let program ({ p_desc = d_list } as p) =
  List.iter build d_list;
  { p with p_desc = List.map program_desc d_list }
