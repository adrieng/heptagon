(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Object code internal representation *)

open Misc
open Names
open Ident

type var_name = ident
type type_name = longname
type fun_name = longname
type class_name = name
type instance_name = longname
type obj_name = name
type op_name = longname
type field_name = longname

type ty =
  | Tint
  | Tfloat
  | Tbool
  | Tid of type_name
  | Tarray of ty * int

type type_dec =
    { t_name : name;
      t_desc : tdesc }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of (name * ty) list

type const =
  | Cint of int
  | Cbool of bool
  | Cfloat of float
  | Cconstr of longname
  | Carray_power of int * const
  | Carray of const list
  | Ctuple of const list

type lhs =
  | Var of var_name
  | Mem of var_name
  | Field of lhs * field_name
  | Array of lhs * exp

and exp =
  | Lhs of lhs
  | Const of const
  | Op of op_name * exp list
  | Struct_lit of type_name * (field_name * exp) list
  | Array_lit of exp list

type obj_call =
  | Context of obj_name
  | Array_context of obj_name * lhs

type act =
  | Assgn of lhs * exp
  | Step_ap of lhs list * obj_call * exp list
  | Comp of act * act
  | Case of exp * (longname * act) list
  | For of var_name * int * int * act
  | Reinit of obj_name
  | Nothing

type var_dec =
    { v_ident : var_name;
      v_type : ty; }

type obj_dec =
    { obj : obj_name;
      cls : instance_name;
      size : int; }

type step_fun =
    { inp    : var_dec list;
      out    : var_dec list;
      local  : var_dec list;
      controllables : var_dec list; (* GD : ugly patch to delay controllable
                                       variables definition to target code
                                       generation *)
      bd     : act }

type reset_fun = act

type class_def =
    { cl_id : class_name;
      mem   : var_dec list;
      objs  : obj_dec list;
      reset : reset_fun;
      step  : step_fun; }

type program =
    { o_pragmas: (name * string) list;
      o_opened : name list;
      o_types : type_dec list;
      o_defs  : class_def list }

let mk_var_dec name ty =
  { v_ident = name; v_type = ty }

let rec var_name x =
  match x with
    | Var x -> x
    | Mem x -> x
    | Field(x,_) -> var_name x
    | Array(l, _) -> var_name l

(** Returns whether an object of name n belongs to
    a list of var_dec. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n or (vd_mem n l)

(** Returns the var_dec object corresponding to the name n
    in a list of var_dec. *)
let rec vd_find n = function
  | [] -> Format.printf "Not found var %s\n" (name n); raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

let lhs_of_exp = function
  | Lhs l -> l
  | _ -> assert false

module Printer =
struct
  open Format
  open Pp_tools

  let rec print_type ff = function
    | Tint    -> fprintf ff "int"
    | Tfloat  -> fprintf ff "float"
    | Tbool   -> fprintf ff "bool"
    | Tid(id) -> print_longname ff id
    | Tarray(ty, n) ->
        print_type ff ty;
        fprintf ff "^%d" n

  let print_vd ff vd =
    fprintf ff "@[<v>";
    print_ident ff vd.v_ident;
    fprintf ff ": ";
    print_type ff vd.v_type;
    fprintf ff "@]"

  let print_obj ff { cls = cls; obj = obj; size = n } =
    fprintf ff "@[<v>"; print_name ff obj;
    fprintf ff " : "; print_longname ff cls;
    if n <> 1 then
      fprintf ff "[%d]" n;
    fprintf ff ";@]"

  let rec print_c ff = function
    | Cint i       -> fprintf ff "%d" i
    | Cfloat f     -> fprintf ff "%f" f
    | Cconstr(tag) -> print_longname ff tag
    | Carray(n,c) ->
        print_c ff c;
        fprintf ff "^%d" n

  let rec print_lhs ff e =
    match e with
      | Var x           -> print_ident ff x
      | Mem x           -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
      | Field (l, f)    -> print_lhs ff l; fprintf ff ".%s" (shortname f)
      | Array(x, idx) ->
          print_lhs ff x;
          fprintf ff "[";
          print_exp ff idx;
          fprintf ff "]"

  and print_exps ff e_list = print_list_r print_exp "" "," "" ff e_list

  and print_exp ff = function
    | Lhs lhs -> print_lhs ff lhs
    | Const c         -> print_c ff c
    | Op(op, e_list) -> print_op ff op e_list
    | Struct_lit(_,f_e_list) ->
        fprintf ff "@[<v 1>";
        print_list_r
          (fun ff (field, e) -> print_longname ff field;fprintf ff " = ";
             print_exp ff e)
          "{" ";" "}" ff f_e_list;
        fprintf ff "@]"
    | Array_lit e_list ->
        fprintf ff "@[";
        print_list_r print_exp "[" ";" "]" ff e_list;
        fprintf ff "@]"

  and print_op ff op e_list =
    print_longname ff op;
    print_list_r print_exp "(" "," ")" ff e_list

  let print_asgn ff pref x e =
    fprintf ff "@[%s" pref; print_lhs ff x; fprintf ff " = ";
    fprintf ff "@["; print_exp ff e; fprintf ff "@]";
    fprintf ff "@]"

  let print_obj_call ff = function
    | Context o -> print_name ff o
    | Array_context (o, i) ->
        fprintf ff "%a[%a]"
          print_name o
          print_lhs i

  let rec print_act ff a =
    match a with
      | Assgn (x, e) -> print_asgn ff "" x e
      | Comp (a1, a2) ->
          fprintf ff "@[<v>";
          print_act ff a1;
          fprintf ff ";@,";
          print_act ff a2;
          fprintf ff "@]"
      | Case(e, tag_act_list) ->
          fprintf ff "@[<v>@[<v 2>switch (";
          print_exp ff e; fprintf ff ") {@,";
          print_tag_act_list ff tag_act_list;
          fprintf ff "@]@,}@]"
      | For(x, i1, i2, act) ->
          fprintf ff "@[<v>@[<v 2>for %s=%d to %d : {@, %a @]@,}@]"
            (name x) i1 i2
            print_act act
      | Step_ap (var_list, o, es) ->
          print_list print_lhs "(" "," ")" ff var_list;
          fprintf ff " = "; print_obj_call ff o; fprintf ff ".step(";
          fprintf ff "@["; print_exps ff es; fprintf ff "@]";
          fprintf ff ")"
      | Reinit o ->
          print_name ff o; fprintf ff ".reset()"
      | Nothing -> fprintf ff "()"

  and print_tag_act_list ff tag_act_list =
    print_list
      (fun ff (tag, a) ->
         fprintf ff "@[<hov 2>case@ ";
         print_longname ff tag;
         fprintf ff ":@ ";
         print_act ff a;
         fprintf ff "@]") "" "" "" ff tag_act_list

  let print_step ff { inp = inp; out = out; local = nl; bd = bd } =
    fprintf ff "@[<v 2>";
    fprintf ff "step(@[";
    print_list_r print_vd "(" ";" ")" ff inp;
    fprintf ff "@]) returns ";
    print_list_r print_vd "(" ";" ")" ff out;
    fprintf ff "@]){@,";
    if nl <> [] then begin
      fprintf ff "@[<hov 4>var ";
      print_list_r print_vd "" ";" "" ff nl;
      fprintf ff ";@]@,"
    end;
    print_act ff bd;
    fprintf ff "}@]"

  let print_reset ff act =
    fprintf ff "@[<v 2>";
    fprintf ff "reset() {@,";
    print_act ff act;
    fprintf ff "}@]"

  let print_def ff
      { cl_id = id; mem = mem; objs = objs; reset = reset; step = step } =
    fprintf ff "@[<v 2>machine "; print_name ff id; fprintf ff " =@,";
    if mem <> [] then begin
      fprintf ff "@[<hov 4>var ";
      print_list_r print_vd "" ";" "" ff mem;
      fprintf ff ";@]@,"
    end;
    if objs <> [] then begin
      fprintf ff "@[<hov 4>obj ";
      print_list print_obj "" ";" "" ff objs;
      fprintf ff ";@]@,"
    end;
    print_reset ff reset;
    fprintf ff "@,";
    print_step ff step;
    fprintf ff "@]"

  let print_type_def ff { t_name = name; t_desc = tdesc } =
    match tdesc with
      | Type_abs -> fprintf ff "@[type %s@\n@]" name
      | Type_enum(tag_name_list) ->
          fprintf ff "@[type %s = " name;
          print_list_r print_name "" "|" "" ff tag_name_list;
          fprintf ff "@\n@]"
      | Type_struct(f_ty_list) ->
          fprintf ff "@[type %s = " name;
          fprintf ff "@[<v 1>";
          print_list
            (fun ff (field, ty) ->
               print_name ff field;
               fprintf ff ": ";
               print_type ff ty) "{" ";" "}" ff f_ty_list;
          fprintf ff "@]@.@]"

  let print_open_module ff name =
    fprintf ff "@[open ";
    print_name ff name;
    fprintf ff "@.@]"

  let print_prog ff { o_opened = modules; o_types = types; o_defs = defs } =
    List.iter (print_open_module ff) modules;
    List.iter (print_type_def ff) types;
    List.iter (fun def -> (print_def ff def; fprintf ff "@ ")) defs

  let print oc p =
    let ff = formatter_of_out_channel oc in
    fprintf ff "@[-- Code generated by the MiniLucid Compiler@.";
    fprintf ff "@[<v>"; print_prog ff p; fprintf ff "@]@]@."
end

