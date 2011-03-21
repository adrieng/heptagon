(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

type class_name = Names.qualname (** [qual] is the package name, [Name] is the class name *)
type obj_ident = Idents.var_ident
type constructor_name = Names.qualname (** [Qual] is the enum class name (type), [NAME] is the constructor name *)
type const_name = Names.qualname
type method_name = Names.name
type field_name = Names.name
type field_ident = Idents.var_ident
type op_name = Names.qualname
type var_ident = Idents.var_ident

type ty = Tclass of class_name
        | Tgeneric of class_name * ty list
        | Tbool
        | Tint
        | Tfloat
        | Tarray of ty * exp
        | Tref of ty
        | Tunit

and classe = { c_protection : protection;
               c_static     : bool;
               c_name       : class_name;
               c_imports     : class_name list;
               c_implements : class_name list;
               c_kind       : class_kind }

and class_kind = Cenum of constructor_name list
               | Cgeneric of class_desc

and class_desc = { cd_fields       : field list;
                   cd_classs       : classe list;
                   cd_constructors : methode list;
                   cd_methodes     : methode list; }

and var_dec = { vd_type  : ty;
                vd_ident : var_ident }

and protection = Ppublic | Pprotected | Pprivate | Ppackage

and field = { f_protection : protection;
              f_static     : bool;
              f_final      : bool;
              f_type       : ty;
              f_ident      : field_ident;
              f_value      : exp option }

and methode = { m_protection : protection;
                m_static     : bool;
                m_name       : method_name;
                m_args       : var_dec list;
                m_returns    : ty;
                m_throws     : class_name list;
                m_body       : block; }


and block = { b_locals : var_dec list;
              b_body   : act list; }

and act = Anewvar of var_dec * exp
        | Aassgn of pattern * exp
        | Amethod_call of exp * method_name * exp list
        | Aswitch of exp * (constructor_name * block) list
        | Aif of exp * block
        | Aifelse of exp * block * block
        | Ablock of block
        | Afor of var_dec * exp * exp * block
        | Areturn of exp

and exp = Eval of pattern
        | Ethis
        | Efun of op_name * exp list
        | Emethod_call of exp * method_name * exp list
        | Enew of ty * exp list
        | Enew_array of ty * exp list (** [ty] is the array base type *)
        | Evoid (*printed as nothing*)
        | Ecast of ty * exp
        | Svar of const_name
        | Sint of int
        | Sfloat of float
        | Sbool of bool
        | Sconstructor of constructor_name
        | Sstring of string
        | Snull


and pattern = Pfield of pattern * field_name
            | Pclass of class_name
            | Pvar of var_ident
            | Parray_elem of pattern * exp
            | Pthis of field_ident

type program = classe list


let rec default_value ty = match ty with
  | Tclass _ -> Snull
  | Tgeneric _ -> Snull
  | Tbool -> Sbool true
  | Tint -> Sint 0
  | Tfloat -> Sfloat 0.0
  | Tunit -> Evoid
  | Tref t ->  default_value t
  | Tarray _ -> Enew_array (ty,[])


let java_pervasive_class c = Names.qualname_of_string ("jeptagon.Pervasives."^c)
let the_java_pervasives = Names.qualname_of_string "jeptagon.Pervasives"


let mk_var x = Eval (Pvar x)

let mk_var_dec x ty =
  { vd_type = ty; vd_ident = x }

let mk_block ?(locals=[]) b =
  { b_locals = locals; b_body = b; }


let mk_methode ?(protection=Ppublic) ?(static=false) ?(args=[]) ?(returns=Tunit) ?(throws=[])
               body name =
  { m_protection = protection; m_static = static; m_name = name; m_args = args;
    m_throws = throws; m_returns = returns; m_body = body; }

let mk_classe ?(imports=[]) ?(protection=Ppublic) ?(static=false) ?(fields=[])
              ?(classes=[]) ?(constrs=[]) ?(methodes=[]) ?(implements=[])
              class_name =
  { c_protection = protection; c_static = static; c_name = class_name; c_imports = imports; c_implements = implements;
    c_kind = Cgeneric { cd_fields = fields; cd_classs = classes; cd_constructors = constrs; cd_methodes = methodes; } }

let mk_enum ?(protection=Ppublic) ?(static=false) ?(imports=[]) ?(implements=[])
            constructor_names class_name =
  { c_protection = protection; c_static = static; c_name = class_name; c_imports = imports; c_implements = implements;
    c_kind = Cenum(constructor_names) }


let mk_field ?(protection = Ppublic) ?(static = false) ?(final = false) ?(value = None)
             ty ident =
  { f_protection = protection; f_static = static; f_final = final; f_type = ty; f_ident = ident; f_value = value }

let vds_to_exps vd_l = List.map (fun { vd_ident = x } -> mk_var x) vd_l

let vds_to_fields ?(protection=Ppublic) vd_l =
  List.map (fun { vd_ident = x; vd_type = t } -> mk_field ~protection:protection t x) vd_l
