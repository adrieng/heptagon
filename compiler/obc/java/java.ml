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
        | Tunit

and classe = { c_protection : protection;
               c_static     : bool;
               c_name       : class_name;
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
              f_name       : field_ident;
              f_value      : exp option }

and methode = { m_protection : protection;
                m_static     : bool;
                m_name       : method_name;
                m_args       : var_dec list;
                m_returns    : ty;
                m_body       : block; }


and block = { b_locals : var_dec list;
              b_body   : act list; }

and act = Anewvar of var_dec * exp
        | Aassgn of pattern * exp
        | Amethod_call of pattern * method_name * exp list
        | Aswitch of exp * (constructor_name * block) list
        | Aif of exp * block
        | Aifelse of exp * block * block
        | Ablock of block
        | Afor of var_dec * exp * exp * block (* TODO var_dec *)
        | Areturn of exp

and exp = Eval of pattern
        | Efun of op_name * exp list
        | Emethod_call of pattern * method_name * exp list
        | Enew of ty * exp list
        | Enew_array of ty * exp list
        | Evoid (*printed as nothing*)
        | Svar of const_name
        | Sint of int
        | Sfloat of float
        | Sbool of bool
        | Sconstructor of constructor_name

and pattern = Pfield of pattern * field_name
            | Pvar of var_ident
            | Parray_elem of pattern * exp
            | Pthis of field_ident

type program = classe list

let mk_var x = Eval (Pvar x)

let mk_var_dec x ty =
  { vd_type = ty; vd_ident = x }

let mk_block ?(locals=[]) b =
  { b_locals = locals; b_body = b; }

let mk_methode ?(protection=Ppublic) ?(static=false) ?(args=[]) ?(returns=Tunit)
               body name =
  { m_protection = protection; m_static = static; m_name = name; m_args = args; m_returns = returns; m_body = body; }

let mk_classe ?(protection=Ppublic) ?(static=false) ?(fields=[]) ?(classes=[]) ?(constrs=[]) ?(methodes=[])
              class_name =
  { c_protection = protection; c_static = static; c_name = class_name;
    c_kind = Cgeneric { cd_fields = fields; cd_classs = classes; cd_constructors = constrs; cd_methodes = methodes; } }

let mk_enum ?(protection=Ppublic) ?(static=false)
            constructor_names class_name =
  { c_protection = protection; c_static = static; c_name = class_name; c_kind = Cenum(constructor_names) }


let mk_field ?(protection = Ppublic) ?(static = false) ?(final = false) ?(value = None)
             ty name =
  { f_protection = protection; f_static = static; f_final = final; f_type = ty; f_name = name; f_value = value }
