%{

open Signature
open Names
open Idents
open Types
open Clocks
open Location
open Minils
open Mls_parsetree
open Mls_utils


%}

%token DOT LPAREN RPAREN LBRACE RBRACE COLON SEMICOL
%token EQUAL EQUALEQUAL BARBAR COMMA BAR LET TEL CONST
%token <string> CONSTRUCTOR
%token <string> NAME
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token TYPE NODE RETURNS VAR OPEN
%token FBY PRE WHEN
%token OR STAR NOT
%token AMPERSAND
%token AMPERAMPER
%token RESET
%token IF THEN ELSE
%token DOUBLE_LESS DOUBLE_GREATER
%token ARROW
%token MERGE
%token POWER
%token AROBASE
%token WITH
%token DOTDOT
%token BASE UNDERSCORE ON COLONCOLON
%token DEFAULT
%token LBRACKET RBRACKET
%token MAP FOLD MAPFOLD
%token <string> PREFIX
%token <string> INFIX0
%token <string> INFIX1
%token <string> INFIX2
%token <string> SUBTRACTIVE
%token <string> INFIX3
%token <string> INFIX4
%token EOF

%right AROBASE
%nonassoc DEFAULT
%left ELSE
%left OR
%left AMPERSAND
%left INFIX0 EQUAL
%right INFIX1 EQUALEQUAL BARBAR AMPERAMPER
%left INFIX2 prefixs
%left STAR INFIX3
%left INFIX4
%left WHEN
%right FBY
%right PRE
%right POWER


%start program
%type <Mls_parsetree.program> program

%%

/** Tools **/
%inline slist(S, x)        : l=separated_list(S, x)                    {l}
%inline snlist(S, x)       : l=separated_nonempty_list(S, x)           {l}
%inline tuple(x)           : LPAREN h=x COMMA t=snlist(COMMA,x) RPAREN { h::t }
%inline option(P,x):
  |/* empty */    { None }
  | P v=x         { Some(v) }

qualified(x) :
  | n=x { Modules.qualname n }
  | m=CONSTRUCTOR DOT n=x { { qual = m; name = n } }

structure(field): LBRACE s=snlist(SEMICOL,field) RBRACE {s}

localize(x): y=x { y, (Loc($startpos(y),$endpos(y))) }


program:
  | o=open_modules c=const_decs t=type_decs n=node_decs EOF
      { mk_program o n t c }

open_modules: l=list(opens) {l}
opens: OPEN c=CONSTRUCTOR {c}

const_decs: c=list(const_dec) {c}
const_dec:
  | CONST n=qualname COLON t=type_ident EQUAL e=const
      { mk_const_dec n t e (Loc($startpos,$endpos)) }

name: n=NAME | LPAREN n=infix RPAREN | LPAREN n=prefix RPAREN { n }
qualname: n=name { Modules.qualname n }

field_type : n=qualname COLON t=type_ident { mk_field n t }

type_ident: qualname { Tid($1) }

type_decs: t=list(type_dec) {t}
type_dec:
  | TYPE n=qualname
    { mk_type_dec Type_abs n (Loc ($startpos,$endpos)) }
  | TYPE n=qualname EQUAL e=snlist(BAR,constructor)
    { mk_type_dec (Type_enum e) n (Loc ($startpos,$endpos)) }
  | TYPE n=qualname EQUAL s=structure(field_type)
    { mk_type_dec (Type_struct s) n (Loc ($startpos,$endpos)) }

node_decs: ns=list(node_dec) {ns}
node_dec:
  NODE n=qualname p=params(n_param) LPAREN args=args RPAREN
  RETURNS LPAREN out=args RPAREN vars=loc_vars eqs=equs
      { mk_node p args out vars eqs ~loc:(Loc ($startpos,$endpos)) n }


args_t: SEMICOL p=args {p}
args:
  | /* empty */ { [] }
  | h=var t=loption(args_t) {h@t}

loc_vars_t:
  | /*empty */ { [] }
  | SEMICOL    { [] }
  | SEMICOL h=var t=loc_vars_t {h@t}
loc_vars_h: VAR h=var t=loc_vars_t  {h@t}
loc_vars: l=loption(loc_vars_h) {l}


ck_base: | UNDERSCORE | BASE {}

ck:
  | ck_base { Cbase }
  | ck=ck ON c=constructor LPAREN x=NAME RPAREN { Con (ck, c, x) }

clock_annot:
  | /*empty*/  { Cbase }
  | COLONCOLON c=ck { c }

var:
  | ns=snlist(COMMA, NAME) COLON t=type_ident c=clock_annot
      { List.map (fun n -> mk_var_dec n t c (Loc ($startpos,$endpos))) ns }

equs: LET e=slist(SEMICOL, equ) TEL { e }
equ: p=pat EQUAL e=exp { mk_equation p e (Loc ($startpos,$endpos)) }

pat:
  | n=NAME                             {Evarpat n}
  | LPAREN p=snlist(COMMA, pat) RPAREN {Etuplepat p}

longname: l=qualified(name) {l}

constructor: /* of type longname */
  | ln=qualified(CONSTRUCTOR) { ln }
  | b=BOOL                    { if b then Initial.ptrue else Initial.pfalse }

field:
  | c=constructor { mk_constructor_exp c (Loc($startpos,$endpos))}


const: c=_const { mk_static_exp ~loc:(Loc ($startpos,$endpos)) c }
_const:
  | i=INT { Sint i }
  | f=FLOAT { Sfloat f }
  | c=constructor { Sconstructor c }

exps: LPAREN e=slist(COMMA, exp) RPAREN {e}

field_exp: longname EQUAL exp { ($1, $3) }


simple_exp:
  | e=_simple_exp {mk_exp e (Loc ($startpos,$endpos)) }
_simple_exp:
  | n=NAME                                 { Evar n }
  | s=structure(field_exp)                 { Estruct s }
  | t=tuple(exp_woc)                       { mk_call [] Etuple t None }
  | t=tuple(const)
      {Econst (mk_static_exp ~loc:(Loc ($startpos,$endpos)) (Stuple t))}
  | LBRACKET es=slist(COMMA, exp) RBRACKET { mk_call [] Earray es None }
  | LPAREN e=_exp RPAREN                   { e }

exp:
  | e=simple_exp { e }
  | e=_exp { mk_exp e (Loc ($startpos,$endpos)) }
exp_woc:
  | e=simple_exp { e }
  | e=_exp_woc { mk_exp e (Loc ($startpos,$endpos)) }

_exp:
  | e=_exp_woc {e}
  | c=const                                { Econst c }
_exp_woc:
  | v=exp FBY e=exp                        { Efby(Some(v), e) }
  | PRE exp                                { Efby(None,$2) }
  | app=funapp a=exps r=reset              { Eapp(app, a, r) }
  | e1=exp i_op=infix e2=exp
      { mk_op_call i_op [e1; e2] }
  | p_op=prefix e=exp %prec prefixs
      { mk_op_call p_op [e] }
  | IF e1=exp THEN e2=exp ELSE e3=exp
      { mk_call [] Eifthenelse [e1; e2; e3] None }
  | e=simple_exp DOT f=field
      { mk_call [f] Efield [e] None }
  | e=exp WHEN c=constructor LPAREN n=name RPAREN  { Ewhen(e, c, n) }
  | MERGE n=name h=handlers  { Emerge(n, h) }
  | LPAREN r=exp WITH DOT f=field EQUAL nv=exp
      { mk_call [f] Efield_update [r; nv] None }
  | e=exp POWER p=e_param
      { mk_call [p] Earray_fill [e] None }
  | e=simple_exp i=indexes(exp) /* not e_params to solve conflicts */
      { mk_call i Eselect [e] None }
  | e=simple_exp i=indexes(exp) DEFAULT d=exp
      { mk_call [] Eselect_dyn ([e; d]@i) None }
  | LPAREN e=exp WITH i=indexes(e_param) EQUAL nv=exp
      { mk_call i Eupdate [e; nv] None }
  | e=simple_exp LBRACKET i1=e_param DOTDOT i2=e_param RBRACKET
      { mk_call [i1; i2] Eselect_slice [e] None }
  | e1=exp AROBASE e2=exp  { mk_call [] Econcat [e1;e2] None }
  | LPAREN f=iterator LPAREN op=funapp RPAREN
      DOUBLE_LESS p=e_param DOUBLE_GREATER
        RPAREN a=exps r=reset  { Eiterator(f,op,p,a,r) }

/* Static indexes [p1][p2]... */
indexes(param): is=nonempty_list(index(param))      { is }
index(param): LBRACKET p=param RBRACKET             { p }




/* Merge handlers ( B -> e ) ( C -> ec )... */
handlers: hs=nonempty_list(handler)    { hs }
handler: LPAREN c=constructor ARROW e=exp RPAREN { c,e }


iterator:
  | MAP     { Imap }
  | FOLD    { Ifold }
  | MAPFOLD { Imapfold }

reset: r=option(RESET,name) { r }

funapp: ln=longname p=params(e_param) { mk_app p (Enode ln) }

/* inline so that precendance of POWER is respected in exp */
%inline e_param: e=exp { e }
n_param: n=NAME COLON ty=type_ident { mk_param n ty }
params(param):
  | /*empty*/                                               { [] }
  | DOUBLE_LESS p=slist(COMMA, param) DOUBLE_GREATER { p }


/*Inlining is compulsory in order to preserve priorities*/
%inline infix:
  | op=INFIX0 | op=INFIX1 | op=INFIX2 | op=INFIX3 | op=INFIX4  { op }
  | STAR            { "*" }
  | EQUAL           { "=" }
  | EQUALEQUAL      { "==" }
  | AMPERSAND       { "&" }   | AMPERAMPER    { "&&" }
  | OR              { "or" }  | BARBAR        { "||" }

%inline prefix:
  | op = PREFIX          { op }
  | NOT                  { "not" }
  | op = SUBTRACTIVE     { "~" ^ op } /*TODO test 3 * -2 and co */





%%
