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
  | n=x { Name(n) }
  | m=CONSTRUCTOR DOT n=x { Modname({ qual = m; id = n }) }
 
structure(field): LBRACE s=snlist(SEMICOL,field) RBRACE {s}

localize(x): y=x { y, (Loc($startpos(y),$endpos(y))) }
 

program:
  | o=open_modules c=const_decs t=type_decs n=node_decs EOF
      { mk_program o n t c }

open_modules: l=list(opens) {l}
opens: OPEN c=CONSTRUCTOR {c}

const_decs: c=list(const_dec) {c}
const_dec:
  | CONST n=NAME COLON t=type_ident EQUAL e=const
      { mk_const_dec n t e (Loc($startpos,$endpos)) }

name: n=NAME | LPAREN n=infix_ RPAREN | LPAREN n=prefix_ RPAREN { n }
ident: n=name { ident_of_name n }

field_type : n=NAME COLON t=type_ident { mk_field n t }

type_ident: NAME { Tid(Name($1)) }

type_decs: t=list(type_dec) {t}
type_dec:
  | TYPE n=NAME
    { mk_type_dec Type_abs n (Loc ($startpos,$endpos)) }
  | TYPE n=NAME EQUAL e=snlist(BAR,NAME)
    { mk_type_dec (Type_enum e) n (Loc ($startpos,$endpos)) }
  | TYPE n=NAME EQUAL s=structure(field_type)
    { mk_type_dec (Type_struct s) n (Loc ($startpos,$endpos)) }

node_decs: ns=list(node_dec) {ns}
node_dec:
  NODE n=name p=params(n_param) LPAREN args=args RPAREN
  RETURNS LPAREN out=args RPAREN vars=loc_vars eqs=equs
      { mk_node ~input:args ~output:out ~local:vars
                ~eq:eqs ~loc:(Loc ($startpos,$endpos)) n }
        

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

ct:
  | LPAREN ctl=snlist(STAR,ct) RPAREN { Cprod ctl }
  | c=ck { Ck c }

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

longname: l=qualified(name) {l} /* qualified var (not a constructor) */
  
constructor: /* of type longname */
  | ln=qualified(CONSTRUCTOR)       { ln }
  | b=BOOL                          { Name(if b then "true" else "false") }

field:
  | ln=longname { mk_static_exp ~loc:(Loc($startpos,$endpos)) (Sconstructor ln)}


const : c=_const { mk_static_exp ~loc:(Loc ($startpos,$endpos)) c }
_const:
  | i=INT { Sint i }
  | f=FLOAT { Sfloat f }
  | c=constructor { Sconstructor c }
  | t=tuple(const) { Stuple t }

exps: LPAREN e=slist(COMMA, exp) RPAREN {e}

field_exp: longname EQUAL exp { ($1, $3) }

simple_exp:
  | e=_simple_exp {mk_exp e (Loc ($startpos,$endpos)) }
_simple_exp:
  | n=NAME                                 { Evar (ident_of_name n) }
  | s=structure(field_exp)                 { Estruct s }
  | t=tuple(exp)                           { Eapp(mk_app Etuple, t, None) }
  | LBRACKET es=slist(COMMA, exp) RBRACKET { Eapp(mk_app Earray, es, None) }
  | LPAREN e=_exp RPAREN                   { e }


exp:
  | e=simple_exp { e }
  | e=_exp { mk_exp e (Loc ($startpos,$endpos)) }
_exp:
  | c=const                                { Econst c }
  | v=const FBY e=exp                      { Efby(Some(v), e) }
  | PRE exp                                { Efby(None,$2) }
  | op=funapp a=exps r=reset               { Eapp(op, a, r) }
  | e1=exp i_op=infix e2=exp
      { Eapp(mk_app (Efun i_op), [e1; e2], None) }
  | p_op=prefix e=exp %prec prefixs
      { Eapp(mk_app (Efun p_op), [e], None) }
  | IF e1=exp THEN e2=exp ELSE e3=exp
      { Eapp( mk_app Eifthenelse, [e1; e2; e3], None) }
  | e=simple_exp DOT f=field
      { Eapp( mk_app ~params:[f] Efield, [e], None) }
  | e=exp WHEN c=constructor LPAREN n=ident RPAREN  { Ewhen(e, c, n) }
  | MERGE n=ident h=handlers  { Emerge(n, h) }
  | LPAREN r=exp WITH DOT f=field EQUAL nv=exp
      { Eapp(mk_app ~params:[f] Efield_update, [r; nv], None) }
  | e=exp POWER p=e_param
      { Eapp(mk_app ~params:[p] Earray_fill, [e], None) }
  | e=simple_exp i=indexes(exp) /* not e_params to solve conflicts */
      { Eapp(mk_app ~params:i Eselect, [e], None) }
  | e=simple_exp i=indexes(exp) DEFAULT d=exp
      { Eapp(mk_app Eselect_dyn, [e; d]@i, None) }
  | LPAREN e=exp WITH i=indexes(e_param) EQUAL nv=exp
      { Eapp(mk_app ~params:i Eupdate, [e; nv], None) }
  | e=simple_exp LBRACKET i1=e_param DOTDOT i2=e_param RBRACKET
      { Eapp(mk_app ~params:[i1; i2] Eselect_slice, [e], None) }
  | e1=exp AROBASE e2=exp  { Eapp(mk_app Econcat, [e1;e2], None) }
  | LPAREN f=iterator LPAREN op=funapp RPAREN
      DOUBLE_LESS p=e_param DOUBLE_GREATER
        RPAREN a=exps r=reset  { Eiterator(f,op,p,a,r) }

/* Static indexes [p1][p2]... */
indexes(param): is=nonempty_list(index(param))      { is }
index(param): LBRACKET p=param RBRACKET             { p }




/* Merge handlers ( B -> e)( C -> ec)... */
handlers: hs=nonempty_list(handler)    { hs }
handler: LPAREN c=constructor ARROW e=exp RPAREN { c,e }


iterator:
  | MAP     { Imap }
  | FOLD    { Ifold }
  | MAPFOLD { Imapfold }

reset: r=option(RESET,ident) { r }

/* TODO : Scoping to deal with node and fun ! */
funapp: ln=longname p=params(e_param) { mk_app p (Enode ln) }

/* inline so that precendance of POWER is respected in exp */
%inline e_param: e=exp { e }
n_param: n=NAME { mk_param n }
params(param):
  | /*empty*/                                               { [] }
  | DOUBLE_LESS p=slist(COMMA, param) DOUBLE_GREATER { p }


/*Inlining is compulsory in order to preserve priorities*/
%inline infix: op=infix_ { Name(op) }
%inline infix_:
  | op=INFIX0 | op=INFIX1 | op=INFIX2 | op=INFIX3 | op=INFIX4  { op }
  | STAR            { "*" }
  | EQUAL           { "=" }
  | EQUALEQUAL      { "==" }
  | AMPERSAND       { "&" }   | AMPERAMPER    { "&&" }
  | OR              { "or" }  | BARBAR        { "||" }

%inline prefix: op=prefix_ { Name(op) }
%inline prefix_:
  | op = PREFIX          { op }
  | NOT                  { "not" }
  | op = SUBTRACTIVE     { "~" ^ op } /*TODO test 3 * -2 and co */





%%
