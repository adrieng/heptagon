%{

open Misc
open Signature
open Names
open Ident
open Types
open Location
open Minils

let mk_exp = mk_exp ~loc:(current_loc())
let mk_node = mk_node ~loc:(current_loc()) 
let mk_equation p e = mk_equation ~loc:(current_loc()) p e  
let mk_type name desc = mk_type_dec ~loc:(current_loc()) ~type_desc: desc name
  

    
let mk_var name ty = mk_var_dec name ty

%}

%token DOT LPAREN RPAREN LBRACE RBRACE COLON SEMICOL
%token EQUAL EQUALEQUAL BARBAR COMMA BAR LET TEL
%token <string> CONSTRUCTOR
%token <string> NAME
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <char> CHAR
%token <string> STRING
%token <string * string> PRAGMA
%token TYPE FUN NODE RETURNS VAR OPEN
%token FBY PRE SWITCH WHEN EVERY
%token OR STAR NOT
%token AMPERSAND
%token AMPERAMPER
%token AUTOMATON
%token PRESENT
%token RESET
%token STATE
%token UNLESS
%token UNTIL
%token EMIT
%token LAST
%token IF
%token THEN
%token ELSE
%token DEFAULT
%token DO
%token CONTINUE
%token CASE
%token CONTRACT
%token ASSUME
%token ENFORCE
%token WITH
%token INLINED
%token AT
%token <string> PREFIX
%token <string> INFIX0
%token <string> INFIX1
%token <string> INFIX2
%token <string> SUBTRACTIVE
%token <string> INFIX3
%token <string> INFIX4
%token EOF


%nonassoc prec_ident
%left IF ELSE
%right ARROW
%nonassoc EVERY
%left OR
%left AMPERSAND
%left INFIX0 EQUAL
%right INFIX1
%left INFIX2 SUBTRACTIVE
%left STAR INFIX3
%left INFIX4
%right prefixs
%right FBY
%right PRE
%right LAST
%right prec_apply
%left DOT



%start program
%type <Minils.program> program

%%


/** Tools **/

/* Redefinitions */
%inline option_list(x)      : l=list(x) {l}
%inline list(x)             : l=nonempty_list(x) {l} 
%inline option_slist(S, x)  : l=separated_list(S, x) {l} 
%inline slist(S, x)         : l=separated_nonempty_list(S, x) {l}

%inline nuple(L, R, S, x)   : L      h=x S t=slist(S,x)     R         { h::t }
%inline stuple(S, x)        : LPAREN h=x S t=slist(S,x) RPAREN        { h::t }
%inline tuple(x)            : t=stuple(COMMA,x)                       { t }
%inline option2(P,x)        : /* empty */    { None }     | P v=x     { Some(v)}

qualified(x) :
  | n=x { Name(n) } %prec prec_ident
  | m=CONSTRUCTOR DOT n=x { Modname({ qual = m; id = n }) }

structure(field): s=nuple(LBRACE, RBRACE, SEMICOL, field) {s}



program:
  | pragma_headers open_modules type_decs node_decs EOF 
    {{ p_pragmas = List.rev $1;
      p_opened = List.rev $2;
      p_types = $3;
      p_nodes = $4;
      p_consts = []}} /*TODO consts dans program*/

pragma: p=PRAGMA {p}

pragma_headers: l=option_list(pragma) {l}


opens: OPEN c=CONSTRUCTOR {c}

open_modules: l=option_list(opens) {l}


field_type : n=NAME COLON t=type_ident { (n, t) }

type_ident: NAME { Tid(Name($1)) }

type_dec:
  | TYPE n=NAME                               { mk_type n Type_abs }
  | TYPE n=NAME EQUAL e=slist(BAR,NAME)       { mk_type n (Type_enum e) }
  | TYPE n=NAME EQUAL s=structure(field_type) { mk_type n (Type_struct s) }

type_decs: t=option_list(type_dec) {t}


node_dec:
  NODE id=ident LPAREN args=params RPAREN RETURNS LPAREN out=params RPAREN
    vars=loc_vars LET eqs=equs TEL
      { mk_node
         ~input: args
         ~output: out
         ~local: vars
         ~eq: eqs
         id }

node_decs: ns=option_list(node_dec) {ns}

params: p=option_slist(SEMICOL, var) {p}

loc_vars: 
  | /* empty */    { [] }
  | VAR vs=slist(SEMICOL, var) { vs }

var:
  | ns=slist(COMMA, NAME) COLON t=type_ident
      { List.map (fun id -> mk_var id t) ns }

equ: p=pat EQUAL e=exp { mk_eq p e }


equs: e=option_slist(SEMICOL, equ) ?SEMICOL {e}


pat:
  | n=NAME                            {Evarpat (ident_of_name n)}
  | LPAREN p=slist(COMMA, pat) RPAREN {Etuplepat p}


longname: l=qualified(ident) {l}
  
constructor:
  | ln=qualified(CONSTRUCTOR)       {ln}
  | b=BOOL                          { Name(if b then "true" else "false") }

const:
  | INT { Cint($1) }
  | FLOAT { Cfloat($1) }
  | constructor { Cconstr($1) }

exps: LPAREN e=option_slist(COMMA, exp) RPAREN {e}

tuple_exp: LPAREN e=option_slist(COMMA, exp) RPAREN {e}

field_exp: longname EQUAL exp { ($1, $3) }

simple_exp:
  | NAME                               { mk_exp (Evar (ident_of_name $1)) }
  | c=const                            { mk_exp (Econst c) }
  | s=structure(field_exp)             { mk_exp (Estruct s) }
  | t=tuple_exp                        { mk_exp (Etuple t) }
  | LPAREN e=exp RPAREN                { e }

exp:
  | e=simple_exp { e }
  | const FBY exp
      { make_exp (Efby(Some($1),$3)) }
  | PRE exp
      { make_exp (Efby(None,$2)) }
  | longname LPAREN exps RPAREN %prec prec_apply
      { make_exp (Eapp(make_app $1 Ino, $3)) }
  | INLINED longname LPAREN exps RPAREN %prec prec_apply
      { make_exp (Eapp(make_app $2 Irec, $4)) }
  | e1=exp op=infix e2=exp
      { make_exp (Eop(Name(op), [e1; e2])) }
  | op=prefix e=exp %prec prefixs
      { make_exp (Eop(Name(op), [e])) }
  | IF exp THEN exp ELSE exp
      { make_exp (Eifthenelse($2, $4, $6)) }
  | exp DOT longname
      { make_exp (Efield($1, $3)) }


ident: n=NAME | LPAREN n=infix RPAREN | LPAREN n=prefix RPAREN { n }

%inline infix:
  | op=INFIX0 | op=INFIX1 | op=INFIX2 | op=INFIX3 | op=INFIX4  { op }
  | STAR            { "*" }
  | EQUAL           { "=" }
  | EQUALEQUAL      { "==" }
  | AMPERSAND       { "&" }   | AMPERAMPER    { "&&" }
  | OR              { "or" }  | BARBAR        { "||" }

prefix:
  | op = PREFIX          { op }
  | NOT                  { "not" }
  | op = SUBTRACTIVE     { "~" ^ op } /*TODO test 3 * -2 and co */





%%
