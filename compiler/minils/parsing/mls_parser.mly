%{

open Misc
open Signature
open Names
open Ident
open Types
open Location
open Minils
open Mls_utils

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
%token DOUBLE_LESS DOUBLE_GREATER
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
%right INFIX1 EQUALEQUAL BARBAR AMPERAMPER
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

/*TODO deal with when merge and co*/
/*TODO add arrow ?*/
/*TODO be happy with the tools*/

/** Tools **/

/* Redefinitions */
%inline slist(S, x)        : l=separated_list(S, x)                    {l} 
%inline snlist(S, x)       : l=separated_nonempty_list(S, x)           {l}
%inline tuple(x)           : LPAREN h=x COMMA t=snlist(COMMA,x) RPAREN { h::t }
%inline option(P,x):
  |/* empty */    { None }    
  | P v=x         { Some(v) }
%inline option2(L,x,R):
  |/* empty */    { None }
  | L v=x R       { Some(v) }

qualified(x) :
  | n=x { Name(n) }
  | m=CONSTRUCTOR DOT n=x { Modname({ qual = m; id = n }) }
 
structure(field): LBRACE s=snlist(SEMICOL,field) RBRACE {s}
 

program:
  | pragma_headers open_modules type_decs node_decs EOF 
    {{ p_pragmas = List.rev $1;
      p_opened = List.rev $2;
      p_types = $3;
      p_nodes = $4;
      p_consts = []}} /*TODO consts dans program*/

pragma_headers: l=list(PRAGMA) {l}

open_modules: l=list(opens) {l}
opens: OPEN c=CONSTRUCTOR {c}

name: n=NAME | LPAREN n=infix_ RPAREN | LPAREN n=prefix_ RPAREN { n }
ident: n=name { ident_of_name n }

field_type : n=NAME COLON t=type_ident { mk_field n t }

type_ident: NAME { Tid(Name($1)) }

type_decs: t=list(type_dec) {t}
type_dec:
  | TYPE n=NAME                               { mk_type n Type_abs }
  | TYPE n=NAME EQUAL e=snlist(BAR,NAME)       { mk_type n (Type_enum e) }
  | TYPE n=NAME EQUAL s=structure(field_type) { mk_type n (Type_struct s) }

node_decs: ns=list(node_dec) {ns}
node_dec:
  NODE n=name p=params(n_param) LPAREN args=args RPAREN
  RETURNS LPAREN out=args RPAREN vars=loc_vars eqs=equs
      { mk_node ~input:args ~output:out ~local:vars ~eq:eqs n }
        

args_t: SEMICOL p=args {p}
args: 
  | /* empty */ {[]}
  | h=var t=loption(args_t) {h@t}

loc_vars_t: SEMICOL h=var t=loc_vars_t {h@t}
loc_vars_h: VAR h=var t=loc_vars_t  {h@t}
loc_vars: l=loption(loc_vars_h) {l}

var:
  | ns=snlist(COMMA, NAME) COLON t=type_ident
      { List.map (fun id -> mk_var (ident_of_name id) t) ns }

equs: LET e=slist(SEMICOL, equ) TEL { e }
equ: p=pat EQUAL e=exp { mk_equation p e }

pat:
  | n=NAME                            {Evarpat (ident_of_name n)}
  | LPAREN p=snlist(COMMA, pat) RPAREN {Etuplepat p}

longname: l=qualified(name) {l}
  
constructor:
  | ln=qualified(CONSTRUCTOR)       {ln}
  | b=BOOL                          { Name(if b then "true" else "false") }

const:
  | INT { Cint($1) }
  | FLOAT { Cfloat($1) }
  | constructor { Cconstr($1) }

exps: LPAREN e=slist(COMMA, exp) RPAREN {e}

field_exp: longname EQUAL exp { ($1, $3) }

simple_exp:
  | NAME                               { mk_exp (Evar (ident_of_name $1)) }
  | s=structure(field_exp)             { mk_exp (Estruct s) }
  | t=tuple(exp)                       { mk_exp (Etuple t) }
  | LPAREN e=exp RPAREN                { e }

exp:
  | e=simple_exp                       { e }
  | c=const                            { mk_exp (Econst c) }
  | const FBY exp                      { mk_exp (Efby(Some($1),$3)) }
  | PRE exp                            { mk_exp (Efby(None,$2)) }
  | op=node_app a=exps r=reset         { mk_exp (Ecall(op, a, r)) }
  | e1=exp i_op=infix e2=exp
        { mk_exp (Ecall(mk_op ~op_kind:Eop i_op, [e1; e2], None)) }
  | p_op=prefix e=exp %prec prefixs
        { mk_exp (Ecall(mk_op ~op_kind:Eop p_op, [e], None)) }
  | IF e1=exp THEN e2=exp ELSE e3=exp  { mk_exp (Eifthenelse(e1, e2, e3)) }
  | e=simple_exp DOT m=longname               { mk_exp (Efield(e, m)) }



reset: r=option(RESET,ident) { r }

node_app: ln=longname p=params(e_param) { mk_op ~op_kind:Enode ~op_params:p ln }


e_param: e=exp { size_exp_of_exp e }
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

prefix: op=prefix_ { Name(op) }
prefix_: 
  | op = PREFIX          { op }
  | NOT                  { "not" }
  | op = SUBTRACTIVE     { "~" ^ op } /*TODO test 3 * -2 and co */





%%