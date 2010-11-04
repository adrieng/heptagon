%{

open Signature
open Location
open Names
open Types
open Hept_parsetree


%}

%token DOT LPAREN RPAREN LBRACE RBRACE COLON SEMICOL
%token EQUAL EQUALEQUAL LESS_GREATER BARBAR COMMA BAR ARROW LET TEL
%token <string> Constructor
%token <string> IDENT
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string * string> PRAGMA
%token TYPE FUN NODE RETURNS VAR VAL OPEN END CONST
%token FBY PRE SWITCH EVERY
%token OR STAR NOT
%token AMPERSAND
%token AMPERAMPER
%token AUTOMATON
%token PRESENT
%token RESET
%token STATE
%token UNLESS
%token UNTIL
%token LAST
%token IF
%token THEN
%token ELSE
%token DEFAULT
%token DO
%token CONTINUE
%token CONTRACT
%token ASSUME
%token ENFORCE
%token WITH
%token WHEN MERGE
%token POWER
%token LBRACKET
%token RBRACKET
%token DOUBLE_DOT
%token AROBASE
%token DOUBLE_LESS DOUBLE_GREATER
%token MAP FOLD FOLDI MAPFOLD
%token <string> PREFIX
%token <string> INFIX0
%token <string> INFIX1
%token <string> INFIX2
%token <string> SUBTRACTIVE
%token <string> INFIX3
%token <string> INFIX4
%token EOF


%right AROBASE
%nonassoc prec_ident
%nonassoc DEFAULT
%left ELSE
%right ARROW
%left OR
%left AMPERSAND
%left INFIX0 EQUAL LESS_GREATER
%right INFIX1
%right WHEN
%left INFIX2 SUBTRACTIVE
%left STAR INFIX3
%left INFIX4
%right NOT
%right prec_uminus
%right FBY
%right PRE
%left POWER
%right PREFIX
%left DOT


%start program
%type <Hept_parsetree.program> program

%start interface
%type <Hept_parsetree.interface> interface

%%

/** Tools **/
%inline slist(S, x)        : l=separated_list(S, x)                    {l}
%inline snlist(S, x)       : l=separated_nonempty_list(S, x)           {l}
%inline tuple(x)           : LPAREN h=x COMMA t=snlist(COMMA,x) RPAREN { h::t }
%inline soption(P,x):
  |/* empty */    { None }
  | P v=x         { Some(v) }

program:
  | pragma_headers open_modules const_decs type_decs node_decs EOF
      {{ p_modname = "";
         p_pragmas = $1;
         p_opened = List.rev $2;
         p_types = $4;
         p_nodes = $5;
         p_consts = $3; }}
;

pragma_headers:
  | /* empty */ { [] }
  | PRAGMA pragma_headers { $1 :: $2 }

open_modules:
  | /* empty */ { [] }
  | open_modules OPEN Constructor { $3 :: $1 }
;

const_decs:
  | /* empty */        { [] }
  | const_dec const_decs { $1 :: $2 }
;

const_dec:
  | CONST IDENT COLON ty_ident EQUAL exp
      { mk_const_dec $2 $4 $6 (Loc($startpos,$endpos)) }
;

type_decs:
  | /* empty */        { [] }
  | type_dec type_decs { $1 :: $2 }
;

type_dec:
  | TYPE IDENT
      { mk_type_dec $2 Type_abs (Loc($startpos,$endpos)) }
  | TYPE IDENT EQUAL ty_ident
      { mk_type_dec $2 (Type_alias $4) (Loc($startpos,$endpos)) }
  | TYPE IDENT EQUAL enum_ty_desc
      { mk_type_dec $2 (Type_enum ($4)) (Loc($startpos,$endpos)) }
  | TYPE IDENT EQUAL struct_ty_desc
      { mk_type_dec $2 (Type_struct ($4)) (Loc($startpos,$endpos)) }
;

enum_ty_desc:
  | Constructor                   {[$1]}
  | BOOL BAR BOOL                 {[(if $1 then "true" else "false");
                                    (if $3 then "true" else "false")]}
  | Constructor BAR enum_ty_desc  {$1 :: $3}
;

struct_ty_desc:
  | LBRACE label_ty_list RBRACE { $2 }
;

label_ty_list:
  | label_ty { [$1] }
  | label_ty SEMICOL label_ty_list { $1 :: $3 }
;

label_ty:
  IDENT COLON ty_ident { $1, $3 }
;

node_decs:
  | /* empty */        {[]}
  | node_dec node_decs {$1 :: $2}
;

node_dec:
  | node_or_fun ident node_params LPAREN in_params RPAREN
    RETURNS LPAREN out_params RPAREN
    contract b=block(LET) TEL
      {{ n_name = $2;
         n_statefull = $1;
         n_input  = $5;
         n_output = $9;
         n_contract = $11;
         n_block = b;
         n_params = $3;
         n_loc = (Loc($startpos,$endpos)) }}
;

node_or_fun:
  | NODE { true }
  | FUN { false }
;

in_params:
  | params {$1}
;

params:
  | /* empty */  { [] }
  | nonmt_params { $1 }
;

nonmt_params:
  | param               { $1 }
  | param SEMICOL nonmt_params { $1 @ $3 }
;

param:
  | ident_list COLON ty_ident
      { List.map (fun id -> mk_var_dec id $3 Var (Loc($startpos,$endpos))) $1 }
;

out_params:
  | /* empty */ { [] }
  | nonmt_out_params { $1 }
;

nonmt_out_params:
  | var_last { $1 }
  | var_last SEMICOL nonmt_out_params { $1 @ $3 }
;

node_params:
  | /* empty */ { [] }
  | DOUBLE_LESS nonmt_params DOUBLE_GREATER { $2 }
;

contract:
  | /* empty */ {None}
  | CONTRACT b=block(LET) TEL? opt_assume enforce
      { Some{ c_block = b;
              c_assume = $4;
              c_enforce = $5 } }
;

opt_assume:
  | /* empty */ { mk_constructor_exp ptrue (Loc($startpos,$endpos)) }
  | ASSUME exp { $2 }
;

enforce:
  | ENFORCE exp { $2 }
;

loc_vars:
  | /* empty */    { [] }
  | VAR loc_params { $2 }
;

loc_params:
  | var_last SEMICOL            { $1 }
  | var_last SEMICOL loc_params { $1 @ $3 }
;


var_last:
  | ident_list COLON ty_ident
      { List.map (fun id -> mk_var_dec id $3 Var (Loc($startpos,$endpos))) $1 }
  | LAST IDENT COLON ty_ident EQUAL exp
      { [ mk_var_dec $2 $4 (Last(Some($6))) (Loc($startpos,$endpos)) ] }
  | LAST IDENT COLON ty_ident
      { [ mk_var_dec $2 $4 (Last(None)) (Loc($startpos,$endpos)) ] }
;

ident_list:
  | IDENT  { [$1] }
  | IDENT COMMA ident_list { $1 :: $3 }
;

ty_ident:
  | qualname
      { Tid $1 }
  | ty_ident POWER simple_exp
      { Tarray ($1, $3) }
;

equs:
  | /* empty */             { [] }
  | non_empty_equs opt_semi { List.rev $1 }
;

non_empty_equs:
  | equ                        { [$1] }
  | non_empty_equs SEMICOL equ {$3 :: $1}
;

opt_semi:
  | {}
  | SEMICOL {}
;

opt_bar:
  | {}
  | BAR {}
;

block(S):
  | l=loc_vars S eq=equs { mk_block l eq (Loc($startpos,$endpos)) }
  | l=loc_vars { mk_block l [] (Loc($startpos,$endpos)) }

equ: eq=_equ { mk_equation eq (Loc($startpos,$endpos)) }
_equ:
  | pat EQUAL exp { Eeq($1, $3) }
  | AUTOMATON automaton_handlers END
      { Eautomaton(List.rev $2) }
  | SWITCH exp opt_bar switch_handlers END
      { Eswitch($2, List.rev $4) }
  | PRESENT opt_bar present_handlers END
      { Epresent(List.rev $3, mk_block [] [] (Loc($startpos,$endpos))) }
  | PRESENT opt_bar present_handlers DEFAULT b=block(DO) END
      { Epresent(List.rev $3, b) }
  | IF exp THEN tb=block(DO) ELSE fb=block(DO) END
      { Eswitch($2,
                   [{ w_name = ptrue; w_block = tb };
                    { w_name = pfalse; w_block = fb }]) }
  | RESET equs EVERY exp
      { Ereset(mk_block [] $2 (Loc($startpos,$endpos)), $4) }
;

automaton_handler:
  | STATE Constructor b=block(DO) ut=opt_until_escapes ul=opt_unless_escapes
      { { s_state = $2; s_block = b; s_until = ut; s_unless = ul } }
;

automaton_handlers:
  | automaton_handler
      { [$1] }
  | automaton_handlers automaton_handler
      { $2 :: $1 }
;

opt_until_escapes:
  | { [] }
  | UNTIL escapes
      { List.rev $2 }
;

opt_unless_escapes:
  | { [] }
  | UNLESS escapes
      { List.rev $2 }
;

escape:
  | exp THEN Constructor
      { { e_cond = $1; e_reset = true; e_next_state = $3 } }
  | exp CONTINUE Constructor
      { { e_cond = $1; e_reset = false; e_next_state = $3 } }
;

escapes:
  | escape
      { [$1] }
  | escapes BAR escape
      { $3 :: $1 }
;

switch_handler:
  | constructor_or_bool b=block(DO)
      { { w_name = $1; w_block = b } }
;

constructor_or_bool:
  | BOOL { if $1 then Q Initial.ptrue else Q Initial.pfalse }
  | constructor { $1 }

switch_handlers:
  | switch_handler
      { [$1] }
  | switch_handlers BAR switch_handler
      { $3 :: $1 }
;

present_handler:
  | exp b=block(DO)
      { { p_cond = $1; p_block = b } }
;

present_handlers:
  | present_handler
      { [$1] }
  | present_handlers BAR present_handler
      { $3 :: $1 }
;

pat:
  | IDENT             {Evarpat $1}
  | LPAREN ids RPAREN {Etuplepat $2}
;

ids:
  | pat COMMA pat {[$1; $3]}
  | pat COMMA ids {$1 :: $3}
;

nonmtexps:
  | exp                 {[$1]}
  | exp COMMA nonmtexps {$1 :: $3}
;

exps:
  | /* empty */    {[]}
  | nonmtexps      {$1}
;

simple_exp:
  | e=_simple_exp { mk_exp e (Loc($startpos,$endpos)) }
  | LPAREN exp RPAREN { $2 }
_simple_exp:
  | IDENT                            { Evar $1 }
  | const                            { Econst $1 }
  | LBRACE field_exp_list RBRACE     { Estruct $2 }
  | LBRACKET array_exp_list RBRACKET { mk_call Earray $2 }
  | LPAREN tuple_exp RPAREN          { mk_call Etuple $2 }
  | simple_exp DOT c=qualname
      { mk_call ~params:[mk_field_exp c (Loc($startpos(c),$endpos(c)))]
                Efield [$1] }
;

node_name:
  | qualname call_params { mk_app (Enode $1) $2 }

merge_handlers:
  | hs=nonempty_list(merge_handler) { hs }
merge_handler:
  | LPAREN c=constructor_or_bool ARROW e=exp RPAREN { (c,e) }

exp:
  | e=simple_exp { e }
  | e=_exp { mk_exp e (Loc($startpos,$endpos)) }
_exp:
  | simple_exp FBY exp
      { Efby ($1, $3) }
  | PRE exp
      { Epre (None, $2) }
  | node_name LPAREN exps RPAREN
      { Eapp($1, $3) }
  | NOT exp
      { mk_op_call "not" [$2] }
  | exp INFIX4 exp
      { mk_op_call $2 [$1; $3] }
  | exp INFIX3 exp
      { mk_op_call $2 [$1; $3] }
  | exp INFIX2 exp
      { mk_op_call $2 [$1; $3] }
  | e=exp WHEN c=constructor_or_bool LPAREN n=IDENT RPAREN
      { Ewhen (e, c, n) }
  | MERGE n=IDENT hs=merge_handlers
      { Emerge (n, hs) }
  | exp INFIX1 exp
      { mk_op_call $2 [$1; $3] }
  | exp INFIX0 exp
      { mk_op_call $2 [$1; $3] }
  | exp EQUAL exp
      { mk_call Eequal [$1; $3] }
  | exp LESS_GREATER exp
      { let e = mk_exp (mk_call Eequal [$1; $3]) (Loc($startpos,$endpos)) in
          mk_op_call "not" [e] }
  | exp OR exp
      { mk_op_call "or" [$1; $3] }
  | exp STAR exp
      { mk_op_call "*" [$1; $3] }
  | exp AMPERSAND exp
      { mk_op_call "&" [$1; $3] }
  | exp SUBTRACTIVE exp
      { mk_op_call $2 [$1; $3] }
  | PREFIX exp
      { mk_op_call $1 [$2] }
  | SUBTRACTIVE exp %prec prec_uminus
      { mk_op_call ("~"^$1) [$2] }
  | IF exp THEN exp ELSE exp
      { mk_call Eifthenelse [$2; $4; $6] }
  | simple_exp ARROW exp
      { mk_call Earrow [$1; $3] }
  | LAST IDENT
      { Elast $2 }
/*Array operations*/
  | exp POWER simple_exp
      { mk_call ~params:[$3] Earray_fill [$1] }
  | simple_exp indexes
      { mk_call ~params:$2 Eselect [$1] }
  | simple_exp DOT indexes DEFAULT exp
      { mk_call Eselect_dyn ([$1; $5]@$3) }
  | LBRACKET exp WITH indexes EQUAL exp RBRACKET
      { mk_call Eupdate ($2::$6::$4) }
  | simple_exp LBRACKET exp DOUBLE_DOT exp RBRACKET
      { mk_call ~params:[$3; $5] Eselect_slice [$1] }
  | exp AROBASE exp
      { mk_call Econcat [$1; $3] }
/*Iterators*/
  | iterator qualname DOUBLE_LESS simple_exp DOUBLE_GREATER LPAREN exps RPAREN
      { mk_iterator_call $1 $2 [] $4 $7 }
  | iterator LPAREN qualname DOUBLE_LESS array_exp_list DOUBLE_GREATER
      RPAREN DOUBLE_LESS simple_exp DOUBLE_GREATER LPAREN exps RPAREN
      { mk_iterator_call $1 $3 $5 $9 $12 }
/*Records operators */
  | LBRACE simple_exp WITH DOT c=qualname EQUAL exp RBRACE
      { mk_call ~params:[mk_field_exp c (Loc($startpos(c),$endpos(c)))]
                Efield_update [$2; $7] }
;

call_params:
  | /* empty */ { [] }
  | DOUBLE_LESS array_exp_list DOUBLE_GREATER { $2 }
;

iterator:
  | MAP { Imap }
  | FOLD { Ifold }
  | FOLDI { Ifoldi }
  | MAPFOLD { Imapfold }
;

indexes:
   LBRACKET exp RBRACKET { [$2] }
  | LBRACKET exp RBRACKET indexes { $2::$4 }
;

constructor:
  | Constructor { ToQ $1 } %prec prec_ident
  | Constructor DOT Constructor { Q {qual = $1; name = $3} }
;

qualname:
  | ident { ToQ $1 }
  | Constructor DOT ident { Q {qual = $1; name = $3} }
;


const: c=_const { mk_static_exp c (Loc($startpos,$endpos)) }
_const:
  | INT         { Sint $1 }
  | FLOAT       { Sfloat $1 }
  | BOOL        { Sbool $1 }
  | constructor { Sconstructor $1 }
  | Constructor DOT ident
      { Svar (Q {qual = $1; name = $3}) }
;

tuple_exp:
  | exp COMMA exp       {[$1; $3]}
  | exp COMMA tuple_exp {$1 :: $3}
;

field_exp_list:
  | field_exp { [$1] }
  | field_exp SEMICOL field_exp_list { $1 :: $3 }
;

array_exp_list:
  | exp { [$1] }
  | exp COMMA array_exp_list { $1 :: $3 }
;

field_exp:
  | qualname EQUAL exp { ($1, $3) }
;

/* identifiers */
ident:
  | IDENT
      { $1 }
  | LPAREN infx RPAREN
      { $2 }
;

infx:
  | INFIX0          { $1 }
  | INFIX1          { $1 }    | INFIX2        { $1 }
  | INFIX3          { $1 }    | INFIX4        { $1 }
  | STAR            { "*" }
  | EQUAL           { "=" }
  | EQUALEQUAL      { "==" }
  | SUBTRACTIVE     { $1 }    | PREFIX        { $1 }
  | AMPERSAND       { "&" }   | AMPERAMPER    { "&&" }
  | OR              { "or" }  | BARBAR        { "||" }
  | NOT             { "not" }
;

interface:
  | interface_decls EOF { List.rev $1 }
;

interface_decls:
  | /* empty */ { [] }
  | interface_decls interface_decl { $2 :: $1 }
;

interface_decl:
  | id=_interface_decl { mk_interface_decl id (Loc($startpos,$endpos)) }
_interface_decl:
  | type_dec         { Itypedef $1 }
  | const_dec        { Iconstdef $1 }
  | OPEN Constructor { Iopen $2 }
  | VAL node_or_fun ident node_params LPAREN params_signature RPAREN
    RETURNS LPAREN params_signature RPAREN
    { Isignature({ sig_name = $3;
                   sig_inputs = $6;
                   sig_statefull = $2;
                   sig_outputs = $10;
                   sig_params = $4;
                   sig_loc = (Loc($startpos,$endpos)) }) }
;

params_signature:
  | /* empty */  {[]}
  | nonmt_params_signature {$1}
;

nonmt_params_signature:
  | param_signature            { [$1] }
  | param_signature SEMICOL nonmt_params_signature { $1 :: $3 }
;

param_signature:
  | IDENT COLON ty_ident { mk_arg (Some $1) $3 }
  | ty_ident { mk_arg None $1 }
;

%%
