%{

open Signature
open Location
open Names
open Types
open Hept_parsetree

let mk_static_exp = mk_static_exp ~loc:(current_loc())

%}

%token DOT LPAREN RPAREN LBRACE RBRACE COLON SEMICOL
%token EQUAL EQUALEQUAL BARBAR COMMA BAR ARROW LET TEL
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
%token POWER
%token LBRACKET
%token RBRACKET
%token DOUBLE_DOT
%token AROBASE
%token DOUBLE_LESS DOUBLE_GREATER
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
%nonassoc prec_ident
%nonassoc DEFAULT
%left ELSE
%right ARROW
%left OR
%left AMPERSAND
%left INFIX0 EQUAL
%right INFIX1
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

program:
  | pragma_headers open_modules const_decs type_decs node_decs EOF
      {{ p_pragmas = $1;
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
      { mk_const_dec $2 $4 $6 }
;

type_decs:
  | /* empty */        { [] }
  | type_dec type_decs { $1 :: $2 }
;

type_dec:
  | TYPE IDENT                      { mk_type_dec $2 Type_abs }
  | TYPE IDENT EQUAL enum_ty_desc   { mk_type_dec $2 (Type_enum ($4)) }
  | TYPE IDENT EQUAL struct_ty_desc { mk_type_dec $2 (Type_struct ($4)) }
;

enum_ty_desc:
  | Constructor BAR Constructor   {[$1;$3]}
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
  IDENT COLON ty_ident { ($1, $3) }
;

node_decs:
  | /* empty */        {[]}
  | node_dec node_decs {$1 :: $2}
;

node_dec:
  | node_or_fun ident node_params LPAREN in_params RPAREN
    RETURNS LPAREN out_params RPAREN
    contract loc_vars LET equs TEL
      {{ n_name   = $2;
   n_statefull = $1;
   n_input  = $5;
   n_output = $9;
   n_contract = $11;
   n_local  = $12;
   n_equs   = $14;
   n_params = $3;
   n_loc = Location.current_loc () }}
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
      { List.map (fun id -> mk_var_dec id $3 Var) $1 }
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
  | CONTRACT loc_vars opt_equs opt_assume enforce opt_with
      {Some{c_local = $2;
	    c_eq = $3;
	    c_assume = $4;
	    c_enforce = $5;
	    c_controllables = $6 }}
;

opt_equs:
  | /* empty */ { [] }
  | LET equs TEL { $2 }
;

opt_assume:
  | /* empty */ {  mk_exp (Econst (mk_static_exp (Sconstructor Initial.ptrue))) }
  | ASSUME exp { $2 }
;

enforce:
  | ENFORCE exp { $2 }
;

opt_with:
  | /* empty */ { [] }
  | WITH LPAREN params RPAREN { $3 }
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
      { List.map (fun id -> mk_var_dec id $3 Var) $1 }
  | LAST IDENT COLON ty_ident EQUAL exp
      { [ mk_var_dec $2 $4 (Last(Some($6))) ] }
  | LAST IDENT COLON ty_ident
      { [ mk_var_dec $2 $4 (Last(None)) ] }
;

ident_list:
  | IDENT  { [$1] }
  | IDENT COMMA ident_list { $1 :: $3 }
;

ty_ident:
  | IDENT
      { Tid(Name($1)) }
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

equ:
  | pat EQUAL exp { mk_equation (Eeq($1, $3)) }
  | AUTOMATON automaton_handlers END
      { mk_equation (Eautomaton(List.rev $2)) }
  | SWITCH exp opt_bar switch_handlers END
      { mk_equation (Eswitch($2, List.rev $4)) }
  | PRESENT opt_bar present_handlers END
      { mk_equation (Epresent(List.rev $3, mk_block [] [])) }
  | PRESENT opt_bar present_handlers DEFAULT loc_vars DO equs END
      { mk_equation (Epresent(List.rev $3, mk_block $5 $7)) }
  | IF exp THEN loc_vars DO equs ELSE loc_vars DO equs END
      { mk_equation (Eswitch($2,
           [{ w_name = Name("true"); w_block = mk_block $4 $6};
      { w_name = Name("false"); w_block = mk_block $8 $10 }])) }
  | RESET equs EVERY exp
      { mk_equation (Ereset($2, $4)) }
;

automaton_handler:
  | STATE Constructor loc_vars DO equs opt_until_escapes opt_unless_escapes
      { { s_state = $2; s_block = mk_block $3 $5;
    s_until = $6; s_unless = $7 } }
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
  | constructor loc_vars DO equs
      { { w_name = $1; w_block = mk_block $2 $4 } }
;

switch_handlers:
  | switch_handler
      { [$1] }
  | switch_handlers BAR switch_handler
      { $3 :: $1 }
;

present_handler:
  | exp loc_vars DO equs
      { { p_cond = $1; p_block = mk_block $2 $4 } }
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
  | IDENT                   { mk_exp (Evar $1) }
  | const                   { mk_exp (Econst $1) }
  | LBRACE field_exp_list RBRACE
      { mk_exp (Estruct $2) }
  | LBRACKET array_exp_list RBRACKET
      { mk_exp (mk_call Earray $2) }
  | LPAREN tuple_exp RPAREN
      { mk_exp (mk_call Etuple $2) }
  | LPAREN exp RPAREN
      { $2 }
;

node_name:
  | longname call_params
      { mk_app (Enode $1) $2 }

exp:
  | simple_exp { $1 }
  | simple_exp FBY exp
      { mk_exp (Efby ($1, $3)) }
  | PRE exp
      { mk_exp (Epre (None, $2)) }
  | node_name LPAREN exps RPAREN
      { mk_exp (Eapp($1, $3)) }
  | NOT exp
      { mk_exp (mk_op_call "not" [$2]) }
  | exp INFIX4 exp
      { mk_exp (mk_op_call $2 [$1; $3]) }
  | exp INFIX3 exp
      { mk_exp (mk_op_call $2 [$1; $3]) }
  | exp INFIX2 exp
      { mk_exp (mk_op_call $2 [$1; $3]) }
  | exp INFIX1 exp
      { mk_exp (mk_op_call $2 [$1; $3]) }
  | exp INFIX0 exp
      { mk_exp (mk_op_call $2 [$1; $3]) }
  | exp EQUAL exp
      { mk_exp (mk_op_call "=" [$1; $3]) }
  | exp OR exp
      { mk_exp (mk_op_call "or" [$1; $3]) }
  | exp STAR exp
      { mk_exp (mk_op_call "*" [$1; $3]) }
  | exp AMPERSAND exp
      { mk_exp (mk_op_call "&" [$1; $3]) }
  | exp SUBTRACTIVE exp
      { mk_exp (mk_op_call $2 [$1; $3]) }
  | PREFIX exp
      { mk_exp (mk_op_call $1 [$2]) }
  | SUBTRACTIVE exp %prec prec_uminus
      { mk_exp (mk_op_call ("~"^$1) [$2]) }
  | IF exp THEN exp ELSE exp
      { mk_exp (mk_call Eifthenelse [$2; $4; $6]) }
  | simple_exp ARROW exp
      { mk_exp (mk_call Earrow [$1; $3]) }
  | LAST IDENT
      { mk_exp (Elast $2) }
  | simple_exp DOT longname
      { mk_exp (Efield ($1, $3)) }
/*Array operations*/
  | exp POWER simple_exp
      { mk_exp (mk_call ~params:[$3] Earray_fill [$1]) }
  | simple_exp indexes
      { mk_exp (mk_call ~params:$2 Eselect [$1]) }
  | simple_exp DOT indexes DEFAULT exp
      { mk_exp (mk_call Eselect_dyn ([$1; $5]@$3)) }
  | LBRACKET exp WITH indexes EQUAL exp RBRACKET
      { mk_exp (mk_call ~params:$4 Eupdate [$2; $6]) }
  | simple_exp LBRACKET exp DOUBLE_DOT exp RBRACKET
      { mk_exp (mk_call ~params:[$3; $5] Eselect_slice [$1]) }
  | exp AROBASE exp
      { mk_exp (mk_call Econcat [$1; $3]) }
/*Iterators*/
  | iterator longname DOUBLE_LESS simple_exp DOUBLE_GREATER LPAREN exps RPAREN
      { mk_exp (mk_iterator_call $1 $2 [] $4 $7) }
  | iterator LPAREN longname DOUBLE_LESS array_exp_list DOUBLE_GREATER
      RPAREN DOUBLE_LESS simple_exp DOUBLE_GREATER LPAREN exps RPAREN
      { mk_exp (mk_iterator_call $1 $3 $5 $9 $12) }
/*Records operators */
  | LBRACE e=simple_exp WITH DOT ln=longname EQUAL nv=exp RBRACE
    { let fn = mk_exp (Econst (mk_static_exp (Sconstructor ln))) in
        mk_exp (mk_call ~params:[fn] Efield_update [e; nv]) }
;

call_params:
  | /* empty */ { [] }
  | DOUBLE_LESS array_exp_list DOUBLE_GREATER { $2 }
;

iterator:
  | MAP { Imap }
  | FOLD { Ifold }
  | MAPFOLD { Imapfold }
;

indexes:
   LBRACKET exp RBRACKET { [$2] }
  | LBRACKET exp RBRACKET indexes { $2::$4 }
;

constructor:
  | Constructor { Name($1) } %prec prec_ident
  | Constructor DOT Constructor { Modname({qual = $1; id = $3}) }
;

longname:
  | ident { Name($1) }
  | Constructor DOT ident { Modname({qual = $1; id = $3}) }
;

const:
  | INT { mk_static_exp (Sint $1) }
  | FLOAT {  mk_static_exp (Sfloat $1) }
  | BOOL {  mk_static_exp (Sbool $1) }
  | constructor {  mk_static_exp (Sconstructor $1) }
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
  | longname EQUAL exp { ($1, $3) }
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
  | type_dec         { mk_interface_decl (Itypedef $1) }
  | const_dec        { mk_interface_decl (Iconstdef $1) }
  | OPEN Constructor { mk_interface_decl (Iopen $2) }
  | VAL node_or_fun ident node_params LPAREN params_signature RPAREN
    RETURNS LPAREN params_signature RPAREN
    { mk_interface_decl (Isignature({ sig_name = $3;
                                      sig_inputs = $6;
                                      sig_statefull = $2;
                                      sig_outputs = $10;
                                      sig_params = $4; })) }
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
