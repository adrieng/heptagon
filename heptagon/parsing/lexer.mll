(* lexer.mll *)

(* $Id$ *)

{
open Lexing
open Parser

type lexical_error =
    Illegal_character
  | Unterminated_comment
  | Bad_char_constant
  | Unterminated_string;;

exception Lexical_error of lexical_error * int * int;;

let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
 "node", NODE;
 "fun", FUN;
 "safe", SAFE;
 "returns", RETURNS;
 "var", VAR;
 "val", VAL;
 "const", CONST;
 "unsafe", UNSAFE;
 "let", LET;
 "tel", TEL;
 "end", END;
 "fby", FBY;
 "switch", SWITCH;
 "when", WHEN;
 "type", TYPE;
 "every", EVERY;
 "true", BOOL(true);
 "false", BOOL(false);
 "pre", PRE;
 "or", OR;
 "not", NOT;
 "open", OPEN;
 "automaton", AUTOMATON;
 "switch", SWITCH;
 "present", PRESENT;
 "reset", RESET;
 "state", STATE;
 "unless", UNLESS;
 "until", UNTIL;
 "emit", EMIT;
 "last", LAST;
 "if", IF;
 "then", THEN;
 "else", ELSE;
 "default", DEFAULT;
 "continue", CONTINUE;
 "case", CASE;
 "do", DO;
 "contract", CONTRACT;
 "assume", ASSUME;
 "enforce", ENFORCE;
 "with", WITH;
 "inlined", INLINED;
 "with", WITH;
 "map", MAP;
 "fold", FOLD;
 "mapfold", MAPFOLD;
 "quo", INFIX3("quo");
 "mod", INFIX3("mod");
 "land", INFIX3("land");
 "lor", INFIX2("lor");
 "lxor", INFIX2("lxor");
 "lsl", INFIX4("lsl");
 "lsr", INFIX4("lsr");
 "asr", INFIX4("asr")
]


(* To buffer string literals *)

let initial_string_buffer = String.create 256
let string_buff = ref initial_string_buffer
let string_index = ref 0

let reset_string_buffer () =
  string_buff := initial_string_buffer;
  string_index := 0;
  ()

(*
let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
*)

let store_string_char c =
  if !string_index >= String.length (!string_buff) then begin
    let new_buff = String.create (String.length (!string_buff) * 2) in
      String.blit (!string_buff) 0 new_buff 0 (String.length (!string_buff));
      string_buff := new_buff
  end;
  String.set (!string_buff) (!string_index) c;
  incr string_index


let get_stored_string () =
  let s = String.sub (!string_buff) 0 (!string_index) in
    string_buff := initial_string_buffer;
    s

let char_for_backslash = function
    'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c   -> c

let char_for_decimal_code lexbuf i =
  let c =
    100 * (int_of_char(Lexing.lexeme_char lexbuf i) - 48) +
     10 * (int_of_char(Lexing.lexeme_char lexbuf (i+1)) - 48) +
          (int_of_char(Lexing.lexeme_char lexbuf (i+2)) - 48) in
  char_of_int(c land 0xFF)


}

rule token = parse
  | [' ' '\010' '\013' '\009' '\012'] +   { token lexbuf }
  | "."             {DOT}
  | "("             {LPAREN}
  | ")"             {RPAREN}
  | "*"             { STAR }
  | "{"             {LBRACE}
  | "}"             {RBRACE}
  | ":"             {COLON}
  | ";"             {SEMICOL}
  | "="             {EQUAL}
  | "=="            {EQUALEQUAL}
  | "&"             {AMPERSAND}
  | "&&"            {AMPERAMPER}
  | "||"            {BARBAR}
  | ","             {COMMA}
  | "->"            {ARROW}
  | "|"             {BAR}
  | "-"             {SUBTRACTIVE "-"}
  | "-."            {SUBTRACTIVE "-."}
  | "^"             {POWER} 
  | "["             {LBRACKET}
  | "]"             {RBRACKET}
  | "@"             {AROBASE}
  | ".."            {DOUBLE_DOT}
  | "<<"            {DOUBLE_LESS}
  | ">>"            {DOUBLE_GREATER}
  | (['A'-'Z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      {Constructor id}
  | (['A'-'Z' 'a'-'z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      { let s = Lexing.lexeme lexbuf in
          begin try
	    Hashtbl.find keyword_table s
          with 
	      Not_found -> IDENT id
	  end 
      }
  | ['0'-'9']+
  | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
  | '0' ['o' 'O'] ['0'-'7']+
  | '0' ['b' 'B'] ['0'-'1']+
      { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, _, string_end) ->
          raise(Lexical_error(Unterminated_string, string_start, string_end))
        end;
        lexbuf.lex_start_pos <- string_start - lexbuf.lex_abs_pos;
        STRING (get_stored_string()) }
  | "'" [^ '\\' '\''] "'"
      { CHAR(Lexing.lexeme_char lexbuf 1) }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { CHAR(char_for_backslash (Lexing.lexeme_char lexbuf 2)) }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { CHAR(char_for_decimal_code lexbuf 2) }
  | "(*@ " (['A'-'Z' 'a'-'z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      {
	reset_string_buffer();
	let pragma_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
	begin try
	  pragma lexbuf
	with Lexical_error(Unterminated_comment, _, pragma_end) ->
	  raise(Lexical_error(Unterminated_comment, pragma_start, pragma_end))
	end;
	lexbuf.lex_start_pos <- pragma_start - lexbuf.lex_abs_pos;
	PRAGMA(id,get_stored_string())
      }
  | "(*"
      { let comment_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        comment_depth := 1;
        begin try
          comment lexbuf
        with Lexical_error(Unterminated_comment, _, comment_end) ->
          raise(Lexical_error(Unterminated_comment,
                              comment_start, comment_end))
        end;
        token lexbuf }
   | ['!' '?' '~']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':'
	  '<' '=' '>' '?' '@' '^' '|' '~'] *
      { PREFIX(Lexing.lexeme lexbuf) }
  | ['=' '<' '>' '&'  '|' '&' '$']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
	  '?' '@' '^' '|' '~'] *
      { INFIX0(Lexing.lexeme lexbuf) }
  | ['@' '^']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
	  '?' '@' '^' '|' '~'] *
      { INFIX1(Lexing.lexeme lexbuf) }
  | ['+' '-']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
	  '?' '@' '^' '|' '~'] *
      { INFIX2(Lexing.lexeme lexbuf) }
  | "**"
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
	  '?' '@' '^' '|' '~'] *
      { INFIX4(Lexing.lexeme lexbuf) }
  | ['*' '/' '%']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
	  '?' '@' '^' '|' '~'] *
      { INFIX3(Lexing.lexeme lexbuf) }
  | eof            {EOF}
  | _              {raise (Lexical_error (Illegal_character,
					  Lexing.lexeme_start lexbuf,
					  Lexing.lexeme_end lexbuf))}

and pragma = parse
    "(*"
      { let comment_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        comment_depth := 1;
        begin try
          comment lexbuf
        with Lexical_error(Unterminated_comment, _, comment_end) ->
          raise(Lexical_error(Unterminated_comment,
                              comment_start, comment_end))
        end;
        pragma lexbuf }
  | "@*)"
      { }
  | eof
      { raise(Lexical_error(Unterminated_comment,0,
                            Lexing.lexeme_start lexbuf)) }

  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
	pragma lexbuf }

and comment = parse
    "(*"
      { comment_depth := succ !comment_depth; comment lexbuf }
  | "*)"
      { comment_depth := pred !comment_depth;
        if !comment_depth > 0 then comment lexbuf }
  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, _, string_end) ->
          raise(Lexical_error(Unterminated_string, string_start, string_end))
        end;
        comment lexbuf }
  | "''"
      { comment lexbuf }
  | "'" [^ '\\' '\''] "'"
      { comment lexbuf }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { comment lexbuf }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { comment lexbuf }
  | eof
      { raise(Lexical_error(Unterminated_comment,0,
                            Lexing.lexeme_start lexbuf)) }
  | _
      { comment lexbuf }

and string = parse
    '"'
      { () }
  | '\\' ("\010" | "\013" | "\013\010") [' ' '\009'] *
      { string lexbuf }
  | '\\' ['\\' '"'  'n' 't' 'b' 'r']
      { store_string_char(char_for_backslash(Lexing.lexeme_char lexbuf 1));
        string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { store_string_char(char_for_decimal_code lexbuf 1);
         string lexbuf }
  | eof
      { raise (Lexical_error
                (Unterminated_string, 0, Lexing.lexeme_start lexbuf)) }
  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
        string lexbuf }

(* eof *)
