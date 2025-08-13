{
open Parser  (* Import token types from parser *)
open Lexing  (* For position handling *)

(* Reserved keywords mapping *)
let reserved = [
  ("int", INT);
  ("void", VOID);
  ("if", IF);
  ("else", ELSE);
  ("while", WHILE);
  ("break", BREAK);
  ("continue", CONTINUE);
  ("return", RETURN);
]


}

(* Regular expression definitions *)
let dig = ('0' | ['1'-'9'] ['0'-'9']*)
let nondig = ['a'-'z' 'A'-'Z' '_']
let ident = nondig (nondig | dig)*

let space = [' ' '\t' '\r']

rule token = parse
  | space+    { token lexbuf }  
  | '\n'           { new_line lexbuf; token lexbuf } 
  
  (* Comments *)
  | "//" [^ '\n']* { token lexbuf }  (* 单行 *)
  | "/*"           { comment lexbuf } (* 多行 *)
  
  (* Identifiers and keywords *)
  | ident as id    { 
      try List.assoc id reserved 
      with Not_found -> ID id 
    }
  
  (* Integer literals *)
  | dig as n   { NUMBER (int_of_string n) }
  
  (* Operators *)
  | "=="   { EQ }
  | "!="   { NEQ }
  | "<="   { LE }
  | ">="   { GE }
  | '<'    { LT }
  | '>'    { GT }
  | "&&"   { LAND }
  | "||"   { LOR }
  | '='    { ASSIGN }
  | '+'    { PLUS }
  | '-'    { MINUS }
  | '*'    { TIMES }
  | '/'    { DIV }
  | '%'    { MOD }
  | '!'    { NOT }
  
  (* Punctuation *)
  | ';'    { SEMI }
  | ','    { COMMA }
  | '('    { LPAREN }
  | ')'    { RPAREN }
  | '{'    { LBRACE }
  | '}'    { RBRACE }
  
  (* End of file *)
  | eof    { EOF }
  
  (* Invalid character *)
  | _ as c  {
      let pos = lexbuf.lex_curr_p in
      failwith (Printf.sprintf "Illegal character '%c' at line %d, column %d"
        c pos.pos_lnum (pos.pos_cnum - pos.pos_bol)) }

(* Comment handling rule *)
and comment = parse
  | "*/"   { token lexbuf }        (* End of comment *)
  | '\n'   { new_line lexbuf; comment lexbuf }  (* Count lines in comments *)
  | _      { comment lexbuf }      (* Any other char in comment *)
  | eof    { failwith "Unterminated comment" }