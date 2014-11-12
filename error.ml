open Printf
open Lexing

let get_location lexbuf =
  let start = lexeme_start_p lexbuf in 
  (lexeme lexbuf, start.pos_lnum, 
   (start.pos_cnum - start.pos_bol))

let get_line lexbuf =
  let start = lexeme_start_p lexbuf in 
  start.pos_lnum

let print_location_error l c str = 
  eprintf "Line %d Col %d: %s\n" l c str; exit 1

let print_line_error l str = 
  eprintf "Line %d: %s\n" l str; exit 1

exception LexerError of string * int * int

exception ParserError of string * int * int

exception RuleError of int
exception FoundRuleError

exception EndOfFile
exception Axiom
