open Printf
open Lexing

let loc_err lexbuf =
  let start = lexeme_start_p lexbuf in 
  (lexeme lexbuf, start.pos_lnum, 
   (start.pos_cnum - start.pos_bol))

let loc_err_line lexbuf =
  let start = lexeme_start_p lexbuf in 
  start.pos_lnum

let error l c str = 
  eprintf "Line %d Col %d: %s\n" l c str; exit 1

exception LexerError of string * int * int
exception ParserError of string * int * int
exception RuleError of int
exception EndOfFile
exception FoundRuleError
exception FoundAxiom
