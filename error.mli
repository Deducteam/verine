(* get token, line and column of a lexing buffer *)
val get_location : Lexing.lexbuf -> string * int * int

(* line of a lexing buffer *)
val get_line : Lexing.lexbuf -> int

(* print error from line, column and string message *)
val print_location_error : int -> int -> string -> unit

(* print error from line and string message *)
val print_line_error : int -> string -> unit

(* lexing error with indications of character/token, line and column *)
exception LexerError of string * int * int

(* parsing error with indications of character/token, line and column *)
exception ParserError of string * int * int

(* rule structure error with indication of line, raised catching FoundRuleError *)
exception RuleError of int
exception FoundRuleError

(* unknown rule needing an axiom declarationr *)
exception Axiom
(* exception raised at the end of the veriT proof file *)
exception EndOfFile
