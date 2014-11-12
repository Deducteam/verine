(* get token, line and column of a lexing buffer *)
val loc_err : Lexing.lexbuf -> string * int * int

(* print error from line, column and string message *)
val error : int -> int -> string -> unit

(* lexing/parsing errors with indications of character/token, line and column *)
exception LexerError of string * int * int
exception ParserError of string * int * int
(* rule structure error *)
exception FoundRuleError
(* unknown rule needing an axiom declarationr *)
exception FoundAxiom
(* rule structure error with indication of line, raised catching FoundRuleError *)
exception RuleError of int
(* exception raised at the end of the veriT proof file *)
exception EndOfFile
