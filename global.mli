(* AST corresponding to one step of a veriT proof *)
type term = 
  | Var of string
  | Fun of string * term list

type prop =
  | Eq of term * term
  | Not of prop
  | And of prop * prop
  | Imply of prop * prop
  | False

type rulename = string

type rule = 
  | Input
  | Eq_reflexive
  | Eq_transitive
  | Resolution
  | Rand
  | Anonrule of string

type step =
  | Step of rulename * rule * rulename list * prop list

(* get token, line and column of a lexing buffer *)
val loc_err : Lexing.lexbuf -> string * int * int

(* print error from line, column and string message *)
val error : int -> int -> string -> unit

(* lexing/parsing errors with indications of character/token, line and column *)
exception LexerError of string * int * int
exception ParserError of string * int * int
(* rule structure error *)
exception FoundRuleError
(* rule structure error with indication of line, raised catching FoundRuleError *)
exception RuleError of int
(* exception raised at the end of the veriT proof file *)
exception EndOfFile
