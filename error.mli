(* get token, line and column of a lexing buffer *)
val get_location : Lexing.lexbuf -> string * int * int

(* line of a lexing buffer *)
val get_line : Lexing.lexbuf -> int

(* print error from line, column and string message *)
val print_location_error : int -> int -> string -> unit

(* print error from line and string message *)
val print_line_error : int -> string -> unit
