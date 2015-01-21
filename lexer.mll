{
  open Parser
  open Lexing

  exception Lexer_error
	 
  let iter_new_line s lexbuf =
    String.iter 
      (fun c -> 
       match c with
       | '\n' -> new_line lexbuf
       | _ -> ()) s

  let escape s =
    let rec iter_escape s n =
      let l = String.length s in 
      if n < l-1 then
	match s.[n], s.[n+1] with
	| '\\', '"' ->
	   let s =
	     String.concat
	       "\"" [String.sub s 0 n; String.sub s (n+2) (l-(n+2))] in
	   iter_escape s n
	| '\\', '\\' ->
	   let s =
	     String.concat
	       "\\" [String.sub s 0 n; String.sub s (n+2) (l-(n+2))] in
	   iter_escape s n
	| _, _ -> iter_escape s (n+1)
      else s in
    iter_escape s 0
}

rule token = parse
  | eof                 { EOF }
  | [' ' '\t' '\r']+    { token lexbuf }
  | '\n'                { new_line lexbuf; token lexbuf }
  | ';' (_ # '\n')*     { token lexbuf }
  | '_'                 { UNDERSCORE }
  | "as"                { AS }
  | "let"               { LET }
  | "forall"            { FORALL }
  | "exists"            { EXISTS }
  | '!'                 { ATTRIBUTE }
  | '('                 { OPEN }
  | ')'                 { CLOSE }
  | ('0' | ['1'-'9'] ['0'-'9']*) as s
        { NUMERAL s }
  | ('0' | ['1'-'9'] ['0'-'9']*) '.' ['0'-'9']+ as s
        { DECIMAL s }
  | '#' 'x' ['0'-'9' 'A'-'F' 'a'-'f']+ as s 
        { HEXADECIMAL s }
  | '#' 'b' ['0' '1']+ as s
        { BINARY s }
  | '"' ((([' '-'~' '\t' '\r' '\n'] # ['\\' '"']) | ('\\' [' '-'~' '\t' '\r' '\n']))* as s) '"' 
        { iter_new_line s lexbuf; STRING (escape s) }
  | ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@'] ['0'-'9' 'a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']* as s
        { SYMBOL s }
  | '|' (([' '-'~' '\t' '\r' '\n'] # ['\\' '|'])* as s) '|'
        { iter_new_line s lexbuf; SYMBOL s }
  | ":clauses"          { CLAUSES }
  | ":conclusion"       { CONCLUSION }
  | ':' ['0'-'9' 'a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']+ as s
        { OTHER_KEYWORD s }
  | _
        { raise Lexer_error }
