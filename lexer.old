{
  open Parser
  open Lexing
} 

let space = [' ' '\t']
let digits = ['0'-'9']+
let symbol = 
  ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']
  ['0'-'9' 'a'-'z' 'A'-'Z' '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']*
 (* symbol from smtlib2 syntax, whithout the | | syntax *) 

rule token = parse
  | space+               { token lexbuf }
  | '\n'                 { new_line lexbuf; token lexbuf}
  | '('                  { OPEN }
  | ')'                  { CLOSE }
  | "let"                { LET }
  | "forall"             { FORALL }
  | "exists"             { EXISTS }
  | '!'                  { BANG }

  | "true"               { TRUE }
  | "false"              { FALSE }
  | "not"                { NOT }
  | "=>"                 { IMPLY }
  | "and"                { AND }
  | "or"                 { OR }
  | "xor"                { XOR }
  | "="                  { EQ }
  | "distinct"           { DISTINCT }
  | "ite"                { ITE }

  | "set"                { SET }
  | ".c" (digits as s)   { STEP ("C"^s) }
  | "input"              { INPUT }
  | "eq_reflexive"       { EQ_REFL }
  | "eq_transitive"      { EQ_TRANS }
  | "eq_congruent"       { EQ_CONGR }
  | "resolution"         { RESOLUTION }
  | ":conclusion"        { CONCLUSION }
  | ":clauses"           { CLAUSES }
  | symbol as s          { SYM s }
  | eof                  { EOF }
  | _                    { let (s, l, c) = Error.get_location lexbuf in
			   raise (Error.LexerError (s, l, c) ) }
      
