{
  open Parseprf
  open Lexing
} 

let space = [' ' '\t']
let num = ['0'-'9']+
let ident = ['a'-'z']+

rule token = parse
  | space+               { token lexbuf }
  | '\n'                 { new_line lexbuf; token lexbuf}
  | '('                  { OPEN }
  | ')'                  { CLOSE }
  | "set"                { SET }
  | ".c" (num as s)      { STEP ("C"^s) }
  | "input"              { INPUT }
  | "eq_reflexive"       { EQ_REFL }
  | "eq_transitive"      { EQ_TRANS }
  | "resolution"         { RESOLUTION }
  | ":conclusion"        { CONCLUSION }
  | ":clauses"           { CLAUSES }
  | "not"                { NOT }
  | "and"                { AND }
  | "false"              { FALSE }
  | "="                  { EQ }
  | ident as s           { ID (s) }
  | _                    { let (s, l, c) = Global.loc_err lexbuf in
raise ( Global.LexerError (s, l, c) ) }
  | eof             { EOF }
      
