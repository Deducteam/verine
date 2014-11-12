open Printf

let filename : string option ref = ref None

let umsg = "Usage: verine <file>"

let argspec = ["-debug", Arg.Set Debug.debugmode, "debug mode"]

let parse_and_run out lexbuf = 
  try 
    let inputstep step = 
      match step with 
      | Proof.Step (_, Proof.Input, _, _) -> true
      | _ -> false in
    let rec parse_and_run_step dkinputvars dkinputconcvars env =
      let step = Scope.scope (Parser.step Lexer.token lexbuf) in
      run_step step dkinputvars dkinputconcvars env
    and run_step step dkinputvars dkinputconcvars env =
      let line, newenv =
	Translate.translate_step 
	  dkinputvars dkinputconcvars step env in
      Translate.print_step out line;
      parse_and_run_step dkinputvars dkinputconcvars newenv    
    in
    let rec parse_and_run_input dkinputvars dkinputconcvars inputs env =
      let step = Scope.scope (Parser.step Lexer.token lexbuf) in
      if inputstep step
      then
 	let newvar, newconcvar, newenv = 
	  Translate.translate_input step env in
	parse_and_run_input 
	  (newvar :: dkinputvars)
	  (newconcvar :: dkinputconcvars) 
	  (step :: inputs) newenv
      else begin
      	  Translate.print_prelude out env inputs dkinputconcvars;
	  run_step step dkinputvars dkinputconcvars env end in
    parse_and_run_input [] [] [] Translate.PrfEnvMap.empty      
  with 
  | Error.EndOfFile -> ()
  | Parsing.Parse_error -> 
    let (s, l, c) = Error.loc_err lexbuf in
    raise (Error.ParserError (s, l, c))
  | Error.FoundRuleError ->
    let (_, l, _) = Error.loc_err lexbuf in
    raise (Error.RuleError l)

let translate_file file = 
  match !filename with
  | Some f -> Arg.usage [] umsg; exit 2
  | None ->
    let name = 
      Scope.convert 
	(Filename.chop_extension (Filename.basename file)) in
    filename := Some name;
    let chan = open_in file in
    let lexbuf = Lexing.from_channel chan in
    let out = stdout in
    Dedukti.p_line out (Dedukti.mk_prelude name);
    parse_and_run out lexbuf
     
let () =
  try
    Arg.parse argspec translate_file umsg;
  with
  | Error.LexerError (s, l, c ) -> Error.error l c (sprintf "Unexpected character '%s'"s)
  | Error.ParserError (s, l, c ) -> Error.error l c (sprintf "Unexpected token '%s'"s)
  | Error.RuleError l -> Error.error l 1 ("Unexpected rule structure")
