open Printf

let filename : string option ref = ref None

let umsg = "Usage: verine <file>"

let argspec = ["-debug", Arg.Set Debug.debugmode, "debug mode"]

let parse_and_run out lexbuf = 
  try 
    let inputstep step = 
      match step with 
      | Global.Step (_, Global.Input, _, _) -> true
      | _ -> false in
    let rec parse_and_run_step dkinputvars dkinputconcvars env =
      let step = Scope.scope (Parseprf.step Lexprf.token lexbuf) in
      run_step step dkinputvars dkinputconcvars env
    and run_step step dkinputvars dkinputconcvars env =
      let line, newenv =
	Translate.translate_step 
	  dkinputvars dkinputconcvars step env in
      Translate.print_step out line;
      parse_and_run_step dkinputvars dkinputconcvars newenv    
    in
    let rec parse_and_run_input dkinputvars dkinputconcvars inputs env =
      let step = Scope.scope (Parseprf.step Lexprf.token lexbuf) in
      if inputstep step
      then
 	let newvar, newconcvar, newinput, newenv = 
	  Translate.translate_input step env in
	parse_and_run_input 
	  (newvar :: dkinputvars)
	  (newconcvar :: dkinputconcvars) 
	  (newinput :: inputs) newenv
      else begin
      	  Translate.print_prelude out inputs dkinputconcvars;
	  run_step step dkinputvars dkinputconcvars env end in
    parse_and_run_input [] [] [] Translate.PrfEnvSet.empty      
  with 
  | Global.EndOfFile -> ()
  | Parsing.Parse_error -> 
    let (s, l, c) = Global.loc_err lexbuf in
    raise (Global.ParserError (s, l, c))
  | Global.FoundRuleError ->
    let (_, l, _) = Global.loc_err lexbuf in
    raise (Global.RuleError l)

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
    Dkterm.p_line out (Dkterm.mk_prelude name);
    parse_and_run out lexbuf
     
let () =
  try
    Arg.parse argspec translate_file umsg;
  with
  | Global.LexerError (s, l, c ) -> Global.error l c (sprintf "Unexpected character '%s'"s)
  | Global.ParserError (s, l, c ) -> Global.error l c (sprintf "Unexpected token '%s'"s)
  | Global.RuleError l -> Global.error l 1 ("Unexpected rule structure")
