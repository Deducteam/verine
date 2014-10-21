open Printf

let filename : string option ref = ref None

let umsg = "Usage: verine <file>"

let argspec = ["-debug", Arg.Set Debug.debugmode, "debug mode"]

let parse_and_run out lexbuf filename= 
  try 
    let input = Parseprf.step Lexprf.token lexbuf in
    let dkinputvar, dkinput, inputenv = 
      Translate.translate_input input in
    Translate.print_prelude out input filename;
    let rec parse_and_run_step env =
      let step = Parseprf.step Lexprf.token lexbuf in
      let line, newenv =
	Translate.translate_step dkinput dkinputvar step env in
      Translate.print_step out line;
      parse_and_run_step newenv in
    parse_and_run_step inputenv
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
    let name = Filename.chop_extension (Filename.basename file) in
    filename := Some name;
    let chan = open_in file in
    let lexbuf = Lexing.from_channel chan in
    (*let out = open_out ((Filename.chop_extension file) ^ ".dk") in*)
    let out = stdout in
    parse_and_run out lexbuf name
     
let () =
  try
    Arg.parse argspec translate_file umsg;
  with
  | Global.LexerError (s, l, c ) -> Global.error l c (sprintf "Unexpected character '%s'"s)
  | Global.ParserError (s, l, c ) -> Global.error l c (sprintf "Unexpected token '%s'"s)
  | Global.RuleError l -> Global.error l 1 ("Unexpected rule structure")
