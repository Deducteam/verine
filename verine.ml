open Printf

exception Catched_lexer_error of string * int * int
exception Catched_parse_error of string * int * int

let umsg = "Usage: verine <file.smt2> <file.proof>"

let files = ref []

let argspec = ["-debug", Arg.Set Debug.debugmode, "debug mode"]

let process_proof signature assertion_bindings lexbuf =
  try
    let rec process_step env =
      let trace_step = Parser.step Lexer.token lexbuf in
      let step = Proof.process_step signature trace_step in
      let line, newenv = Translate.translate_step signature assertion_bindings in
      Smt2d.Dedukti.print_line stdout line;
      process_step newenv in
    process_step ()

    (* let inputstep step = *)
    (*   match step with *)
    (*   | Proof.Step (_, Proof.Input, _, _) -> true *)
    (*   | _ -> false in *)
    (* let rec parse_and_run_step dkinputvars dkinputconcvars env = *)
    (*   let step = Scope.scope (Parser.step Lexer.token lexbuf) in *)
    (*   run_step step dkinputvars dkinputconcvars env *)
    (* and run_step step dkinputvars dkinputconcvars env = *)
    (*   let line, newenv = *)
    (* 	Translate.translate_step  *)
    (* 	  dkinputvars dkinputconcvars step env in *)
    (*   Translate.print_step stdout line; *)
    (*   parse_and_run_step dkinputvars dkinputconcvars newenv     *)
    (* in *)
    (* let rec parse_and_run_input dkinputvars dkinputconcvars inputs env = *)
    (*   let step = Scope.scope (Parser.step Lexer.token lexbuf) in *)
    (*   if inputstep step *)
    (*   then *)
    (* 	let newvar, newconcvar, newenv =  *)
    (* 	  Translate.translate_input step env in *)
    (* 	parse_and_run_input  *)
    (* 	  (newvar :: dkinputvars) *)
    (* 	  (newconcvar :: dkinputconcvars)  *)
    (* 	  (step :: inputs) newenv *)
    (*   else begin *)
    (*   	  Translate.print_prelude stdout env inputs dkinputconcvars; *)
    (* 	  run_step step dkinputvars dkinputconcvars env end in *)
    (* parse_and_run_input [] [] [] Translate.PrfEnvMap.empty *)

  with
  | Error.EndOfFile -> ()
  | Lexer.Lexer_error -> 
     let (s, l, c) = Error.get_location lexbuf in
     raise (Catched_lexer_error (s, l, c))
  | Parsing.Parse_error -> 
    let (s, l, c) = Error.get_location lexbuf in
    raise (Catched_parse_error (s, l, c))
  | Error.FoundRuleError ->
     let l = Error.get_line lexbuf in
    raise (Error.RuleError l)

let process_smt2 lexbuf =
  let signature, assertions = Smt2d.Process_script.get_unique_context lexbuf in
  let sort_context = Smt2d.Translate.tr_sort_context signature in
  let fun_context = Smt2d.Translate.tr_fun_context signature in
  let assertion_bindings = 
    List.mapi 
      (fun i term ->
       term, Smt2d.Dedukti.var (("I_"^(string_of_int (i+1))))) assertions in
  let inputs = Smt2d.Translate.tr_assertion_bindings signature assertion_bindings in
  List.iter (Smt2d.Dedukti.print_line stdout) sort_context;
  List.iter (Smt2d.Dedukti.print_line stdout) fun_context;
  List.iter (Smt2d.Dedukti.print_line stdout) inputs;
  signature, assertion_bindings

let () =
  try
    Arg.parse argspec (fun f -> files := f :: !files) umsg;
    match !files with
    | [smt2_file; proof_file] -> 
       let modname = 
	 Smt2d.Translate.tr_string (Filename.chop_extension (Filename.basename smt2_file)) in
       let prelude = Smt2d.Dedukti.prelude modname in
       Smt2d.Dedukti.print_line stdout prelude;
       let smt2_lexbuf = Lexing.from_channel (open_in smt2_file) in
       let signature, assertion_bindings = process_smt2 smt2_lexbuf in
       let proof_lexbuf = Lexing.from_channel (open_in proof_file) in
       process_proof signature assertion_bindings proof_lexbuf
    | _ -> Arg.usage argspec umsg; exit 1
  with
  | Catched_lexer_error (s, l, c ) -> 
     Error.print_location_error l c (sprintf "Unexpected character '%s'"s)
  | Catched_parse_error (s, l, c ) -> 
     Error.print_location_error l c (sprintf "Unexpected token '%s'"s)
  | Error.RuleError l -> 
     Error.print_line_error l ("Unexpected rule structure")
