open Printf

exception Catched_lexer_error of string * int * int
exception Catched_parse_error of string * int * int
exception Catched_translate_error of int

let umsg = "Usage: verine <file.smt2> <file.proof>"

let files = ref []

let argspec = ["-debug", Arg.Set Debug.debug_mode, "debug mode"]

let process_proof signature assertions assertion_vars lexbuf =
  try
    let smt2_env =
      { Translate.signature = signature;
	Translate.input_terms = assertions;
	Translate.input_term_vars = assertion_vars;
	Translate.input_proof_idents = 
	  List.mapi
	    (fun i _ -> "HI_"^(string_of_int (i+1))) assertion_vars;
      } in
    let rec process_step proof_env =
      let step = Parser.step Lexer.token lexbuf in
      (* let step = Proof.process_step trace_step in *)
      let line, new_proof_env = Translate.translate_step smt2_env proof_env step in
      Smt2d.Dedukti.print_line stdout line;
      process_step new_proof_env in
    process_step Translate.PrfEnvMap.empty
  with
  | End_of_file -> ()
  | Lexer.Lexer_error -> 
     let (s, l, c) = Error.get_location lexbuf in
     raise (Catched_lexer_error (s, l, c))
  | Parsing.Parse_error -> 
    let (s, l, c) = Error.get_location lexbuf in
    raise (Catched_parse_error (s, l, c))
  | Translate.Translate_error ->
     let l = Error.get_line lexbuf in
    raise (Catched_translate_error l)

let process_smt2 lexbuf =
  let signature, assertions = Smt2d.Process_script.get_context lexbuf in
  let sort_context = Smt2d.Translate.tr_sort_context signature in
  let fun_context = Smt2d.Translate.tr_fun_context signature in
  let assertion_vars = 
    List.mapi 
      (fun i _ -> Smt2d.Dedukti.var ("I_"^(string_of_int (i+1)))) assertions in
  let assertion_context = 
    Smt2d.Translate.tr_assertion_bindings 
      signature (List.combine assertions assertion_vars) in
  List.iter (Smt2d.Dedukti.print_line stdout) sort_context;
  List.iter (Smt2d.Dedukti.print_line stdout) fun_context;
  List.iter (Smt2d.Dedukti.print_line stdout) assertion_context;
  signature, assertions, assertion_vars 

let () =
  try
    Arg.parse argspec (fun f -> files := f :: !files) umsg;
    match !files with
    | [proof_file; smt2_file] ->
       let modname = 
	 Smt2d.Translate.tr_string (Filename.chop_extension (Filename.basename smt2_file)) in
       let prelude = Smt2d.Dedukti.prelude modname in
       Smt2d.Dedukti.print_line stdout prelude;
       let smt2_lexbuf = Lexing.from_channel (open_in smt2_file) in
       let signature, assertions, assertion_vars = process_smt2 smt2_lexbuf in
       let proof_lexbuf = Lexing.from_channel (open_in proof_file) in
       process_proof 
	 (* signature (List.map Proof.mk_term assertions) *)
	 signature assertions
	 assertion_vars proof_lexbuf
    | _ -> Arg.usage argspec umsg; exit 1
  with
  | Catched_lexer_error (s, l, c ) -> 
     Error.print_location_error l c (sprintf "Unexpected character '%s'"s)
  | Catched_parse_error (s, l, c ) -> 
     Error.print_location_error l c (sprintf "Unexpected token '%s'"s)
  | Catched_translate_error l -> 
     Error.print_line_error l ("Unexpected inference")
