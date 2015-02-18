(* remains false unless -debug option is called *)
let debug_mode = ref false

(* apply_if_debug f applies f only in debug mode, and flushes stderr afterwards *)
let apply_if_debug f = 
  if !debug_mode then ( f; Printf.eprintf "%!" )

(* print a dedukti term on stderr *)
let print_term t =
  Smt2d.Dedukti.print_term stderr t
	 
(* print a dedukti list on stderr *)
let print_terms ts = 
  Printf.eprintf "[ ";
  begin 
    match ts with
    | [] -> ()
    | t :: ts ->
       print_term t; List.iter (fun t -> Printf.eprintf " | "; print_term t) ts end;
  Printf.eprintf " ]";

