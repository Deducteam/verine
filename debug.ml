let debugmode = ref false

let printterm t = 
  Smt2d.Dedukti.print_term stderr t
	 
let printlist ts = 
  let xeprintdks ts =
    match ts with
    | [] -> ()
    | t :: ts -> 
       printterm t; 
       List.iter 
	 (fun t -> Printf.eprintf " | "; printterm t) ts in
  Printf.eprintf "[ ";
  xeprintdks ts;
  Printf.eprintf " ]"
  
let printcontext s1 ts s2 = 
  Printf.eprintf "%s" s1; printlist ts; Printf.eprintf "%s" s2

let ddo f = 
  if !debugmode then ( f; Printf.eprintf "%!" )

let dprintterm t = ddo (printterm t)
    
let dprintlist ts = ddo (printlist ts)
      
let dprintcontext s1 ts s2 = ddo (printcontext s1 ts s2)
