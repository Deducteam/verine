let debugmode = ref false

let eprints s = 
  if !debugmode then Printf.eprintf "%s%!" s
    
let eprintdk term = 
  if !debugmode then (
    Dkterm.p_term stderr term;
    eprints "")
    
let eprintdks terms = 
  if !debugmode then (
    let rec xeprintdks terms =
      match terms with
      | [] -> ()
      | t :: ts -> eprintdk t; 
	List.iter (fun t -> eprints " | "; eprintdk t) ts in
    eprints "[";
    xeprintdks terms;
    eprints "]";)
    
let eprintdksc s1 ts s2 = 
  if !debugmode then (eprints s1; eprintdks ts; eprints s2)
