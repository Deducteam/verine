open Parsetree

let scope_symbol sym = 
  match sym with
  | Symbol s ->     
     let buf = Buffer.create (2*String.length s) in
     String.iter
       (fun c -> 
	match c with
	| 'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char buf c
	| '_' -> Buffer.add_string buf "__"
	| _ -> 
	   Buffer.add_string 
	     buf ("_"^(string_of_int (int_of_char c)))) s;
     Buffer.contents buf

let rec scope_term smtterm = 
  match smtterm with
  | Var (sym) -> 
     Global.Var (scope_symbol sym)
  | Fun (sym, smtterms) -> 
     Global.Fun (scope_symbol sym, List.map scope_term smtterms)
  | Let (bindings, smtterm) -> assert false 
  | Core (smtcore) -> assert false

let rec scope_prop smtterm = 
  match smtterm with
  | Var (sym) -> Global.Pred (scope_symbol sym, [])
  | Fun (sym, smtterms) -> 
     Global.Pred (scope_symbol sym, List.map scope_term smtterms)
  | Let (bindings, smtterm) -> assert false 
  | Core (smtcore) -> 
     match smtcore with
     | True -> Global.True
     | False -> Global.False
     | Not (smtterm) -> Global.Not (scope_prop smtterm)
     | Imply (smtterms) -> 
	let mkimply p1 p2 = Global.Imply (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec mkimplys ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkimply p1 p2
	  | p :: ps -> mkimply p (mkimplys ps) in
	mkimplys ps
     | And (smtterms) ->
	let mkand p1 p2 = Global.And (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec xmkands ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkand p2 p1
	  | p :: ps -> mkand (xmkands ps) p in
	xmkands (List.rev ps)
     | Or (smtterms) ->
	let mkor p1 p2 = Global.Or (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec xmkors ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkor p2 p1
	  | p :: ps -> mkor (xmkors ps) p in
	xmkors (List.rev ps)
     | Xor (smtterms) ->
	let mkxor p1 p2 = Global.Xor (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec xmkxors ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkxor p2 p1
	  | p :: ps -> mkxor (xmkxors ps) p in
	xmkxors (List.rev ps)
     | Eq (smtterms) ->
	let mkand p1 p2 = Global.And (p1, p2) in
	let mkeq t1 t2 = Global.Eq (t1, t2) in
	let ts = List.map scope_term smtterms in
	let rec mkeqs ts =
	  match ts with
	  | [] | [_] -> assert false
	  | [t1; t2] -> [mkeq t1 t2]
	  | t1 :: t2 :: ts -> 
	     (mkeq t1 t2) :: mkeqs (t2 :: ts) in
	let rec xmkands ps = 
	  match ps with
	  | [] -> assert false
	  | [p] -> p
	  | [p1; p2] -> mkand p2 p1
	  | p :: ps -> mkand (xmkands ps) p in
	xmkands (List.rev (mkeqs ts))
     | Distinct (smtterms) -> assert false
     | Ite (smtterm1, smtterm2, smtterm3) -> assert false
				    
let scope line =
  match line with
  | Line (name, rule, names, smtterms) ->
     Global.Step (name, rule, names, List.map scope_prop smtterms)
