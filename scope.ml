module Tr = Trace
module Pr = Proof

module BindVarSet = Map.Make (
  struct
    type t = Tr.symbol
    let compare = Pervasives.compare
  end)

let scope_binding env binding =
  match binding with
  | Tr.Varbinding (sym, smtterm) -> BindVarSet.add sym smtterm env

let rec unfold env smtterm =
  match smtterm with
  | Tr.Var (sym) -> 
     if BindVarSet.mem sym env
     then unfold env (BindVarSet.find sym env)
     else smtterm
  | Tr.Fun (sym, smtterms) -> 
     Tr.Fun (sym, List.map (unfold env) smtterms)
  | Tr.Let (bindings, smtterm) ->
     let newenv = List.fold_left scope_binding env bindings in
     unfold newenv smtterm
  | Tr.Core (smtcore) ->
     let smtc = match smtcore with
     | Tr.True -> Tr.True
     | Tr.False -> Tr.False
     | Tr.Not (smtterm) -> Tr.Not (unfold env smtterm)
     | Tr.Imply (smtterms) -> Tr.Imply (List.map (unfold env) smtterms)
     | Tr.And (smtterms) -> Tr.And (List.map (unfold env) smtterms)
     | Tr.Or (smtterms) -> Tr.Or (List.map (unfold env) smtterms)
     | Tr.Xor (smtterms) -> Tr.Xor (List.map (unfold env) smtterms)
     | Tr.Eq (smtterms) -> Tr.Eq (List.map (unfold env) smtterms)
     | Tr.Distinct (smtterms) -> Tr.Distinct (List.map (unfold env) smtterms)
     | Tr.Ite (smtterm1, smtterm2, smtterm3) -> 
	Tr.Ite (unfold env smtterm1, unfold env smtterm2, unfold env smtterm3) in
     Tr.Core smtc
	     
let convert s =
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

let scope_symbol sym = 
  match sym with
  | Tr.Symbol s -> convert s

let rec scope_term smtterm = 
  match smtterm with
  | Tr.Var (sym) -> 
     Pr.Var (scope_symbol sym)
  | Tr.Fun (sym, smtterms) -> 
     Pr.Fun (scope_symbol sym, List.map scope_term smtterms)
  | Tr.Let (bindings, smtterm) -> assert false 
  | Tr.Core (smtcore) -> assert false

let rec scope_prop smtterm = 
  match smtterm with
  | Tr.Var (sym) -> 
     Pr.Pred (scope_symbol sym, [])
  | Tr.Fun (sym, smtterms) -> 
     Pr.Pred (scope_symbol sym, List.map scope_term smtterms)
  | Tr.Let (bindings, smtterm) -> assert false
  | Tr.Core (smtcore) -> 
     match smtcore with
     | Tr.True -> Pr.True
     | Tr.False -> Pr.False
     | Tr.Not (smtterm) -> Pr.Not (scope_prop smtterm)
     | Tr.Imply (smtterms) -> 
	let mkimply p1 p2 = Pr.Imply (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec mkimplys ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkimply p1 p2
	  | p :: ps -> mkimply p (mkimplys ps) in
	mkimplys ps
     | Tr.And (smtterms) ->
	let mkand p1 p2 = Pr.And (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec xmkands ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkand p2 p1
	  | p :: ps -> mkand (xmkands ps) p in
	xmkands (List.rev ps)
     | Tr.Or (smtterms) ->
	let mkor p1 p2 = Pr.Or (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec xmkors ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkor p2 p1
	  | p :: ps -> mkor (xmkors ps) p in
	xmkors (List.rev ps)
     | Tr.Xor (smtterms) ->
	let mkxor p1 p2 = Pr.Xor (p1, p2) in
	let ps = List.map scope_prop smtterms in
	let rec xmkxors ps = 
	  match ps with
	  | [] | [_] -> assert false
	  | [p1; p2] -> mkxor p2 p1
	  | p :: ps -> mkxor (xmkxors ps) p in
	xmkxors (List.rev ps)
     | Tr.Eq (smtterms) ->
	let mkand p1 p2 = Pr.And (p1, p2) in
	let rec xmkands ps = 
	  match ps with
	  | [] -> assert false
	  | [p] -> p
	  | [p1; p2] -> mkand p2 p1
	  | p :: ps -> mkand (xmkands ps) p in
	let mkeq t1 t2 = Pr.Eq (t1, t2) in
	let rec mkeqs ts =
	  match ts with
	  | [] | [_] -> assert false
	  | [t1; t2] -> [mkeq t1 t2]
	  | t1 :: t2 :: ts -> 
	     (mkeq t1 t2) :: mkeqs (t2 :: ts) in
	let ts = List.map scope_term smtterms in
	xmkands (List.rev (mkeqs ts))
     | Tr.Distinct (smtterms) -> 
	let mkand p1 p2 = Pr.And (p1, p2) in
	let rec xmkands ps = 
	  match ps with
	  | [] -> assert false
	  | [p] -> p
	  | [p1; p2] -> mkand p2 p1
	  | p :: ps -> mkand (xmkands ps) p in
	let mkdist t1 t2 = Pr.Distinct (t1, t2) in
	let rec mkdists ts = 
	  match ts with
	  | [] -> assert false
	  | [_] -> []
	  | t :: ts -> List.map (mkdist t) ts @ mkdists ts in
	let ts = List.map scope_term smtterms in
	xmkands (List.rev (mkdists ts))
     | Tr.Ite (smtterm1, smtterm2, smtterm3) -> assert false

let scope_rule rule = 
  match rule with
  | Tr.Input -> Pr.Input
  | Tr.Eq_reflexive -> Pr.Eq_reflexive
  | Tr.Eq_transitive -> Pr.Eq_transitive
  | Tr.Eq_congruent -> Pr.Eq_congruent
  | Tr.Resolution -> Pr.Resolution
  | Tr.Unknown s -> Pr.Unknown s
					    
let scope step =
  match step with
  | Tr.Step (name, rule, names, smtterms) ->
     let smtterms_unfold = List.map (unfold BindVarSet.empty) smtterms in
     Pr.Step (name, scope_rule rule, names, List.map scope_prop smtterms_unfold)
