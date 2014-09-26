open Global
open Dkterm

module FreeVarSet = Set.Make (
  struct
    type t = dkvar
    let compare = String.compare
  end)
  
module PrfEnvSet = Map.Make (
  struct 
    type t = rulename
    let compare = String.compare
  end)

(* transformer les preuves *)

let mk_dblneg prf prop n =
  let h = "H"^(string_of_int n) in  
  mk_lam h (mk_prf (mk_not prop)) 
    (mk_app2 (mk_var h) prf), n+1

let rec mk_clause props = 
  match props with
  | p :: ps -> mk_imply (mk_not p) (mk_clause ps)
  | [] -> mk_false

let mk_str types n =
  let vars, newn = 
    List.fold_left (fun (l,n) t -> 
      (("H"^(string_of_int n)) :: l), n+1 ) ([],n) types in
  List.rev vars, newn

let mk_abs vars types f =
  List.fold_left2 (fun term var t -> mk_lam var t term) 
    (f (List.map mk_var vars)) (List.rev vars) (List.rev types) 

exception NotFound

let rec find_prop_resolution p1s p2s =
  match p1s, p2s with
  | (Dkapp [Dknot; p]) :: p1s, p2 :: p2s when (p = p2) ->
    true, p, [], p1s, [], p2s
  | p1 :: p1s, (Dkapp [Dknot; p]) :: p2s when (p = p1) ->
    false, p, [], p1s, [], p2s
  | p1 :: p1s, p2 :: p2s ->
    begin 
      try 
	let b, p, p1h, p1t, p2h, p2t = find_prop_resolution p1s (p2 :: p2s) in
	b, p, p1 :: p1h, p1t, p2h, p2t
      with
      | NotFound -> 
	let b, p, p1h, p1t, p2h, p2t = find_prop_resolution (p1 :: p1s) p2s in
	b, p, p1h, p1t, p2 :: p2h, p2t	
    end
  | _, _ -> raise NotFound

(* translate_proof *)
    
let translate_term term =
  match term with
  | Var (s) -> mk_var s

let rec translate_prop prop =
  match prop with
  | Eq (x, y) -> mk_eq (translate_term x) (translate_term y)
  | Not (p) -> mk_not (translate_prop p)
  | And (p, q) -> mk_and (translate_prop p) (translate_prop q)
  | Imply (p, q) -> mk_imply (translate_prop p) (translate_prop q)
  | False -> mk_false

let translate_resolution (prf1, p1s) (prf2, p2s) n =
  let order, p, p1h, p1t, p2h, p2t = find_prop_resolution p1s p2s in
  let t = mk_prf (mk_not p) in
  let t1h = List.map (fun p -> mk_prf (mk_not p)) p1h in
  let t1t = List.map (fun p -> mk_prf (mk_not p)) p1t in
  let t2h = List.map (fun p -> mk_prf (mk_not p)) p2h in
  let t2t = List.map (fun p -> mk_prf (mk_not p)) p2t in
  let s = "H"^(string_of_int n) in
  let s1h, n1 = mk_str t1h (n+1) in
  let s1t, n2 = mk_str t1t n1 in
  let s2h, n3 = mk_str t2h n2 in
  let s2t, newn = mk_str t2t n3 in
  let fprf v1h v1t v2h v2t = 
    match order, v1t, v2t with
    | true, _, [] -> mk_app (prf1 :: (v1h @ [mk_app (prf2 :: v2h)] @ v1t))
    | true, _, _ -> 
      mk_app (prf1 :: (v1h @ [mk_lam s t (mk_app (prf2 :: (v2h @ [mk_var s] @ v2t)))] @ v1t))
    | false, [], _ -> mk_app (prf2 :: (v2h @ [mk_app (prf1 :: v1h)] @ v2t))
    | false, _, _ -> 
      mk_app (prf2 :: (v2h @ [mk_lam s t (mk_app (prf1 :: (v1h @ [mk_var s] @ v1t)))] @ v2t)) in
  mk_abs s1h t1h (fun v1h -> 
    mk_abs s1t t1t (fun v1t ->
      mk_abs s2h t2h (fun v2h -> 
	mk_abs s2t t2t (fun v2t -> 
	  fprf v1h v1t v2h v2t)))), p1h@p1t@p2h@p2t, newn

let rec translate_rule rule hyps concs env n = 
  match rule, hyps, concs with
  | Input, _,  _ -> assert false
  | Eq_reflexive, [], [Dkapp [Dkeq; t; u] as conc] -> 
    assert (t = u);
    let p = "P"^(string_of_int n) in  
    let h = "H"^(string_of_int (n+1)) in 
    let prf = 
      mk_lam p (mk_arrow mk_termtype mk_proptype)
	(mk_lam h (mk_prf (mk_app2 (mk_var p) t))
	   (mk_var h)) in
    mk_dblneg prf conc (n+2)
  | Eq_transitive, [], 
    [Dkapp [Dknot; Dkapp [Dkeq; t1; u1] as p1]; 
     Dkapp [Dknot; Dkapp [Dkeq; t2; u2] as p2]; 
     Dkapp [Dkeq; t3; u3] as p3] ->
    begin match t1, t2, t3, u1, u2, u3 with
    | x, x1, y, y1, z, z1 when (x1 = x && y1 = y && z1 = z) ->
      let h1 = "H"^(string_of_int n) in (*not not x = y*)
      let h2 = "H"^(string_of_int (n+1)) in (*not not x = z*)
      let h3 = "H"^(string_of_int (n+2)) in (*not y = z*)
      let h4 = "H"^(string_of_int (n+3)) in (*x = y*)
      let h5 = "H"^(string_of_int (n+4)) in (*x = z*)
      let t = "T"^(string_of_int (n+6)) in  
      mk_lam h1 (mk_prf (mk_not (mk_not p1)))
	(mk_lam h2 (mk_prf (mk_not (mk_not p2)))
	   (mk_lam h3 (mk_prf (mk_not p3))
	      (mk_app2 (mk_var h1)
		 (mk_lam h4 (mk_prf p1)
		    (mk_app2 (mk_var h2)
		       (mk_lam h5 (mk_prf p2)
			  (mk_app2 (mk_var h3)
			     (mk_app3 (mk_var h4)
				(mk_lam t mk_termtype 
				   (mk_eq (mk_var t) z))
				(mk_var h5))))))))), n+7
    | _, _, _, _, _, _ -> assert false end
  | Resolution, [prf1, p1s; prf2, p2s], _ -> 
    let prf, concs, newn = 
      translate_resolution (prf1, p1s) (prf2, p2s) n in
    prf, newn
  | Resolution, c1 :: c2 :: cs, _ ->
    let prf, newconcs, newn = 
      translate_resolution c1 c2 n in
    translate_rule Resolution ((prf, newconcs) :: cs) concs env newn
  | Rand, [prf, [(Dkapp [Dkand; p; q]) as dkprop]], [conc] -> 
    let h1 = "H"^(string_of_int n) in 
    let h2 = "H"^(string_of_int (n+1)) in 
    let h3 = "H"^(string_of_int (n+2)) in 
    let h4 = "H"^(string_of_int (n+3)) in 
    if (p = conc)
    then
      mk_lam h1 (mk_prf (mk_not p)) 
	(mk_app2 prf 
	   (mk_lam h2 (mk_prf dkprop) 
	      (mk_app2 (mk_var h1) 
		 (mk_app3 (mk_var h2) p 
		    (mk_lam h3 (mk_prf p) 
		       (mk_lam h4 (mk_prf q) 
			  (mk_var h3))))))), n+4
    else if (q = conc)
    then
      mk_lam h1 (mk_prf (mk_not q)) 
	(mk_app2 prf 
	   (mk_lam h2 (mk_prf dkprop) 
	      (mk_app2 (mk_var h1) 
		 (mk_app3 (mk_var h2) q 
		    (mk_lam h3 (mk_prf p) 
		       (mk_lam h4 (mk_prf q) 
			  (mk_var h4))))))), n+4
    else assert false
  | Anonrule (name), _, _ -> assert false
  | _, _, _ -> raise FoundRuleError

let rec translate_step inputname dkinput step env =
  match step with
  | Step (name, rule, prems, concs) -> 
    let hyps = List.map 
      (fun prem -> PrfEnvSet.find prem env) prems in
    let dkconcs = List.map translate_prop concs in
    let prf, _ = translate_rule rule hyps dkconcs env 1 in
    let line = 
      mk_deftype name
	(mk_prf (mk_imply dkinput (mk_clause dkconcs))) 
	(mk_lam inputname (mk_prf dkinput) prf) in
    let newenv =
      PrfEnvSet.add name 
	(mk_app2 (mk_var name) (mk_var inputname), dkconcs) env in 
    line, newenv

let print_step out line =
  p_line out line

(* get_vars *)

let get_vars_term env term =
  match term with
  | Var (s) -> FreeVarSet.add s env

let rec get_vars_prop env prop =
  match prop with
  | Eq (t1, t2) -> 
    get_vars_term (get_vars_term env t1) t2
  | Not (p) -> get_vars_prop env p
  | And (p, q) -> get_vars_prop (get_vars_prop env p) q
  | Imply (p, q) -> get_vars_prop (get_vars_prop env p) q
  | False -> env

let get_vars env step = 
  match step with
  | Step (_, _, _, concs) -> 
    List.fold_left get_vars_prop env concs

(* premiere ligne *)

let translate_input input =
  match input with 
  | Step (name, Input, [], concs) -> 
    let dkconcs = List.map translate_prop concs in
    name, mk_clause dkconcs, 
    PrfEnvSet.add name (mk_var name, dkconcs) PrfEnvSet.empty
  | _ -> raise FoundRuleError

let print_prelude out input filename = 
  p_line out (mk_prelude filename);
  let env = get_vars FreeVarSet.empty input in
  FreeVarSet.iter
    (fun var -> p_line out (mk_decl var mk_termtype)) env
