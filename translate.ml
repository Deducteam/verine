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

let translate_rule rule hyps concs env n = 
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
    [Dkapp [Dknot; Dkapp [Dkeq; t1; u1] as c1]; 
     Dkapp [Dknot; Dkapp [Dkeq; t2; u2] as c2]; 
     Dkapp [Dkeq; t3; u3] as c3] ->
    begin match t1, t2, t3, u1, u2, u3 with
    | x, x1, y, y1, z, z1 when (x1 = x && y1 = y && z1 = z) ->
      let h1 = "H"^(string_of_int n) in (*not not x = y*)
      let h2 = "H"^(string_of_int (n+1)) in (*not not x = z*)
      let h3 = "H"^(string_of_int (n+2)) in (*not y = z*)
      let h4 = "H"^(string_of_int (n+3)) in (*x = y*)
      let h5 = "H"^(string_of_int (n+4)) in (*x = z*)
      let t = "T"^(string_of_int (n+6)) in  
      mk_lam h1 (mk_prf (mk_not (mk_not c1)))
	(mk_lam h2 (mk_prf (mk_not (mk_not c2)))
	   (mk_lam h3 (mk_prf (mk_not c3))
	      (mk_app2 (mk_var h1)
		 (mk_lam h4 (mk_prf c1)
		    (mk_app2 (mk_var h2)
		       (mk_lam h5 (mk_prf c2)
			  (mk_app2 (mk_var h3)
			     (mk_app3 (mk_var h4)
				(mk_lam t mk_termtype 
				   (mk_eq (mk_var t) z))
				(mk_var h5))))))))), n+7
    | _, _, _, _, _, _ -> assert false end
  | Resolution, [prf1, [p1]; prf2, [p2]], [] -> 
    begin match p1, p2 with
    | Dkapp [Dknot; p], p2 when (p = p2) -> mk_app2 prf1 prf2, n
    | p1, Dkapp [Dknot; p] when (p = p1) -> mk_app2 prf2 prf1, n
    | _, _ -> assert false end
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
