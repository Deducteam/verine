module Dk = Smt2d.Dedukti
module Pr = Proof
  
module PrfEnvMap = Map.Make (
  struct 
    type t = string
    let compare = Pervasives.compare
  end)

let mk_newvar s n = 
  s^(string_of_int n), n+1

let mk_newvars s l n =
  let vars, newn = 
    List.fold_left (fun (vs,m) _ -> 
      let v, newm = mk_newvar s m in
      (v :: vs), newm) ([],n) l in
  List.rev vars, newn

let rec mk_clause props = 
  match props with
  | p :: ps -> Dk.l_imply (Dk.l_not p) (mk_clause ps)
  | [] -> Dk.l_false

let rec translate_term term =
  match term with
  | Pr.Var (s) -> Dk.var s
  | Pr.Fun (s, ts) -> Dk.app (Dk.var s) (List.map translate_term ts)

let rec translate_prop prop =
  match prop with
  | Pr.True -> Dk.l_true
  | Pr.False -> Dk.l_false
  | Pr.Not (p) -> Dk.l_not (translate_prop p)
  | Pr.Imply (p, q) -> Dk.l_imply (translate_prop p) (translate_prop q)
  | Pr.And (p, q) -> Dk.l_and (translate_prop p) (translate_prop q)
  | Pr.Or (p, q) -> Dk.l_or (translate_prop p) (translate_prop q)
  | Pr.Xor (p, q) -> assert false
  | Pr.Eq (x, y) -> Dk.l_eq (translate_term x) (translate_term y)
  | Pr.Distinct (x, y) -> Dk.l_not (Dk.l_eq (translate_term x) (translate_term y))
  | Pr.Ite (p, x, y) -> assert false
  | Pr.Pred (s, ts) -> Dk.app
    (Dk.var (s^(string_of_int (List.length ts)))) (List.map translate_term ts)

(* *** TRANSLATION OF EQUALITIES *** *)

(* returns a proof of x = x *)
let find_reflexive x n =
  let p, n1 = mk_newvar "P" n in  
  let h, newn = mk_newvar "H" n1 in 
  Dk.lam p (Dk.arrow Dk.l_term Dk.l_prop)
    (Dk.lam h (Dk.l_prf (Dk.app2 (Dk.var p) (translate_term x))) (Dk.var h)), newn

(* from h a proof of x = y, returns a proof of y = x *)
let find_symmetric h x y n =
  let refl, n1 = find_reflexive x n in
  let t, newn = mk_newvar "T" n1 in
  Dk.app3 h (Dk.lam t Dk.l_term (Dk.l_eq (Dk.var t) (translate_term x))) refl, newn

(* from:
   - xi, yi such that x1 = y1, x2 = y2, x3 = y3 are of the form 
     x = y, y = z, x = z up to equality symmetries,
   - prf1 a proof of x1 = y1, prf2 a proof of x2 = y2
   returns a proof of x3 = y3 *)
let rec find_transitive prf1 prf2 x1 y1 x2 y2 x3 y3 n =
  let t, n1 = mk_newvar "T" n in
  match y3 = y2, y3 = y1, x2 = x1 with
  | true, _, true ->             (* case y = x, y = z, x = z *)
    Dk.app3 prf1 (Dk.lam t Dk.l_term (Dk.l_eq (Dk.var t) (translate_term y3))) prf2, n1
  | true, _, false ->            (* case x = y, y = z, x = z *)
    Dk.app3 prf2 (Dk.lam t Dk.l_term (Dk.l_eq (translate_term x3) (Dk.var t))) prf1, n1
  | false, true, true ->         (* case y = x, y = z, z = x *)
    Dk.app3 prf2 (Dk.lam t Dk.l_term (Dk.l_eq (Dk.var t) (translate_term y3))) prf1, n1
  | false, true, false ->        (* case y = x, z = y, z = x *)
    Dk.app3 prf1 (Dk.lam t Dk.l_term (Dk.l_eq (translate_term x3) (Dk.var t))) prf2, n1
  | false, false, _ -> 
    match y3 = x1 with
    | true ->                    (* case x = y, _ = _, z = x: use a proof of y = x *)
      let sym, n2 = find_symmetric prf1 x1 y1 n1 in
      find_transitive sym prf2 y1 x1 x2 y2 x3 y3 n2
    | false ->                   (* case _ = _, z = y, x = z: use a proof of y = z *)
      let sym, n2 = find_symmetric prf2 x2 y2 n1 in
      find_transitive prf1 sym x1 y1 y2 x2 x3 y3 n2

let rec find_transitives prfs xys x y n =
  match prfs, xys with 
  | [prf1; prf2], [(x1, y1); (x2, y2)] -> 
    find_transitive prf1 prf2 x1 y1 x2 y2 x y n 
  | (prf1 :: prf2 :: ps), ((x1, y1) :: (x2, y2) :: vs) ->
    let t, n1 = mk_newvar "T" n in
    let prf, xy, n3 =
      match x1 = x2, x1 = y2, y1 = x2 with
      | true, _, _ ->                (* case y = x, y = z *)
	Dk.app3 prf1 
		  (Dk.lam t Dk.l_term (Dk.l_eq (Dk.var t) (translate_term y2))) prf2, (y1, y2), n1
      | false, true, _ ->            (* case y = x, z = y *)
	Dk.app3 prf1 
		  (Dk.lam t Dk.l_term (Dk.l_eq (translate_term x2) (Dk.var t))) prf2, (x2, y1), n1
      | false, false, true ->        (* case x = y, y = z *)
	Dk.app3 prf2 
		  (Dk.lam t Dk.l_term (Dk.l_eq (translate_term x1) (Dk.var t))) prf1, (x1, y2), n1
      | false, false, false ->       (* case x = y, z = y: use a proof of y = x *)
	let sym, n2 = find_symmetric prf1 x1 y1 n1 in
	Dk.app3 
	  sym (Dk.lam t Dk.l_term (Dk.l_eq (translate_term x2) (Dk.var t))) prf2, (x2, x1), n2 in
    find_transitives (prf :: ps) (xy :: vs) x y n3
  | _, _ -> assert false
    
(* from hs, xs and ys such that for each i, hi is a proof of xi = yi, 
   returns a proof of f(xs) = f(ys) *)
let find_congruent hs f xs ys n =
  let tx = Pr.Fun (f, xs) in
  let dktx = translate_term tx in
  let dkz, n1 = mk_newvar "T" n in
  let refl, _ = find_reflexive tx n1 in               (* tx = tx *)
  let onestep (prf,dkys,dkxxs) h dky =             (* tx = f(ys,x,xs) => tx = f(ys,y,xs) *)
    match dkxxs with
    | dkx :: dkxs ->
      let dktz = Dk.app (Dk.var f) (dkys@[Dk.var dkz]@dkxs) in
      Dk.app3 h (Dk.lam dkz Dk.l_term (Dk.l_eq dktx dktz)) prf, (dkys@[dky]), dkxs 
    | _ -> assert false in
  let prf, _, _ = 
    List.fold_left2 onestep (refl, [], List.map translate_term xs) hs (List.map translate_term ys) in
  prf


(* *** TRANSLATION OF RESOLUTIONS *** *)

exception NotFound

(* for p1s of the form p1h@[p]@p1t and p2s of the form p2h@[q]@p2t
   such that 
   - p is (not q): returns true, q, p1h, p1t, p2h, p2t
   - q is (not p): returns false, p, p1h, p1t, p2h, p2t *)
let find_split p1s p2s =
  let rec xfind_split p1h p1t p2h p2t =
    match p1t, p2t with
    | Pr.Not p :: p1t', p2 :: p2t' when (p = p2) ->
      true, p, p1h, p1t', p2h, p2t'
    | p1 :: p1t', Pr.Not p :: p2t' when (p = p1) ->
      false, p, p1h, p1t', p2h, p2t'
    | p1 :: p1', p2 :: p2t' ->
      xfind_split p1h p1t (p2 :: p2h) p2t'
    | p1 :: p1t', [] ->
      xfind_split (p1 :: p1h) p1t' [] p2s
    | _, _ -> assert false in
  let b, p, p1h, p1t, p2h, p2t = xfind_split [] p1s [] p2s in
  b, p, List.rev p1h, p1t, List.rev p2h, p2t

let rec split l1 l2 l3 l4 l =
  match l1, l2, l3, l4, l with
  | x1 :: l1, l2, l3, l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in x :: r1, r2, r3, r4
  | [], x2 :: l2, l3, l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in r1, x :: r2, r3, r4
  | [], [], x3 :: l3, l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in r1, r2, x :: r3, r4
  | [], [], [], x4 :: l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in r1, r2, r3, x :: r4
  | [], [], [], [], [] -> [], [], [], []
  | _, _, _, _, _ -> assert false

(* from proofs of the hypotheses as functions 
   from negations of propositions to false, 
   returns a function proving the conclusion *)
let rec find_resolution hyps n =
  match hyps with
  | (fun1, p1s) :: (fun2, p2s) :: hyps ->
    let b, p, p1h, p1t, xp2h, xp2t = find_split p1s p2s in
    let cleanlist l = List.filter (fun x -> not (List.mem x (p1h@p1t))) l in
    let p2h, p2t = cleanlist xp2h, cleanlist xp2t in
    let h, newn = mk_newvar "H" n in
    let newfun =
      fun vs ->
	let v1h, v1t, v2h, v2t = split p1h p1t p2h p2t vs in
	let env = List.combine (p1h@p1t) (v1h@v1t) in
	let cplh = List.combine p2h v2h in
	let cplt = List.combine p2t v2t in
	let xv2h = List.map 
	  (fun p -> 
	    let l1 = List.filter (fun (q, x) -> p = q) cplh in
	    let l2 = List.filter (fun (q, x) -> p = q) env in
	    match l1@l2 with (q, x) :: _ -> x | _ -> assert false ) xp2h in
	let xv2t = List.map 
	  (fun p -> 
	    let l1 = List.filter (fun (q, x) -> p = q) cplt in
	    let l2 = List.filter (fun (q, x) -> p = q) env in
	    match l1@l2 with (q, x) :: _ -> x | _ -> assert false ) xp2t in
	match b with
	| true ->
	  fun1 (v1h @ [Dk.lam h (Dk.l_prf (Dk.l_not (translate_prop p))) (
	    fun2 (xv2h @ [Dk.var h] @ xv2t))] @ v1t)
	| false -> 
	  fun2 (xv2h @ [Dk.lam h (Dk.l_prf (Dk.l_not (translate_prop p))) (
	    fun1 (v1h @ [Dk.var h] @ v1t))] @ xv2t) in
    find_resolution ((newfun, p1h@p1t@p2h@p2t) :: hyps) newn
  | [func, _] -> func
  | _ -> assert false
	
(* *** TRANSLATE STEPS *** *)

let translate_rule rule rulehyps concs = 
  let vconcvars, n = mk_newvars "H" concs 1 in
  let concvars = List.map Dk.var vconcvars in
  let useprf prf =
    Dk.lams vconcvars 
	    (List.map (fun p -> Dk.l_prf (Dk.l_not (translate_prop p))) concs) prf in
  match rule, rulehyps, (List.combine concvars concs) with
  | Pr.Input, _, _ -> assert false
  | Pr.Eq_reflexive, [], [cprf, Pr.Eq (x, _)] -> 
     let refl, _ = find_reflexive x n in
     useprf (Dk.app2 cprf refl)
  | Pr.Eq_transitive, [], chyps ->
     let firstlasts l = match List.rev l with x :: xs -> List.rev xs, x | _ -> assert false in
     let hyps, hyp = firstlasts chyps in
     let pxys = 
       List.map 
	 (fun (v, t) -> 
	  match t with 
	  | Pr.Not ( Pr.Eq (x, y) as p) -> 
	     (v, translate_prop p), (x, y) 
	  | _ -> assert false) hyps in
     let cprf, x, y = match hyp with 
	 cprf, Pr.Eq (x,  y) -> cprf, x, y 
       | _ -> assert false in
     let cps, xys = List.split pxys in
     let hs, n1 = mk_newvars "H" cps n in
     let prf, _ = find_transitives (List.map Dk.var hs) xys x y n1 in
     useprf (
	 List.fold_left2
	   (fun prf h (cprf, p) -> Dk.app2 cprf (Dk.lam h (Dk.l_prf p) prf)) 
	   (Dk.app2 cprf prf) hs cps)
  | Pr.Eq_congruent, [], chyps ->
     let (cprf, eq), hyps = 
       match List.rev chyps with 
       | h :: hs -> h, List.rev hs 
       | _ -> assert false in
     let hs, n1 = mk_newvars "H" hyps n in       (* x'j = y'j where forall i exists j, 
                                       (xi = x'j and yi = y'i) or (xi = y'j and yi = x'i)*)
     let f, xs, ys = 
       match eq with
       | Pr.Eq (Pr.Fun (fx, xs), Pr.Fun (fy, ys)) -> 
	  fx, xs, ys
       | _ -> assert false in
     let eqprfs, n2 =                                                (* xi = yi *)
       List.fold_left2 
	 (fun (eqprfs, n) x y -> 
	  let rec findeq hhyps = 
	    match hhyps with
	    | [] -> assert false
	    | (h, (_, Pr.Not (Pr.Eq (a, b)))) :: hhyps -> 
	       if (x = a) && (y = b)
	       then eqprfs@[h], n
	       else if (x = b) && (y = a)
	       then 
		 let eqprf, newn = find_symmetric h a b n in
		 eqprfs@[eqprf], newn
	       else findeq hhyps
	    | _ -> assert false in
	  findeq (List.combine (List.map Dk.var hs) hyps)) ([], n1) xs ys in
     let prf = 
       find_congruent eqprfs f xs ys n2 in
                      (* f(xs) = f(ys) *)
     let applylam prf h (cprf, neq) = 
       match neq with
       | Pr.Not eq -> Dk.app2 cprf (Dk.lam h (Dk.l_prf (translate_prop eq)) prf)
       | _ -> assert false in
     useprf (List.fold_left2 applylam (Dk.app2 cprf prf) hs hyps)
  | Pr.Resolution, rh1 :: rh2 :: rhs, _ -> 
     let hyps = 
       List.map 
	 (fun (prf, ps) -> (fun hs -> Dk.app prf hs), ps) 
		  rulehyps in
     useprf ((find_resolution hyps n) concvars)
  | Pr.Unknown (name), _, _ -> raise Error.Axiom
  | _, _, _ -> raise Error.FoundRuleError

let rec translate_step env input step =
  let name = Smt2d.Translate.tr_string step.Pr.id in
  let premices = 
    List.map (fun hyp -> PrfEnvMap.find hyp env) step.Pr.clauses in
  let preconclusion = mk_clause (List.map translate_prop step.Pr.conclusion) in
  let conclusion = 
    List.fold_left 
      (fun p q -> Dk.l_imply q p) 
      preconclusion 
      (List.rev_map (mk_clause) assertion_bindings) in
  let line = 
    try 
      let proof = translate_rule step.Pr.rule premices step.Pr.conclusion in
      Dk.definition 
	(Dk.var name) (Dk.l_proof conclusion)
	(Dk.lams (input.proof_vars) (List.map Dk.l_proof input.prop_vars) proof) 
    with
    | Error.Axiom ->
      Dk.declaration 
	(Dk.var name) (Dk.l_proof conclusion) in
  let new_env =
    PrfEnvMap.add 
      step.Pr.id 
      (Dk.app (Dk.var name) (List.map Dk.var input.proof_vars), step.Pr.conclusion) env in
  line, new_env
