module Dk = Smt2d.Dedukti
module Abs = Smt2d.Abstract
module Tr = Smt2d.Translate

exception Translate_error
exception Axiom

type smt2_env =
    { signature: Smt2d.Signature.signature;
      input_terms: Smt2d.Abstract.term list;
      input_term_vars: Smt2d.Dedukti.term list;
      input_proof_idents: Smt2d.Dedukti.ident list; }

module PrfEnvMap = Map.Make (
  struct
    type t = string
    let compare = Pervasives.compare
  end)

type proof_env = (Smt2d.Dedukti.term * Smt2d.Abstract.term list) PrfEnvMap.t

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

(* *** TRANSLATION OF EQUALITIES *** *)

(* returns a proof of x = x with x : s *)
let find_reflexive s x n =
  let p, n1 = mk_newvar "P" n in
  let h, newn = mk_newvar "H" n1 in
  Dk.lam p (Dk.arrow (Dk.l_term s) (Dk.l_term Dk.l_bool))
    (Dk.lam h (Dk.l_proof (Dk.app2 (Dk.var p) x)) (Dk.var h)), newn

(* from h a proof of x = y, and x : s, returns a proof of y = x *)
let find_symmetric h s x n =
  let refl, n1 = find_reflexive s x n in
  let t, newn = mk_newvar "T" n1 in
  Dk.app3 h (Dk.lam t (Dk.l_term s) (Dk.l_equal s (Dk.var t) x)) refl, newn

(* from:
   - xi, yi such that x1 = y1, x2 = y2, x3 = y3 are of the form 
     x = y, y = z, x = z up to equality symmetries,
   - x : s
   - prf1 a proof of x1 = y1, prf2 a proof of x2 = y2
   returns a proof of x3 = y3 *)
let rec find_transitive prf1 prf2 s x1 y1 x2 y2 x3 y3 n =
  let t, n1 = mk_newvar "T" n in
  match y3 = y2, y3 = y1, x2 = x1 with
  | true, _, true ->             (* case y = x, y = z, x = z *)
    Dk.app3 prf1 (Dk.lam t (Dk.l_term s) (Dk.l_equal s (Dk.var t) y3)) prf2, n1
  | true, _, false ->            (* case x = y, y = z, x = z *)
    Dk.app3 prf2 (Dk.lam t (Dk.l_term s) (Dk.l_equal s x3 (Dk.var t))) prf1, n1
  | false, true, true ->         (* case y = x, y = z, z = x *)
    Dk.app3 prf2 (Dk.lam t (Dk.l_term s) (Dk.l_equal s (Dk.var t) y3)) prf1, n1
  | false, true, false ->        (* case y = x, z = y, z = x *)
    Dk.app3 prf1 (Dk.lam t (Dk.l_term s) (Dk.l_equal s x3 (Dk.var t))) prf2, n1
  | false, false, _ ->
    match y3 = x1 with
    | true ->                    (* case x = y, _ = _, z = x: use a proof of y = x *)
      let sym, n2 = find_symmetric prf1 s x1 n1 in
      find_transitive sym prf2 s y1 x1 x2 y2 x3 y3 n2
    | false ->                   (* case _ = _, z = y, x = z: use a proof of y = z *)
      let sym, n2 = find_symmetric prf2 s x2 n1 in
      find_transitive prf1 sym s x1 y1 y2 x2 x3 y3 n2

let rec find_transitives prfs s xys x y n =
  match prfs, xys with
  | [prf1; prf2], [(x1, y1); (x2, y2)] ->
    find_transitive prf1 prf2 s x1 y1 x2 y2 x y n
  | (prf1 :: prf2 :: ps), ((x1, y1) :: (x2, y2) :: vs) ->
    let t, n1 = mk_newvar "T" n in
    let prf, xy, n3 =
      match x1 = x2, x1 = y2, y1 = x2 with
      | true, _, _ ->                (* case y = x, y = z *)
  	Dk.app3 prf1
  		(Dk.lam t (Dk.l_term s) (Dk.l_equal s (Dk.var t) y2)) prf2, (y1, y2), n1
      | false, true, _ ->            (* case y = x, z = y *)
  	Dk.app3 prf1
  		(Dk.lam t (Dk.l_term s) (Dk.l_equal s x2 (Dk.var t))) prf2, (x2, y1), n1
      | false, false, true ->        (* case x = y, y = z *)
  	Dk.app3 prf2
  		(Dk.lam t (Dk.l_term s) (Dk.l_equal s x1 (Dk.var t))) prf1, (x1, y2), n1
      | false, false, false ->       (* case x = y, z = y: use a proof of y = x *)
  	let sym, n2 = find_symmetric prf1 s x1 n1 in
  	Dk.app3
  	  sym (Dk.lam t (Dk.l_term s) (Dk.l_equal s x2 (Dk.var t))) prf2, (x2, x1), n2 in
    find_transitives (prf :: ps) s (xy :: vs) x y n3
  | _, _ -> raise Translate_error
    
(* from hs, xs and ys such that for each i, hi is a proof of xi = yi, xi : s 
   returns a proof of f(xs) = f(ys) *)
let find_congruent hs s f xs ys n =
  let tx = Dk.app f xs in
  let dkz, n1 = mk_newvar "T" n in
  let refl, _ = 
    find_reflexive s tx n1 in                      (* tx = tx *)
  let onestep (prf,dkys,dkxxs) h dky =             (* tx = f(ys,x,xs) => tx = f(ys,y,xs) *)
    match dkxxs with
    | _ :: dkxs ->
      let dktz = Dk.app f (dkys@[Dk.var dkz]@dkxs) in
      Dk.app3 h (Dk.lam dkz (Dk.l_term s) (Dk.l_equal s tx dktz)) prf, (dkys@[dky]), dkxs
    | _ -> raise Translate_error in
  let prf, _, _ =
    List.fold_left2 onestep (refl, [], xs) hs ys in
  prf

(* *** TRANSLATION OF RESOLUTIONS *** *)

(* for p1s of the form p1h@[p]@p1t and p2s of the form p2h@[q]@p2t
   such that 
   - p is (not q): returns true, q, p1h, p1t, p2h, p2t
   - q is (not p): returns false, p, p1h, p1t, p2h, p2t *)
let find_split p1s p2s =
  let rec xfind_split p1h p1t p2h p2t =
    match p1t, p2t with
    | p1 :: p1t', p2 :: p2t' ->
       begin 
	 match View.mk_view p1, View.mk_view p2 with 
	 | View.Not p, _ when (View.equal p p2) ->
	    true, p, p1h, p1t', p2h, p2t'
	 | _, View.Not p when (View.equal p p1) ->
	    false, p, p1h, p1t', p2h, p2t'
	 | View.App _, _ | View.True, _ | View.False, _ | View.Not _, _
	 | View.Imply _, _ | View.And _, _ | View.Or _, _ | View.Xor _, _
	 | View.Equal _, _ | View.Distinct _, _ | View.Ite _, _ -> 
	    xfind_split p1h p1t (p2 :: p2h) p2t'
       end
    | p1 :: p1t', [] ->
       xfind_split (p1 :: p1h) p1t' [] p2s
    | _, _ -> raise Translate_error in
  let b, p, p1h, p1t, p2h, p2t = xfind_split [] p1s [] p2s in
  b, p, List.rev p1h, p1t, List.rev p2h, p2t

let rec split l1 l2 l3 l4 l =
  match l1, l2, l3, l4, l with
  | _ :: l1, l2, l3, l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in x :: r1, r2, r3, r4
  | [], _ :: l2, l3, l4, x :: l ->
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in r1, x :: r2, r3, r4
  | [], [], _ :: l3, l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in r1, r2, x :: r3, r4
  | [], [], [], _ :: l4, x :: l -> 
    let r1, r2, r3, r4 = split l1 l2 l3 l4 l in r1, r2, r3, x :: r4
  | [], [], [], [], [] -> [], [], [], []
  | _, _, _, _, _ -> raise Translate_error

(* from proofs of the hypotheses as functions 
   from negations of propositions to false, 
   returns a function proving the conclusion *)
let rec find_resolution signature hyps n =
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
  	    let l1 = List.filter (fun (q, _) -> p = q) cplh in
  	    let l2 = List.filter (fun (q, _) -> p = q) env in
  	    match l1@l2 with (_, x) :: _ -> x | _ -> raise Translate_error ) xp2h in
  	let xv2t = List.map
  	  (fun p ->
  	    let l1 = List.filter (fun (q, _) -> p = q) cplt in
  	    let l2 = List.filter (fun (q, _) -> p = q) env in
  	    match l1@l2 with (_, x) :: _ -> x | _ -> raise Translate_error ) xp2t in
  	match b with
  	| true ->
  	  fun1 (v1h @ [Dk.lam h (Dk.l_proof (Dk.l_not (Tr.tr_term signature p))) (
  	    fun2 (xv2h @ [Dk.var h] @ xv2t))] @ v1t)
  	| false ->
  	  fun2 (xv2h @ [Dk.lam h (Dk.l_proof (Dk.l_not (Tr.tr_term signature p))) (
  	    fun1 (v1h @ [Dk.var h] @ v1t))] @ xv2t) in
    find_resolution signature ((newfun, p1h@p1t@p2h@p2t) :: hyps) newn
  | [func, _] -> func
  | _ -> raise Translate_error

(* *** TRANSLATE STEPS *** *)

let translate_rule smt2_env rule rulehyps concs = 
  let vconcvars, n = mk_newvars "H" concs 1 in
  let concvars = List.map Dk.var vconcvars in
  let useprf prf =
    Dk.lams 
      vconcvars
      (List.map (fun p -> Dk.l_proof (Dk.l_not (Tr.tr_term smt2_env.signature p))) concs) prf in
  match rule with
  | Proof.Input -> raise Axiom
  | Proof.Eq_reflexive ->
     begin 
       match List.combine concvars concs with
       | [cprf, eq] -> 
	  let x, _ = View.match_equal eq in
	  let refl, _ = 
	    find_reflexive 
	      (Tr.tr_sort (Smt2d.Get_sort.get_sort smt2_env.signature x))
	      (Tr.tr_term smt2_env.signature x) n in
	  useprf (Dk.app2 cprf refl)
       | _ -> raise Translate_error end
  | Proof.Eq_transitive ->
     let hyps, hyp = 
       Smt2d.Util.separate_last (List.combine concvars concs) in
     let dkpxys =
       List.map
  	 (fun (v, t) ->
	  let p = View.match_not t in
	  let x, y = View.match_equal p in
  	  (v, Tr.tr_term smt2_env.signature p), 
	  (Tr.tr_term smt2_env.signature x, 
	   Tr.tr_term smt2_env.signature y)) hyps in
     let cprf, eq = hyp in 
     let x, y = View.match_equal eq in
     let cps, dkxys = List.split dkpxys in
     let hs, n1 = mk_newvars "H" cps n in
     let prf, _ = 
       find_transitives 
	 (List.map Dk.var hs) 
	 (Tr.tr_sort (Smt2d.Get_sort.get_sort smt2_env.signature x))
	 dkxys (Tr.tr_term smt2_env.signature x) 
	 (Tr.tr_term smt2_env.signature y) n1 in
     useprf (
  	 List.fold_left2
  	   (fun prf h (cprf, p) -> Dk.app2 cprf (Dk.lam h (Dk.l_proof p) prf))
  	   (Dk.app2 cprf prf) hs cps)
  | Proof.Eq_congruent ->
     let (cprf, eq), hyps =
       match List.rev (List.combine concvars concs) with
       | h :: hs -> h, List.rev hs
       | _ -> raise Translate_error in
     let hs, n1 = mk_newvars "H" hyps n in       (* x'j = y'j where forall i exists j,
                                       (xi = x'j and yi = y'i) or (xi = y'j and yi = x'i)*)
     let t, u = View.match_equal eq in
     let f, xs = View.match_app t in
     let _, ys = View.match_app u in
     let s = Tr.tr_sort (Smt2d.Get_sort.get_sort smt2_env.signature t) in
     let eqprfs, n2 =                                                (* xi = yi *)
       List.fold_left2
	 (fun (eqprfs, n) x y ->
  	  let rec findeq hhyps =
  	    match hhyps with
  	    | [] -> raise Translate_error
	    | (h, (_, t)) :: hhyps ->
	       let p = View.match_not t in
	       let a, b = View.match_equal p in
  	       if (View.equal x a) && (View.equal y b)
  	       then eqprfs@[h], n
  	       else if (View.equal x b) && (View.equal y a)
  	       then
  	    	 let eqprf, newn =
	    	   find_symmetric
	    	     h (Tr.tr_sort (Smt2d.Get_sort.get_sort smt2_env.signature a))
	    	     (Tr.tr_term smt2_env.signature a) n in
  	    	 eqprfs@[eqprf], newn
  	       else findeq hhyps in
  	  findeq (List.combine (List.map Dk.var hs) hyps)) ([], n1) xs ys in
     let prf =
       find_congruent 
	 eqprfs s (Tr.tr_fun_symbol f) 
	 (List.map (Tr.tr_term smt2_env.signature) xs) 
	 (List.map (Tr.tr_term smt2_env.signature) ys) n2 in (* f(xs) = f(ys) *)
     let applylam prf h (cprf, neq) =
       let eq = View.match_not neq in
       Dk.app2 
	 cprf 
	 (Dk.lam h (Dk.l_proof (Tr.tr_term smt2_env.signature eq)) prf) in
     useprf (List.fold_left2 applylam (Dk.app2 cprf prf) hs hyps)
  | Proof.Resolution ->
     let hyps =
       List.map
  	 (fun (prf, ps) -> (fun hs -> Dk.app prf hs), ps)
  		  rulehyps in
     useprf ((find_resolution smt2_env.signature hyps n) concvars)
  | Proof.Unknown_rule _ -> raise Axiom

(* preuve de I1 => .. => In => mk_clause conclusion *)
let translate_step smt2_env proof_env step =
  let name = Tr.tr_string step.Proof.id in
  let premices =
    List.map (fun hyp -> PrfEnvMap.find hyp proof_env) step.Proof.clauses in
  let preconclusion = 
    mk_clause (List.map (Tr.tr_term smt2_env.signature) step.Proof.conclusion) in
  let conclusion = 
    List.fold_left 
      (fun p q -> Dk.l_imply q p)
      preconclusion (List.rev smt2_env.input_term_vars) in
  let line = 
    try
      let proof = translate_rule smt2_env step.Proof.rule premices step.Proof.conclusion in
      Dk.definition
	(Dk.var name) (Dk.l_proof conclusion)
	(Dk.lams (smt2_env.input_proof_idents) (List.map Dk.l_proof smt2_env.input_term_vars) proof)
    with
    | Axiom ->
      Dk.declaration
	(Dk.var name) (Dk.l_proof conclusion) in
  let new_proof_env =
    PrfEnvMap.add
      step.Proof.id
      (Dk.app 
	 (Dk.var name) 
	 (List.map Dk.var smt2_env.input_proof_idents), step.Proof.conclusion) proof_env in
  line, new_proof_env
