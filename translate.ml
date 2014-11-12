open Proof
open Dedukti

module FreeVarSet = Set.Make (
  struct
    type t = dkterm * dkterm
    let compare = Pervasives.compare
  end)
  
module PrfEnvMap = Map.Make (
  struct 
    type t = string
    let compare = Pervasives.compare
  end)

let mk_newvar s n = 
  mk_var (s^(string_of_int n)), n+1

let mk_newvars s l n =
  let vars, newn = 
    List.fold_left (fun (vs,m) _ -> 
      let v, newm = mk_newvar s m in
      (v :: vs), newm) ([],n) l in
  List.rev vars, newn

let rec mk_clause props = 
  match props with
  | p :: ps -> mk_imply (mk_not p) (mk_clause ps)
  | [] -> mk_false

(* *** TRANSLATION OF EQUALITIES *** *)

(* returns a proof of x = x *)
let find_reflexive x n =
  let p, n1 = mk_newvar "P" n in  
  let h, newn = mk_newvar "H" n1 in 
  mk_lam p (mk_arrow mk_termtype mk_proptype)
    (mk_lam h (mk_prf (mk_app2 p x)) h), newn

(* from h a proof of x = y, returns a proof of y = x *)
let find_symmetric h x y n =
  let refl, n1 = find_reflexive x n in
  let t, newn = mk_newvar "T" n1 in
  mk_app3 h (mk_lam t mk_termtype (mk_eq t x)) refl, newn

(* from:
   - xi, yi such that x1 = y1, x2 = y2, x3 = y3 are of the form 
     x = y, y = z, x = z up to equality symmetries,
   - prf1 a proof of x1 = y1, prf2 a proof of x2 = y2
   returns a proof of x3 = y3 *)
let rec find_transitive prf1 prf2 x1 y1 x2 y2 x3 y3 n =
  let t, n1 = mk_newvar "T" n in
  match y3 = y2, y3 = y1, x2 = x1 with
  | true, _, true ->             (* case y = x, y = z, x = z *)
    mk_app3 prf1 (mk_lam t mk_termtype (mk_eq t y3)) prf2, n1
  | true, _, false ->            (* case x = y, y = z, x = z *)
    mk_app3 prf2 (mk_lam t mk_termtype (mk_eq x3 t)) prf1, n1
  | false, true, true ->         (* case y = x, y = z, z = x *)
    mk_app3 prf2 (mk_lam t mk_termtype (mk_eq t y3)) prf1, n1
  | false, true, false ->        (* case y = x, z = y, z = x *)
    mk_app3 prf1 (mk_lam t mk_termtype (mk_eq x3 t)) prf2, n1
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
	mk_app3 prf1 (mk_lam t mk_termtype (mk_eq t y2)) prf2, (y1, y2), n1
      | false, true, _ ->            (* case y = x, z = y *)
	mk_app3 prf1 (mk_lam t mk_termtype (mk_eq x2 t)) prf2, (x2, y1), n1
      | false, false, true ->        (* case x = y, y = z *)
	mk_app3 prf2 (mk_lam t mk_termtype (mk_eq x1 t)) prf1, (x1, y2), n1
      | false, false, false ->       (* case x = y, z = y: use a proof of y = x *)
	let sym, n2 = find_symmetric prf1 x1 y1 n1 in
	mk_app3 sym (mk_lam t mk_termtype (mk_eq x2 t)) prf2, (x2, x1), n2 in
    find_transitives (prf :: ps) (xy :: vs) x y n3
  | _, _ -> assert false
    
(* from hs, xs and ys such that for each i, hi is a proof of xi = yi, 
   returns a proof of f(xs) = f(ys) *)
let find_congruent hs f xs ys n =
  let tx = mk_app f xs in
  let z, n1 = mk_newvar "T" n in
  let refl, _ = find_reflexive tx n1 in      (* tx = tx *)
  let onestep (prf,ys,xxs) h y =             (* tx = f(ys,x,xs) => tx = f(ys,y,xs) *)
    match xxs with
    | x :: xs ->
      let tz = mk_app f (ys@[z]@xs) in
      mk_app3 h	(mk_lam z mk_termtype (mk_eq tx tz)) prf, (ys@[y]), xs 
    | _ -> assert false in
  let prf, _, _ = List.fold_left2 onestep (refl,[],xs) hs ys in
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
    | (Dkapp [Dknot; p]) :: p1t', p2 :: p2t' when (p = p2) ->
      true, p, p1h, p1t', p2h, p2t'
    | p1 :: p1t', (Dkapp [Dknot; p]) :: p2t' when (p = p1) ->
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
	  fun1 (v1h @ [mk_lam h (mk_prf (mk_not p)) (
	    fun2 (xv2h @ [h] @ xv2t))] @ v1t)
	| false -> 
	  fun2 (xv2h @ [mk_lam h (mk_prf (mk_not p)) (
	    fun1 (v1h @ [h] @ v1t))] @ xv2t) in
    find_resolution ((newfun, p1h@p1t@p2h@p2t) :: hyps) newn
  | [func, _] -> func
  | _ -> assert false
	
(* *** TRANSLATE STEPS *** *)
	
let rec translate_term term =
  match term with
  | Var (s) -> mk_var s
  | Fun (s, ts) -> mk_app (mk_var s) (List.map translate_term ts)

let rec translate_prop prop =
  match prop with
  | True -> mk_true
  | False -> mk_false
  | Not (p) -> mk_not (translate_prop p)
  | Imply (p, q) -> mk_imply (translate_prop p) (translate_prop q)
  | And (p, q) -> mk_and (translate_prop p) (translate_prop q)
  | Or (p, q) -> mk_or (translate_prop p) (translate_prop q)
  | Xor (p, q) -> assert false
  | Eq (x, y) -> mk_eq (translate_term x) (translate_term y)
  | Distinct (x, y) -> mk_not (mk_eq (translate_term x) (translate_term y))
  | Ite (p, x, y) -> assert false
  | Pred (s, ts) -> mk_app 
    (mk_var (s^(string_of_int (List.length ts)))) (List.map translate_term ts)

let translate_rule rule rulehyps concs = 
  let concvars, n = mk_newvars "H" concs 1 in
  let useprf prf =
    mk_lams concvars 
	    (List.map (fun p -> mk_prf (mk_not (translate_prop p))) concs) prf in
  match rule, rulehyps, (List.combine concvars concs) with
  | Trace.Input, _, _ -> assert false
  | Trace.Eq_reflexive, [], [cprf, Eq (x, _)] -> 
     let refl, _ = find_reflexive (translate_term x) n in
     useprf (mk_app2 cprf refl)
  | Trace.Eq_transitive, [], chyps ->
     let firstlasts l = match List.rev l with x :: xs -> List.rev xs, x | _ -> assert false in
     let hyps, hyp = firstlasts chyps in
     let pxys = 
       List.map 
	 (fun (v, t) -> 
	  match t with 
	  | Not ( Eq (x, y) as p) -> 
	     (v, translate_prop p), (translate_term x, translate_term y) 
	  | _ -> assert false) hyps in
     let cprf, x, y = match hyp with 
	 cprf, Eq (x,  y) -> cprf, translate_term x, translate_term y 
       | _ -> assert false in
     let cps, xys = List.split pxys in
     let hs, n1 = mk_newvars "H" cps n in
     let prf, _ = find_transitives hs xys x y n1 in
     useprf (
	 List.fold_left2
	   (fun prf h (cprf, p) -> mk_app2 cprf (mk_lam h (mk_prf p) prf)) 
	   (mk_app2 cprf prf) hs cps)
  | Trace.Eq_congruent, [], chyps ->
     let (cprf, eq), hyps = 
       match List.rev chyps with 
       | h :: hs -> h, List.rev hs 
       | _ -> assert false in
     (* Debug.eprintdksc "concs" concs "\n"; *)
     let hs, n1 = mk_newvars "H" hyps n in       (* x'j = y'j where forall i exists j, 
                                       (xi = x'j and yi = y'i) or (xi = y'j and yi = x'i)*)
     let f, xs, ys = 
       match eq with
       | Eq (Fun (fx, xs), Fun (fy, ys)) -> 
	  mk_var fx, xs, ys
       | _ -> assert false in
     let eqprfs, n2 =                                                (* xi = yi *)
       List.fold_left2 
	 (fun (eqprfs, n) x y -> 
	  let rec findeq hhyps = 
	    match hhyps with
	    | [] -> assert false
	    | (h, (_, Not (Eq (a, b)))) :: hhyps -> 
	       if (x = a) && (y = b)
	       then eqprfs@[h], n
	       else if (x = b) && (y = a)
	       then 
		 let eqprf, newn = find_symmetric h (translate_term a) (translate_term b) n in
		 eqprfs@[eqprf], newn
	       else findeq hhyps
	    | _ -> assert false in
	  findeq (List.combine hs hyps)) ([], n1) xs ys in
     let prf = 
       find_congruent eqprfs f (List.map translate_term xs) (List.map translate_term ys) n2 in
                      (* f(xs) = f(ys) *)
     let applylam prf h (cprf, neq) = 
       match neq with
       | Not eq -> mk_app2 cprf (mk_lam h (mk_prf (translate_prop eq)) prf)
       | _ -> assert false in
     useprf (List.fold_left2 applylam (mk_app2 cprf prf) hs hyps)
  | Trace.Resolution, rh1 :: rh2 :: rhs, _ -> 
     let hyps = List.map 
		  (fun (prf, ps) -> (fun hs -> mk_app prf hs), 
				    List.map translate_prop ps) 
		  rulehyps in
     useprf ((find_resolution hyps n) concvars)
  | Trace.Anonrule (name), _, _ -> raise Global.FoundAxiom
  | _, _, _ -> raise Global.FoundRuleError

let rec translate_step dkinputvars dkinputconcvars step env =
  match step with
  | Step (name, rule, hyps, concs) -> 
    let rulehyps = List.map 
      (fun hyp -> 
       PrfEnvMap.find hyp env) hyps in
    let dkconcs = List.map translate_prop concs in
    try
      let prf = translate_rule rule rulehyps concs in
      let proved = 
	List.fold_left 
	  (fun q p -> mk_imply p q) (mk_clause dkconcs)
	  (List.rev dkinputconcvars) in
      let line =
	mk_deftype (mk_var name) (mk_prf proved) 
	  (mk_lams dkinputvars (List.map mk_prf dkinputconcvars) prf) in
      let newenv =
	PrfEnvMap.add name
	  (mk_app (mk_var name) dkinputvars, concs) env in 
      line, newenv
    with
    | Global.FoundAxiom -> 
      let proved = 
	List.fold_left 
	  (fun q p -> mk_imply p q) (mk_clause dkconcs)
	  (List.rev dkinputconcvars) in
      let line = mk_decl (mk_var name) (mk_prf proved) in
      let newenv = 
	PrfEnvMap.add name
	  (mk_app (mk_var name) dkinputvars, concs) env in
      line, newenv

let print_step out line =
  p_line out line

(* *** FIND FREE VARIABLES *** *)

let rec get_vars_term varenv term =
  match term with
  | Var (s) -> 
    FreeVarSet.add (mk_var s, mk_termtype) varenv
  | Fun (s, ts) -> 
    let newenv, typ = 
      List.fold_left 
	(fun (env, typ) t -> 
	  get_vars_term env t, mk_arrow mk_termtype typ)
	(varenv, mk_termtype) ts in
    FreeVarSet.add (mk_var s, typ) newenv

let rec get_vars_prop varenv prop =
  match prop with
  | True -> varenv
  | False -> varenv
  | Not (p) -> get_vars_prop varenv p
  | Imply (p, q) -> get_vars_prop (get_vars_prop varenv p) q
  | And (p, q) -> get_vars_prop (get_vars_prop varenv p) q
  | Or (p, q) -> get_vars_prop (get_vars_prop varenv p) q
  | Xor (p, q) -> get_vars_prop (get_vars_prop varenv p) q
  | Eq (t1, t2) -> get_vars_term (get_vars_term varenv t1) t2
  | Distinct (t1, t2) -> get_vars_term (get_vars_term varenv t1) t2
  | Ite (p, t1, t2) -> assert false
  | Pred (s, ts) -> 
    let newenv, typ =
      List.fold_left
	(fun (env, typ) t ->
	  get_vars_term env t, mk_arrow mk_termtype typ)
	(varenv, mk_proptype) ts in
    FreeVarSet.add 
      (mk_var (s^(string_of_int (List.length ts))), typ) newenv

let get_vars varenv step = 
  match step with
  | Step (_, _, _, concs) -> 
    List.fold_left get_vars_prop varenv concs

(* *** TRANSLATE INPUT *** *)

let translate_input input env =
  match input with 
  | Step (name, Input, [], concs) -> 
    mk_var name, mk_var ("P"^name), 
    PrfEnvMap.add name (mk_var name, concs) env
  | _ -> raise Global.FoundRuleError

let print_prelude out env inputs dkinputconcvars = 
  let freevars = 
    PrfEnvMap.fold 
      (fun _ (_, concs) freevars -> 
       List.fold_left get_vars_prop freevars concs) 
      env FreeVarSet.empty in
  FreeVarSet.iter
    (fun (var, typ) -> p_line out (mk_decl var typ)) freevars;
  List.iter2
    (fun input dkinputconcvar ->
     match input with 
     | Step (_, _, _, concs) -> 
	let dkconcs = List.map translate_prop concs in
	let dkinput = mk_clause dkconcs in
     p_line out (mk_deftype dkinputconcvar mk_proptype dkinput))
    inputs dkinputconcvars
