open Global
open Dkterm

module FreeVarSet = Set.Make (
  struct
    type t = dkterm * dkterm
    let compare = Pervasives.compare
  end)
  
module PrfEnvSet = Map.Make (
  struct 
    type t = dkterm
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
let rec find_split p1s p2s =
  match p1s, p2s with
  | (Dkapp [Dknot; p]) :: p1s, p2 :: p2s when (p = p2) -> true, p, [], p1s, [], p2s
  | p1 :: p1s, (Dkapp [Dknot; p]) :: p2s when (p = p1) -> false, p, [], p1s, [], p2s
  | p1 :: p1s, p2 :: p2s ->
    begin 
      try 
	let b, p, p1h, p1t, p2h, p2t = find_split p1s (p2 :: p2s) in
	b, p, p1 :: p1h, p1t, p2h, p2t
      with
      | NotFound -> 
	let b, p, p1h, p1t, p2h, p2t = find_split (p1 :: p1s) p2s in
	b, p, p1h, p1t, p2 :: p2h, p2t
    end
  | _, _ -> raise NotFound

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
    Debug.eprintdksc "p1s : " p1s "\n";
    Debug.eprintdksc "p2s : " p2s "\n";
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
  | Eq (x, y) -> mk_eq (translate_term x) (translate_term y)
  | Not (p) -> mk_not (translate_prop p)
  | Imply (p, q) -> mk_imply (translate_prop p) (translate_prop q)
  | False -> mk_false
  | Anonpropfun (s, ps) -> mk_app 
    (mk_var (s^(string_of_int (List.length ps)))) (List.map translate_prop ps)

let translate_rule rule rulehyps concs = 
  let concvars, n = mk_newvars "H" concs 1 in
  let useprf prf =
    mk_lams concvars 
      (List.map (fun p -> mk_prf (mk_not p)) concs) prf in
  match rule, rulehyps, (List.combine concvars concs) with
  | Input, _, _ -> assert false
  | Eq_reflexive, [], [cprf, Dkapp [Dkeq; x; _]] -> 
    let refl, _ = find_reflexive x n in
    useprf (mk_app2 cprf refl)
  | Eq_transitive, [], chyps ->
    let firstlasts l = match List.rev l with x :: xs -> List.rev xs, x | _ -> assert false in
    let hyps, hyp = firstlasts chyps in
    let pxys = List.map 
      (fun (v, t) -> match t with 
	Dkapp [Dknot; Dkapp [Dkeq; x; y] as p] -> (v, p), (x, y) | _ -> assert false) hyps in
    let cprf, x, y = match hyp with 
	cprf, Dkapp [Dkeq; x; y] -> cprf, x, y | _ -> assert false in
    let cps, xys = List.split pxys in
    let hs, n1 = mk_newvars "H" cps n in
    let prf, _ = find_transitives hs xys x y n1 in
    useprf (
      List.fold_left2
	(fun prf h (cprf, p) -> mk_app2 cprf (mk_lam h (mk_prf p) prf)) 
	(mk_app2 cprf prf) hs cps)
  | Eq_congruent, [], chyps ->
    let (cprf, eq), hyps = 
      match List.rev chyps with h :: hs -> h, List.rev hs | _ -> assert false in
    let hs, n1 = mk_newvars "H" hyps n in                          (* xi = yi *)
    let f, xs, ys = 
      match eq with
      | Dkapp [Dkeq; Dkapp (fx :: xs); Dkapp (fy :: ys)] -> fx, xs, ys
      | _ -> assert false in
    let prf = find_congruent hs f xs ys n1 in                      (* f(xs) = f(ys) *)
    let applylam prf h (cprf, neq) = 
      match neq with
      | Dkapp [Dknot; eq] -> mk_app2 cprf (mk_lam h (mk_prf eq) prf)
      | _ -> assert false in
    useprf (List.fold_left2 applylam (mk_app2 cprf prf) hs hyps)
  | Resolution, rh1 :: rh2 :: rhs, _ -> 
    let hyps = List.map 
      (fun (prf, ps) -> (fun hs -> mk_app prf hs), ps) rulehyps in
    useprf ((find_resolution hyps n) concvars)
  | Anonrule (name), _, _ -> raise FoundAxiom
  | _, _, _ -> raise FoundRuleError

let rec translate_step dkinput dkinputvar step env =
  match step with
  | Step (name, rule, hyps, concs) -> 
    let rulehyps = List.map 
      (fun hyp -> PrfEnvSet.find (mk_var hyp) env) hyps in
    let dkconcs = List.map translate_prop concs in
    try
      let prf = translate_rule rule rulehyps dkconcs in
      let line =
	mk_deftype (mk_var name)
	  (mk_prf (mk_imply dkinput (mk_clause dkconcs))) 
	  (mk_lam dkinputvar (mk_prf dkinput) prf) in
      let newenv =
	PrfEnvSet.add (mk_var name)
	  (mk_app2 (mk_var name) dkinputvar, dkconcs) env in 
      line, newenv
    with
    | FoundAxiom -> 
      let line = mk_decl (mk_var name) (mk_prf (mk_imply dkinput (mk_clause dkconcs))) in
      let newenv = 
	PrfEnvSet.add (mk_var name)
	  (mk_app2 (mk_var name) dkinputvar, dkconcs) env in
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
  | Eq (t1, t2) -> 
    get_vars_term (get_vars_term varenv t1) t2
  | Not (p) -> get_vars_prop varenv p
  (* | And (p, q) -> get_vars_prop (get_vars_prop varenv p) q *)
  | Imply (p, q) -> get_vars_prop (get_vars_prop varenv p) q
  | False -> varenv
  | Anonpropfun (s, ps) -> 
    let newenv, typ =
      List.fold_left
	(fun (env, typ) p ->
	  get_vars_prop env p, mk_arrow mk_proptype typ)
	(varenv, mk_proptype) ps in
    FreeVarSet.add (mk_var (s^(string_of_int (List.length ps))), typ) newenv

let get_vars varenv step = 
  match step with
  | Step (_, _, _, concs) -> 
    List.fold_left get_vars_prop varenv concs

(* *** TRANSLATE INPUT *** *)

let translate_input input =
  match input with 
  | Step (name, Input, [], concs) -> 
    let dkconcs = List.map translate_prop concs in
    mk_var name, mk_clause dkconcs, 
    PrfEnvSet.add (mk_var name) 
      (mk_var name, dkconcs) PrfEnvSet.empty
  | _ -> raise FoundRuleError

let print_prelude out input filename = 
  p_line out (mk_prelude filename);
  let env = get_vars FreeVarSet.empty input in
  FreeVarSet.iter
    (fun (var, typ) -> p_line out (mk_decl var typ)) env
