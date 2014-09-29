open Global
open Dkterm

module FreeVarSet = Set.Make (
  struct
    type t = dkterm
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

(* special functions for equalities *)

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

(* if x1 = y1, x2 = y2, x3 = y3 if of the form 
   x = y, y = z, x = z up to equality symmetries, 
   returns a proof of x3 = y3 from a proof h1 of x1 = y1 and a proof h2 of x2 = y2 *)
let rec find_transitive h1 h2 x1 y1 x2 y2 x3 y3 n =
  let t, n1 = mk_newvar "T" n in
  match y3 = y2, y3 = y1, x2 = x1 with
  | true, _, true ->             (* case y = x, y = z, x = z *)
    mk_app3 h1 (mk_lam t mk_termtype (mk_eq t y3)) h2, n1
  | true, _, false ->            (* case x = y, y = z, x = z *)
    mk_app3 h2 (mk_lam t mk_termtype (mk_eq x3 t)) h1, n1
  | false, true, true ->         (* case y = x, y = z, z = x *)
    mk_app3 h2 (mk_lam t mk_termtype (mk_eq t y3)) h1, n1
  | false, true, false ->        (* case y = x, z = y, z = x *)
    mk_app3 h1 (mk_lam t mk_termtype (mk_eq x3 t)) h2, n1
  | false, false, _ -> 
    match y3 = x1 with
    | true ->                    (* case x = y, _ = _, z = x: use a proof of y = x *)
      let sym, n3 = find_symmetric h1 x1 y1 n1 in
      find_transitive sym h2 y1 x1 x2 y2 x3 y3 n3
    | false ->                   (* case _ = _, z = y, x = z: use a proof of y = z *)
      let sym, n3 = find_symmetric h2 x2 y2 n1 in
      find_transitive h1 sym x1 y1 y2 x2 x3 y3 n3

(* special functions for resolution *)

exception NotFound

(* for p1s of the form p1h@[p]@p1t and p2s of the form p2h@[q]@p2t, 
   - if p is (not q), returns true, q, p1h, p1t, p2h, p2t
   - if q is (not p), returns false, p, p1h, p1t, p2h, p2t *)
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

(* returns a proof of resolution and its inferred conclusion *)
let rec find_resolution (prf1, p1s) (prf2, p2s) cs n =
  match cs with
  | c :: cs -> 
    let prf, concs, newn = find_resolution (prf1, p1s) (prf2, p2s) [] n in
    find_resolution (prf, concs) c cs newn
  | [] ->
    let b, p, p1h, p1t, p2h, p2t = find_split p1s p2s in
    let v1h, n1 = mk_newvars "H" p1h n in
    let v1t, n2 = mk_newvars "H" p1t n1 in
    let v2h, n3 = mk_newvars "H" p2h n2 in
    let v2t, n4 = mk_newvars "H" p2t n3 in
    let prf, newn = match b, v1t, v2t with
      | true, _, [] -> mk_app prf1 (v1h @ [mk_app prf2 v2h] @ v1t), n4
      | true, _, _ -> 
	let h, newn = mk_newvar "H" n4 in
	mk_app prf1 (v1h @ [
	  mk_lam h (mk_prf (mk_not p)) (mk_app prf2 (v2h @ [h] @ v2t))] @ v1t), newn
      | false, [], _ -> mk_app prf2 (v2h @ [mk_app prf1 v1h] @ v2t), n4
      | false, _, _ -> 
	let h, newn = mk_newvar "H" n4 in
	mk_app prf2 (v2h @ [
	  mk_lam h (mk_prf (mk_not p)) (mk_app prf1 (v1h @ [h] @ v1t))] @ v2t), newn in
    let concs = p1h@p1t@p2h@p2t in
    let prfvars = List.map (fun p -> mk_prf (mk_not p)) concs in
    mk_lams (v1h@v1t@v2h@v2t) prfvars prf, concs, newn

(* main translation functions *)

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

let translate_rule rule rulehyps concs = 
  let prfvars = List.map (fun p -> mk_prf (mk_not p)) concs in
  let concvars, n = mk_newvars "H" concs 1 in
  let useprf prf = mk_lams concvars prfvars prf in
  match rule, rulehyps, (List.combine concvars concs) with
  | Input, _, _ -> assert false
  | Eq_reflexive, [], [cprf, Dkapp [Dkeq; x; _]] -> 
    let refl, newn = find_reflexive x n in
    useprf (
      mk_app2 cprf refl)
  | Eq_transitive, [],
    [cprf1, Dkapp [Dknot; Dkapp [Dkeq; x1; y1] as p1]; 
     cprf2, Dkapp [Dknot; Dkapp [Dkeq; x2; y2] as p2]; 
     cprf3, Dkapp [Dkeq; x3; y3]] ->
    let h1, n1 = mk_newvar "H" n in                                 (* x1 = y1 *)
    let h2, n2 = mk_newvar "H" n1 in                                (* x2 = y2 *)
    let prf, newn = find_transitive h1 h2 x1 y1 x2 y2 x3 y3 n2 in   (* x3 = y3 *)
    useprf (
      mk_app2 cprf1 (mk_lam h1 (mk_prf p1) (
	mk_app2 cprf2 (mk_lam h2 (mk_prf p2) (
	  mk_app2 cprf3 prf)))))
  | Resolution, (prf1, p1s) :: (prf2, p2s) :: cs, _ ->
    let prf, _, _ = find_resolution (prf1, p1s) (prf2, p2s) cs 1 in
    prf
  | Rand, [prf, [(Dkapp [Dkand; p; q]) as dkprop]], [cprf, conc] -> 
    let h1, n1 = mk_newvar "H" n in 
    let h2, n2 = mk_newvar "H" n1 in 
    let h3, _ = mk_newvar "H" n2 in 
    if (p = conc)
    then
      useprf (
	mk_app2 prf (mk_lam h1 (mk_prf dkprop) (
	  mk_app2 cprf (mk_app3 h1 p (mk_lam h2 (mk_prf p) (mk_lam h3 (mk_prf q) h2))))))
    else if (q = conc)
    then
      useprf (
	mk_app2 prf (mk_lam h1 (mk_prf dkprop) (
	  mk_app2 cprf (mk_app3 h1 q (mk_lam h2 (mk_prf p) (mk_lam h3 (mk_prf q) h3))))))
    else assert false
  | Anonrule (name), _, _ -> assert false
  | _, _, _ -> raise FoundRuleError

let rec translate_step dkinputvar dkinput step env =
  match step with
  | Step (name, rule, prems, concs) -> 
    let rulehyps = List.map 
      (fun prem -> PrfEnvSet.find (mk_var prem) env) prems in
    let dkconcs = List.map translate_prop concs in
    let prf = translate_rule rule rulehyps dkconcs in
    let line = 
      mk_deftype (mk_var name)
	(mk_prf (mk_imply dkinput (mk_clause dkconcs))) 
	(mk_lam dkinputvar (mk_prf dkinput) prf) in
    let newenv =
      PrfEnvSet.add (mk_var name)
	(mk_app2 (mk_var name) dkinputvar, dkconcs) env in 
    line, newenv

let print_step out line =
  p_line out line

(* get_vars *)

let get_vars_term env term =
  match term with
  | Var (s) -> FreeVarSet.add (mk_var s) env

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
    mk_var name, mk_clause dkconcs, 
    PrfEnvSet.add (mk_var name) (mk_var name, dkconcs) PrfEnvSet.empty
  | _ -> raise FoundRuleError

let print_prelude out input filename = 
  p_line out (mk_prelude filename);
  let env = get_vars FreeVarSet.empty input in
  FreeVarSet.iter
    (fun var -> p_line out (mk_decl var mk_termtype)) env
