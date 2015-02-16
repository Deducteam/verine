(* AST corresponding to veriT proof traces, using smtlib2 terms *)

module Abs = Smt2d.Abstract

exception Proof_error

type view =
  | App of Abs.fun_symbol * Abs.term list
  | True
  | False
  | Not of Abs.term
  | Imply of Abs.term * Abs.term
  | And of Abs.term * Abs.term
  | Or of Abs.term * Abs.term
  | Xor of Abs.term * Abs.term
  | Equal of Abs.term * Abs.term
  | Distinct of Abs.term * Abs.term
  | Ite of Abs.term * Abs.term * Abs.term

(* Variable environment *)
module VarBindings =
  Map.Make
    (struct
      type t = Abs.variable
      let compare = Pervasives.compare
    end)

let empty_env = VarBindings.empty

let rec substitute_core env core =
  match core with
  | Abs.True -> Abs.t_true
  | Abs.False -> Abs.t_false
  | Abs.Not t -> Abs.t_not (substitute env t)
  | Abs.Imply (t1, t2) -> Abs.t_imply (substitute env t1) (substitute env t2)
  | Abs.And (t1, t2) -> Abs.t_and (substitute env t1) (substitute env t2)
  | Abs.Or (t1, t2) -> Abs.t_or (substitute env t1) (substitute env t2)
  | Abs.Xor (t1, t2) -> Abs.t_xor (substitute env t1) (substitute env t2)
  | Abs.Equal (t1, t2) -> Abs.t_equal (substitute env t1) (substitute env t2)
  | Abs.Distinct (t1, t2) -> Abs.t_distinct (substitute env t1) (substitute env t2)
  | Abs.Ite (t1, t2, t3) ->
     Abs.t_ite (substitute env t1) (substitute env t2) (substitute env t3)

and substitute env term =
  if env = empty_env 
  then term 
  else
    match term with
    | Abs.Var var ->
       begin try VarBindings.find var env with Not_found -> Abs.t_var var end
    | Abs.App (fun_sym, opt, terms) ->
       Abs.t_app fun_sym opt (List.map (substitute env) terms)
    | Abs.Core core -> substitute_core env core
    | Abs.Let (bindings, term) ->
       Abs.t_let (List.map (fun (x,t) -> x, substitute env t) bindings) (substitute env term)
    | Abs.Forall (sorted_vars, term) -> Abs.t_forall sorted_vars (substitute env term)
    | Abs.Exists (sorted_vars, term) -> Abs.t_exists sorted_vars (substitute env term)
    | Abs.Attributed (term, attr) -> Abs.t_attributed (substitute env term) attr

let rec equal_core_env env1 env2 core1 core2 =
  match core1, core2 with
  | Abs.True, Abs.True -> true
  | Abs.False, Abs.False -> true
  | Abs.Not t, Abs.Not u -> equal_env env1 env2 t u
  | Abs.Imply (t1, t2), Abs.Imply (u1, u2) -> equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2
  | Abs.And (t1, t2), Abs.And (u1, u2) -> equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2
  | Abs.Or (t1, t2), Abs.Or (u1, u2) -> equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2
  | Abs.Xor (t1, t2), Abs.Xor (u1, u2) -> equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2
  | Abs.Equal (t1, t2), Abs.Equal (u1, u2) -> equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2
  | Abs.Distinct (t1, t2), Abs.Distinct (u1, u2) -> 
     equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2
  | Abs.Ite (t1, t2, t3), Abs.Ite (u1, u2, u3) -> 
     equal_env env1 env2 t1 u1 && equal_env env1 env2 t2 u2 && equal_env env1 env2 t3 u3
  | Abs.True, _ | Abs.False, _ | Abs.Not _, _
  | Abs.Imply _, _ | Abs.And _, _ | Abs.Or _, _ | Abs.Xor _, _
  | Abs.Equal _, _ | Abs.Distinct _, _ | Abs.Ite _, _ -> false

and equal_env env1 env2 t u =
  match t, u with
  | Abs.Var v, _ ->
     let new_t = 
       try VarBindings.find v env1 with Not_found -> raise Proof_error in
     equal_env env1 env2 new_t u
  | _, Abs.Var w ->
     let new_u = 
       try VarBindings.find w env2  with Not_found -> raise Proof_error in
     equal_env env1 env2 t new_u
  | Abs.Let (bindings, t), _ ->
     let new_env1 = 
       List.fold_left (fun env (x, t) -> VarBindings.add x t env) env1 bindings in
     equal_env new_env1 env2 t u
  | _, Abs.Let (bindings, u) ->
     let new_env2 = 
       List.fold_left (fun env (x, t) -> VarBindings.add x t env) env2 bindings in
     equal_env env1 new_env2 t u
  | Abs.Attributed (t, _), _ -> equal_env env1 env2 t u
  | _, Abs.Attributed (u, _) -> equal_env env1 env2 t u
  | Abs.App (fun_sym1, _, ts), Abs.App (fun_sym2, _, us) ->
     fun_sym1 = fun_sym2 &&
       List.for_all2 (equal_env env1 env2) ts us
  | Abs.App _, _ -> false
  | Abs.Core core1, Abs.Core core2 ->
     equal_core_env env1 env2 core1 core2
  | Abs.Core _, _ -> false
  | Abs.Forall _, _ -> raise Proof_error
  | Abs.Exists _, _ -> raise Proof_error

let equal t1 t2 = 
  equal_env empty_env empty_env t1 t2

(* ---------------------------------------------- *)

let rec mk_view_core_env env core =
  match core with
  | Abs.True -> True
  | Abs.False -> False
  | Abs.Not t -> Not (substitute env t)
  | Abs.Imply (t1, t2) -> Imply (substitute env t1, substitute env t2)
  | Abs.And (t1, t2) -> And (substitute env t1, substitute env t2)
  | Abs.Or (t1, t2) -> Or (substitute env t1, substitute env t2)
  | Abs.Xor (t1, t2) -> Xor (substitute env t1, substitute env t2)
  | Abs.Equal (t1, t2) -> Equal (substitute env t1, substitute env t2)
  | Abs.Distinct (t1, t2) -> Distinct (substitute env t1, substitute env t2)
  | Abs.Ite (t1, t2, t3) -> Ite (substitute env t1, substitute env t2, substitute env t3)

and mk_view_env env term =
  match term with
  | Abs.Var var ->
     let t = try VarBindings.find var env with Not_found -> raise Proof_error in
     mk_view_env env t
  | Abs.App (fun_sym, _, terms) ->
     App (fun_sym, List.map (substitute env) terms)
  | Abs.Core core ->
     mk_view_core_env env core
  | Abs.Let (bindings, term) ->
     let new_env = 
       List.fold_left (fun env (x, t) -> VarBindings.add x t env) env bindings in
     mk_view_env new_env term
  | Abs.Forall _ -> raise Proof_error
  | Abs.Exists _ -> raise Proof_error
  | Abs.Attributed (term, _) -> mk_view_env env term

let mk_view term = 
  mk_view_env empty_env term

let match_app t =
  match mk_view t with
  | App (f, ts) -> f, ts 
  | True | False | Not _
  | Imply _ | And _ | Or _ | Xor _
  | Equal _ | Distinct _ | Ite _ -> raise Proof_error

let match_not t =
  match mk_view t with
  | Not x -> x
  | App _ | True | False
  | Imply _ | And _ | Or _ | Xor _
  | Equal _ | Distinct _ | Ite _ -> raise Proof_error

let match_equal t =
  match mk_view t with
  | Equal (x, y) -> x, y
  | App _ | True | False | Not _
  | Imply _ | And _ | Or _ | Xor _
  | Distinct _ | Ite _ -> raise Proof_error
