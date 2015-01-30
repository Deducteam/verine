(* AST corresponding to veriT proof traces, using smtlib2 terms *)

module Abs = Smt2d.Abstract

type id  = Trace.id

type rule = Trace.rule

(* terms with no bindings or attributes *)
type term = Smt2d.Abstract.term

type step = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: term list;
}

(* Variable environment *)

module VarBindings =
  Map.Make
    (struct
      type t = Abs.variable
      let compare = Pervasives.compare
    end)

let empty_env = VarBindings.empty

let add_bindings bindings env =
  List.fold_left 
    (fun env (var, term) -> VarBindings.add var term env) env bindings

(* from trace.ml to proof.ml: scopes, expands,
 and eliminates constructors {var, let, forall, exists, attributed} *)
let rec simplify_aux_core env core =
  match core with
  | Abs.True -> Abs.t_true
  | Abs.False -> Abs.t_false
  | Abs.Not t -> Abs.t_not (simplify_aux env t)
  | Abs.Imply (t1, t2) -> Abs.t_imply (simplify_aux env t1) (simplify_aux env t2)
  | Abs.And (t1, t2) -> Abs.t_and (simplify_aux env t1) (simplify_aux env t2)
  | Abs.Or (t1, t2) -> Abs.t_or (simplify_aux env t1) (simplify_aux env t2)
  | Abs.Xor (t1, t2) -> Abs.t_xor (simplify_aux env t1) (simplify_aux env t2)
  | Abs.Equal (t1, t2) -> Abs.t_equal (simplify_aux env t1) (simplify_aux env t2)
  | Abs.Distinct (t1, t2) -> Abs.t_distinct (simplify_aux env t1) (simplify_aux env t2)
  | Abs.Ite (t1, t2, t3) -> 
     Abs.t_ite (simplify_aux env t1) (simplify_aux env t2) (simplify_aux env t3)

and simplify_aux env term =
  match term with
  | Abs.Var var -> VarBindings.find var env     
  | Abs.App (fun_sym, opt, terms) -> Abs.t_app fun_sym opt (List.map (simplify_aux env) terms)
  | Abs.Core core ->
     simplify_aux_core env core
  | Abs.Let (bindings, term) -> 
     simplify_aux (add_bindings bindings env) term
  | Abs.Forall (sorted_vars, term) -> raise Smt2d.Error.Not_implemented
  | Abs.Exists (sorted_vars, term) -> raise Smt2d.Error.Not_implemented
  | Abs.Attributed (term, attributes) -> simplify_aux env term

let simplify term =
  simplify_aux empty_env term

let process_step trace_step =
  {
    id = trace_step.Trace.id;
    rule = trace_step.Trace.rule;
    clauses = trace_step.Trace.clauses;
    conclusion = List.map simplify trace_step.Trace.conclusion
  }
