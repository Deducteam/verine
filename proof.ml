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
let rec elim_aux env term =
  match term with
  | Abs.Var var -> VarBindings.find var env     
  | Abs.App (fun_sym, opt, terms) -> Abs.t_app fun_sym opt (List.map (elim_aux env) terms)
  | Abs.Let (bindings, term) -> 
     elim_aux (add_bindings bindings env) term
  | Abs.Forall (sorted_vars, term) -> raise Smt2d.Error.Not_implemented
  | Abs.Exists (sorted_vars, term) -> raise Smt2d.Error.Not_implemented
  | Abs.Attributed (term, attributes) -> elim_aux env term

let elim_bindings_attributes (term: Smt2d.Expand.term) =
  elim_aux empty_env (term :> Abs.term)

let process_step signature trace_step =
  {
    id = trace_step.Trace.id;
    rule = trace_step.Trace.rule;
    clauses = trace_step.Trace.clauses;
    conclusion = 
      let abstract_conclusion = 
	List.map (Smt2d.Abstract.tr_term Smt2d.Abstract.empty_vars) trace_step.Trace.conclusion in
      let expanded_conclusion = 
	List.map (Smt2d.Expand.expand signature) abstract_conclusion in
      List.map elim_bindings_attributes expanded_conclusion;
  }
