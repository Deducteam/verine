(* AST corresponding to veriT proof traces, using smtlib2 terms *)

type id  = Trace.id

exception Proof_error

type rule = Trace.rule

(* terms with no bindings or attributes *)
type term = private Smt2d.Abstract.term

type step = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: term list;
}

(* from trace.ml to proof.ml: expands,
 and eliminates constructors {var, let, forall, exists, attributed} *)
val simplify: Smt2d.Abstract.term -> term
val process_step: Trace.step -> step
