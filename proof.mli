(* AST corresponding to veriT proof traces, using smtlib2 terms *)

type id  = Trace.id

type rule = Trace.rule

(* terms with no bindings or attributes *)
type term = private Smt2d.Abstract.term

type step = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: term list;
}

(* from trace.ml to proof.ml: scopes, expands,
 and eliminates constructors {var, let, forall, exists, attributed} *)
val process_step: Smt2d.Signature.signature -> Trace.step -> step
