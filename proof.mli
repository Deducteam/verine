(* AST corresponding to veriT proof traces, using smtlib2 terms *)

type id = string
type rule = string	      

type prestep = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: Smt2d.Concrete.term list;
}

type step = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: Smt2d.Expand.term list;
}

val mk_step:  Smt2d.Signature.signature -> prestep -> step
