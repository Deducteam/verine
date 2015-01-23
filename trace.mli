(* AST corresponding to veriT proof traces, using smtlib2 terms *)

type id = string

type rule = 
  | Input
  | Eq_reflexive
  | Eq_transitive
  | Eq_congruent
  | Resolution
  | Unknown_rule of string

val mk_rule: string -> rule

type step = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: Smt2d.Concrete.term list;
}
