(* AST corresponding to veriT proof traces, using smtlib2 terms *)

type id = string

type rule = 
  | Input
  | Eq_reflexive
  | Eq_transitive
  | Eq_congruent
  | Resolution
  | Unknown_rule of string

let mk_rule s = 
  match s with
  | "input" -> Input
  | "eq_reflexive" -> Eq_reflexive
  | "eq_transitive" -> Eq_transitive
  | "eq_congruent" -> Eq_congruent
  | "resolution" -> Resolution
  | _ -> Unknown_rule s

type step = {
  id: id;
  rule: rule;
  clauses: id list;
  conclusion: Smt2d.Concrete.term list;
}
