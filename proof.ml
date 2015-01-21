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

let mk_step signature (prestep : prestep) = 
  let newconclusion =
    List.map 
      (fun t -> Smt2d.Expand.expand signature (Smt2d.Abstract.tr_term Smt2d.Abstract.empty_vars t)) 
      prestep.conclusion in
  {
    id = prestep.id;
    rule = prestep.rule;
    clauses = prestep.clauses;
    conclusion = newconclusion;
  }
