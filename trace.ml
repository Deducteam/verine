type symbol =
  | Symbol of string

(* Missing *)
(* spec_constants  *)
(* qualidentifier: (as identifier sort) *)
(* identifier: (_ symbol numeral+) *)
(* forall *)
(* exists *)
(* bang *)
type smtterm =
  | Var of symbol
  | Fun of symbol * smtterm list
  | Let of smtvarbinding list * smtterm
  | Core of smtcore

and smtvarbinding =
  | Varbinding of symbol * smtterm

and smtcore =
  | True
  | False
  | Not of smtterm
  | Imply of smtterm list
  | And of smtterm list
  | Or of smtterm list
  | Xor of smtterm list
  | Eq of smtterm list
  | Distinct of smtterm list
  | Ite of smtterm * smtterm * smtterm

type rule = 
  | Input
  | Eq_reflexive
  | Eq_transitive
  | Eq_congruent
  | Resolution
  | Anonrule of string

type line =
  | Line of string * rule * string list * smtterm list
