(* AST corresponding to one step of a veriT proof *)
type term = 
  | Var of string
  | Fun of string * term list

type prop =
  | True
  | False
  | Not of prop
  | Imply of prop * prop
  | And of prop * prop
  | Or of prop * prop
  | Xor of prop * prop
  | Eq of term * term
  | Distinct of term * term
  | Ite of prop * term * term
  | Pred of string * term list

type rulename = string

type rule = 
  | Input
  | Eq_reflexive
  | Eq_transitive
  | Eq_congruent
  | Resolution
  | Unknown of string

type step =
  | Step of rulename * rule * rulename list * prop list
