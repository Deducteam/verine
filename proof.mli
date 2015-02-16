(* AST corresponding to veriT proof traces, using smtlib2 terms *)

exception Proof_error

type view =
  | App of Smt2d.Abstract.fun_symbol * Smt2d.Abstract.term list
  | True
  | False
  | Not of Smt2d.Abstract.term
  | Imply of Smt2d.Abstract.term * Smt2d.Abstract.term
  | And of Smt2d.Abstract.term * Smt2d.Abstract.term
  | Or of Smt2d.Abstract.term * Smt2d.Abstract.term
  | Xor of Smt2d.Abstract.term * Smt2d.Abstract.term
  | Equal of Smt2d.Abstract.term * Smt2d.Abstract.term
  | Distinct of Smt2d.Abstract.term * Smt2d.Abstract.term
  | Ite of Smt2d.Abstract.term * Smt2d.Abstract.term * Smt2d.Abstract.term

val mk_view: Smt2d.Abstract.term -> view

val equal: Smt2d.Abstract.term -> Smt2d.Abstract.term -> bool

val match_app: Smt2d.Abstract.term -> Smt2d.Abstract.fun_symbol * Smt2d.Abstract.term list

val match_not: Smt2d.Abstract.term -> Smt2d.Abstract.term

val match_equal: Smt2d.Abstract.term -> Smt2d.Abstract.term * Smt2d.Abstract.term
