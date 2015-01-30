(* Dedukti variable *)
type var = string
(* Dedukti term *)
type term
(* Dedukti line (e.g. definition) *)
type line

(* Building Dedukti terms *)
val var : var -> term
val lam : var -> term -> term -> term
val lams : var list -> term list -> term -> term
val app : term -> term list -> term
val app2 : term -> term -> term
val app3 : term -> term -> term -> term
val arrow : term -> term -> term

(* Building Dedukti terms in the logic.dk context *)
val l_term : term
val l_prop : term
val l_true : term
val l_false : term
val l_not : term -> term
val l_imply : term -> term -> term
val l_and : term -> term -> term
val l_or : term -> term -> term
val l_eq : term -> term -> term
val l_prf : term -> term

(* Building Dedukti lines *)
val declaration : term -> term -> line
val definition : term -> term -> term -> line
val prelude : string -> line

(* print functions *)
val print_var : out_channel -> var -> unit
val print_term : out_channel -> term -> unit
val print_terms : out_channel -> term list -> unit
val print_line : out_channel -> line -> unit
