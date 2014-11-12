(* AST corresponding to a Dedukti output *)
type var = string
type term
type line

(* constructor functions *)
val dkvar : var -> term
val dklam : var -> term -> term -> term
val dklams : var list -> term list -> term -> term
val dkapp : term -> term list -> term
val dkapp2 : term -> term -> term
val dkapp3 : term -> term -> term -> term
val dkarrow : term -> term -> term

val dkterm : term
val dkprop : term
val dktrue : term
val dkfalse : term
val dknot : term -> term
val dkimply : term -> term -> term
val dkand : term -> term -> term
val dkor : term -> term -> term
val dkeq : term -> term -> term
val dkprf : term -> term

val dkdecl : term -> term -> line
val dkdeftype : term -> term -> term -> line
val dkprelude : string -> line

(* print functions *)
val print_var : out_channel -> var -> unit
val print_term : out_channel -> term -> unit
val print_terms : out_channel -> term list -> unit
val print_line : out_channel -> line -> unit
