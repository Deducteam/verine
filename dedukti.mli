(* AST corresponding to a Dedukti output *)
type dkvar
type dkterm
type dkline

(* constructor functions *)
val mk_var : string -> dkterm
val mk_lam : dkterm -> dkterm -> dkterm -> dkterm
val mk_lams : dkterm list -> dkterm list -> dkterm -> dkterm
val mk_app : dkterm -> dkterm list -> dkterm
val mk_app2 : dkterm -> dkterm -> dkterm
val mk_app3 : dkterm -> dkterm -> dkterm -> dkterm
val mk_arrow : dkterm -> dkterm -> dkterm
val mk_termtype : dkterm
val mk_proptype : dkterm
val mk_true : dkterm
val mk_false : dkterm
val mk_not : dkterm -> dkterm
val mk_imply : dkterm -> dkterm -> dkterm
val mk_and : dkterm -> dkterm -> dkterm
val mk_or : dkterm -> dkterm -> dkterm
val mk_eq : dkterm -> dkterm -> dkterm
val mk_prf : dkterm -> dkterm

val mk_decl : dkterm -> dkterm -> dkline
val mk_deftype : dkterm -> dkterm -> dkterm -> dkline
val mk_prelude : string -> dkline

(* print functions *)
val p_var : out_channel -> dkvar -> unit
val p_term : out_channel -> dkterm -> unit
val p_terms : out_channel -> dkterm list -> unit
val p_line : out_channel -> dkline -> unit
