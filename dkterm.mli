open Printf

type dkvar = string

type dkterm = private
  | Dkvar of dkvar
  | Dklam of dkvar * dkterm * dkterm
  | Dkapp of dkterm list
  | Dkarrow of dkterm * dkterm
  | Dktermtype
  | Dkproptype
  | Dknot
  | Dkand
  | Dkimply
  | Dkfalse
  | Dkeq
  | Dkprf

type dkline = private
  | Dkdecl of dkvar * dkterm
  | Dkdeftype of dkvar * dkterm * dkterm
  | Dkprelude of string

val mk_var : dkvar -> dkterm
val mk_lam : dkvar -> dkterm -> dkterm -> dkterm
val mk_app : dkterm list -> dkterm
val mk_app2 : dkterm -> dkterm -> dkterm
val mk_app3 : dkterm -> dkterm -> dkterm -> dkterm
val mk_arrow : dkterm -> dkterm -> dkterm
val mk_termtype : dkterm
val mk_proptype : dkterm
val mk_not : dkterm -> dkterm
val mk_and : dkterm -> dkterm -> dkterm
val mk_imply : dkterm -> dkterm -> dkterm
val mk_false : dkterm
val mk_eq : dkterm -> dkterm -> dkterm
val mk_prf : dkterm -> dkterm

val mk_decl : dkvar -> dkterm -> dkline
val mk_deftype : dkvar -> dkterm -> dkterm -> dkline
val mk_prelude : string -> dkline

val p_var : out_channel -> dkvar -> unit
val p_term : out_channel -> dkterm -> unit
val p_term_p : out_channel -> dkterm -> unit
val p_terms : out_channel -> dkterm list -> unit
val p_line : out_channel -> dkline -> unit