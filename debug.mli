(* remains false unless -debug option is called *)
val debug_mode : bool ref

(* apply_if_debug f applies f only in debug mode, and flushes stderr afterwards *)
val apply_if_debug : unit -> unit

(* print a dedukti term on stderr *)
val print_term :  Smt2d.Dedukti.term -> unit

(* print a dedukti list on stderr *)
val print_terms :  Smt2d.Dedukti.term list -> unit
