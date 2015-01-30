(* remains false unless -debug option is called *)
val debugmode : bool ref

(* ddo f applies f only in debug mode, and flushes stderr afterwards *)
val ddo : unit -> unit

(* ddo print a dedukti term on stderr *)
val dprintterm :  Smt2d.Dedukti.term -> unit

(* ddo print a dedukti list on stderr *)
val dprintlist :  Smt2d.Dedukti.term list -> unit

(* ddo print a dedukti list between two strings on stderr *)
val dprintcontext : string -> Smt2d.Dedukti.term list -> string -> unit
