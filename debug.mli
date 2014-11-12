(* remains false unless -debug option is called *)
val debugmode : bool ref

(* ddo f applies f only in debug mode, and flushes stderr afterwards *)
val ddo : unit -> unit

(* ddo print a dedukti term on stderr *)
val dprintterm :  Dedukti.term -> unit

(* ddo print a dedukti list on stderr *)
val dprintlist :  Dedukti.term list -> unit

(* ddo print a dedukti list between two strings on stderr *)
val dprintcontext : string -> Dedukti.term list -> string -> unit
