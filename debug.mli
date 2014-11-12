(* remains false unless -debug option is called *)
val debugmode : bool ref

(* ddo f applies f only in debug mode, and flushes stderr afterwards *)
val ddo : unit -> unit

(* ddo print a dedukti term on stderr *)
val dprintterm :  Dedukti.dkterm -> unit

(* ddo print a dedukti list on stderr *)
val dprintlist :  Dedukti.dkterm list -> unit

(* ddo print a dedukti list between two strings on stderr *)
val dprintcontext : string -> Dedukti.dkterm list -> string -> unit
