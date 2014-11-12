(* environment: association table mapping a rulename to a couple
   (dedukti proof term, clause as a list of dedukti propositions) *)
module PrfEnvMap :
sig
  type 'a t
  val empty: 'a t
end

(* from:
   - the input clause as one dedukti variable (dkinput)
   - a proof of the input clause (dkinputvar)
   - a step
   - an environment containing proofs of the previous steps
     including (dkinputvar)
   computes:
   - a dedukti proof (prf) of the step clause in this environment
   returns: 
   - a dedukti definition of a variable (dkclausevar)
     as the proof (lambda dkinputvar. prf),
   - the environment enriched with (dkclausevar dkinputvar)*)
val translate_step : 
  Dedukti.var list -> Dedukti.term list -> Proof.step ->
  (Dedukti.term * Proof.prop list) PrfEnvMap.t ->
  Dedukti.line * ((Dedukti.term * Proof.prop list) PrfEnvMap.t) 

(* prints a dedukti line using Dedukti p_line function *)
val print_step : out_channel -> Dedukti.line -> unit

(* from the input step, returns: 
   - a dedukti variable used as a proof of the input clause (dkvar)
   - the input clause as one dedukti propositions
   - an environment containing the proof (dkvar) *)
val translate_input : 
  Proof.step -> ((Dedukti.term * Proof.prop list) PrfEnvMap.t) -> 
  Dedukti.var * Dedukti.term *
    ((Dedukti.term * Proof.prop list) PrfEnvMap.t)

(* print the header of the dedukti file and the declarations of free variables *)
val print_prelude : 
  out_channel -> ((Dedukti.term * Proof.prop list) PrfEnvMap.t) -> Proof.step list -> Dedukti.term list -> unit
