(* environment: association table mapping a rulename to a couple
   (dedukti proof term, clause as a list of dedukti propositions) *)
module PrfEnvSet :
sig
  type 'a t
end

(* from:
   - the input clause as one dedukti proposition (dkinput)
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
  Dkterm.dkterm-> Dkterm.dkterm -> Global.step ->
  (Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t ->
  Dkterm.dkline * ((Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t) 

(* prints a dedukti line using Dkterm p_line function *)
val print_step : out_channel -> Dkterm.dkline -> unit

(* from the input step, returns: 
   - a dedukti variable used as a proof of the input clause (dkvar)
   - the input clause as one dedukti propositions
   - an environment containing the proof (dkvar) *)
val translate_input : 
  Global.step -> Dkterm.dkterm * Dkterm.dkterm * 
  ((Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t)

(* print the header of the dedukti file and the declarations of free variables *)
val print_prelude : out_channel -> Global.step -> string -> unit
