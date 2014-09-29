(* environment: association table mapping a step rulename to a couple
   (dedukti proof term, proven clause as a list of dedukti propositions) 
   corresponding to this step *)
module PrfEnvSet :
sig
  type 'a t
end

(* from :
   - a dedukti variable used as a proof of the input clause (dkinputvar)
   - the input clause as a dedukti proposition (dkinput)
   - a step
   - an environment containing proofs of the previous steps clauses (including the input)
   computes :
   - a dedukti proof (prf) of the step clause as a dedukti proposition (dkclause) 
     in this environment
   returns : 
   - a dedukti definition of a variable (dkclausevar)
     being (lambda dkinputvar : proof(dkinput) . prf),
     which is a proof of (dkinput implies dkclause)
   - the environment enriched with (dkclausevar dkinputvar)*)
val translate_step : 
  Dkterm.dkterm-> Dkterm.dkterm -> Global.step ->
  (Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t ->
  Dkterm.dkline * ((Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t) 

(* prints a dedukti line using Dkterm p_line function *)
val print_step : out_channel -> Dkterm.dkline -> unit

(* from an input step, returns: 
   - a dedukti variable used as a proof of the input clause (dkvar)
   - the input clause as a list of dedukti propositions (dklist)
   - an environment containing one association, the association
     input name -> (dkvar, dklist) *)
val translate_input : 
  Global.step -> Dkterm.dkterm * Dkterm.dkterm * 
  ((Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t)

(* print the header of the dedukti file and the declarations of free variables *)
val print_prelude : out_channel -> Global.step -> string -> unit
