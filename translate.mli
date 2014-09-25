(* environment: association table mapping a step rulename to a couple
   (dedukti proof term, proven clause as a list of dedukti propositions) 
   corresponding to this step *)
module PrfEnvSet :
sig
  type 'a t
end

(* from :
   - the rulename and the dedukti proposition of the input
   - a step
   - and an environment containing a proof of the input clause
   computes :
   - a dedukti proof (prf) of the step clause
   returns : 
   - a dedukti line declaring a proof term for the implication (input clause => step clause)
   - the environment enriched with (prf, step clause as a list of dedukti propositions)*)
val translate_step : 
  Global.rulename -> Dkterm.dkterm -> Global.step ->
  (Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t ->
  Dkterm.dkline * ((Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t) 

(* prints a dedukti line using Dkterm p_line function *)
val print_step : out_channel -> Dkterm.dkline -> unit

(* from an input step, returns: 
   - its rulename (name)
   - its clause as a list of dedukti propositions (dklist)
   - an environment containing
     (dedukti variable from name, dklist) *)
val translate_input : 
  Global.step -> Global.rulename * Dkterm.dkterm * 
  ((Dkterm.dkterm * Dkterm.dkterm list) PrfEnvSet.t)

(* print the header of the dedukti file and the declarations of free variables *)
val print_prelude : out_channel -> Global.step -> string -> unit
