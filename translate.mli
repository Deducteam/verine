exception Translate_error
exception Axiom

type smt2_env =
    { signature: Smt2d.Signature.signature;
      input_terms: Smt2d.Abstract.term list;
      input_term_vars: Smt2d.Dedukti.term list;
      input_proof_idents: Smt2d.Dedukti.ident list; }

module PrfEnvMap :
sig
  type 'a t
  val empty: 'a t
end

type proof_env = (Smt2d.Dedukti.term * Smt2d.Abstract.term list) PrfEnvMap.t

val translate_step : smt2_env -> proof_env -> Proof.step -> Smt2d.Dedukti.line * proof_env 
