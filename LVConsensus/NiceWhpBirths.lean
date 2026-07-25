import LVConsensus.NiceWhpBirthsProof

set_option autoImplicit false

namespace LVConsensus

/-- Paper `lemma:nice-whp-births`: births before extinction are `O(log^2 n)` w.h.p. -/
theorem lemma_nice_whp_births
    (N : NiceChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    WhpTailBound (fun n t => birthTail N.toBirthDeathChain n t) logSqScaleNat :=
  nice_whp_births_logsq_unconditional N

end LVConsensus
