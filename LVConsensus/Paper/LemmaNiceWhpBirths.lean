import LVConsensus.NiceWhpBirths

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:nice-whp-births`. -/
theorem lemma_nice_whp_births
    (N : NiceChain) :
    WhpTailBound
      (fun n t => birthTail N.toBirthDeathChain n t)
      logSqScaleNat :=
  LVConsensus.lemma_nice_whp_births N

end LVConsensus.Paper
