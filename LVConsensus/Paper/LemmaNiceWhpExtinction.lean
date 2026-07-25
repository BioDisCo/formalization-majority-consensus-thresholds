import LVConsensus.NiceWhpExtinction

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:nice-whp-extinction`. -/
theorem lemma_nice_whp_extinction
    (N : NiceChain) :
    WhpTailBound
      (fun n t => extinctionTail N.toBirthDeathChain n t)
      (fun n => n) :=
  LVConsensus.lemma_nice_whp_extinction N

end LVConsensus.Paper
