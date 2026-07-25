import LVConsensus.NiceExtinction

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:nice-extinction`. -/
theorem lemma_nice_extinction
    (N : NiceChain) :
    IsThetaEventually
      (fun n => (expectedExtinctionTime N.toBirthDeathChain n).toReal)
      (fun n => (n : Real)) :=
  LVConsensus.lemma_nice_extinction N

end LVConsensus.Paper
