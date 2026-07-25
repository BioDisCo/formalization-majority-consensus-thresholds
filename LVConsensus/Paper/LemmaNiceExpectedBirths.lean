import LVConsensus.NiceExpectedBirths

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:nice-expected-births`. -/
theorem lemma_nice_expected_births
    (N : NiceChain) :
    IsBigOEventually
      (fun n =>
        (expectedBirthsBeforeExtinction N.toBirthDeathChain n).toReal)
      logScale :=
  LVConsensus.lemma_nice_expected_births N

end LVConsensus.Paper
