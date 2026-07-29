import LVConsensus.NiceExpectedBirths

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:nice-expected-births`. -/
theorem lemma_nice_expected_births
    (N : NiceChain) :
    IsBigOEventuallyENN
      (fun n => expectedBirthsBeforeExtinction N.toBirthDeathChain n)
      logScale :=
  LVConsensus.lemma_nice_expected_births N

end LVConsensus.Paper
