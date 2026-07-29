import LVConsensus.Definitions
import LVConsensus.NiceExtinction
import LVConsensus.ExpectedBirthsProof

set_option autoImplicit false

namespace LVConsensus

/-- Paper `lemma:nice-expected-births`: expected births are `O(log n)`. -/
theorem lemma_nice_expected_births
    (N : NiceChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    IsBigOEventuallyENN
      (fun n => expectedBirthsBeforeExtinction N.toBirthDeathChain n)
      logScale :=
  bd_expected_births_logarithmic_unconditional
    N.toBirthDeathChain N.C N.C_pos N.p_le N.D N.D_pos N.q_ge

end LVConsensus
