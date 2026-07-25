import LVConsensus.Definitions
import LVConsensus.NiceWhpBirths
import LVConsensus.MarkovLib
import LVConsensus.NiceWhpExtinctionProof

set_option autoImplicit false

namespace LVConsensus

/-- Paper `lemma:nice-whp-extinction`: extinction time is `O(n)` w.h.p. -/
theorem lemma_nice_whp_extinction
    (N : NiceChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    WhpTailBound (fun n t => extinctionTail N.toBirthDeathChain n t) (fun n => n) := by
  exact nice_whp_extinction_linear_unconditional N

end LVConsensus
