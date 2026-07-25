import LVConsensus.Definitions
import LVConsensus.MarkovLib

set_option autoImplicit false

namespace LVConsensus

/-- Intraspecific-only competition has positive failure probability for every fixed (a,b).
    Requires γ₀ > 0 and γ₁ > 0 (both species have intraspecific competition) and δ > 0
    (individual death is present). The δ > 0 constraint prevents parity-deterministic
    outcomes under purely intraspecific self-destructive competition.
    Paper: Section 8.2 (line 1071), α = 0, γ > 0, and δ > 0.

    NOTE (WEAKER THAN PAPER): ε depends on (a,b). The paper claims a uniform ε via a
    continuous-time independence argument; that argument does not directly transfer to the
    discrete-time kernel formulation used here. -/
theorem thm_intraspecific_only_constant_failure
    (v : LVVariant)
    (params : LVParams)
    (hInter0 : params.alpha0 = 0)
    (hInter1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    ∀ a b : Nat, 0 < b → b < a →
      ∃ ε : Real, 0 < ε ∧
        majorityConsensusProb v params (a, b) ≤ 1 - ENNReal.ofReal ε :=
  intraspecific_only_constant_failure v params hInter0 hInter1 hGamma0 hGamma1 hDelta

end LVConsensus
