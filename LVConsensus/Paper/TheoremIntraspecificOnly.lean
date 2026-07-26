import LVConsensus.IntraspecificOnly

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Paper intraspecific-only theorem, with one positive failure
constant uniform over all positive initial populations. -/
theorem theorem_intraspecific_only
    (v : LVVariant)
    (params : LVParams)
    (hInter0 : params.alpha0 = 0)
    (hInter1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta) :
    ∃ ε : Real, 0 < ε ∧
      ∀ a b : Nat, 0 < b → b < a →
        majorityConsensusProb v params (a, b) ≤
          1 - ENNReal.ofReal ε :=
  LVConsensus.thm_intraspecific_only_constant_failure
    v params hInter0 hInter1
      hGamma0 hGamma1 hDelta

end LVConsensus.Paper
