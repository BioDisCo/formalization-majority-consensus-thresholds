import LVConsensus.SelfDestructiveLowerThreshold

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Corrected paper `theorem:self-destructive-lower`. -/
theorem theorem_self_destructive_lower
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hAlpha : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∀ ε : Real, 0 < ε →
      ∃ φ : Real, 0 < φ ∧ ∃ n₀ : Nat,
        ∀ a b : Nat, n₀ ≤ a + b → 0 < b → b ≤ a →
          (a : Real) - b ≤
              φ * Real.sqrt (Real.log (a + b)) →
            majorityConsensusProb
                LVVariant.selfDestructive params (a, b) ≤
              ENNReal.ofReal (1 / 2 + ε) :=
  LVConsensus.thm_self_destructive_lower_threshold
    params hNeutral hAlpha hBetaDelta hBetaPos hGamma0 hGamma1

end LVConsensus.Paper
