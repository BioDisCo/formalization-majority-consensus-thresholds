import LVConsensus.NonSelfDestructiveLower

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper NSD lower-bound theorem. -/
theorem thm_non_self_destructive_lower
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∀ ε : Real, 0 < ε →
      ∃ φ : Real, 0 < φ ∧ ∃ n₀ : Nat,
        ∀ a b : Nat, n₀ ≤ a + b → 0 < b → b ≤ a →
          (a : Real) - b ≤ φ * Real.sqrt (a + b) →
            majorityConsensusProb LVVariant.nonSelfDestructive
                params (a, b) ≤
              ENNReal.ofReal (1 / 2 + ε) :=
  LVConsensus.thm_non_self_destructive_lower
    params hNeutral hInter hBetaDelta hGamma0 hGamma1

end LVConsensus.Paper
