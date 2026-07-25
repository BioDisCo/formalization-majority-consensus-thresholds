import LVConsensus.SelfDestructiveUpper

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Paper theorem: the self-destructive majority-consensus upper bound, with
the dominating nice chain constructed from the LV parameters. -/
theorem theorem_self_destructive_upper
    (params : LVParams)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∀ k : Nat, ∃ C : Real, 0 < C ∧
      ∃ n₀ : Nat, ∀ a b : Nat, n₀ ≤ a + b →
        b < a →
        C * logSqScale (a + b) ≤
          (a : Real) - (b : Real) →
          majorityConsensusProb
              LVVariant.selfDestructive params (a, b) ≥
            ENNReal.ofReal
              (1 - 1 /
                (((a + b : Nat) + 1 : Real) ^ k)) := by
  have hGood :
      0 < effectiveGoodRate
        LVVariant.selfDestructive params := by
    simp only [effectiveGoodRate]
    linarith
  obtain ⟨N, hDom⟩ :=
    lemma_domination LVVariant.selfDestructive
      params hGood hGamma0 hGamma1
  exact thm_self_destructive_upper
    params hInter hGamma0 hGamma1 N hDom

end LVConsensus.Paper
