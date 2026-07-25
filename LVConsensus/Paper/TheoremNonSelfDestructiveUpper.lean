import LVConsensus.NonSelfDestructiveUpper

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Paper theorem: the non-self-destructive majority-consensus upper bound,
with the dominating nice chain constructed from the LV parameters. -/
theorem theorem_non_self_destructive_upper
    (params : LVParams)
    (hInter : 0 < min params.alpha0 params.alpha1)
    (hBias : params.alpha1 ≤ params.alpha0)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∀ k : Nat, ∃ C : Real, 0 < C ∧
      ∃ n₀ : Nat, ∀ a b : Nat, n₀ ≤ a + b →
        0 < b →
        b < a →
        C *
            Real.sqrt
              (((a + b : Nat) : Real) *
                logScale (a + b)) ≤
          (a : Real) - (b : Real) →
        majorityConsensusProb
            LVVariant.nonSelfDestructive params (a, b) ≥
          ENNReal.ofReal
            (1 - 1 /
              (((a + b : Nat) + 1 : Real) ^ k)) := by
  have hGood :
      0 < effectiveGoodRate
        LVVariant.nonSelfDestructive params := by
    simpa only [effectiveGoodRate] using hInter
  obtain ⟨N, hDom⟩ :=
    lemma_domination LVVariant.nonSelfDestructive
      params hGood hGamma0 hGamma1
  exact thm_non_self_destructive_upper
    params hInter hBias hGamma0 hGamma1 N hDom

end LVConsensus.Paper
