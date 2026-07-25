import LVConsensus.NiceUpperDomination

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Paper theorem `thm:nice-upper-domination`, with the dominating nice chain
constructed from the LV parameters rather than supplied as a hypothesis. -/
theorem theorem_nice_upper_domination
    (v : LVVariant)
    (params : LVParams)
    (hAlpha : 0 < min params.alpha0 params.alpha1)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s0 : PopState, 0 < s0.1 + s0.2 →
      expectedConsensusTimeTail v params s0 ≤
        ENNReal.ofReal (C * (s0.1 + s0.2))) ∧
    (∀ k : ℕ, ∃ C n₀ : ℕ, 0 < C ∧ ∀ s0 : PopState,
      n₀ ≤ s0.1 + s0.2 →
        consensusTail v params s0 (C * (s0.1 + s0.2)) ≤
          (((s0.1 + s0.2 + 1 : ℕ) : ℝ≥0∞) ^ k)⁻¹) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s0 : PopState, 0 < s0.1 + s0.2 →
      expectedLabeledBadCount v params s0 ≤
        ENNReal.ofReal (C * logScale (s0.1 + s0.2))) ∧
    (∀ k : ℕ, ∃ C n₀ : ℕ, 0 < C ∧ ∀ s0 : PopState,
      n₀ ≤ s0.1 + s0.2 →
        labeledBadTail v params s0
            (C * logSqScaleNat (s0.1 + s0.2)) ≤
          (((s0.1 + s0.2 + 1 : ℕ) : ℝ≥0∞) ^ k)⁻¹) := by
  have hGood : 0 < effectiveGoodRate v params := by
    cases v with
    | selfDestructive =>
        simp only [effectiveGoodRate]
        have h0 : 0 < params.alpha0 :=
          lt_of_lt_of_le hAlpha (min_le_left _ _)
        have h1 : 0 < params.alpha1 :=
          lt_of_lt_of_le hAlpha (min_le_right _ _)
        linarith
    | nonSelfDestructive =>
        simpa only [effectiveGoodRate] using hAlpha
  obtain ⟨N, hDom⟩ :=
    lemma_domination v params hGood hGamma0 hGamma1
  exact thm_nice_upper_domination
    v params hGamma0 hGamma1 N hDom

end LVConsensus.Paper
