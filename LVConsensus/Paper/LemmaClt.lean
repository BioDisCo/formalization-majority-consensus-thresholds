import LVConsensus.Preliminaries

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus.Paper

/-- Paper `lemma:clt`. -/
theorem lemma_clt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Nat → Ω → Real)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : Real) 1)
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hVar : ∀ i, variance (X i) μ = 1)
    (ε : Real) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ θ : Real, 0 < θ ∧ ∃ n₀ : Nat, ∀ n, n₀ ≤ n →
      ENNReal.ofReal (1 - ε) ≤ μ {ω | ∃ k ∈ Finset.range (n + 1),
        θ * Real.sqrt n ≤ ∑ i ∈ Finset.range k, X i ω} :=
  LVConsensus.lemma_clt μ X hBound hMeas hIndep hIdent hMean hVar
    (1 - ε) (sub_pos.mpr hε1) (by linarith)

end LVConsensus.Paper
