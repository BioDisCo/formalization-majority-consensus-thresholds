import LVConsensus.Preliminaries

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus.Paper

/-- Paper `lemma:hoeffding`. -/
theorem lemma_hoeffding
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Real)
    (hBound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : Real) 1)
    (hMeas : AEMeasurable X μ)
    (hMean : ∫ ω, X ω ∂μ ≤ 0)
    (lam : Real) (hlam : 0 ≤ lam) :
    mgf X μ lam ≤ Real.exp (lam ^ (2 : Nat) / 2) :=
  LVConsensus.lemma_hoeffding_mgf μ X hBound hMeas hMean lam hlam

end LVConsensus.Paper
