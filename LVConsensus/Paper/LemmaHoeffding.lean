import LVConsensus.Preliminaries

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus.Paper

/-- Paper `lemma:hoeffding`, with the corrected constant. -/
theorem lemma_hoeffding
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Real)
    (hBound : ∀ i ω, X i ω ∈ Set.Icc (-1 : Real) 1)
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (t : Real) (ht : 0 ≤ t) :
    μ {ω |
        t ≤
          |(∑ i : Fin n, X i ω) -
            (∫ x, (∑ i : Fin n, X i x) ∂μ)|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(t ^ (2 : Nat)) / (2 * n))) :=
  LVConsensus.lemma_hoeffding μ n X hBound hMeas hIndep t ht

end LVConsensus.Paper
