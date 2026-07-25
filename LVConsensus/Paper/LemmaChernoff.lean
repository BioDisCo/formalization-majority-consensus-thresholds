import LVConsensus.Preliminaries

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus.Paper

/-- Paper `lemma:chernoff`. -/
theorem lemma_chernoff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Bool) (S : Ω → Real)
    (hRep : ∀ ω, S ω = ∑ i : Fin n, if X i ω then (1 : Real) else 0)
    (hXMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ) :
    (∀ ε : Real, 0 < ε →
      μ {ω | S ω ≥ (1 + ε) * (∫ x, S x ∂μ)} ≤
        ENNReal.ofReal
          (Real.exp (-(∫ x, S x ∂μ) * ε ^ (2 : Nat) / (2 + ε)))) ∧
    (∀ ε : Real, 0 < ε → ε < 1 →
      μ {ω | S ω ≤ (1 - ε) * (∫ x, S x ∂μ)} ≤
        ENNReal.ofReal
          (Real.exp (-(∫ x, S x ∂μ) * ε ^ (2 : Nat) / 2))) :=
  LVConsensus.lemma_chernoff μ n X S hRep hXMeas hIndep

end LVConsensus.Paper
