import LVConsensus.Preliminaries

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus.Paper

/-- Paper `lemma:couple-with-independent`, both directions. -/
theorem lemma_couple_with_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat)
    (X Y : Fin n → Ω → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y μ) :
    (BernoulliConditionallyLE μ X Y →
      StochDom μ
        (fun ω => ∑ i : Fin n, if X i ω then (1 : Real) else 0)
        (fun ω => ∑ i : Fin n, if Y i ω then (1 : Real) else 0)) ∧
    (BernoulliConditionallyGE μ X Y →
      StochDom μ
        (fun ω => ∑ i : Fin n, if Y i ω then (1 : Real) else 0)
        (fun ω => ∑ i : Fin n, if X i ω then (1 : Real) else 0)) :=
  LVConsensus.lemma_couple_with_independent μ n X Y
    hXMeas hYMeas hYIndep

end LVConsensus.Paper
