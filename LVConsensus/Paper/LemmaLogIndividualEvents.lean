import LVConsensus.LogIndividualEvents

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Paper `lemma:log-individual-events`: logarithmically many individual
reactions before consensus, with a polynomial lower-tail bound. -/
theorem lemma_log_individual_events
    (v : LVVariant)
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (hGood : 0 < effectiveGoodRate v params)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∃ f g : ℝ, 0 < f ∧ 0 < g ∧
      ∀ (s0 : PopState) (m : ℕ),
        Nat.min s0.1 s0.2 = m → 0 < m →
          lvLabeledPathMeasure v params s0
              {ζ | labeledIndividualCountBeforeConsensus ζ <
                Nat.ceil (f * Real.log m)} ≤
            ENNReal.ofReal
              (Real.exp (-(g * Real.log m))) :=
  LVConsensus.lemma_log_individual_events_full
    v params hTheta hGood hGamma0 hGamma1

end LVConsensus.Paper
