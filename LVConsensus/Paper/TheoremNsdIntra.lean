import LVConsensus.LineageFixation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Corrected paper `thm:nsd-intra`, including both the conditional identity
and its almost-sure-consensus specialization. -/
theorem theorem_nsd_intra
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a) :
    (0 < lvPathMeasure .nonSelfDestructive params (a, b)
          {ω | consensusReachedEvent ω} ∧
      majorityConsensusProb
          LVVariant.nonSelfDestructive params (a, b) =
        ENNReal.ofReal ((a : Real) / (a + b)) *
          lvPathMeasure .nonSelfDestructive params (a, b)
            {ω | consensusReachedEvent ω}) ∧
    (lvPathMeasure .nonSelfDestructive params (a, b)
          {ω | consensusReachedEvent ω} = 1 ∧
      majorityConsensusProb
          LVVariant.nonSelfDestructive params (a, b) =
        ENNReal.ofReal ((a : Real) / (a + b))) := by
  have hGamma0 : 0 < params.gamma0 := by
    rw [hEq0]
    positivity
  have hGamma1 : 0 < params.gamma1 := by
    rw [hEq1, ← hNeutral]
    positivity
  have hAlphaSum : 0 < params.alpha0 + params.alpha1 := by
    rw [← hNeutral]
    linarith
  have hcons :=
    LVConsensus.nsd_consensus_almost_sure_general params
      hGamma0 hGamma1 hAlphaSum a b hposA hposB
      hAlpha hNeutral hEq0 hEq1
  have hprob :=
    LVConsensus.nsd_majority_probability_via_lineages
      params hAlpha hNeutral hEq0 hEq1
      a b hposA hposB hba
  refine ⟨⟨?_, ?_⟩, ⟨hcons, hprob⟩⟩
  · rw [hcons]
    exact zero_lt_one
  · rw [hprob, hcons, mul_one]

end LVConsensus.Paper
