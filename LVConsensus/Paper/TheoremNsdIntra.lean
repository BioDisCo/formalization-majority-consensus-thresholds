import LVConsensus.NsdIntra

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
  exact
    ⟨LVConsensus.thm_nsd_intra_part1_general
        params hAlpha hNeutral hEq0 hEq1
          a b hposA hposB hba,
      LVConsensus.thm_nsd_intra_full_general
        params hAlpha hNeutral hEq0 hEq1
          a b hposA hposB hba⟩

end LVConsensus.Paper
