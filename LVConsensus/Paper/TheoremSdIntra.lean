import LVConsensus.SdIntra

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Corrected paper `thm:sd-intra`: the martingale identity including the
draw event, together with the majority-probability upper bound. -/
theorem theorem_sd_intra
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    (hab3 : 3 ≤ a + b) :
    (majorityConsensusProb
          LVVariant.selfDestructive params (a, b) +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure
            LVVariant.selfDestructive params (a, b)
              {ω | drawAtConsensusEvent ω} =
        ENNReal.ofReal
          ((a : Real) / (a + b : Real))) ∧
      majorityConsensusProb
          LVVariant.selfDestructive params (a, b) ≤
        ENNReal.ofReal
          ((a : Real) / (a + b : Real)) :=
  ⟨LVConsensus.thm_sd_intra_part1
      params hAlpha hNeutral hEq0 hEq1
        a b hposA hposB hba hab3,
    LVConsensus.thm_sd_intra_part2
      params hAlpha hNeutral hEq0 hEq1
        a b hposA hposB hba hab3⟩

end LVConsensus.Paper
