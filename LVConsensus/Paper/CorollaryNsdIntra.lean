import LVConsensus.IntraCorollary

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-- Corrected paper `cor:nsd-intra`, for arbitrary common demographic
rates. -/
theorem corollary_nsd_intra
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe0 : 2 * params.alpha0 ≤ params.gamma0)
    (hGe1 : 2 * params.alpha1 ≤ params.gamma1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a) :
    lvPathMeasure .nonSelfDestructive params (a, b)
          {ω | consensusReachedEvent ω} = 1 ∧
      majorityConsensusProb
          LVVariant.nonSelfDestructive params (a, b) ≤
        ENNReal.ofReal ((a : Real) / (a + b)) :=
  LVConsensus.cor_nsd_intra_full
    params hAlpha hNeutral hGamma hGe0 hGe1
      a b hposA hposB hba

end LVConsensus.Paper
