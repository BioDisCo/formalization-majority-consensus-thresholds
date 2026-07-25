import LVConsensus.IdenticalGapFail

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:identical-gap-fail`, exact displayed form. -/
theorem lemma_identical_gap_fail
    (v : LVVariant)
    (params : LVParams)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    (s0 : PopState) :
    ENNReal.ofReal (1 / 2) *
        (lvPathMeasure v params s0)
          {ω | ∃ t : Nat,
            (t : WithTop Nat) < consensusTime ω ∧ gap (ω t) = 0} ≤
      1 - majorityConsensusProb v params s0 :=
  LVConsensus.lemma_identical_gap_fail_full
    v params hNeutralAlpha hNeutralGamma s0

end LVConsensus.Paper
