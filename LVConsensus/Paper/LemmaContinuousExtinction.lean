import LVConsensus.ContinuousTimeExtinction

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:continuous-extinction`, with the necessary explicit
hypothesis that every positive state has a positive downward rate. -/
theorem lemma_continuous_extinction
    (M : ContinuousTimeBirthDeathChain)
    (hRates : HasAtMostLinearBirthQuadraticDeathRates M) :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ m : Nat, ctMeanAbsorptionTime M m ≤ C :=
  LVConsensus.lemma_continuous_extinction_of_bounds M hRates

end LVConsensus.Paper
