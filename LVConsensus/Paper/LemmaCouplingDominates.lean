import LVConsensus.DominationCategoricalCoupling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus.Paper

/-- Paper `lem:coupling:dominates`, for the explicitly constructed
pseudo-coupling. -/
theorem lem_coupling_dominates
    (v : LVVariant)
    (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState)
    (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure
        v params hGamma0 hGamma1 N hDom z0 n0,
      ∀ t : Nat,
        Nat.min (ω t).1.1.1 (ω t).1.1.2 ≤ (ω t).2 ∧
          pseudoBadCountUpTo v ω t ≤
            birthsUpTo (fun i => (ω i).2) t := by
  filter_upwards [
    lvPseudoCouplingPathMeasure_min_le
      v params hGamma0 hGamma1 N hDom z0 n0 hStart,
    lvPseudoCouplingPathMeasure_bad_le_births
      v params hGamma0 hGamma1 N hDom z0 n0
  ] with ω hmin hbad
  exact fun t => ⟨hmin t, hbad t⟩

end LVConsensus.Paper
