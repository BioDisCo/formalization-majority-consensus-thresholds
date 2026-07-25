import LVConsensus.DominationCategoricalCoupling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel

namespace LVConsensus.Paper

/-- Paper `lemma:delayed-coupling` for the explicitly constructed
pseudo-coupling.  Every active time exists almost surely, and sampling the
left coordinate at active times has the law of the LV path stopped at its
first consensus state. -/
theorem lemma_delayed_coupling
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (s0 : PopState) (n₀ : Nat)
    (hStart : Nat.min s0.1 s0.2 ≤ n₀)
    (hExtinct :
      bdPathMeasure N n₀
        {η | extinctionTime η = ⊤} = 0) :
    let P := lvPseudoCouplingPathMeasure
      v params hGamma0 hGamma1 N hDom (s0, .idle) n₀
    let R := lvLabeledPathMeasure v params s0
    (∀ᵐ ω ∂ P, ∀ k : Nat,
      ∃ t : Nat, pseudoKthActiveAt k t ω) ∧
    P.map pseudoEmbeddedLabeledPath =
      R.map (pathStoppedAt labeledConsensusSet) := by
  dsimp only
  let P := lvPseudoCouplingPathMeasure
    v params hGamma0 hGamma1 N hDom (s0, .idle) n₀
  let R := lvLabeledPathMeasure v params s0
  constructor
  · have hinfinite :
        ∀ᵐ ω ∂ P, ∀ start, ∃ t, start ≤ t ∧
          isPseudoActive (ω t) := by
      filter_upwards [
        lvPseudoCouplingPathMeasure_min_le
          v params hGamma0 hGamma1 N hDom
            (s0, .idle) n₀ hStart,
        lvPseudoCouplingPathMeasure_aux_eventually_zero
          v params hGamma0 hGamma1 N hDom
            (s0, .idle) n₀ hExtinct] with
          ω hminor heventually
      intro start
      obtain ⟨t, hst, hzero⟩ :=
        heventually start
      refine ⟨t, hst, ?_⟩
      unfold isPseudoActive
      have hle := hminor t
      omega
    filter_upwards [hinfinite] with ω hω
    exact pseudoKthActiveAt_exists ω hω
  · calc
      P.map pseudoEmbeddedLabeledPath =
          homogeneousPathMeasure
            (Measure.dirac (s0, .idle))
            (lvStoppedLabeledKernel v params) := by
        exact lvPseudoCouplingPathMeasure_map_embedded
          v params hGamma0 hGamma1 N hDom
            (s0, .idle) n₀ hStart hExtinct
      _ = R.map
          (pathStoppedAt labeledConsensusSet) := by
        exact
          (lvLabeledPathMeasure_map_stopped
            v params s0).symm

end LVConsensus.Paper
