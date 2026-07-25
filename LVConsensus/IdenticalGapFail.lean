import LVConsensus.SwapInvariance
import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus

/-- Full paper `lemma:identical-gap-fail`.

    For identical species, failure has probability at least one half of the
    probability that the chain visits a positive diagonal.  The paper's event
    `∃ t < T, Δₜ = 0` is a subset of the positive-diagonal event used here. -/
theorem lemma_identical_gap_fail_paper
    (v : LVVariant)
    (params : LVParams)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    (s0 : PopState)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    ENNReal.ofReal (1 / 2) *
        (lvPathMeasure v params s0)
          {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} ≤
      (lvPathMeasure v params s0)
        {ω | ¬majorityConsensusEvent s0 ω} := by
  let μ := lvPathMeasure v params s0
  let MC : Set (ℕ → PopState) := {ω | majorityConsensusEvent s0 ω}
  let D : Set (ℕ → PopState) :=
    {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold lvPathMeasure homogeneousPathMeasure
    infer_instance
  have hMC_meas : MeasurableSet MC := by
    simpa [MC] using measurableSet_majorityConsensusEvent s0
  have hD_meas : MeasurableSet D := by
    have hD_eq :
        D = ⋃ k : ℕ,
          (fun ω : ℕ → PopState => ω k) ⁻¹'
            {s : PopState | s.1 = s.2 ∧ 0 < s.1} := by
      ext ω
      simp [D]
    rw [hD_eq]
    exact MeasurableSet.iUnion fun k =>
      (measurable_pi_apply k) (DiscreteMeasurableSpace.forall_measurableSet _)
  have hNR0 : ∀ t, μ {ω | (ω t).1 = 0 ∧ (ω (t + 1)).1 ≠ 0} = 0 := by
    intro t
    simpa [μ] using lv_path_species0_dead_forward v params s0 t 1
  have hNR1 : ∀ t, μ {ω | (ω t).2 = 0 ∧ (ω (t + 1)).2 ≠ 0} = 0 := by
    intro t
    simpa [μ] using lv_path_species1_dead_forward v params s0 t 1
  have hcap : μ (MC ∩ D) ≤ ENNReal.ofReal (1 / 2) * μ D := by
    simpa [μ, MC, D] using
      mc_cap_any_diagonal_le_half_mul v params s0 s0
        hNeutralAlpha hNeutralGamma hNR0 hNR1
  have hMC_bound :
      μ MC ≤ ENNReal.ofReal (1 / 2) * μ D + μ Dᶜ := by
    calc
      μ MC ≤ μ ((MC ∩ D) ∪ (MC ∩ Dᶜ)) := by
        apply measure_mono
        intro ω hω
        by_cases hDω : ω ∈ D
        · exact Or.inl ⟨hω, hDω⟩
        · exact Or.inr ⟨hω, hDω⟩
      _ ≤ μ (MC ∩ D) + μ (MC ∩ Dᶜ) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 2) * μ D + μ Dᶜ :=
        add_le_add hcap (measure_mono Set.inter_subset_right)
  have hhalf_add :
      ENNReal.ofReal (1 / 2) * μ D + ENNReal.ofReal (1 / 2) * μ D = μ D := by
    rw [← add_mul]
    have hhalf : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    rw [hhalf, one_mul]
  have hsum :
      ENNReal.ofReal (1 / 2) * μ D + μ MC ≤ 1 := by
    calc
      ENNReal.ofReal (1 / 2) * μ D + μ MC
          ≤ ENNReal.ofReal (1 / 2) * μ D +
              (ENNReal.ofReal (1 / 2) * μ D + μ Dᶜ) := by
            simpa only [add_comm] using
              add_le_add_right hMC_bound (ENNReal.ofReal (1 / 2) * μ D)
      _ = μ D + μ Dᶜ := by rw [← add_assoc, hhalf_add]
      _ = 1 := by
        rw [measure_compl hD_meas (measure_ne_top μ D), measure_univ, add_comm,
          tsub_add_cancel_of_le (prob_le_one : μ D ≤ 1)]
  have hfailure :
      ENNReal.ofReal (1 / 2) * μ D ≤ 1 - μ MC :=
    ENNReal.le_sub_of_add_le_right (measure_ne_top μ MC) hsum
  change ENNReal.ofReal (1 / 2) * μ D ≤ μ MCᶜ
  rw [measure_compl hMC_meas (measure_ne_top μ MC), measure_univ]
  exact hfailure

/-- Exact displayed form of paper `lemma:identical-gap-fail`:
    `1 - ρ(S) ≥ (1/2) P[∃ t < T(S), Δₜ = 0]`. -/
theorem lemma_identical_gap_fail_full
    (v : LVVariant)
    (params : LVParams)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    (s0 : PopState)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    ENNReal.ofReal (1 / 2) *
        (lvPathMeasure v params s0)
          {ω | ∃ t : ℕ, (t : WithTop ℕ) < consensusTime ω ∧ gap (ω t) = 0} ≤
      1 - majorityConsensusProb v params s0 := by
  let μ := lvPathMeasure v params s0
  let MC : Set (ℕ → PopState) := {ω | majorityConsensusEvent s0 ω}
  let Dpaper : Set (ℕ → PopState) :=
    {ω | ∃ t : ℕ, (t : WithTop ℕ) < consensusTime ω ∧ gap (ω t) = 0}
  let D : Set (ℕ → PopState) :=
    {ω | ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1}
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold lvPathMeasure homogeneousPathMeasure
    infer_instance
  have hsub : Dpaper ⊆ D := by
    intro ω hω
    rcases hω with ⟨t, ht, hgap⟩
    have hnot : ¬reachedConsensus (ω t) := by
      intro hrc
      have hle : consensusTime ω ≤ (t : WithTop ℕ) :=
        consensusTime_le_of_reached' ω t hrc
      exact (not_le_of_gt ht) hle
    have heq : (ω t).1 = (ω t).2 := by
      simp only [gap] at hgap
      omega
    have hpos : 0 < (ω t).1 := by
      simp only [reachedConsensus] at hnot
      exact Nat.pos_of_ne_zero (fun hzero => hnot (Or.inl hzero))
    exact ⟨t, heq, hpos⟩
  have hmono :
      ENNReal.ofReal (1 / 2) * μ Dpaper ≤ ENNReal.ofReal (1 / 2) * μ D :=
    mul_le_mul_left' (measure_mono hsub) _
  have hstrong :
      ENNReal.ofReal (1 / 2) * μ D ≤ μ MCᶜ := by
    change ENNReal.ofReal (1 / 2) * μ D ≤
      μ {ω | ¬majorityConsensusEvent s0 ω}
    simpa [μ, D] using
      lemma_identical_gap_fail_paper v params hNeutralAlpha hNeutralGamma s0
  have hle : ENNReal.ofReal (1 / 2) * μ Dpaper ≤ μ MCᶜ :=
    hmono.trans hstrong
  have hMC_meas : MeasurableSet MC := by
    simpa [MC] using measurableSet_majorityConsensusEvent s0
  change ENNReal.ofReal (1 / 2) * μ Dpaper ≤ 1 - μ MC
  rw [← measure_univ (μ := μ), ← measure_compl hMC_meas (measure_ne_top μ MC)]
  exact hle

end LVConsensus
