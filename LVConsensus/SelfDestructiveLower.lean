import LVConsensus.Preliminaries
import LVConsensus.SwapInvariance
import LVConsensus.MarkovLib
import LVConsensus.ProofHelpers

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LVConsensus

/-! ## SD gap symmetry: P(gap+1) = P(gap-1) under neutral parameters -/

/-- Under neutral SD (α₀=α₁, β=δ, γ=0), the kernel assigns equal weight to
    gap-increasing and gap-decreasing transitions.
    Gap +1: Birth0 (β·a) + Death1 (β·b) = β(a+b)
    Gap -1: Birth1 (β·b) + Death0 (β·a) = β(a+b)
    Inter events go to (a-1,b-1) with gap unchanged. -/
private lemma sd_gap_kernel_symmetric
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (lvKernel .selfDestructive params (a, b))
      {s : PopState | gap s = gap (a, b) + 1} =
    (lvKernel .selfDestructive params (a, b))
      {s : PopState | gap s = gap (a, b) - 1} := by
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    have h1 : gap (a, b) ≠ gap (a, b) + 1 := by unfold gap; omega
    have h2 : gap (a, b) ≠ gap (a, b) - 1 := by unfold gap; omega
    simp [Measure.dirac_apply, h1, h2]
  · rw [lvKernel_sd_apply params a b hφ]
    simp only [Measure.smul_apply, Measure.add_apply]
    -- Gap computations for each target state
    have hg_b0_p : gap (a + 1, b) = gap (a, b) + 1 := by simp [gap]; omega
    have hg_b1_p : gap (a, b + 1) ≠ gap (a, b) + 1 := by simp [gap]; omega
    have hg_d0_p : gap (a - 1, b) ≠ gap (a, b) + 1 := by simp [gap]; omega
    have hg_d1_p : gap (a, b - 1) = gap (a, b) + 1 := by simp [gap]; omega
    have hg_int_p : gap (a - 1, b - 1) ≠ gap (a, b) + 1 := by simp [gap]; omega
    -- Gap -1 targets
    have hg_b0_m : gap (a + 1, b) ≠ gap (a, b) - 1 := by simp [gap]; omega
    have hg_b1_m : gap (a, b + 1) = gap (a, b) - 1 := by simp [gap]; omega
    have hg_d0_m : gap (a - 1, b) = gap (a, b) - 1 := by simp [gap]; omega
    have hg_d1_m : gap (a, b - 1) ≠ gap (a, b) - 1 := by simp [gap]; omega
    have hg_int_m : gap (a - 1, b - 1) ≠ gap (a, b) - 1 := by simp [gap]; omega
    -- Intra terms vanish since γ = 0
    -- (no need to analyze gap direction for these)
    -- Dirac evaluations for gap+1
    have hd_b0_p : Measure.dirac (a + 1, b) {s : PopState | gap s = gap (a, b) + 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_b0_p])
    have hd_b1_p : Measure.dirac (a, b + 1) {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_b1_p]
    have hd_d0_p : Measure.dirac (a - 1, b) {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_d0_p]
    have hd_d1_p : Measure.dirac (a, b - 1) {s : PopState | gap s = gap (a, b) + 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_d1_p])
    have hd_int_p : Measure.dirac (a - 1, b - 1) {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_int_p]
    -- Dirac evaluations for gap-1
    have hd_b0_m : Measure.dirac (a + 1, b) {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_b0_m]
    have hd_b1_m : Measure.dirac (a, b + 1) {s : PopState | gap s = gap (a, b) - 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_b1_m])
    have hd_d0_m : Measure.dirac (a - 1, b) {s : PopState | gap s = gap (a, b) - 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_d0_m])
    have hd_d1_m : Measure.dirac (a, b - 1) {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_d1_m]
    have hd_int_m : Measure.dirac (a - 1, b - 1) {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_int_m]
    -- Substitute β = δ, α₀ = α₁, γ₀ = γ₁ = 0 and simplify
    -- Intra terms vanish (γ = 0), inter terms have gap unchanged, only birth/death matter
    rw [hBetaDelta, hNeutral, hGamma0, hGamma1]
    simp only [hd_b0_p, hd_b1_p, hd_d0_p, hd_d1_p, hd_int_p,
      hd_b0_m, hd_b1_m, hd_d0_m, hd_d1_m, hd_int_m,
      smul_eq_mul, mul_one, mul_zero, zero_mul, ENNReal.ofReal_zero, zero_smul]
    ring

/-- The unconditional one-step estimate used in the paper's
`lemma:log-individual-events`.  The further stopped-level coupling needed for
the logarithmic pathwise conclusion is intentionally not asserted here. -/
theorem lemma_log_individual_events
    (v : LVVariant)
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (hAlpha : 0 < params.alpha0 + params.alpha1)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    ∀ a b : Nat, 0 < b → b ≤ a →
      ENNReal.ofReal
          ((params.beta + params.delta) /
            ((params.alpha0 + params.alpha1) * b +
              2 * (params.beta + params.delta))) ≤
        (lvKernel v params (a, b))
          {s |
            (s.1 = a + 1 ∧ s.2 = b) ∨
            (s.1 = a ∧ s.2 = b + 1) ∨
            (s.1 = a - 1 ∧ s.2 = b) ∨
            (s.1 = a ∧ s.2 = b - 1)} := by
  clear hAlpha
  intro a b hb hab
  exact lvKernel_indiv_event_prob_lb v params a b hab hb
    hGamma0 hGamma1 hTheta

/-- Once the SD chain reaches diagonal `(m,m)` with `m > 0`, the Markov
property and swap invariance give
`P(MC ∩ diagonal_reached) ≤ (1/2) P(diagonal_reached)`. -/
private lemma sd_mc_cap_diagonal_le_half_mul
    (params : LVParams)
    (_hNeutral : params.alpha0 = params.alpha1)
    (_hGamma0 : params.gamma0 = 0)
    (_hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)]
    (a b : Nat) (_hb : 0 < b) (_hab : b ≤ a) :
    (lvPathMeasure LVVariant.selfDestructive params (a, b))
      ({ω | majorityConsensusEvent (a, b) ω} ∩
        {ω | ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1}) ≤
      ENNReal.ofReal (1 / 2) *
        (lvPathMeasure LVVariant.selfDestructive params (a, b))
          {ω | ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
  exact mc_cap_any_diagonal_le_half_mul _ params (a, b) (a, b) _hNeutral
    (by rw [_hGamma0, _hGamma1])
    (fun t => sd_path_no_revival_species0_general params (a, b) t)
    (fun t => sd_path_no_revival_species1_general params (a, b) t)
private lemma measurableSet_diagonal_reach_unbounded :
    MeasurableSet {ω : ℕ → PopState |
      ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
  rw [show {ω : ℕ → PopState | ∃ t, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} =
    ⋃ t : ℕ, ((fun ω : ℕ → PopState => ω t) ⁻¹'
      {s : PopState | s.1 = s.2 ∧ 0 < s.1}) from by
        ext ω; simp [Set.mem_iUnion]]
  exact MeasurableSet.iUnion fun t =>
    (measurable_pi_apply t) (DiscreteMeasurableSpace.forall_measurableSet _)

theorem thm_self_destructive_lower
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    ∀ a b : Nat, 0 < b → b ≤ a →
      majorityConsensusProb LVVariant.selfDestructive params (a, b) ≤
        ENNReal.ofReal (1 / 2) +
          ENNReal.ofReal (1 / 2) *
            lvPathMeasure LVVariant.selfDestructive params (a, b)
              {ω | ¬∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
  intro a b hb hab
  let μ := lvPathMeasure LVVariant.selfDestructive params (a, b)
  let mcE := {ω : ℕ → PopState | majorityConsensusEvent (a, b) ω}
  let diagE :=
    {ω : ℕ → PopState | ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1}
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hdiag_meas : MeasurableSet diagE :=
    measurableSet_diagonal_reach_unbounded
  have h_mc_diag :
      μ (mcE ∩ diagE) ≤ ENNReal.ofReal (1 / 2) * μ diagE :=
    sd_mc_cap_diagonal_le_half_mul params hNeutral hGamma0 hGamma1 a b hb hab
  have h_split : μ mcE = μ (mcE ∩ diagE) + μ (mcE \ diagE) :=
    (measure_inter_add_diff mcE hdiag_meas).symm
  have h_diff_le : μ (mcE \ diagE) ≤ μ diagEᶜ :=
    measure_mono fun _ h => h.2
  have hprob : μ diagE + μ diagEᶜ = 1 := by
    simpa only [measure_univ] using
      measure_add_measure_compl hdiag_meas (μ := μ)
  have hhalf :
      ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    calc
      ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) =
          ENNReal.ofReal ((1 / 2 : ℝ) + 1 / 2) :=
        (ENNReal.ofReal_add
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
      _ = 1 := by norm_num
  change μ mcE ≤
    ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) * μ diagEᶜ
  rw [h_split]
  refine (add_le_add h_mc_diag h_diff_le).trans ?_
  calc
    ENNReal.ofReal (1 / 2) * μ diagE + μ diagEᶜ =
        ENNReal.ofReal (1 / 2) * μ diagE +
          (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2)) *
            μ diagEᶜ := by rw [hhalf, one_mul]
    _ = ENNReal.ofReal (1 / 2) * (μ diagE + μ diagEᶜ) +
          ENNReal.ofReal (1 / 2) * μ diagEᶜ := by ring
    _ = ENNReal.ofReal (1 / 2) +
          ENNReal.ofReal (1 / 2) * μ diagEᶜ := by
            rw [hprob, mul_one]
    _ ≤ ENNReal.ofReal (1 / 2) +
          ENNReal.ofReal (1 / 2) * μ diagEᶜ := le_rfl

end LVConsensus
