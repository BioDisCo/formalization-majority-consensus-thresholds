import LVConsensus.Preliminaries
import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory

namespace LVConsensus

/-- Under neutral NSD parameters, gap-increasing and gap-decreasing transitions
have equal one-step probability at every interior state. -/
lemma nsd_gap_kernel_symmetric_unconditional
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (lvKernel .nonSelfDestructive params (a, b))
      {s : PopState | gap s = gap (a, b) + 1} =
    (lvKernel .nonSelfDestructive params (a, b))
      {s : PopState | gap s = gap (a, b) - 1} := by
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    have h1 : gap (a, b) ≠ gap (a, b) + 1 := by unfold gap; omega
    have h2 : gap (a, b) ≠ gap (a, b) - 1 := by unfold gap; omega
    simp [Measure.dirac_apply, h1, h2]
  · rw [lvKernel_nsd_apply params a b hφ]
    simp only [Measure.smul_apply, Measure.add_apply]
    have hg_b0_p : gap (a + 1, b) = gap (a, b) + 1 := by
      simp [gap]; omega
    have hg_b1_p : gap (a, b + 1) ≠ gap (a, b) + 1 := by
      simp [gap]; omega
    have hg_d0_p : gap (a - 1, b) ≠ gap (a, b) + 1 := by
      simp [gap]; omega
    have hg_d1_p : gap (a, b - 1) = gap (a, b) + 1 := by
      simp [gap]; omega
    have hg_b0_m : gap (a + 1, b) ≠ gap (a, b) - 1 := by
      simp [gap]; omega
    have hg_b1_m : gap (a, b + 1) = gap (a, b) - 1 := by
      simp [gap]; omega
    have hg_d0_m : gap (a - 1, b) = gap (a, b) - 1 := by
      simp [gap]; omega
    have hg_d1_m : gap (a, b - 1) ≠ gap (a, b) - 1 := by
      simp [gap]; omega
    have hd_b0_p : Measure.dirac (a + 1, b)
        {s : PopState | gap s = gap (a, b) + 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_b0_p])
    have hd_b1_p : Measure.dirac (a, b + 1)
        {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_b1_p]
    have hd_d0_p : Measure.dirac (a - 1, b)
        {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_d0_p]
    have hd_d1_p : Measure.dirac (a, b - 1)
        {s : PopState | gap s = gap (a, b) + 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_d1_p])
    have hd_b0_m : Measure.dirac (a + 1, b)
        {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_b0_m]
    have hd_b1_m : Measure.dirac (a, b + 1)
        {s : PopState | gap s = gap (a, b) - 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_b1_m])
    have hd_d0_m : Measure.dirac (a - 1, b)
        {s : PopState | gap s = gap (a, b) - 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_d0_m])
    have hd_d1_m : Measure.dirac (a, b - 1)
        {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_d1_m]
    rw [hBetaDelta, hNeutral, hGamma0, hGamma1]
    simp only [hd_b0_p, hd_b1_p, hd_d0_p, hd_d1_p, hd_b0_m,
      hd_b1_m, hd_d0_m, hd_d1_m, smul_eq_mul, mul_one, mul_zero]
    ring

end LVConsensus
