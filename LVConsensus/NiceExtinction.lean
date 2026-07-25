import LVConsensus.Definitions
import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LVConsensus

/-- A nearest-neighbour birth--death chain cannot reach `0` from `n` in fewer
than `n` steps. -/
lemma kernelIter_bdKernel_zero_before
    (N : BirthDeathChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)] :
    ∀ n t : Nat, t < n → (kernelIter (bdKernel N) t) n {0} = 0 := by
  intro n t
  induction t generalizing n with
  | zero =>
      intro h
      simp [kernelIter_zero, ProbabilityTheory.Kernel.id_apply,
        show n ≠ 0 by omega]
  | succ t ih =>
      intro h
      have hstep :
          (kernelIter (bdKernel N) (t + 1)) n {0} =
            ∫⁻ j, (kernelIter (bdKernel N) t) j {0} ∂(bdKernel N) n := by
        have :
            (kernelIter (bdKernel N) (t + 1)) n {0} =
              ((bdKernel N) n).bind
                (fun j => (kernelIter (bdKernel N) t) j) {0} := by
          rw [kernelIter_succ_right]
          rfl
        rw [this, Measure.bind_apply (measurableSet_singleton 0)
          (ProbabilityTheory.Kernel.measurable _).aemeasurable]
      rw [hstep, bdKernel_apply,
        lintegral_add_measure, lintegral_add_measure,
        lintegral_smul_measure, lintegral_smul_measure,
        lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
        lintegral_dirac]
      rw [ih (n + 1) (by omega), ih (n - 1) (by omega), ih n (by omega)]
      simp

/-- If extinction is almost sure, its expected time is at least the initial
population, since every transition decreases the population by at most one. -/
lemma expectedExtinctionTime_ge_start
    (N : BirthDeathChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)]
    (n : Nat)
    (hExtinct :
      bdPathMeasure N n {ω | extinctionTime ω = ⊤} = 0) :
    (n : ENNReal) ≤ expectedExtinctionTime N n := by
  let P := bdPathMeasure N n
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold bdPathMeasure homogeneousPathMeasure
    infer_instance
  let early : Set (Nat → Nat) :=
    ⋃ j : Fin n, {ω | ω j.1 = 0}
  have hEarly : P early = 0 := by
    apply measure_iUnion_null
    intro j
    change bdPathMeasure N n {ω | ω j.1 ∈ ({0} : Set Nat)} = 0
    rw [bdPathMeasure_coord_eq N n j.1 ({0} : Set Nat)
      (measurableSet_singleton 0)]
    exact kernelIter_bdKernel_zero_before N n j.1 j.2
  have hFiniteAE :
      ∀ᵐ ω ∂P, ω ∈ ({ω | extinctionTime ω = ⊤} : Set (Nat → Nat))ᶜ :=
    compl_mem_ae_iff.mpr hExtinct
  have hNoEarlyAE : ∀ᵐ ω ∂P, ω ∈ earlyᶜ :=
    compl_mem_ae_iff.mpr hEarly
  have hPoint : ∀ᵐ ω ∂P, n ≤ (extinctionTime ω).untopD 0 := by
    filter_upwards [hFiniteAE, hNoEarlyAE] with ω hFinite hNoEarly
    change extinctionTime ω ≠ ⊤ at hFinite
    change ω ∉ early at hNoEarly
    cases hτ : extinctionTime ω with
    | top => exact (hFinite hτ).elim
    | coe m =>
        simp only [WithTop.untopD_coe]
        by_contra hnm
        have hm : m < n := Nat.lt_of_not_ge hnm
        obtain ⟨j, hjm, hj0⟩ :=
          ext_time_hit_exists ω m (by simp [hτ])
        have hjn : j < n := hjm.trans_lt hm
        apply hNoEarly
        exact Set.mem_iUnion.mpr ⟨⟨j, hjn⟩, hj0⟩
  unfold expectedExtinctionTime
  calc
    (n : ENNReal) = ∫⁻ _ω, (n : ENNReal) ∂P := by simp [P]
    _ ≤ ∫⁻ ω, (((extinctionTime ω).untopD 0 : Nat) : ENNReal) ∂P :=
      lintegral_mono_ae (hPoint.mono fun _ h => by exact_mod_cast h)

/-- Paper `lemma:nice-extinction`: expected extinction time is `Θ(n)`. -/
theorem lemma_nice_extinction
    (N : NiceChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    IsThetaEventually
      (fun n => (expectedExtinctionTime N.toBirthDeathChain n).toReal)
      (fun n => (n : Real)) := by
  obtain ⟨n₀, hn₀⟩ := nice_drift_neg N
  have hD2 : (0 : ℝ) < N.D / 2 := half_pos N.D_pos
  have hDrift : ∀ n, n₀ ≤ n → 0 < n →
      N.toBirthDeathChain.p n - N.toBirthDeathChain.q n ≤ -(N.D / 2) := by
    intro n hn hpos
    have := hn₀ n hn hpos
    linarith
  obtain ⟨C, hC, hbound⟩ :=
    bd_expected_extinction_linear_ennreal N.toBirthDeathChain
      (N.D / 2) hD2 n₀ hDrift N.D N.D_pos N.q_ge
  have hExtinct : ∀ n : Nat,
      bdPathMeasure N.toBirthDeathChain n
        {ω | extinctionTime ω = ⊤} = 0 := by
    intro n
    exact bd_extinction_almost_sure N.toBirthDeathChain
      (N.D / 2) hD2 n₀ hDrift N.D N.D_pos N.q_ge n
  constructor
  · refine ⟨C, 0, hC, ?_⟩
    intro n _
    have hne : expectedExtinctionTime N.toBirthDeathChain n ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound n)
    rw [← ENNReal.toReal_ofReal (mul_nonneg hC (Nat.cast_nonneg n))]
    exact (ENNReal.toReal_le_toReal hne ENNReal.ofReal_ne_top).mpr (hbound n)
  · refine ⟨1, 0, one_pos, ?_⟩
    intro n _
    have hlow :=
      expectedExtinctionTime_ge_start N.toBirthDeathChain n (hExtinct n)
    have hne : expectedExtinctionTime N.toBirthDeathChain n ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound n)
    have hreal :=
      (ENNReal.toReal_le_toReal (by simp : (n : ENNReal) ≠ ⊤) hne).mpr hlow
    simpa using hreal

end LVConsensus
