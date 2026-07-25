import LVConsensus.DominationCategoricalCoupling
import LVConsensus.NiceWhpExtinction

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus

private lemma birthTail_tsum_eq_expected
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    ∑' t : ℕ, birthTail N n (t + 1) =
      expectedBirthsBeforeExtinction N n := by
  unfold expectedBirthsBeforeExtinction
  rw [lintegral_nat_eq_tsum_meas_gt
    (bdPathMeasure N n) birthsBeforeExtinction
    measurable_birthsBeforeExtinction]
  apply tsum_congr
  intro t
  unfold birthTail
  congr 1

private lemma nice_birth_tail_tsum_log_uniform
    (N : NiceChain)
    [IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, 1 ≤ n → m ≤ n →
      (∑' t : ℕ, birthTail N.toBirthDeathChain m (t + 1)) ≤
        ENNReal.ofReal (C * logScale n) := by
  obtain ⟨A, hA, hmean⟩ :=
    expectedBirthsBeforeExtinction_ennreal_le
      N.toBirthDeathChain N.C N.D N.C_pos N.D_pos N.p_le N.q_ge
  let L : ℝ := 1 + 1 / Real.log 2
  let C : ℝ := A.toReal * (N.C / N.D) * L
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  refine ⟨C, by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg ENNReal.toReal_nonneg
        (div_nonneg N.C_pos.le N.D_pos.le)) hL, ?_⟩
  intro n m hn hm
  rw [birthTail_tsum_eq_expected]
  refine (hmean m).trans ?_
  have hlogm : Real.log m ≤ logScale n := by
    by_cases hm0 : m = 0
    · subst m
      simp [logScale]
      exact Real.log_nonneg (by norm_num)
    · unfold logScale
      apply Real.log_le_log
      · exact_mod_cast (Nat.pos_of_ne_zero hm0)
      · exact_mod_cast (hm.trans (Nat.le_add_right n 1))
  have hlogn : Real.log 2 ≤ logScale n := by
    unfold logScale
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 2 ≤ n + 1 by omega)
  have hone : 1 ≤ (1 / Real.log 2) * logScale n := by
    calc
      1 = (1 / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (1 / Real.log 2) * logScale n :=
        mul_le_mul_of_nonneg_left hlogn (by positivity)
  have hreal :
      A.toReal * (N.C / N.D) * (Real.log m + 1) ≤
        C * logScale n := by
    have hratio : 0 < N.C / N.D := div_pos N.C_pos N.D_pos
    have hAnn : 0 ≤ A.toReal := ENNReal.toReal_nonneg
    have hscale :
        Real.log m + 1 ≤ L * logScale n := by
      dsimp [L]
      nlinarith
    dsimp [C]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hscale
        (mul_nonneg hAnn hratio.le)
  calc
    A * ENNReal.ofReal
          ((N.C / N.D) * (Real.log m + 1)) =
        ENNReal.ofReal
          (A.toReal * ((N.C / N.D) * (Real.log m + 1))) := by
      calc
        A * ENNReal.ofReal
            ((N.C / N.D) * (Real.log m + 1)) =
          ENNReal.ofReal A.toReal * ENNReal.ofReal
            ((N.C / N.D) * (Real.log m + 1)) := by
              rw [ENNReal.ofReal_toReal hA]
        _ = _ :=
          (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
    _ ≤ ENNReal.ofReal (C * logScale n) :=
      ENNReal.ofReal_le_ofReal (by nlinarith)

private lemma nice_extinction_tail_tsum_linear_uniform
    (N : NiceChain)
    [IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, 1 ≤ n → m ≤ n →
      (∑' t : ℕ,
        extinctionTail N.toBirthDeathChain m (t + 1)) ≤
          ENNReal.ofReal (C * n) := by
  let bd := N.toBirthDeathChain
  obtain ⟨n₀, hDrift0⟩ := nice_drift_neg N
  have hDrift :
      ∀ x, n₀ ≤ x → 0 < x →
        bd.p x - bd.q x ≤ -(N.D / 2) := by
    intro x hx hxp
    have := hDrift0 x hx hxp
    dsimp [bd]
    linarith
  obtain ⟨C₀, hC₀, hsum⟩ :=
    bd_survival_sum_uniform bd (N.D / 2) (half_pos N.D_pos)
      n₀ hDrift N.D N.D_pos N.q_ge
  let C : ℝ := 2 / N.D + C₀
  refine ⟨C, by
    dsimp [C]
    exact add_nonneg (div_nonneg (by norm_num) N.D_pos.le) hC₀, ?_⟩
  intro n m hn hm
  have htail :
      (∑' t : ℕ, extinctionTail bd m (t + 1)) ≤
        ∑' t : ℕ,
          (kernelIter (bdKernel bd) t) m {x | 0 < x} :=
    ENNReal.tsum_le_tsum fun t =>
      extinctionTail_le_marginal bd m t
  by_cases hm0 : m = 0
  · subst m
    have hzero :
        (∑' t : ℕ,
          (kernelIter (bdKernel bd) t) 0 {x | 0 < x}) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro t
      rw [kernelIter_bdKernel_zero]
      simp
    rw [hzero] at htail
    exact htail.trans (by positivity)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hfinite :
        ∀ t, (kernelIter (bdKernel bd) t) m {x | 0 < x} ≠ ⊤ := by
      intro t
      letI : IsProbabilityMeasure
          ((kernelIter (bdKernel bd) t) m) :=
        (kernelIter_isMarkov t).isProbabilityMeasure m
      exact measure_ne_top _ _
    have hbound :
        (∑' t : ℕ,
          (kernelIter (bdKernel bd) t) m {x | 0 < x}) ≤
            ENNReal.ofReal ((m : ℝ) / (N.D / 2) + C₀) :=
      ennreal_tsum_le_of_toReal_sum_le hfinite
        (add_nonneg
          (div_nonneg (Nat.cast_nonneg m) (half_pos N.D_pos).le) hC₀)
        (fun T => hsum T m hmpos)
    refine htail.trans (hbound.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hfrac :
        (m : ℝ) / (N.D / 2) ≤ (n : ℝ) / (N.D / 2) :=
      div_le_div_of_nonneg_right hmR (half_pos N.D_pos).le
    have hCmul : C₀ ≤ C₀ * n := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hnR hC₀
    calc
      (m : ℝ) / (N.D / 2) + C₀
          ≤ (n : ℝ) / (N.D / 2) + C₀ * n :=
        add_le_add hfrac hCmul
      _ = C * n := by
        dsimp [C]
        field_simp

/-- Paper `thm:nice-upper-domination`, with all four claims and with `J`
represented by reaction-labelled paths.  The expectations use tail sums, so a
positive probability of never reaching consensus gives infinite expectation. -/
theorem thm_nice_upper_domination
    (v : LVVariant)
    (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : NiceChain)
    (hDom : IsDominatingChain N.toBirthDeathChain
      (lvEventProfile v params))
    [IsMarkovKernel (lvKernel v params)] :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s0 : PopState, 0 < s0.1 + s0.2 →
      expectedConsensusTimeTail v params s0 ≤
        ENNReal.ofReal (C * (s0.1 + s0.2))) ∧
    (∀ k : ℕ, ∃ C n₀ : ℕ, 0 < C ∧ ∀ s0 : PopState,
      n₀ ≤ s0.1 + s0.2 →
        consensusTail v params s0 (C * (s0.1 + s0.2)) ≤
          (((s0.1 + s0.2 + 1 : ℕ) : ℝ≥0∞) ^ k)⁻¹) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s0 : PopState, 0 < s0.1 + s0.2 →
      expectedLabeledBadCount v params s0 ≤
        ENNReal.ofReal (C * logScale (s0.1 + s0.2))) ∧
    (∀ k : ℕ, ∃ C n₀ : ℕ, 0 < C ∧ ∀ s0 : PopState,
      n₀ ≤ s0.1 + s0.2 →
        labeledBadTail v params s0
            (C * logSqScaleNat (s0.1 + s0.2)) ≤
          (((s0.1 + s0.2 + 1 : ℕ) : ℝ≥0∞) ^ k)⁻¹) := by
  obtain ⟨CE, hCE, hExtMean⟩ :=
    nice_extinction_tail_tsum_linear_uniform N
  obtain ⟨CJ, hCJ, hBirthMean⟩ :=
    nice_birth_tail_tsum_log_uniform N
  refine ⟨⟨CE, hCE, ?_⟩, ?_, ⟨CJ, hCJ, ?_⟩, ?_⟩
  · intro s0 hn
    let n := s0.1 + s0.2
    let m := Nat.min s0.1 s0.2
    obtain ⟨hCons, _⟩ :=
      chain_domination_unconditional v params hGamma0 hGamma1 s0
        N.toBirthDeathChain m le_rfl hDom
        (niceChain_extinction_almost_sure N m)
    unfold expectedConsensusTimeTail
    calc
      (∑' t : ℕ, consensusTail v params s0 (t + 1))
          ≤ ∑' t : ℕ,
              extinctionTail N.toBirthDeathChain m (t + 1) :=
        ENNReal.tsum_le_tsum fun t => hCons (t + 1)
      _ ≤ ENNReal.ofReal (CE * n) :=
        hExtMean n m hn
          ((Nat.min_le_left s0.1 s0.2).trans
            (Nat.le_add_right s0.1 s0.2))
      _ = ENNReal.ofReal (CE * (s0.1 + s0.2)) := by
        simp [n, Nat.cast_add]
  · intro k
    obtain ⟨C, n₀, hC, hExt⟩ :=
      nice_whp_extinction_linear_uniform_unconditional N k
    refine ⟨C, n₀, hC, ?_⟩
    intro s0 hn
    let n := s0.1 + s0.2
    let m := Nat.min s0.1 s0.2
    obtain ⟨hCons, _⟩ :=
      chain_domination_unconditional v params hGamma0 hGamma1 s0
        N.toBirthDeathChain m le_rfl hDom
        (niceChain_extinction_almost_sure N m)
    exact (hCons (C * n)).trans (by
      simpa [n, m, Nat.cast_add] using
      hExt n hn m
        ((Nat.min_le_left s0.1 s0.2).trans
          (Nat.le_add_right s0.1 s0.2)))
  · intro s0 hn
    let n := s0.1 + s0.2
    let m := Nat.min s0.1 s0.2
    obtain ⟨_, hBad⟩ :=
      chain_domination_unconditional v params hGamma0 hGamma1 s0
        N.toBirthDeathChain m le_rfl hDom
        (niceChain_extinction_almost_sure N m)
    unfold expectedLabeledBadCount
    calc
      (∑' t : ℕ, labeledBadTail v params s0 (t + 1))
          ≤ ∑' t : ℕ,
              birthTail N.toBirthDeathChain m (t + 1) :=
        ENNReal.tsum_le_tsum fun t => hBad (t + 1)
      _ ≤ ENNReal.ofReal (CJ * logScale n) :=
        hBirthMean n m hn
          ((Nat.min_le_left s0.1 s0.2).trans
            (Nat.le_add_right s0.1 s0.2))
  · intro k
    obtain ⟨C, n₀, hC, hBirth⟩ :=
      nice_whp_births_logsq_uniform_unconditional N k
    refine ⟨C, n₀, hC, ?_⟩
    intro s0 hn
    let n := s0.1 + s0.2
    let m := Nat.min s0.1 s0.2
    obtain ⟨_, hBad⟩ :=
      chain_domination_unconditional v params hGamma0 hGamma1 s0
        N.toBirthDeathChain m le_rfl hDom
        (niceChain_extinction_almost_sure N m)
    exact (hBad (C * logSqScaleNat n)).trans (by
      simpa [n, m, Nat.cast_add] using
      hBirth n hn m
        ((Nat.min_le_left s0.1 s0.2).trans
          (Nat.le_add_right s0.1 s0.2)))

end LVConsensus
