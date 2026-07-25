import LVConsensus.NsdConsensus

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal

namespace LVConsensus

/-!
# Almost-sure consensus for neutral self-destructive competition

For neutral parameters with `γᵢ = 2 αᵢ`, the total population has transition
probabilities depending only on its current total.  Before consensus, the
excess `a+b-1` jumps by `+1` after a birth, by `-1` after an individual death,
and by `-2` after a competitive reaction.  The last jump is the only
difference from the NSD total-population birth--death chain.
-/

/-- Birth probability of the SD excess chain. -/
noncomputable def sdExcessP (params : LVParams) (m : ℕ) : ℝ :=
  if m = 0 then 0
  else params.beta /
    (params.beta + params.delta + params.alpha0 * (m : ℝ))

/-- Individual-death probability of the SD excess chain. -/
noncomputable def sdExcessQ₁ (params : LVParams) (m : ℕ) : ℝ :=
  if m = 0 then 0
  else params.delta /
    (params.beta + params.delta + params.alpha0 * (m : ℝ))

/-- Competitive-death probability of the SD excess chain. -/
noncomputable def sdExcessQ₂ (params : LVParams) (m : ℕ) : ℝ :=
  if m = 0 then 0
  else params.alpha0 * (m : ℝ) /
    (params.beta + params.delta + params.alpha0 * (m : ℝ))

/-- Total-population-minus-one kernel for neutral SD dynamics. -/
noncomputable def sdTotalExcessKernel (params : LVParams) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun m =>
    if m = 0 then
      Measure.dirac 0
    else
      ENNReal.ofReal (sdExcessP params m) • Measure.dirac (m + 1) +
        ENNReal.ofReal (sdExcessQ₁ params m) • Measure.dirac (m - 1) +
        ENNReal.ofReal (sdExcessQ₂ params m) • Measure.dirac (m - 2)

lemma sdTotalExcessKernel_isMarkov
    (params : LVParams) (hAlpha : 0 < params.alpha0) :
    IsMarkovKernel (sdTotalExcessKernel params) := by
  constructor
  intro m
  constructor
  by_cases hm : m = 0
  · subst m
    simp [sdTotalExcessKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    let den : ℝ :=
      params.beta + params.delta + params.alpha0 * (m : ℝ)
    have hden : 0 < den := by
      dsimp [den]
      nlinarith [params.beta_nonneg, params.delta_nonneg,
        mul_pos hAlpha hmR]
    have hβ : 0 ≤ params.beta / den :=
      div_nonneg params.beta_nonneg hden.le
    have hδ : 0 ≤ params.delta / den :=
      div_nonneg params.delta_nonneg hden.le
    have hαm : 0 ≤ params.alpha0 * (m : ℝ) / den :=
      div_nonneg (mul_nonneg hAlpha.le hmR.le) hden.le
    simp only [sdTotalExcessKernel, sdExcessP, sdExcessQ₁, sdExcessQ₂,
      hm, ↓reduceIte,
      Kernel.ofFunOfCountable, Kernel.coe_mk, Measure.add_apply,
      Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hβ hδ,
      ← ENNReal.ofReal_add (add_nonneg hβ hδ) hαm]
    have hsum :
        params.beta / den + params.delta / den +
            params.alpha0 * (m : ℝ) / den = 1 := by
      rw [← add_div, ← add_div]
      exact div_self hden.ne'
    rw [hsum, ENNReal.ofReal_one]

lemma sdTotalExcessKernel_zero (params : LVParams) :
    sdTotalExcessKernel params 0 = Measure.dirac 0 := by
  simp [sdTotalExcessKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]

lemma sdTotalExcessKernel_pos (params : LVParams) (m : ℕ) (hm : 0 < m) :
    sdTotalExcessKernel params m =
      ENNReal.ofReal (sdExcessP params m) • Measure.dirac (m + 1) +
        ENNReal.ofReal (sdExcessQ₁ params m) • Measure.dirac (m - 1) +
        ENNReal.ofReal (sdExcessQ₂ params m) • Measure.dirac (m - 2) := by
  simp [sdTotalExcessKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, hm.ne']

private noncomputable def sdExcessSurv
    (params : LVParams) (m t : ℕ) : ℝ :=
  ((kernelIter (sdTotalExcessKernel params) t) m {x | 0 < x}).toReal

private noncomputable def sdExcessSurvLimit
    (params : LVParams) (m : ℕ) : ℝ :=
  ⨅ t : ℕ, sdExcessSurv params m t

private lemma sdExcess_kernelIter_zero
    (params : LVParams) (hAlpha : 0 < params.alpha0) (t : ℕ) :
    (kernelIter (sdTotalExcessKernel params) t) 0 = Measure.dirac 0 := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  induction t with
  | zero => simp [kernelIter_zero, Kernel.id_apply]
  | succ t ih =>
      simp only [kernelIter_succ]
      rw [Kernel.comp_apply, ih]
      simp only [Measure.dirac_bind (Kernel.measurable _)]
      exact sdTotalExcessKernel_zero params

private lemma sdExcessSurv_antitone
    (params : LVParams) (hAlpha : 0 < params.alpha0) (m : ℕ) :
    Antitone (sdExcessSurv params m) := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  intro t u htu
  apply ENNReal.toReal_mono
  · haveI : IsProbabilityMeasure
        ((kernelIter (sdTotalExcessKernel params) t) m) :=
      (kernelIter_isMarkov (K := sdTotalExcessKernel params) t)
        |>.isProbabilityMeasure m
    exact measure_ne_top _ _
  · rw [show u = t + (u - t) by omega, kernelIter_add,
      Kernel.comp_apply' _ _ _ ((Set.to_countable _).measurableSet)]
    calc
      ∫⁻ y, (kernelIter (sdTotalExcessKernel params) (u - t)) y
            {x | 0 < x}
          ∂(kernelIter (sdTotalExcessKernel params) t) m
          ≤ ∫⁻ y, Set.indicator {x | 0 < x} (fun _ => 1) y
              ∂(kernelIter (sdTotalExcessKernel params) t) m := by
            apply lintegral_mono
            intro y
            by_cases hy : 0 < y
            · simp only [Set.indicator_apply, Set.mem_setOf_eq, hy,
                ↓reduceIte, Pi.one_apply]
              haveI : IsProbabilityMeasure
                  ((kernelIter (sdTotalExcessKernel params) (u - t)) y) :=
                (kernelIter_isMarkov (K := sdTotalExcessKernel params) (u - t))
                  |>.isProbabilityMeasure y
              exact prob_le_one
            · have hy0 : y = 0 := by omega
              subst y
              simp [sdExcess_kernelIter_zero params hAlpha,
                Measure.dirac_apply]
      _ = (kernelIter (sdTotalExcessKernel params) t) m {x | 0 < x} := by
            rw [lintegral_indicator ((Set.to_countable _).measurableSet)]
            simp

private lemma sdExcessSurv_tendsto
    (params : LVParams) (hAlpha : 0 < params.alpha0) (m : ℕ) :
    Filter.Tendsto (sdExcessSurv params m) Filter.atTop
      (nhds (sdExcessSurvLimit params m)) := by
  exact tendsto_atTop_ciInf (sdExcessSurv_antitone params hAlpha m)
    ⟨0, fun x hx => by
      rcases hx with ⟨t, rfl⟩
      exact ENNReal.toReal_nonneg⟩

private lemma sdExcessSurvLimit_nonneg
    (params : LVParams) (m : ℕ) :
    0 ≤ sdExcessSurvLimit params m :=
  le_ciInf fun _ => ENNReal.toReal_nonneg

private lemma sdExcessSurvLimit_le_one
    (params : LVParams) (hAlpha : 0 < params.alpha0) (m : ℕ) :
    sdExcessSurvLimit params m ≤ 1 := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  refine ciInf_le_of_le ?_ 0 ?_
  · exact ⟨0, fun x hx => by
      rcases hx with ⟨t, rfl⟩
      exact ENNReal.toReal_nonneg⟩
  · unfold sdExcessSurv
    rw [kernelIter_zero, Kernel.id_apply, Measure.dirac_apply]
    by_cases hm : 0 < m <;> simp [Set.indicator_apply, hm]

private lemma sdExcessSurvLimit_zero
    (params : LVParams) (hAlpha : 0 < params.alpha0) :
    sdExcessSurvLimit params 0 = 0 := by
  apply le_antisymm
  · refine (ciInf_le ?_ 0).trans ?_
    · exact ⟨0, fun x hx => by
        rcases hx with ⟨t, rfl⟩
        exact ENNReal.toReal_nonneg⟩
    · simp [sdExcessSurv, kernelIter_zero, Kernel.id_apply,
        Measure.dirac_apply]
  · exact sdExcessSurvLimit_nonneg params 0

private lemma sdExcess_prob_facts
    (params : LVParams) (hAlpha : 0 < params.alpha0)
    (m : ℕ) (hm : 0 < m) :
    0 ≤ sdExcessP params m ∧
    0 ≤ sdExcessQ₁ params m ∧
    0 < sdExcessQ₂ params m ∧
    sdExcessP params m + sdExcessQ₁ params m +
        sdExcessQ₂ params m = 1 := by
  have hm0 : m ≠ 0 := hm.ne'
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let den : ℝ :=
    params.beta + params.delta + params.alpha0 * (m : ℝ)
  have hden : 0 < den := by
    dsimp [den]
    nlinarith [params.beta_nonneg, params.delta_nonneg,
      mul_pos hAlpha hmR]
  simp only [sdExcessP, sdExcessQ₁, sdExcessQ₂, hm0, ↓reduceIte]
  refine ⟨div_nonneg params.beta_nonneg hden.le,
    div_nonneg params.delta_nonneg hden.le,
    div_pos (mul_pos hAlpha hmR) hden, ?_⟩
  rw [← add_div, ← add_div]
  exact div_self hden.ne'

private lemma sdExcessP_pos
    (params : LVParams) (hBeta : 0 < params.beta)
    (hAlpha : 0 < params.alpha0) (m : ℕ) (hm : 0 < m) :
    0 < sdExcessP params m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [sdExcessP, hm0, ↓reduceIte]
  apply div_pos hBeta
  nlinarith [params.delta_nonneg, mul_pos hAlpha hmR]

private lemma sdExcessSurv_succ
    (params : LVParams) (hAlpha : 0 < params.alpha0)
    (m t : ℕ) (hm : 0 < m) :
    sdExcessSurv params m (t + 1) =
      sdExcessP params m * sdExcessSurv params (m + 1) t +
      sdExcessQ₁ params m * sdExcessSurv params (m - 1) t +
      sdExcessQ₂ params m * sdExcessSurv params (m - 2) t := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  have hm0 : m ≠ 0 := hm.ne'
  unfold sdExcessSurv
  rw [kernelIter_succ_right,
    Kernel.comp_apply' _ _ _ ((Set.to_countable _).measurableSet),
    sdTotalExcessKernel_pos params m hm]
  simp only [lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  have hp0 := (sdExcess_prob_facts params hAlpha m hm).1
  have hq10 := (sdExcess_prob_facts params hAlpha m hm).2.1
  have hq20 := (sdExcess_prob_facts params hAlpha m hm).2.2.1.le
  have hfinite :
      ∀ x : ℕ,
        (kernelIter (sdTotalExcessKernel params) t) x {y | 0 < y} ≠ ⊤ := by
    intro x
    letI : IsProbabilityMeasure
        ((kernelIter (sdTotalExcessKernel params) t) x) :=
      (kernelIter_isMarkov (K := sdTotalExcessKernel params) t)
        |>.isProbabilityMeasure x
    exact measure_ne_top _ _
  have hpTop :
      ENNReal.ofReal (sdExcessP params m) *
          (kernelIter (sdTotalExcessKernel params) t) (m + 1)
            {x | 0 < x} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite (m + 1))
  have hq1Top :
      ENNReal.ofReal (sdExcessQ₁ params m) *
          (kernelIter (sdTotalExcessKernel params) t) (m - 1)
            {x | 0 < x} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite (m - 1))
  have hq2Top :
      ENNReal.ofReal (sdExcessQ₂ params m) *
          (kernelIter (sdTotalExcessKernel params) t) (m - 2)
            {x | 0 < x} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite (m - 2))
  rw [ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨hpTop, hq1Top⟩) hq2Top,
    ENNReal.toReal_add hpTop hq1Top,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hq10,
    ENNReal.toReal_ofReal hq20]

private lemma sdExcessSurvLimit_harmonic
    (params : LVParams) (hAlpha : 0 < params.alpha0)
    (m : ℕ) (hm : 0 < m) :
    sdExcessSurvLimit params m =
      sdExcessP params m * sdExcessSurvLimit params (m + 1) +
      sdExcessQ₁ params m * sdExcessSurvLimit params (m - 1) +
      sdExcessQ₂ params m * sdExcessSurvLimit params (m - 2) := by
  have hshift :
      Filter.Tendsto (fun t => sdExcessSurv params m (t + 1))
        Filter.atTop (nhds (sdExcessSurvLimit params m)) :=
    (sdExcessSurv_tendsto params hAlpha m).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hp := (tendsto_const_nhds (x := sdExcessP params m)).mul
    (sdExcessSurv_tendsto params hAlpha (m + 1))
  have hq1 := (tendsto_const_nhds (x := sdExcessQ₁ params m)).mul
    (sdExcessSurv_tendsto params hAlpha (m - 1))
  have hq2 := (tendsto_const_nhds (x := sdExcessQ₂ params m)).mul
    (sdExcessSurv_tendsto params hAlpha (m - 2))
  have hr := (hp.add hq1).add hq2
  exact tendsto_nhds_unique hshift
    (by simpa only [sdExcessSurv_succ params hAlpha _ _ hm] using hr)

private lemma sdExcess_increment_relation_one
    (params : LVParams) (hAlpha : 0 < params.alpha0) :
    sdExcessP params 1 *
        (sdExcessSurvLimit params 2 - sdExcessSurvLimit params 1) =
      (sdExcessQ₁ params 1 + sdExcessQ₂ params 1) *
        (sdExcessSurvLimit params 1 - sdExcessSurvLimit params 0) := by
  have hh := sdExcessSurvLimit_harmonic params hAlpha 1 Nat.one_pos
  have hsum := (sdExcess_prob_facts params hAlpha 1 Nat.one_pos).2.2.2
  norm_num at hh ⊢
  linear_combination -hh -
    hsum * sdExcessSurvLimit params 1

private lemma sdExcess_increment_relation
    (params : LVParams) (hAlpha : 0 < params.alpha0)
    (m : ℕ) (hm : 2 ≤ m) :
    sdExcessP params m *
        (sdExcessSurvLimit params (m + 1) -
          sdExcessSurvLimit params m) =
      sdExcessQ₁ params m *
          (sdExcessSurvLimit params m -
            sdExcessSurvLimit params (m - 1)) +
        sdExcessQ₂ params m *
          ((sdExcessSurvLimit params m -
              sdExcessSurvLimit params (m - 1)) +
            (sdExcessSurvLimit params (m - 1) -
              sdExcessSurvLimit params (m - 2))) := by
  have hh := sdExcessSurvLimit_harmonic params hAlpha m (by omega)
  have hsum := (sdExcess_prob_facts params hAlpha m (by omega)).2.2.2
  linear_combination -hh -
    hsum * sdExcessSurvLimit params m

private lemma sdExcess_two_p_le_q₂_eventually
    (params : LVParams) (hAlpha : 0 < params.alpha0) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ m : ℕ, L ≤ m →
      2 * sdExcessP params m ≤ sdExcessQ₂ params m := by
  let L := Nat.ceil (2 * params.beta / params.alpha0) + 1
  refine ⟨L, by simp [L], ?_⟩
  intro m hm
  have hmpos : 0 < m := lt_of_lt_of_le (by simp [L]) hm
  have hm0 : m ≠ 0 := hmpos.ne'
  have hceil :
      2 * params.beta / params.alpha0 ≤
        (Nat.ceil (2 * params.beta / params.alpha0) : ℝ) :=
    Nat.le_ceil _
  have hmcast :
      (Nat.ceil (2 * params.beta / params.alpha0) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show Nat.ceil (2 * params.beta / params.alpha0) ≤ m by
      dsimp [L] at hm
      omega)
  have hnum : 2 * params.beta ≤ params.alpha0 * (m : ℝ) := by
    have := hceil.trans hmcast
    have hx : params.beta * 2 ≤ (m : ℝ) * params.alpha0 :=
      (div_le_iff₀ hAlpha).mp (by simpa [mul_comm] using this)
    simpa [mul_comm] using hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hden :
      0 < params.beta + params.delta + params.alpha0 * (m : ℝ) := by
    nlinarith [params.beta_nonneg, params.delta_nonneg,
      mul_pos hAlpha hmR]
  simp only [sdExcessP, sdExcessQ₂, hm0, ↓reduceIte]
  rw [show 2 * (params.beta /
      (params.beta + params.delta + params.alpha0 * (m : ℝ))) =
        (2 * params.beta) /
          (params.beta + params.delta + params.alpha0 * (m : ℝ)) by ring]
  exact div_le_div_of_nonneg_right hnum hden.le

private lemma sdExcessSurvLimit_eq_zero
    (params : LVParams) (hAlpha : 0 < params.alpha0)
    (hBeta : 0 < params.beta) :
    ∀ m : ℕ, sdExcessSurvLimit params m = 0 := by
  let u : ℕ → ℝ := sdExcessSurvLimit params
  let d : ℕ → ℝ := fun n => u (n + 1) - u n
  have hu0 : u 0 = 0 := sdExcessSurvLimit_zero params hAlpha
  have hu1 : u 1 = 0 := by
    by_contra hne
    have hu1pos : 0 < u 1 := by
      have := sdExcessSurvLimit_nonneg params 1
      exact lt_of_le_of_ne this (Ne.symm hne)
    have hd0 : 0 < d 0 := by
      dsimp [d]
      rw [hu0]
      simpa using hu1pos
    have hdpos : ∀ n : ℕ, 0 < d n := by
      intro n
      induction n using Nat.case_strong_induction_on with
      | hz => exact hd0
      | hi n ih =>
          by_cases hn0 : n = 0
          · subst n
            have hrel := sdExcess_increment_relation_one params hAlpha
            have hp := sdExcessP_pos params hBeta hAlpha 1 Nat.one_pos
            have hq2 :=
              (sdExcess_prob_facts params hAlpha 1 Nat.one_pos).2.2.1
            have hq1 :=
              (sdExcess_prob_facts params hAlpha 1 Nat.one_pos).2.1
            have hprev : 0 < d 0 := hd0
            have hrhs :
                0 < (sdExcessQ₁ params 1 + sdExcessQ₂ params 1) * d 0 :=
              mul_pos (by linarith) hprev
            have hlhs :
                0 < sdExcessP params 1 * d 1 := by
              simpa [d, u] using hrel.symm ▸ hrhs
            by_contra hn
            have hdle : d 1 ≤ 0 := le_of_not_gt hn
            have := mul_nonpos_of_nonneg_of_nonpos hp.le hdle
            linarith
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
            have hm2 : 2 ≤ n + 1 := by omega
            have hrel :=
              sdExcess_increment_relation params hAlpha (n + 1) hm2
            have hp :=
              sdExcessP_pos params hBeta hAlpha (n + 1) (by omega)
            have hq2 :=
              (sdExcess_prob_facts params hAlpha (n + 1)
                (by omega)).2.2.1
            have hprev : 0 < d n := ih n le_rfl
            have hprev2 : 0 < d (n - 1) := ih (n - 1) (by omega)
            have hidx2 : n + 1 - 2 = n - 1 := by omega
            have hsumpos : 0 < d n + d (n - 1) := by linarith
            have hrhspos :
                0 <
                  sdExcessQ₁ params (n + 1) * d n +
                    sdExcessQ₂ params (n + 1) *
                      (d n + d (n - 1)) := by
              have hq1 :=
                (sdExcess_prob_facts params hAlpha (n + 1)
                  (by omega)).2.1
              have hfirst :
                  0 ≤ sdExcessQ₁ params (n + 1) * d n :=
                mul_nonneg hq1 hprev.le
              have hsecond :
                  0 < sdExcessQ₂ params (n + 1) *
                    (d n + d (n - 1)) :=
                mul_pos hq2 hsumpos
              linarith
            have hrel' :
                sdExcessP params (n + 1) * d (n + 1) =
                  sdExcessQ₁ params (n + 1) * d n +
                    sdExcessQ₂ params (n + 1) *
                      (d n + d (n - 1)) := by
              dsimp [d, u]
              rw [Nat.sub_add_cancel hnpos]
              simp only [Nat.add_sub_cancel] at hrel
              rw [hidx2] at hrel
              linear_combination hrel
            have hlhs : 0 <
                sdExcessP params (n + 1) * d (n + 1) :=
              hrel'.symm ▸ hrhspos
            by_contra hn
            have hdle : d (n + 1) ≤ 0 := le_of_not_gt hn
            have := mul_nonpos_of_nonneg_of_nonpos hp.le hdle
            linarith
    obtain ⟨L, hL, hratio⟩ :=
      sdExcess_two_p_le_q₂_eventually params hAlpha
    have hstep : ∀ m : ℕ, L ≤ m → 2 * d (m - 1) ≤ d m := by
      intro m hm
      have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_one.trans_le hL) hm
      have hp := sdExcessP_pos params hBeta hAlpha m hmpos
      have hq1 :=
        (sdExcess_prob_facts params hAlpha m hmpos).2.1
      have hq2 :=
        (sdExcess_prob_facts params hAlpha m hmpos).2.2.1.le
      have hrat := hratio m hm
      by_cases hm1 : m = 1
      · subst m
        have hrel := sdExcess_increment_relation_one params hAlpha
        have hd0' := hdpos 0
        dsimp [d, u] at hrel ⊢ hd0'
        nlinarith
      · have hm2 : 2 ≤ m := by omega
        have hrel := sdExcess_increment_relation params hAlpha m hm2
        have hdprev : 0 ≤ u m - u (m - 1) := by
          have := (hdpos (m - 1)).le
          simpa [d, Nat.sub_add_cancel (by omega : 1 ≤ m)] using this
        have hdprev2 : 0 ≤ u (m - 1) - u (m - 2) := by
          have := (hdpos (m - 2)).le
          have hidx2 : m - 2 + 1 = m - 1 := by omega
          simpa [d, hidx2] using this
        have hrel' :
            sdExcessP params m * d m =
              sdExcessQ₁ params m * d (m - 1) +
                sdExcessQ₂ params m *
                  (d (m - 1) + d (m - 2)) := by
          have hidx1 : m - 1 + 1 = m := by omega
          have hidx2 : m - 2 + 1 = m - 1 := by omega
          simpa [d, u, hidx1, hidx2] using hrel
        have hq1term : 0 ≤ sdExcessQ₁ params m * d (m - 1) :=
          mul_nonneg hq1 (hdpos (m - 1)).le
        have hq2extra : 0 ≤ sdExcessQ₂ params m * d (m - 2) :=
          mul_nonneg hq2 (hdpos (m - 2)).le
        have hmul :
            sdExcessP params m * (2 * d (m - 1)) ≤
              sdExcessP params m * d m := by
          calc
            sdExcessP params m * (2 * d (m - 1)) =
                (2 * sdExcessP params m) * d (m - 1) := by ring
            _ ≤ sdExcessQ₂ params m * d (m - 1) :=
              mul_le_mul_of_nonneg_right hrat (hdpos (m - 1)).le
            _ ≤ sdExcessQ₁ params m * d (m - 1) +
                  sdExcessQ₂ params m *
                    (d (m - 1) + d (m - 2)) := by
              nlinarith
            _ = sdExcessP params m * d m := hrel'.symm
        exact le_of_mul_le_mul_left hmul hp
    let base := L - 1
    have hbase : base + 1 = L := by dsimp [base]; omega
    have hgrow : ∀ k : ℕ, 2 ^ k * d base ≤ d (base + k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc
            (2 : ℝ) ^ (k + 1) * d base =
                2 * ((2 : ℝ) ^ k * d base) := by
                  rw [pow_succ]
                  ring
            _ ≤ 2 * d (base + k) := by nlinarith
            _ ≤ d (base + (k + 1)) := by
              have hs := hstep (base + k + 1) (by omega)
              simpa [Nat.add_assoc] using hs
    have hbasepos : 0 < d base := hdpos base
    obtain ⟨k, hk⟩ :=
      pow_unbounded_of_one_lt (1 / d base) (by norm_num : (1 : ℝ) < 2)
    have hk' : 1 < (2 : ℝ) ^ k * d base := by
      exact (div_lt_iff₀ hbasepos).mp (by simpa [one_div] using hk)
    have hdupper : d (base + k) ≤ 1 := by
      have hnn := sdExcessSurvLimit_nonneg params (base + k)
      have htop :=
        sdExcessSurvLimit_le_one params hAlpha (base + k + 1)
      dsimp [d, u]
      linarith
    linarith [hk', hgrow k, hdupper]
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rcases m with _ | m
      · exact hu0
      · rcases m with _ | m
        · exact hu1
        · have hcur : u (m + 1) = 0 :=
            ih (m + 1) (by omega)
          have hlo1 : u (m + 1 - 1) = 0 := by
            simpa using ih m (by omega)
          have hlo2 : u (m + 1 - 2) = 0 := by
            by_cases hm0 : m = 0
            · subst m
              simpa using hu0
            · exact ih (m - 1) (by omega)
          have hh :=
            sdExcessSurvLimit_harmonic params hAlpha (m + 1) (by omega)
          have hp :=
            sdExcessP_pos params hBeta hAlpha (m + 1) (by omega)
          change u (m + 2) = 0
          dsimp [u] at hh hcur hlo1 hlo2 ⊢
          rw [hcur, hlo1, hlo2] at hh
          norm_num at hh
          exact hh.resolve_left hp.ne'

private lemma sdExcessSurvLimit_eq_zero_of_beta_zero
    (params : LVParams) (hAlpha : 0 < params.alpha0)
    (hBeta : params.beta = 0) :
    ∀ m : ℕ, sdExcessSurvLimit params m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm0 : m = 0
      · subst m
        exact sdExcessSurvLimit_zero params hAlpha
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hh :=
          sdExcessSurvLimit_harmonic params hAlpha m hmpos
        have hp0 : sdExcessP params m = 0 := by
          simp [sdExcessP, hm0, hBeta]
        have hlo1 : sdExcessSurvLimit params (m - 1) = 0 :=
          ih (m - 1) (by omega)
        have hlo2 : sdExcessSurvLimit params (m - 2) = 0 :=
          ih (m - 2) (by omega)
        rw [hp0, zero_mul, hlo1, mul_zero, hlo2, mul_zero,
          add_zero] at hh
        simpa using hh

private lemma sdExcessSurvLimit_eq_zero_all
    (params : LVParams) (hAlpha : 0 < params.alpha0) :
    ∀ m : ℕ, sdExcessSurvLimit params m = 0 := by
  by_cases hBeta0 : params.beta = 0
  · exact sdExcessSurvLimit_eq_zero_of_beta_zero params hAlpha hBeta0
  · exact sdExcessSurvLimit_eq_zero params hAlpha
      (lt_of_le_of_ne params.beta_nonneg (Ne.symm hBeta0))

theorem sdExcess_survival_iInf_eq_zero
    (params : LVParams) (hAlpha : 0 < params.alpha0) (m : ℕ) :
    (⨅ t : ℕ,
      (kernelIter (sdTotalExcessKernel params) t) m {x | 0 < x}) = 0 := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  let S : ℝ≥0∞ :=
    ⨅ t : ℕ,
      (kernelIter (sdTotalExcessKernel params) t) m {x | 0 < x}
  have hS_le_one : S ≤ 1 := by
    calc
      S ≤ (kernelIter (sdTotalExcessKernel params) 0) m {x | 0 < x} :=
        iInf_le _ 0
      _ ≤ 1 := by
        haveI : IsProbabilityMeasure
            ((kernelIter (sdTotalExcessKernel params) 0) m) :=
          (kernelIter_isMarkov (K := sdTotalExcessKernel params) 0)
            |>.isProbabilityMeasure m
        exact prob_le_one
  have hSne : S ≠ ⊤ := ne_top_of_le_ne_top (by simp) hS_le_one
  have hreal : S.toReal = 0 := by
    apply le_antisymm
    · rw [← sdExcessSurvLimit_eq_zero_all params hAlpha m]
      apply le_ciInf
      intro t
      have hRne :
          (kernelIter (sdTotalExcessKernel params) t) m {x | 0 < x} ≠ ⊤ := by
        haveI : IsProbabilityMeasure
            ((kernelIter (sdTotalExcessKernel params) t) m) :=
          (kernelIter_isMarkov (K := sdTotalExcessKernel params) t)
            |>.isProbabilityMeasure m
        exact measure_ne_top _ _
      exact ENNReal.toReal_mono hRne (iInf_le _ t)
    · exact ENNReal.toReal_nonneg
  have hzero : S = 0 :=
    (ENNReal.toReal_eq_zero_iff S).mp hreal |>.resolve_right hSne
  simpa only [S] using hzero

set_option maxHeartbeats 800000 in
-- Expanding the finite-support LV kernel and normalizing its arithmetic
-- requires more heartbeats than Lean's default.
lemma sd_kernel_map_popExcessOne
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((lvKernel .selfDestructive params) (a, b)).map popExcessOne =
      sdTotalExcessKernel params (popExcessOne (a, b)) := by
  let n := a + b
  let m := n - 1
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hmpos : 0 < m := by dsimp [m]; omega
  have hm0 : m ≠ 0 := hmpos.ne'
  have hexcess : popExcessOne (a, b) = m := by
    simp [popExcessOne, m, n]
  let den : ℝ :=
    params.beta + params.delta + params.alpha0 * (m : ℝ)
  have hmcast :
      (m : ℝ) = (a : ℝ) + b - 1 := by
    dsimp [m, n]
    rw [Nat.cast_sub (by omega : 1 ≤ a + b), Nat.cast_add,
      Nat.cast_one]
  have hdenpos : 0 < den := by
    dsimp [den]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    nlinarith [params.beta_nonneg, params.delta_nonneg,
      mul_pos hAlpha hmR]
  have hφeq :
      lvTotalPropensity params (a, b) = (n : ℝ) * den := by
    have h :=
      nsd_neutral_totalPropensity_eq params hNeutral hEq0 hEq1 a b
    dsimp [n, den]
    rw [hmcast]
    simpa [Nat.cast_add] using h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hφpos : 0 < lvTotalPropensity params (a, b) := by
    rw [hφeq]
    exact mul_pos hnR hdenpos
  have hφ : lvTotalPropensity params (a, b) ≠ 0 := hφpos.ne'
  have hinvφ : 0 ≤ 1 / lvTotalPropensity params (a, b) := by positivity
  have hβa : 0 ≤ params.beta * (a : ℝ) :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  have hβb : 0 ≤ params.beta * (b : ℝ) :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  have hδa : 0 ≤ params.delta * (a : ℝ) :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  have hδb : 0 ≤ params.delta * (b : ℝ) :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  have hα0ab : 0 ≤ params.alpha0 * (a : ℝ) * (b : ℝ) :=
    mul_nonneg (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hα1ab : 0 ≤ params.alpha1 * (a : ℝ) * (b : ℝ) :=
    mul_nonneg (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have haa : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (Nat.one_le_cast.mpr ha)))
      (by norm_num)
  have hbb : 0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (Nat.one_le_cast.mpr hb)))
      (by norm_num)
  have hγ0aa :
      0 ≤ params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) :=
    mul_nonneg params.gamma0_nonneg haa
  have hγ1bb :
      0 ≤ params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) :=
    mul_nonneg params.gamma1_nonneg hbb
  have hP :
      ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          (ENNReal.ofReal (params.beta * a) +
            ENNReal.ofReal (params.beta * b)) =
        ENNReal.ofReal (sdExcessP params m) := by
    rw [← ENNReal.ofReal_add hβa hβb,
      ← ENNReal.ofReal_mul hinvφ]
    apply congrArg ENNReal.ofReal
    simp only [sdExcessP, hm0, ↓reduceIte]
    change
      1 / lvTotalPropensity params (a, b) *
          (params.beta * (a : ℝ) + params.beta * (b : ℝ)) =
        params.beta / den
    rw [hφeq]
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    field_simp [hn0, hdenpos.ne']
    dsimp [n]
    push_cast
    ring
  have hQ₁ :
      ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          (ENNReal.ofReal (params.delta * a) +
            ENNReal.ofReal (params.delta * b)) =
        ENNReal.ofReal (sdExcessQ₁ params m) := by
    rw [← ENNReal.ofReal_add hδa hδb,
      ← ENNReal.ofReal_mul hinvφ]
    apply congrArg ENNReal.ofReal
    simp only [sdExcessQ₁, hm0, ↓reduceIte]
    change
      1 / lvTotalPropensity params (a, b) *
          (params.delta * (a : ℝ) + params.delta * (b : ℝ)) =
        params.delta / den
    rw [hφeq]
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    field_simp [hn0, hdenpos.ne']
    dsimp [n]
    push_cast
    ring
  have hcomp :
      params.alpha0 * (a : ℝ) * (b : ℝ) +
          params.alpha1 * (a : ℝ) * (b : ℝ) +
          params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) +
          params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) =
        (n : ℝ) * (params.alpha0 * (m : ℝ)) := by
    have hγ1 : params.gamma1 = 2 * params.alpha0 := by
      rw [hEq1, ← hNeutral]
    rw [← hNeutral, hEq0, hγ1]
    rw [hmcast]
    dsimp [n]
    push_cast
    ring
  have hcomp01 :
      0 ≤ params.alpha0 * (a : ℝ) * (b : ℝ) +
        params.alpha1 * (a : ℝ) * (b : ℝ) :=
    add_nonneg hα0ab hα1ab
  have hcomp012 :
      0 ≤ params.alpha0 * (a : ℝ) * (b : ℝ) +
          params.alpha1 * (a : ℝ) * (b : ℝ) +
          params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) :=
    add_nonneg hcomp01 hγ0aa
  have hQ₂ :
      ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          (ENNReal.ofReal (params.alpha0 * a * b) +
            ENNReal.ofReal (params.alpha1 * a * b) +
            ENNReal.ofReal
              (params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) +
            ENNReal.ofReal
              (params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2))) =
        ENNReal.ofReal (sdExcessQ₂ params m) := by
    rw [← ENNReal.ofReal_add hα0ab hα1ab,
      ← ENNReal.ofReal_add hcomp01 hγ0aa,
      ← ENNReal.ofReal_add hcomp012 hγ1bb,
      ← ENNReal.ofReal_mul hinvφ, hcomp]
    apply congrArg ENNReal.ofReal
    simp only [sdExcessQ₂, hm0, ↓reduceIte]
    change
      1 / lvTotalPropensity params (a, b) *
          ((n : ℝ) * (params.alpha0 * (m : ℝ))) =
        params.alpha0 * (m : ℝ) / den
    rw [hφeq]
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    field_simp [hn0, hdenpos.ne']
  have hb0 : popExcessOne (a + 1, b) = m + 1 := by
    unfold popExcessOne
    dsimp [m, n]
    omega
  have hb1 : popExcessOne (a, b + 1) = m + 1 := by
    unfold popExcessOne
    dsimp [m, n]
    omega
  have hd0 : popExcessOne (a - 1, b) = m - 1 := by
    unfold popExcessOne
    dsimp [m, n]
    omega
  have hd1 : popExcessOne (a, b - 1) = m - 1 := by
    unfold popExcessOne
    dsimp [m, n]
    omega
  have hi : popExcessOne (a - 1, b - 1) = m - 2 := by
    unfold popExcessOne
    dsimp [m, n]
    omega
  rw [lvKernel_sd_apply params a b hφ]
  simp only [Measure.map_smul, Measure.map_add _ _
    (measurable_of_countable popExcessOne),
    Measure.map_dirac' (measurable_of_countable popExcessOne)]
  rw [hexcess, sdTotalExcessKernel_pos params m hmpos]
  rw [hb0, hb1, hd0, hd1, hi]
  rcases Nat.eq_or_lt_of_le ha with ha1 | ha2
  · subst a
    rcases Nat.eq_or_lt_of_le hb with hb1' | hb2
    · subst b
      simp only [Nat.cast_one, sub_self, mul_zero, zero_div,
        ENNReal.ofReal_zero, zero_smul, add_zero]
      apply Measure.ext_of_singleton
      intro k
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply, Nat.add_comm 1 m]
      ring_nf at hP hQ₁ hQ₂ ⊢
      have hPk := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m + 1) * x) hP
      have hQ₁k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 1) * x) hQ₁
      have hQ₂k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 2) * x) hQ₂
      have hsum := congrArg₂ (fun x y : ℝ≥0∞ => x + y)
        (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hPk hQ₁k) hQ₂k
      try simp only [ENNReal.ofReal_zero, mul_zero, zero_mul, add_zero,
        zero_add] at hsum
      convert hsum using 1 <;> ring
    · have hi1 : popExcessOne (1, b - 2) = m - 2 := by
        unfold popExcessOne
        dsimp [m, n]
        omega
      rw [hi1]
      simp only [Nat.cast_one, sub_self, mul_zero, zero_div,
        ENNReal.ofReal_zero, zero_smul, add_zero]
      apply Measure.ext_of_singleton
      intro k
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply, Nat.add_comm 1 m]
      ring_nf at hP hQ₁ hQ₂ ⊢
      have hPk := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m + 1) * x) hP
      have hQ₁k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 1) * x) hQ₁
      have hQ₂k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 2) * x) hQ₂
      have hsum := congrArg₂ (fun x y : ℝ≥0∞ => x + y)
        (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hPk hQ₁k) hQ₂k
      try simp only [ENNReal.ofReal_zero, mul_zero, zero_mul, add_zero,
        zero_add] at hsum
      convert hsum using 1 <;> ring
  · have hi0 : popExcessOne (a - 2, b) = m - 2 := by
      unfold popExcessOne
      dsimp [m, n]
      omega
    rcases Nat.eq_or_lt_of_le hb with hb1' | hb2
    · subst b
      rw [hi0]
      simp only [Nat.cast_one, sub_self, mul_zero, zero_div,
        ENNReal.ofReal_zero, zero_smul, add_zero]
      apply Measure.ext_of_singleton
      intro k
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply, Nat.add_comm 1 m]
      ring_nf at hP hQ₁ hQ₂ ⊢
      have hPk := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m + 1) * x) hP
      have hQ₁k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 1) * x) hQ₁
      have hQ₂k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 2) * x) hQ₂
      have hsum := congrArg₂ (fun x y : ℝ≥0∞ => x + y)
        (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hPk hQ₁k) hQ₂k
      try simp only [ENNReal.ofReal_zero, mul_zero, zero_mul, add_zero,
        zero_add] at hsum
      convert hsum using 1 <;> ring
    · have hi1 : popExcessOne (a, b - 2) = m - 2 := by
        unfold popExcessOne
        dsimp [m, n]
        omega
      rw [hi0, hi1]
      apply Measure.ext_of_singleton
      intro k
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply, Nat.add_comm 1 m]
      ring_nf at hP hQ₁ hQ₂ ⊢
      have hPk := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m + 1) * x) hP
      have hQ₁k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 1) * x) hQ₁
      have hQ₂k := congrArg
        (fun x : ℝ≥0∞ =>
          Set.indicator ({k} : Set ℕ) (1 : ℕ → ℝ≥0∞) (m - 2) * x) hQ₂
      have hsum := congrArg₂ (fun x y : ℝ≥0∞ => x + y)
        (congrArg₂ (fun x y : ℝ≥0∞ => x + y) hPk hQ₁k) hQ₂k
      try simp only [ENNReal.ofReal_zero, mul_zero, zero_mul, add_zero,
        zero_add] at hsum
      convert hsum using 1 <;> ring

private lemma sd_kernelIter_species0_dead_absorbing_general
    (params : LVParams) (s : PopState) (m : ℕ)
    (hs : s.1 = 0)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    (kernelIter (lvKernel .selfDestructive params) m) s
      {s' : PopState | s'.1 ≠ 0} = 0 := by
  induction m with
  | zero =>
      rw [kernelIter_zero, Kernel.id_apply]
      rw [Measure.dirac_apply' _ (by measurability)]
      simp [Set.mem_setOf_eq, hs]
  | succ n ih =>
      rw [kernelIter_succ, Kernel.comp_apply]
      have hbind :
          (⇑(lvKernel .selfDestructive params) ∘ₘ
              (kernelIter (lvKernel .selfDestructive params) n) s)
              {s' | s'.1 ≠ 0} =
            ∫⁻ y, (lvKernel .selfDestructive params) y {s' | s'.1 ≠ 0}
              ∂((kernelIter (lvKernel .selfDestructive params) n) s) := by
        apply Measure.bind_apply <;> measurability
      rw [hbind]
      apply le_antisymm _ zero_le
      have hpw : ∀ y : PopState,
          (lvKernel .selfDestructive params) y {s' : PopState | s'.1 ≠ 0} ≤
            Set.indicator {s' : PopState | s'.1 ≠ 0}
              (1 : PopState → ℝ≥0∞) y := by
        intro y
        by_cases hy : y.1 = 0
        · simp [Set.indicator, Set.mem_setOf_eq, hy,
            sd_kernel_species0_dead_absorbing_general params y hy]
        · simp [Set.indicator, Set.mem_setOf_eq, hy]
          exact prob_le_one
      calc
        ∫⁻ y, (lvKernel .selfDestructive params) y {s' | s'.1 ≠ 0}
              ∂((kernelIter (lvKernel .selfDestructive params) n) s)
            ≤ ∫⁻ y, Set.indicator {s' : PopState | s'.1 ≠ 0}
                (1 : PopState → ℝ≥0∞) y
              ∂((kernelIter (lvKernel .selfDestructive params) n) s) :=
                lintegral_mono hpw
        _ = ((kernelIter (lvKernel .selfDestructive params) n) s)
              {s' | s'.1 ≠ 0} := lintegral_indicator_one (by measurability)
        _ = 0 := ih

private lemma sd_kernelIter_species1_dead_absorbing_general
    (params : LVParams) (s : PopState) (m : ℕ)
    (hs : s.2 = 0)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    (kernelIter (lvKernel .selfDestructive params) m) s
      {s' : PopState | s'.2 ≠ 0} = 0 := by
  induction m with
  | zero =>
      rw [kernelIter_zero, Kernel.id_apply]
      rw [Measure.dirac_apply' _ (by measurability)]
      simp [Set.mem_setOf_eq, hs]
  | succ n ih =>
      rw [kernelIter_succ, Kernel.comp_apply]
      have hbind :
          (⇑(lvKernel .selfDestructive params) ∘ₘ
              (kernelIter (lvKernel .selfDestructive params) n) s)
              {s' | s'.2 ≠ 0} =
            ∫⁻ y, (lvKernel .selfDestructive params) y {s' | s'.2 ≠ 0}
              ∂((kernelIter (lvKernel .selfDestructive params) n) s) := by
        apply Measure.bind_apply <;> measurability
      rw [hbind]
      apply le_antisymm _ zero_le
      have hpw : ∀ y : PopState,
          (lvKernel .selfDestructive params) y {s' : PopState | s'.2 ≠ 0} ≤
            Set.indicator {s' : PopState | s'.2 ≠ 0}
              (1 : PopState → ℝ≥0∞) y := by
        intro y
        by_cases hy : y.2 = 0
        · simp [Set.indicator, Set.mem_setOf_eq, hy,
            sd_kernel_species1_dead_absorbing_general params y hy]
        · simp [Set.indicator, Set.mem_setOf_eq, hy]
          exact prob_le_one
      calc
        ∫⁻ y, (lvKernel .selfDestructive params) y {s' | s'.2 ≠ 0}
              ∂((kernelIter (lvKernel .selfDestructive params) n) s)
            ≤ ∫⁻ y, Set.indicator {s' : PopState | s'.2 ≠ 0}
                (1 : PopState → ℝ≥0∞) y
              ∂((kernelIter (lvKernel .selfDestructive params) n) s) :=
                lintegral_mono hpw
        _ = ((kernelIter (lvKernel .selfDestructive params) n) s)
              {s' | s'.2 ≠ 0} := lintegral_indicator_one (by measurability)
        _ = 0 := ih

lemma sd_kernelIter_interior_le_excess
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    ∀ (t : ℕ) (s : PopState),
      (kernelIter (lvKernel .selfDestructive params) t) s
          {x | 0 < x.1 ∧ 0 < x.2} ≤
        (kernelIter (sdTotalExcessKernel params) t)
          (popExcessOne s) {m | 0 < m} := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  intro t
  induction t with
  | zero =>
      intro s
      simp only [kernelIter_zero, Kernel.id_apply]
      rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      by_cases hsI : 0 < s.1 ∧ 0 < s.2
      · have hsE : 0 < popExcessOne s := by
          dsimp [popExcessOne]
          omega
        simp [hsI, hsE]
      · simp [hsI]
  | succ t ih =>
      intro s
      by_cases hs0 : s.1 = 0
      · have hdead :=
          sd_kernelIter_species0_dead_absorbing_general params s (t + 1) hs0
        have hle :
            (kernelIter (lvKernel .selfDestructive params) (t + 1)) s
                {x | 0 < x.1 ∧ 0 < x.2} ≤
              (kernelIter (lvKernel .selfDestructive params) (t + 1)) s
                {x | x.1 ≠ 0} := by
          apply measure_mono
          intro x hx
          exact Nat.ne_of_gt hx.1
        exact le_trans (hle.trans_eq hdead) zero_le
      · by_cases hs1 : s.2 = 0
        · have hdead :=
            sd_kernelIter_species1_dead_absorbing_general params s (t + 1) hs1
          have hle :
              (kernelIter (lvKernel .selfDestructive params) (t + 1)) s
                  {x | 0 < x.1 ∧ 0 < x.2} ≤
                (kernelIter (lvKernel .selfDestructive params) (t + 1)) s
                  {x | x.2 ≠ 0} := by
            apply measure_mono
            intro x hx
            exact Nat.ne_of_gt hx.2
          exact le_trans (hle.trans_eq hdead) zero_le
        · have hs0p : 0 < s.1 := Nat.pos_of_ne_zero hs0
          have hs1p : 0 < s.2 := Nat.pos_of_ne_zero hs1
          rw [kernelIter_succ_right, kernelIter_succ_right,
            Kernel.comp_apply' _ _ _
              (Set.to_countable {x : PopState | 0 < x.1 ∧ 0 < x.2}).measurableSet,
            Kernel.comp_apply' _ _ _
              (Set.to_countable {m : ℕ | 0 < m}).measurableSet]
          calc
            ∫⁻ y, (kernelIter (lvKernel .selfDestructive params) t) y
                  {x | 0 < x.1 ∧ 0 < x.2}
                ∂(lvKernel .selfDestructive params) s
                ≤ ∫⁻ y, (kernelIter (sdTotalExcessKernel params) t)
                    (popExcessOne y) {m | 0 < m}
                  ∂(lvKernel .selfDestructive params) s := by
                    exact lintegral_mono ih
            _ = ∫⁻ m, (kernelIter (sdTotalExcessKernel params) t)
                    m {m | 0 < m}
                  ∂((lvKernel .selfDestructive params) s).map popExcessOne := by
                    rw [MeasureTheory.lintegral_map
                      (Kernel.measurable_coe
                        (kernelIter (sdTotalExcessKernel params) t)
                        (Set.to_countable {m : ℕ | 0 < m}).measurableSet)
                      (measurable_of_countable popExcessOne)]
            _ = ∫⁻ m, (kernelIter (sdTotalExcessKernel params) t)
                    m {m | 0 < m}
                  ∂sdTotalExcessKernel params (popExcessOne s) := by
                    rw [sd_kernel_map_popExcessOne params hNeutral hEq0 hEq1
                      hAlpha s.1 s.2 hs0p hs1p]

lemma sd_path_stay_interior_le_excess
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    (a b t : ℕ)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    lvPathMeasure .selfDestructive params (a, b)
        {ω | ∀ u ≤ t, 0 < (ω u).1 ∧ 0 < (ω u).2} ≤
      (kernelIter (sdTotalExcessKernel params) t)
        (popExcessOne (a, b)) {m | 0 < m} := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  let P := lvPathMeasure .selfDestructive params (a, b)
  let F : Set (ℕ → PopState) :=
    {ω | ∀ u ≤ t, 0 < (ω u).1 ∧ 0 < (ω u).2}
  let E : Set (ℕ → PopState) := {ω | 0 < (ω t).1 ∧ 0 < (ω t).2}
  calc
    P F ≤ P E := by
      apply measure_mono
      intro ω hω
      exact hω t le_rfl
    _ = (kernelIter (lvKernel .selfDestructive params) t) (a, b)
        {s | 0 < s.1 ∧ 0 < s.2} := by
      dsimp [P, E]
      unfold lvPathMeasure
      rw [show ({ω : ℕ → PopState | 0 < (ω t).1 ∧ 0 < (ω t).2} :
            Set (ℕ → PopState)) =
          (fun ω : ℕ → PopState => ω t) ⁻¹'
            ({s : PopState | 0 < s.1 ∧ 0 < s.2}) from rfl,
        ← Measure.map_apply (measurable_pi_apply t) (by measurability),
        homogeneousPathMeasure_dirac_marginal]
    _ ≤ (kernelIter (sdTotalExcessKernel params) t)
          (popExcessOne (a, b)) {m | 0 < m} :=
      sd_kernelIter_interior_le_excess params hNeutral hEq0 hEq1 hAlpha t (a, b)

theorem sd_consensus_almost_sure
    (params : LVParams)
    (a b : ℕ) (hposA : 0 < a) (hposB : 0 < b)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    lvPathMeasure .selfDestructive params (a, b)
      {ω | consensusReachedEvent ω} = 1 := by
  letI : IsMarkovKernel (sdTotalExcessKernel params) :=
    sdTotalExcessKernel_isMarkov params hAlpha
  let P := lvPathMeasure .selfDestructive params (a, b)
  let C : Set (ℕ → PopState) := {ω | consensusReachedEvent ω}
  let A : Set (ℕ → PopState) := {ω | ¬consensusReachedEvent ω}
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hA_le : ∀ t : ℕ,
      P A ≤
        (kernelIter (sdTotalExcessKernel params) t)
          (popExcessOne (a, b)) {m | 0 < m} := by
    intro t
    calc
      P A ≤ P {ω | ∀ u ≤ t, 0 < (ω u).1 ∧ 0 < (ω u).2} := by
        apply measure_mono
        intro ω hω u hu
        have hnreach : ¬reachedConsensus (ω u) := by
          intro hreach
          apply hω
          exact lt_of_le_of_lt
            (consensusTime_le_of_reached' ω u hreach)
            (WithTop.coe_lt_top u)
        simp only [reachedConsensus, not_or] at hnreach
        exact ⟨Nat.pos_of_ne_zero hnreach.1,
          Nat.pos_of_ne_zero hnreach.2⟩
      _ ≤ (kernelIter (sdTotalExcessKernel params) t)
          (popExcessOne (a, b)) {m | 0 < m} :=
        sd_path_stay_interior_le_excess params hNeutral hEq0 hEq1 hAlpha a b t
  have hA_zero : P A = 0 := by
    apply le_antisymm
    · calc
        P A ≤ ⨅ t : ℕ,
            (kernelIter (sdTotalExcessKernel params) t)
              (popExcessOne (a, b)) {m | 0 < m} := le_iInf hA_le
        _ = 0 :=
          sdExcess_survival_iInf_eq_zero params hAlpha
            (popExcessOne (a, b))
    · exact zero_le
  have hC_union :
      C = ⋃ t : ℕ, {ω : ℕ → PopState | consensusTime ω = ↑t} := by
    ext ω
    constructor
    · intro hω
      change consensusTime ω < ⊤ at hω
      rcases WithTop.ne_top_iff_exists.mp
          (WithTop.lt_top_iff_ne_top.mp hω) with ⟨t, ht⟩
      exact Set.mem_iUnion.mpr ⟨t, ht.symm⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨t, ht⟩
      change consensusTime ω < ⊤
      rw [ht]
      exact WithTop.coe_lt_top t
  have hC_meas : MeasurableSet C := by
    rw [hC_union]
    exact MeasurableSet.iUnion fun t =>
      measurableSet_consensusTime_eq_coe t
  have hcomp : Cᶜ = A := by
    ext ω
    simp [C, A]
  have hsum := measure_add_measure_compl hC_meas (μ := P)
  rw [hcomp, hA_zero, add_zero, measure_univ] at hsum
  simpa [P, C] using hsum

end LVConsensus
