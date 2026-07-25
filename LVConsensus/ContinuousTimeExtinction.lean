import LVConsensus.Definitions
import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus

/-!
# Continuous-time birth--death extinction

For a continuous-time birth--death chain, the embedded jump chain chooses an
up/down transition with probabilities proportional to the two rates, while
the mean holding time in state `n` is the reciprocal of their sum.  The
expected absorption time is therefore the expected accumulated holding cost
of the embedded chain.  The definitions below express this directly and avoid
introducing an auxiliary family of exponential random variables.
-/

/-- A conservative continuous-time birth--death rate matrix on `ℕ`, with zero
absorbing and every positive state able to move down. -/
structure ContinuousTimeBirthDeathChain where
  birthRate : Nat → Real
  deathRate : Nat → Real
  birth_nonneg : ∀ n, 0 ≤ birthRate n
  death_nonneg : ∀ n, 0 ≤ deathRate n
  rates_zero : birthRate 0 = 0 ∧ deathRate 0 = 0
  death_pos : ∀ n, 0 < n → 0 < deathRate n

/-- Embedded discrete-time jump chain. -/
noncomputable def ContinuousTimeBirthDeathChain.embedded
    (M : ContinuousTimeBirthDeathChain) : BirthDeathChain where
  p := fun n =>
    if n = 0 then 0 else M.birthRate n / (M.birthRate n + M.deathRate n)
  q := fun n =>
    if n = 0 then 0 else M.deathRate n / (M.birthRate n + M.deathRate n)
  p_nonneg := by
    intro n
    split_ifs with hn
    · exact le_rfl
    · exact div_nonneg (M.birth_nonneg n)
        (add_nonneg (M.birth_nonneg n) (M.death_nonneg n))
  q_nonneg := by
    intro n
    split_ifs with hn
    · exact le_rfl
    · exact div_nonneg (M.death_nonneg n)
        (add_nonneg (M.birth_nonneg n) (M.death_nonneg n))
  pq_le_one := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hden : 0 < M.birthRate n + M.deathRate n := by
        linarith [M.birth_nonneg n, M.death_pos n hnpos]
      rw [← add_div, div_le_one hden]
  absorb_zero := by simp

/-- Mean holding time in state `n`. -/
noncomputable def ctHoldingCost
    (M : ContinuousTimeBirthDeathChain) (n : Nat) : ENNReal :=
  if n = 0 then 0
  else ENNReal.ofReal (1 / (M.birthRate n + M.deathRate n))

/-- Expected holding cost accumulated during the first `t` jumps, stopped at
state zero. -/
noncomputable def ctAbsorptionReward
    (M : ContinuousTimeBirthDeathChain) : Nat → Nat → ENNReal
  | 0, _ => 0
  | t + 1, n =>
      if n = 0 then 0
      else
        ctHoldingCost M n +
          ∫⁻ m, ctAbsorptionReward M t m ∂
            bdKernel M.embedded n

/-- Mean continuous-time absorption time, as the monotone limit of finite
horizon expected holding costs. -/
noncomputable def ctMeanAbsorptionTime
    (M : ContinuousTimeBirthDeathChain) (n : Nat) : ENNReal :=
  ⨆ t : Nat, ctAbsorptionReward M t n

/-- A bounded Foster--Lyapunov certificate for continuous-time absorption.
The drift inequality is the first-step form of `𝓛V ≤ -1`. -/
structure CTAbsorptionCertificate
    (M : ContinuousTimeBirthDeathChain) where
  V : Nat → ENNReal
  bound : ENNReal
  bound_ne_top : bound ≠ ⊤
  zero : V 0 = 0
  le_bound : ∀ n, V n ≤ bound
  drift : ∀ n, 0 < n →
    ctHoldingCost M n +
        ∫⁻ m, V m ∂bdKernel M.embedded n ≤
      V n

lemma ctAbsorptionReward_le_certificate
    (M : ContinuousTimeBirthDeathChain)
    (cert : CTAbsorptionCertificate M) :
    ∀ t n, ctAbsorptionReward M t n ≤ cert.V n := by
  intro t
  induction t with
  | zero =>
      intro n
      simp [ctAbsorptionReward]
  | succ t ih =>
      intro n
      by_cases hn : n = 0
      · subst n
        simp [ctAbsorptionReward, cert.zero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        simp only [ctAbsorptionReward, hn, ↓reduceIte]
        calc
          ctHoldingCost M n +
              ∫⁻ m, ctAbsorptionReward M t m ∂bdKernel M.embedded n
              ≤ ctHoldingCost M n +
                  ∫⁻ m, cert.V m ∂bdKernel M.embedded n := by
                gcongr with m
                exact ih m
          _ ≤ cert.V n := cert.drift n hnpos

theorem ctMeanAbsorptionTime_le_certificate
    (M : ContinuousTimeBirthDeathChain)
    (cert : CTAbsorptionCertificate M) :
    ∀ n, ctMeanAbsorptionTime M n ≤ cert.bound := by
  intro n
  unfold ctMeanAbsorptionTime
  refine iSup_le fun t => ?_
  exact (ctAbsorptionReward_le_certificate M cert t n).trans
    (cert.le_bound n)

/-- Eventual linear/quadratic rate bounds, stated in the notation already used
throughout the formalization. -/
def HasLinearBirthQuadraticDeathRates
    (M : ContinuousTimeBirthDeathChain) : Prop :=
  IsThetaEventually M.birthRate (fun n => (n : Real)) ∧
    IsThetaEventually M.deathRate (fun n => (n : Real) ^ 2)

/-- Bounded potential obtained by summing nonnegative increments. -/
noncomputable def ctPotentialFromIncrements
    (d : Nat → Real) (n : Nat) : Real :=
  ∑ i ∈ Finset.range (n + 1), d i

lemma ctPotentialFromIncrements_zero
    (d : Nat → Real) (hd0 : d 0 = 0) :
    ctPotentialFromIncrements d 0 = 0 := by
  simp [ctPotentialFromIncrements, hd0]

lemma ctPotentialFromIncrements_succ
    (d : Nat → Real) (n : Nat) :
    ctPotentialFromIncrements d (n + 1) =
      ctPotentialFromIncrements d n + d (n + 1) := by
  simp [ctPotentialFromIncrements, Finset.sum_range_succ]

lemma ctPotentialFromIncrements_pred
    (d : Nat → Real) (n : Nat) (hn : 0 < n) :
    ctPotentialFromIncrements d (n - 1) =
      ctPotentialFromIncrements d n - d n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [ctPotentialFromIncrements_succ]
  simp

lemma ctPotentialFromIncrements_nonneg
    (d : Nat → Real) (hd : ∀ n, 0 ≤ d n) (n : Nat) :
    0 ≤ ctPotentialFromIncrements d n := by
  exact Finset.sum_nonneg fun i _ => hd i

lemma ctPotentialFromIncrements_le_tsum
    (d : Nat → Real) (hd : ∀ n, 0 ≤ d n)
    (hsum : Summable d) (n : Nat) :
    ctPotentialFromIncrements d n ≤ ∑' i, d i := by
  exact hsum.sum_le_tsum (Finset.range (n + 1)) fun i _ => hd i

/-- The standard bounded-potential argument, expressed in terms of its
increments.  Unlike an externally supplied certificate, these hypotheses are
elementary scalar inequalities that will be derived below from the rate
assumptions. -/
noncomputable def ctAbsorptionCertificate_of_increments
    (M : ContinuousTimeBirthDeathChain)
    (d : Nat → Real)
    (hd0 : d 0 = 0)
    (hd : ∀ n, 0 ≤ d n)
    (hsum : Summable d)
    (hDrift : ∀ n, 0 < n →
      1 + M.birthRate n * d (n + 1) ≤ M.deathRate n * d n) :
    CTAbsorptionCertificate M := by
  let Vreal := ctPotentialFromIncrements d
  let V : Nat → ENNReal := fun n => ENNReal.ofReal (Vreal n)
  let C : ENNReal := ENNReal.ofReal (∑' i, d i)
  refine
    { V := V
      bound := C
      bound_ne_top := ENNReal.ofReal_ne_top
      zero := ?_
      le_bound := ?_
      drift := ?_ }
  · simp [V, Vreal, ctPotentialFromIncrements_zero d hd0]
  · intro n
    exact ENNReal.ofReal_le_ofReal
      (ctPotentialFromIncrements_le_tsum d hd hsum n)
  · intro n hn
    have hBirth : 0 ≤ M.birthRate n := M.birth_nonneg n
    have hDeath : 0 ≤ M.deathRate n := M.death_nonneg n
    have hDeathPos : 0 < M.deathRate n := M.death_pos n hn
    have hspos : 0 < M.birthRate n + M.deathRate n := by linarith
    have hVnonneg : ∀ m, 0 ≤ Vreal m :=
      fun m => ctPotentialFromIncrements_nonneg d hd m
    have hstep :
        (1 / (M.birthRate n + M.deathRate n)) +
            (M.birthRate n / (M.birthRate n + M.deathRate n)) *
              Vreal (n + 1) +
            (M.deathRate n / (M.birthRate n + M.deathRate n)) *
              Vreal (n - 1) ≤
          Vreal n := by
      dsimp only [Vreal]
      rw [ctPotentialFromIncrements_succ,
        ctPotentialFromIncrements_pred d n hn]
      field_simp [ne_of_gt hspos]
      nlinarith [hDrift n hn]
    have hhold :
        1 - M.birthRate n / (M.birthRate n + M.deathRate n) -
            M.deathRate n / (M.birthRate n + M.deathRate n) = 0 := by
      field_simp [ne_of_gt hspos]
      ring
    simp only [ctHoldingCost, hn.ne', ↓reduceIte,
      ContinuousTimeBirthDeathChain.embedded, bdKernel,
      ProbabilityTheory.Kernel.ofFunOfCountable,
      ProbabilityTheory.Kernel.coe_mk]
    rw [lintegral_add_measure, lintegral_add_measure,
      lintegral_smul_measure, lintegral_smul_measure,
      lintegral_smul_measure, lintegral_dirac, lintegral_dirac,
      lintegral_dirac]
    simp only [hn.ne', ↓reduceIte, V, holdProb, hhold,
      ENNReal.ofReal_zero, zero_smul, add_zero, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (div_nonneg hBirth hspos.le),
      ← ENNReal.ofReal_mul (div_nonneg hDeath hspos.le),
      ← ENNReal.ofReal_add
        (mul_nonneg (div_nonneg hBirth hspos.le) (hVnonneg (n + 1)))
        (mul_nonneg (div_nonneg hDeath hspos.le) (hVnonneg (n - 1)))]
    simp only [zero_mul, add_zero]
    rw [← ENNReal.ofReal_add
      (one_div_nonneg.mpr hspos.le)
      (add_nonneg
        (mul_nonneg (div_nonneg hBirth hspos.le) (hVnonneg (n + 1)))
        (mul_nonneg (div_nonneg hDeath hspos.le) (hVnonneg (n - 1))))]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [add_assoc] using hstep)

/-- Summable shape used for the Lyapunov increments.  Above the cutoff it is
the square-summable tail `1/n²`; below the cutoff it grows geometrically when
read towards zero, allowing finitely many birth-heavy states. -/
noncomputable def ctRateIncrementShape
    (cutoff : Nat) (ratio : Real) (n : Nat) : Real :=
  if n = 0 then 0
  else if cutoff ≤ n then 1 / (n : Real) ^ 2
  else (1 / (cutoff : Real) ^ 2) * ratio ^ (cutoff - n)

lemma ctRateIncrementShape_nonneg
    (cutoff : Nat) (ratio : Real) (hratio : 0 ≤ ratio) :
    ∀ n, 0 ≤ ctRateIncrementShape cutoff ratio n := by
  intro n
  simp only [ctRateIncrementShape]
  split_ifs
  · exact le_rfl
  · positivity
  · positivity

lemma ctRateIncrementShape_pos
    (cutoff : Nat) (ratio : Real)
    (hcutoff : 0 < cutoff) (hratio : 0 < ratio)
    (n : Nat) (hn : 0 < n) :
    0 < ctRateIncrementShape cutoff ratio n := by
  simp only [ctRateIncrementShape, hn.ne', ↓reduceIte]
  split_ifs
  · positivity
  · positivity

lemma ctRateIncrementShape_summable
    (cutoff : Nat) (ratio : Real) (hcutoff : 0 < cutoff) :
    Summable (ctRateIncrementShape cutoff ratio) := by
  have hsq :
      Summable (fun n : Nat => 1 / (n : Real) ^ (2 : Nat)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply hsq.congr_atTop
  filter_upwards [Filter.eventually_ge_atTop cutoff] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le hcutoff hn
  simp [ctRateIncrementShape, hn, hnpos.ne']

lemma ctRateIncrementShape_low_step
    (cutoff : Nat) (ratio : Real)
    (hcutoff : 0 < cutoff)
    (n : Nat) (hn : 0 < n) (hnlow : n < cutoff) :
    ctRateIncrementShape cutoff ratio n =
      ratio * ctRateIncrementShape cutoff ratio (n + 1) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hnnot : ¬ cutoff ≤ n := Nat.not_le_of_gt hnlow
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hnlow) with hsucc | hsucc
  · have hsucc0 : n + 1 ≠ 0 := by omega
    have hsuccnot : ¬ cutoff ≤ n + 1 := Nat.not_le_of_gt hsucc
    have hexp : cutoff - n = (cutoff - (n + 1)) + 1 := by omega
    simp only [ctRateIncrementShape, hn0, ↓reduceIte, hnnot,
      hsucc0, hsuccnot]
    rw [hexp, pow_succ]
    ring
  · have hsucc0 : n + 1 ≠ 0 := by omega
    have hsuccle : cutoff ≤ n + 1 := hsucc.ge
    have hexp : cutoff - n = 1 := by omega
    simp only [ctRateIncrementShape, hn0, ↓reduceIte, hnnot,
      hsucc0, hsuccle, hexp, pow_one]
    rw [← hsucc]
    ring

private lemma exists_finite_positive_scale
    (s : Finset Nat) (g : Nat → Real)
    (hg : ∀ n ∈ s, 0 < g n) :
    ∃ A : Real, 0 < A ∧ ∀ n ∈ s, 1 ≤ A * g n := by
  let A : Real := 1 + ∑ n ∈ s, 1 / g n
  have hsum_nonneg : 0 ≤ ∑ n ∈ s, 1 / g n := by
    exact Finset.sum_nonneg fun n hn =>
      one_div_nonneg.mpr (hg n hn).le
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro n hn
  have hsingle :
      1 / g n ≤ ∑ i ∈ s, 1 / g i := by
    exact Finset.single_le_sum
      (s := s) (f := fun i => 1 / g i)
      (fun i hi => one_div_nonneg.mpr (hg i hi).le) hn
  have hle : 1 / g n ≤ A := by
    dsimp [A]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hle (hg n hn).le
  rw [one_div_mul_cancel (ne_of_gt (hg n hn))] at hmul
  simpa only [mul_comm] using hmul

private lemma exists_finite_rate_ratio
    (s : Finset Nat) (birth death : Nat → Real)
    (hBirth : ∀ n, 0 ≤ birth n)
    (hDeath : ∀ n ∈ s, 0 < death n) :
    ∃ R : Real, 1 ≤ R ∧
      ∀ n ∈ s, birth n ≤ death n * (R - 1) := by
  let R : Real := 1 + ∑ n ∈ s, birth n / death n
  have hsum_nonneg : 0 ≤ ∑ n ∈ s, birth n / death n := by
    exact Finset.sum_nonneg fun n hn =>
      div_nonneg (hBirth n) (hDeath n hn).le
  refine ⟨R, by dsimp [R]; linarith, ?_⟩
  intro n hn
  have hsingle :
      birth n / death n ≤ ∑ i ∈ s, birth i / death i := by
    exact Finset.single_le_sum
      (fun i hi => div_nonneg (hBirth i) (hDeath i hi).le) hn
  have hratio : birth n / death n ≤ R - 1 := by
    simpa only [R, add_sub_cancel_left] using hsingle
  have hmul := (div_le_iff₀ (hDeath n hn)).mp hratio
  simpa only [mul_comm] using hmul

private lemma ct_rate_increment_high_margin
    (birth death : Nat → Real) (C D : Real)
    (hC : 0 ≤ C) (hD : 0 < D)
    (n₀ : Nat)
    (hBirth : ∀ n, n₀ ≤ n → birth n ≤ C * (n : Real))
    (hDeath : ∀ n, n₀ ≤ n → D * (n : Real) ^ 2 ≤ death n)
    (n : Nat)
    (hn₀ : n₀ ≤ n)
    (hnlarge : Nat.ceil (2 * C / D) + 1 ≤ n) :
    D / 2 ≤
      death n * (1 / (n : Real) ^ 2) -
        birth n * (1 / ((n + 1 : Nat) : Real) ^ 2) := by
  have hn : 0 < n := by
    have hceil_nonneg : 0 ≤ Nat.ceil (2 * C / D) := Nat.zero_le _
    omega
  have hnR : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hsuccR : (0 : Real) < (n + 1 : Nat) := by positivity
  have hdeathDiv : D ≤ death n / (n : Real) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hnR)]
    simpa only [mul_comm] using hDeath n hn₀
  have hbirthDiv :
      birth n / ((n + 1 : Nat) : Real) ^ 2 ≤ C / (n : Real) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hsuccR) hnR]
    calc
      birth n * (n : Real)
          ≤ (C * (n : Real)) * (n : Real) :=
            mul_le_mul_of_nonneg_right (hBirth n hn₀) hnR.le
      _ ≤ C * ((n + 1 : Nat) : Real) ^ 2 := by
        push_cast
        nlinarith
  have hCdiv : C / (n : Real) ≤ D / 2 := by
    rw [div_le_div_iff₀ hnR (by positivity : (0 : Real) < 2)]
    have h1 :
        (Nat.ceil (2 * C / D) : Real) + 1 ≤ n := by
      exact_mod_cast hnlarge
    have h2 :
        2 * C / D ≤ (Nat.ceil (2 * C / D) : Real) :=
      Nat.le_ceil _
    have h3 : 2 * C / D ≤ (n : Real) - 1 := by linarith
    have h4 : 2 * C ≤ D * ((n : Real) - 1) := by
      simpa only [mul_comm] using (div_le_iff₀ hD).mp h3
    nlinarith
  rw [mul_one_div, mul_one_div]
  linarith

/-- The paper's continuous-time extinction lemma.  The proof is the
first-step recurrence underlying the birth--death series used in Cho et al.,
Lemma 6: a summable sequence of potential increments is constructed from the
linear upper bound on births and the quadratic lower bound on deaths.  The
finitely many states below the asymptotic cutoff are handled using the strict
positivity of every downward rate. -/
theorem lemma_continuous_extinction
    (M : ContinuousTimeBirthDeathChain)
    (hRates : HasLinearBirthQuadraticDeathRates M) :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ m : Nat, ctMeanAbsorptionTime M m ≤ C := by
  rcases hRates.1.1 with ⟨C, nBirth, hC, hBirth⟩
  rcases hRates.2.2 with ⟨D, nDeath, hD, hDeath⟩
  let cutoff :=
    max (max nBirth nDeath) (Nat.ceil (2 * C / D) + 1)
  have hcutoff_pos : 0 < cutoff := by
    dsimp only [cutoff]
    have hle :
        Nat.ceil (2 * C / D) + 1 ≤
          max (max nBirth nDeath) (Nat.ceil (2 * C / D) + 1) :=
      le_max_right _ _
    omega
  let lowStates := Finset.Ico 1 cutoff
  obtain ⟨R, hR, hRateRatio⟩ :=
    exists_finite_rate_ratio lowStates M.birthRate M.deathRate
      M.birth_nonneg (by
        intro n hn
        exact M.death_pos n (by
          have := (Finset.mem_Ico.mp hn).1
          omega))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let shape := ctRateIncrementShape cutoff R
  let margin := fun n =>
    M.deathRate n * shape n - M.birthRate n * shape (n + 1)
  have hmargin_pos : ∀ n, 0 < n → 0 < margin n := by
    intro n hn
    by_cases hnlow : n < cutoff
    · have hnmem : n ∈ lowStates := by
        exact Finset.mem_Ico.mpr ⟨hn, hnlow⟩
      have hratio := hRateRatio n hnmem
      have hshapeSucc :
          0 < shape (n + 1) := by
        exact ctRateIncrementShape_pos cutoff R hcutoff_pos hRpos
          (n + 1) (Nat.succ_pos n)
      have hstep :
          shape n = R * shape (n + 1) := by
        exact ctRateIncrementShape_low_step cutoff R hcutoff_pos n hn hnlow
      have hdeath := M.death_pos n hn
      dsimp only [margin]
      rw [hstep]
      nlinarith [mul_pos hdeath hshapeSucc]
    · have hncut : cutoff ≤ n := Nat.le_of_not_gt hnlow
      have hnlarge : Nat.ceil (2 * C / D) + 1 ≤ n :=
        le_trans (le_max_right _ _) hncut
      have hhigh :=
        ct_rate_increment_high_margin M.birthRate M.deathRate C D hC hD
          (max nBirth nDeath)
          (fun k hk =>
            hBirth k (le_trans (le_max_left _ _) hk))
          (fun k hk =>
            hDeath k (le_trans (le_max_right _ _) hk))
          n
          (le_trans (le_max_left _ _) hncut)
          hnlarge
      have hshapeN :
          shape n = 1 / (n : Real) ^ 2 := by
        simp [shape, ctRateIncrementShape, hn.ne', hncut]
      have hshapeSucc :
          shape (n + 1) = 1 / ((n + 1 : Nat) : Real) ^ 2 := by
        have hs : cutoff ≤ n + 1 := hncut.trans (Nat.le_succ n)
        simp [shape, ctRateIncrementShape, hs]
      dsimp only [margin]
      rw [hshapeN, hshapeSucc]
      linarith
  obtain ⟨A₀, hA₀pos, hA₀⟩ :=
    exists_finite_positive_scale lowStates margin (by
      intro n hn
      exact hmargin_pos n (by
        have := (Finset.mem_Ico.mp hn).1
        omega))
  let A := max A₀ (2 / D)
  have hApos : 0 < A := lt_of_lt_of_le hA₀pos (le_max_left _ _)
  have hA₀le : A₀ ≤ A := le_max_left _ _
  have hADle : 2 / D ≤ A := le_max_right _ _
  have hscaled_margin :
      ∀ n, 0 < n → 1 ≤ A * margin n := by
    intro n hn
    by_cases hnlow : n < cutoff
    · have hnmem : n ∈ lowStates :=
        Finset.mem_Ico.mpr ⟨hn, hnlow⟩
      exact (hA₀ n hnmem).trans
        (mul_le_mul_of_nonneg_right hA₀le (hmargin_pos n hn).le)
    · have hncut : cutoff ≤ n := Nat.le_of_not_gt hnlow
      have hnlarge : Nat.ceil (2 * C / D) + 1 ≤ n :=
        le_trans (le_max_right _ _) hncut
      have hhigh :=
        ct_rate_increment_high_margin M.birthRate M.deathRate C D hC hD
          (max nBirth nDeath)
          (fun k hk =>
            hBirth k (le_trans (le_max_left _ _) hk))
          (fun k hk =>
            hDeath k (le_trans (le_max_right _ _) hk))
          n
          (le_trans (le_max_left _ _) hncut)
          hnlarge
      have hshapeN :
          shape n = 1 / (n : Real) ^ 2 := by
        simp [shape, ctRateIncrementShape, hn.ne', hncut]
      have hshapeSucc :
          shape (n + 1) = 1 / ((n + 1 : Nat) : Real) ^ 2 := by
        have hs : cutoff ≤ n + 1 := hncut.trans (Nat.le_succ n)
        simp [shape, ctRateIncrementShape, hs]
      have hmarginHigh : D / 2 ≤ margin n := by
        dsimp only [margin]
        rw [hshapeN, hshapeSucc]
        exact hhigh
      have hscale : 1 ≤ A * (D / 2) := by
        have hmul :=
          mul_le_mul_of_nonneg_right hADle
            (show 0 ≤ D / 2 by positivity)
        have hDne : D ≠ 0 := ne_of_gt hD
        calc
          1 = (2 / D) * (D / 2) := by field_simp
          _ ≤ A * (D / 2) := hmul
      exact hscale.trans
        (mul_le_mul_of_nonneg_left hmarginHigh hApos.le)
  let d := fun n => A * shape n
  have hd0 : d 0 = 0 := by
    simp [d, shape, ctRateIncrementShape]
  have hdnonneg : ∀ n, 0 ≤ d n := by
    intro n
    exact mul_nonneg hApos.le
      (ctRateIncrementShape_nonneg cutoff R hRpos.le n)
  have hdsum : Summable d := by
    exact Summable.mul_left A
      (ctRateIncrementShape_summable cutoff R hcutoff_pos)
  have hDrift :
      ∀ n, 0 < n →
        1 + M.birthRate n * d (n + 1) ≤ M.deathRate n * d n := by
    intro n hn
    have h := hscaled_margin n hn
    dsimp only [d, margin] at h ⊢
    nlinarith
  let cert :=
    ctAbsorptionCertificate_of_increments M d hd0 hdnonneg hdsum hDrift
  exact
    ⟨cert.bound, cert.bound_ne_top,
      ctMeanAbsorptionTime_le_certificate M cert⟩

/-- Internal reduction retained for downstream developments that already have
an explicit bounded potential. -/
theorem continuous_extinction_from_certificate
    (M : ContinuousTimeBirthDeathChain)
    (_hRates : HasLinearBirthQuadraticDeathRates M)
    (cert : CTAbsorptionCertificate M) :
    ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ m : Nat, ctMeanAbsorptionTime M m ≤ C := by
  refine ⟨cert.bound, ?_, ctMeanAbsorptionTime_le_certificate M cert⟩
  exact cert.bound_ne_top

end LVConsensus
