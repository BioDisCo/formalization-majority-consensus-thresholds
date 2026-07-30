import LVConsensus.MarkovLib
import LVConsensus.NsdConsensusGeneral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.Kernel

namespace LVConsensus

private noncomputable def nsdRatio (s : PopState) : ℝ :=
  if s = (0, 0) then 0 else (s.1 : ℝ) / (s.1 + s.2)

private lemma nsdRatio_of_ne (s : PopState) (hs : s ≠ (0, 0)) :
    nsdRatio s = (s.1 : ℝ) / (s.1 + s.2) := by
  simp [nsdRatio, hs]

private lemma nsdRatio_bound (s : PopState) :
    0 ≤ nsdRatio s ∧ nsdRatio s ≤ 1 := by
  rcases s with ⟨a, b⟩
  by_cases hzero : (a, b) = (0, 0)
  · simp [nsdRatio, hzero]
  · have hsum : 0 < (a : ℝ) + b := by
      have : 0 < a + b := by
        rw [Nat.add_pos_iff_pos_or_pos]
        by_contra h
        push_neg at h
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero h.1
        have hb0 : b = 0 := Nat.eq_zero_of_le_zero h.2
        exact hzero (by simp [ha0, hb0])
      exact_mod_cast this
    simp only [nsdRatio, hzero, ↓reduceIte]
    constructor
    · positivity
    · rw [div_le_one hsum]
      exact_mod_cast Nat.le_add_right a b

private lemma nsdRatio_consensus0 (a : ℕ) (ha : 0 < a) :
    nsdRatio (a, 0) = 1 := by
  simp [nsdRatio, ha.ne']

private lemma nsdRatio_diagonal (m : ℕ) (hm : 0 < m) :
    nsdRatio (m, m) = 1 / 2 := by
  unfold nsdRatio
  rw [if_neg (show (m, m) ≠ (0, 0) from by
    intro h
    have hm0 : m = 0 := congrArg Prod.fst h
    omega)]
  simp only [Prod.fst, Prod.snd]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  field_simp
  ring

/-- Boundary used in the comparison proof: stop when species 0 is no
    longer strictly ahead, or when species 1 has become extinct. -/
private def nsdMajorityBoundary (s : PopState) : Prop :=
  s.2 = 0 ∨ s.1 ≤ s.2

private instance nsdMajorityBoundary_decidable (s : PopState) :
    Decidable (nsdMajorityBoundary s) := by
  unfold nsdMajorityBoundary
  infer_instance

private noncomputable def nsdMajorityStoppedKernel
    (params : LVParams) : Kernel PopState PopState :=
  Kernel.ofFunOfCountable fun s =>
    if nsdMajorityBoundary s then Measure.dirac s
    else (lvKernel .nonSelfDestructive params) s

private instance nsdMajorityStoppedKernel_isMarkov
    (params : LVParams)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    IsMarkovKernel (nsdMajorityStoppedKernel params) := by
  constructor
  intro s
  constructor
  simp only [nsdMajorityStoppedKernel, Kernel.ofFunOfCountable,
    Kernel.coe_mk]
  split_ifs
  · exact Measure.dirac.isProbabilityMeasure.measure_univ
  · exact (IsMarkovKernel.isProbabilityMeasure s).measure_univ

private lemma nsdMajorityStoppedKernel_boundary
    (params : LVParams) (s : PopState)
    (hs : nsdMajorityBoundary s) :
    nsdMajorityStoppedKernel params s = Measure.dirac s := by
  change (if nsdMajorityBoundary s then Measure.dirac s
    else (lvKernel .nonSelfDestructive params) s) = Measure.dirac s
  rw [if_pos hs]

private lemma nsdMajorityStoppedKernel_open
    (params : LVParams) (s : PopState)
    (hs : ¬nsdMajorityBoundary s) :
    nsdMajorityStoppedKernel params s =
      lvKernel .nonSelfDestructive params s := by
  change (if nsdMajorityBoundary s then Measure.dirac s
    else (lvKernel .nonSelfDestructive params) s) =
      (lvKernel .nonSelfDestructive params) s
  rw [if_neg hs]

/-- In a finite history, the first boundary state belongs to `A`. -/
private def nsdStopOutcomeBy
    (A : Set PopState) : ℕ → (ℕ → PopState) → Prop
  | 0, ω => ω 0 ∈ A
  | N + 1, ω =>
      if nsdMajorityBoundary (ω 0) then ω 0 ∈ A
      else nsdStopOutcomeBy A N (pathShift 1 ω)

private lemma measurable_pathShift_one :
    Measurable (pathShift 1 : (ℕ → PopState) → (ℕ → PopState)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (1 + n)

private lemma measurableSet_nsdStopOutcomeBy
    (A : Set PopState) (hA : MeasurableSet A) :
    ∀ N : ℕ, MeasurableSet {ω : ℕ → PopState | nsdStopOutcomeBy A N ω} := by
  intro N
  induction N with
  | zero =>
      exact hA.preimage (measurable_pi_apply 0)
  | succ N ih =>
      have hB : MeasurableSet {s : PopState | nsdMajorityBoundary s} :=
        (Set.to_countable _).measurableSet
      have hEq :
          {ω : ℕ → PopState | nsdStopOutcomeBy A (N + 1) ω} =
            (((fun ω : ℕ → PopState => ω 0) ⁻¹'
                {s | nsdMajorityBoundary s}) ∩
              (fun ω : ℕ → PopState => ω 0) ⁻¹' A) ∪
            (((fun ω : ℕ → PopState => ω 0) ⁻¹'
                {s | nsdMajorityBoundary s})ᶜ ∩
              (pathShift 1) ⁻¹'
                {ω | nsdStopOutcomeBy A N ω}) := by
        ext ω
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_setOf_eq, Set.mem_compl_iff]
        by_cases hω : nsdMajorityBoundary (ω 0)
        · simp [nsdStopOutcomeBy, hω]
        · simp [nsdStopOutcomeBy, hω]
      rw [hEq]
      exact ((hB.preimage (measurable_pi_apply 0)).inter
          (hA.preimage (measurable_pi_apply 0))).union
        ((hB.preimage (measurable_pi_apply 0)).compl.inter
          (ih.preimage measurable_pathShift_one))

private lemma lvPath_initial_ae_intra
    (params : LVParams) (s : PopState)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∀ᵐ ω ∂lvPathMeasure .nonSelfDestructive params s, ω 0 = s := by
  rw [ae_iff]
  simpa [lvPathMeasure] using
    homogeneousPathMeasure_initial_ne_null
      (lvKernel .nonSelfDestructive params) s

private lemma nsdStopOutcomeBy_measure_succ
    (params : LVParams) (A : Set PopState) (hA : MeasurableSet A)
    (N : ℕ) (s : PopState)
    (hs : ¬nsdMajorityBoundary s)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s
        {ω | nsdStopOutcomeBy A (N + 1) ω} =
      ∫⁻ x, lvPathMeasure .nonSelfDestructive params x
          {ω | nsdStopOutcomeBy A N ω}
        ∂(lvKernel .nonSelfDestructive params) s := by
  have hEvent :
      lvPathMeasure .nonSelfDestructive params s
          {ω | nsdStopOutcomeBy A (N + 1) ω} =
        lvPathMeasure .nonSelfDestructive params s
          ((pathShift 1) ⁻¹'
            {ω | nsdStopOutcomeBy A N ω}) := by
    apply measure_congr
    filter_upwards [lvPath_initial_ae_intra params s] with ω hω0
    apply propext
    change nsdStopOutcomeBy A (N + 1) ω ↔
      nsdStopOutcomeBy A N (pathShift 1 ω)
    have hωopen : ¬nsdMajorityBoundary (ω 0) := by
      simpa [hω0] using hs
    rw [nsdStopOutcomeBy, if_neg hωopen]
  rw [hEvent]
  simpa [lvPathMeasure, kernelIter_one_generic] using
    homogeneousPathMeasure_shift_apply
      (lvKernel .nonSelfDestructive params) s 1
      {ω | nsdStopOutcomeBy A N ω}
      (measurableSet_nsdStopOutcomeBy A hA N)

private lemma nsdMajorityStoppedKernel_iter_boundary
    (params : LVParams)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)]
    (N : ℕ) (s : PopState) (hs : nsdMajorityBoundary s) :
    kernelIter (nsdMajorityStoppedKernel params) N s =
      Measure.dirac s := by
  induction N with
  | zero => simp [kernelIter_zero, Kernel.id_apply]
  | succ N ih =>
      rw [kernelIter_succ, Kernel.comp_apply, ih]
      simp only [Measure.dirac_bind (Kernel.measurable _)]
      exact nsdMajorityStoppedKernel_boundary params s hs

private lemma nsdMajorityStoppedKernel_outcomeBy_eq
    (params : LVParams)
    (A : Set PopState) (hA : MeasurableSet A)
    (hAB : A ⊆ {s | nsdMajorityBoundary s})
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∀ (N : ℕ) (s : PopState),
      kernelIter (nsdMajorityStoppedKernel params) N s A =
        lvPathMeasure .nonSelfDestructive params s
          {ω | nsdStopOutcomeBy A N ω} := by
  intro N
  induction N with
  | zero =>
      intro s
      letI : IsProbabilityMeasure
          (lvPathMeasure .nonSelfDestructive params s) := by
        dsimp [lvPathMeasure, homogeneousPathMeasure]
        infer_instance
      rw [kernelIter_zero, Kernel.id_apply,
        Measure.dirac_apply' _ hA]
      by_cases hsA : s ∈ A
      · simp only [Set.indicator_of_mem hsA]
        calc
          1 = lvPathMeasure .nonSelfDestructive params s Set.univ := by
            rw [measure_univ]
          _ = lvPathMeasure .nonSelfDestructive params s
                {ω | nsdStopOutcomeBy A 0 ω} := by
            apply measure_congr
            filter_upwards [lvPath_initial_ae_intra params s] with ω hω0
            apply propext
            change True ↔ ω 0 ∈ A
            rw [hω0]
            exact (iff_true_intro hsA).symm
      · simp only [Set.indicator_of_notMem hsA]
        calc
          0 = lvPathMeasure .nonSelfDestructive params s ∅ := by
            rw [measure_empty]
          _ = lvPathMeasure .nonSelfDestructive params s
                {ω | nsdStopOutcomeBy A 0 ω} := by
            apply measure_congr
            filter_upwards [lvPath_initial_ae_intra params s] with ω hω0
            apply propext
            change False ↔ ω 0 ∈ A
            rw [hω0]
            exact (iff_false_intro hsA).symm
  | succ N ih =>
      intro s
      letI : IsProbabilityMeasure
          (lvPathMeasure .nonSelfDestructive params s) := by
        dsimp [lvPathMeasure, homogeneousPathMeasure]
        infer_instance
      by_cases hs : nsdMajorityBoundary s
      · rw [nsdMajorityStoppedKernel_iter_boundary params (N + 1) s hs,
          Measure.dirac_apply' _ hA]
        by_cases hsA : s ∈ A
        · simp only [Set.indicator_of_mem hsA]
          calc
            1 = lvPathMeasure .nonSelfDestructive params s Set.univ := by
              rw [measure_univ]
            _ = lvPathMeasure .nonSelfDestructive params s
                  {ω | nsdStopOutcomeBy A (N + 1) ω} := by
              apply measure_congr
              filter_upwards [lvPath_initial_ae_intra params s] with ω hω0
              apply propext
              change True ↔
                (if nsdMajorityBoundary (ω 0) then
                  ω 0 ∈ A else nsdStopOutcomeBy A N (pathShift 1 ω))
              rw [hω0, if_pos hs]
              exact (iff_true_intro hsA).symm
        · simp only [Set.indicator_of_notMem hsA]
          calc
            0 = lvPathMeasure .nonSelfDestructive params s ∅ := by
              rw [measure_empty]
            _ = lvPathMeasure .nonSelfDestructive params s
                  {ω | nsdStopOutcomeBy A (N + 1) ω} := by
              apply measure_congr
              filter_upwards [lvPath_initial_ae_intra params s] with ω hω0
              apply propext
              change False ↔
                (if nsdMajorityBoundary (ω 0) then
                  ω 0 ∈ A else nsdStopOutcomeBy A N (pathShift 1 ω))
              rw [hω0, if_pos hs]
              exact (iff_false_intro hsA).symm
      · rw [kernelIter_succ_right, Kernel.comp_apply' _ _ _ hA,
          nsdMajorityStoppedKernel_open params s hs,
          nsdStopOutcomeBy_measure_succ params A hA N s hs]
        exact lintegral_congr fun x => ih x

private lemma nsdRatio_weighted_superharmonic
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    params.beta * a * nsdRatio (a + 1, b) +
      params.beta * b * nsdRatio (a, b + 1) +
      (params.delta * a + params.alpha1 * a * b +
        params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) *
          nsdRatio (a - 1, b) +
      (params.delta * b + params.alpha0 * a * b +
        params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) *
          nsdRatio (a, b - 1) ≤
      lvTotalPropensity params (a, b) * nsdRatio (a, b) := by
  have hcur : (a, b) ≠ (0, 0) := by
    intro h
    have : a = 0 := congrArg Prod.fst h
    omega
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hsum : (a : ℝ) + b ≠ 0 := by positivity
  have hsump : (a : ℝ) + b + 1 ≠ 0 := by positivity
  have hsumm : (a : ℝ) + b - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (a : ℝ) + b := by
      exact_mod_cast (show 2 ≤ a + b by omega)
    linarith
  have hmain :=
    nsd_superharmonic_weighted_le_general
      (a : ℝ) (b : ℝ) params.alpha0 params.gamma0
      params.beta params.delta
      (Nat.cast_nonneg a) (Nat.cast_nonneg b)
      (by exact_mod_cast hba) hGe hsum hsump hsumm
      (by exact_mod_cast (show 1 ≤ a + b by omega))
  rw [nsdRatio_of_ne (a + 1, b) (by
      intro h
      have : a + 1 = 0 := congrArg Prod.fst h
      omega),
    nsdRatio_of_ne (a, b + 1) (by
      intro h
      have : b + 1 = 0 := congrArg Prod.snd h
      omega),
    nsdRatio_of_ne (a - 1, b) (by
      intro h
      have : b = 0 := congrArg Prod.snd h
      omega),
    nsdRatio_of_ne (a, b - 1) (by
      intro h
      have : a = 0 := congrArg Prod.fst h
      omega),
    nsdRatio_of_ne (a, b) hcur]
  simp only [Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (show 1 ≤ a from ha),
    Nat.cast_sub (show 1 ≤ b from hb)]
  unfold lvTotalPropensity
  rw [← hNeutral, ← hGamma]
  convert hmain using 1 <;> ring

private lemma nsdRatio_stopped_superharmonic
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (s : PopState)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∫ x, nsdRatio x ∂nsdMajorityStoppedKernel params s ≤
      nsdRatio s := by
  by_cases hs : nsdMajorityBoundary s
  · rw [nsdMajorityStoppedKernel_boundary params s hs,
      integral_dirac' nsdRatio s
        (measurable_of_countable nsdRatio).stronglyMeasurable]
  · rw [nsdMajorityStoppedKernel_open params s hs]
    rcases s with ⟨a, b⟩
    have hb0 : b ≠ 0 := by
      intro h
      exact hs (Or.inl h)
    have hnotle : ¬a ≤ b := by
      intro h
      exact hs (Or.inr h)
    have ha : 0 < a := by omega
    have hb : 0 < b := Nat.pos_of_ne_zero hb0
    have hba : b ≤ a := by omega
    have hφ : lvTotalPropensity params (a, b) ≠ 0 := by
      have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
      have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
      have ha1R : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
      have hb1R : (1 : ℝ) ≤ b := Nat.one_le_cast.mpr hb
      have hinter :
          0 < params.alpha0 * (a : ℝ) * (b : ℝ) := by
        positivity
      have hga :
          0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := by
        exact div_nonneg
          (mul_nonneg haR.le (by linarith)) (by norm_num)
      have hgb :
          0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 := by
        exact div_nonneg
          (mul_nonneg hbR.le (by linarith)) (by norm_num)
      unfold lvTotalPropensity
      nlinarith [params.beta_nonneg, params.delta_nonneg,
        params.alpha1_nonneg, params.gamma0_nonneg,
        params.gamma1_nonneg,
        mul_nonneg params.beta_nonneg haR.le,
        mul_nonneg params.beta_nonneg hbR.le,
        mul_nonneg params.delta_nonneg haR.le,
        mul_nonneg params.delta_nonneg hbR.le,
        mul_nonneg (mul_nonneg params.alpha1_nonneg haR.le) hbR.le,
        mul_nonneg params.gamma0_nonneg hga,
        mul_nonneg params.gamma1_nonneg hgb]
    exact lvKernel_nsd_superharmonic_integral
      params nsdRatio a b ha hb hφ
        (nsdRatio_weighted_superharmonic
          params hNeutral hGamma hGe a b ha hb hba)

private lemma nsdRatio_stopped_iter_le
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (s : PopState) (N : ℕ)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∫ x, nsdRatio x
        ∂kernelIter (nsdMajorityStoppedKernel params) N s ≤
      nsdRatio s := by
  apply kernelIter_superharmonic_integral_le_at
    (nsdMajorityStoppedKernel params) nsdRatio s N
      (fun _ => Set.univ)
  · intro k hk
    simp
  · intro k hk x hx
    exact nsdRatio_stopped_superharmonic
      params hAlpha hNeutral hGamma hGe x
  · intro k hk
    haveI : IsProbabilityMeasure
        (kernelIter (nsdMajorityStoppedKernel params) k s) :=
      (kernelIter_isMarkov k).isProbabilityMeasure s
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable nsdRatio).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr
      ⟨by linarith [(nsdRatio_bound x).1],
        (nsdRatio_bound x).2⟩

private lemma nsd_boundary_payoff_by_le
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (a b N : ℕ)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
          {ω | nsdStopOutcomeBy {s | 0 < s.1 ∧ s.2 = 0} N ω} +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure .nonSelfDestructive params (a, b)
            {ω | nsdStopOutcomeBy
              {s | s.1 = s.2 ∧ 0 < s.1} N ω} ≤
      ENNReal.ofReal (nsdRatio (a, b)) := by
  let A : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  let D : Set PopState := {s | s.1 = s.2 ∧ 0 < s.1}
  let μ : Measure PopState :=
    kernelIter (nsdMajorityStoppedKernel params) N (a, b)
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hD : MeasurableSet D := (Set.to_countable D).measurableSet
  have hAB : A ⊆ {s | nsdMajorityBoundary s} := by
    intro s hs
    exact Or.inl hs.2
  have hDB : D ⊆ {s | nsdMajorityBoundary s} := by
    intro s hs
    exact Or.inr (le_of_eq hs.1)
  rw [show {s : PopState | 0 < s.1 ∧ s.2 = 0} = A from rfl,
    show {s : PopState | s.1 = s.2 ∧ 0 < s.1} = D from rfl,
    ← nsdMajorityStoppedKernel_outcomeBy_eq
      params A hA hAB N (a, b),
    ← nsdMajorityStoppedKernel_outcomeBy_eq
      params D hD hDB N (a, b)]
  haveI : IsProbabilityMeasure μ :=
    (kernelIter_isMarkov
      (K := nsdMajorityStoppedKernel params) N)
      |>.isProbabilityMeasure (a, b)
  have hInt : Integrable nsdRatio μ := by
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable nsdRatio).aestronglyMeasurable
    filter_upwards with s
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr
      ⟨by linarith [(nsdRatio_bound s).1],
        (nsdRatio_bound s).2⟩
  have hPayoff :
      ∫⁻ s, ENNReal.ofReal (nsdRatio s) ∂μ ≤
        ENNReal.ofReal (nsdRatio (a, b)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun s => (nsdRatio_bound s).1)]
    exact ENNReal.ofReal_le_ofReal
      (nsdRatio_stopped_iter_le
        params hAlpha hNeutral hGamma hGe (a, b) N)
  have hAm :
      Measurable (A.indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hA
  calc
    μ A + ENNReal.ofReal (1 / 2) * μ D =
        (∫⁻ s, A.indicator (fun _ => (1 : ENNReal)) s ∂μ) +
          ∫⁻ s, D.indicator
            (fun _ => ENNReal.ofReal (1 / 2)) s ∂μ := by
      rw [lintegral_indicator_const hA, lintegral_indicator_const hD]
      simp
    _ = ∫⁻ s,
          A.indicator (fun _ => (1 : ENNReal)) s +
            D.indicator (fun _ => ENNReal.ofReal (1 / 2)) s ∂μ := by
      rw [lintegral_add_left hAm]
    _ ≤ ∫⁻ s, ENNReal.ofReal (nsdRatio s) ∂μ := by
      apply lintegral_mono
      intro s
      by_cases hsA : s ∈ A
      · have hsD : s ∉ D := by
          intro hsD
          simp only [A, D, Set.mem_setOf_eq] at hsA hsD
          omega
        rcases s with ⟨x, y⟩
        simp only [A, Set.mem_setOf_eq] at hsA
        rcases hsA with ⟨hx, rfl⟩
        have hxA : (x, 0) ∈ A := ⟨hx, rfl⟩
        have hxD : (x, 0) ∉ D := hsD
        simp [Set.indicator_of_mem hxA,
          Set.indicator_of_notMem hxD,
          nsdRatio_consensus0 x hx]
      · by_cases hsD : s ∈ D
        · rcases s with ⟨x, y⟩
          simp only [D, Set.mem_setOf_eq] at hsD
          rcases hsD with ⟨hxy, hx⟩
          subst y
          have hxD : (x, x) ∈ D := ⟨rfl, hx⟩
          have hxA : (x, x) ∉ A := hsA
          simp [Set.indicator_of_notMem hxA,
            Set.indicator_of_mem hxD,
            nsdRatio_diagonal x hx]
        · simp [Set.indicator_of_notMem hsA,
            Set.indicator_of_notMem hsD]
    _ ≤ ENNReal.ofReal (nsdRatio (a, b)) := hPayoff

private lemma nsdStopOutcomeBy_monotone
    (A : Set PopState)
    (hAB : A ⊆ {s | nsdMajorityBoundary s}) :
    Monotone (fun N : ℕ =>
      {ω : ℕ → PopState | nsdStopOutcomeBy A N ω}) := by
  intro N M hNM
  suffices hstep : ∀ n : ℕ,
      {ω : ℕ → PopState | nsdStopOutcomeBy A n ω} ⊆
        {ω | nsdStopOutcomeBy A (n + 1) ω} by
    induction M, hNM using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ M hNM ih => exact ih.trans (hstep M)
  intro n
  induction n with
  | zero =>
      intro ω hω
      by_cases hB : nsdMajorityBoundary (ω 0)
      · simpa [nsdStopOutcomeBy, hB] using hω
      · exact (hB (hAB hω)).elim
  | succ n ih =>
      intro ω hω
      by_cases hB : nsdMajorityBoundary (ω 0)
      · simpa [nsdStopOutcomeBy, hB] using hω
      · have hω' :
            nsdStopOutcomeBy A n (pathShift 1 ω) := by
          simpa [nsdStopOutcomeBy, hB] using hω
        have hout := ih hω'
        simpa [nsdStopOutcomeBy, hB] using hout

private def nsdStopOutcome
    (A : Set PopState) (ω : ℕ → PopState) : Prop :=
  ∃ N : ℕ, nsdStopOutcomeBy A N ω

private lemma nsdStopOutcome_eq_iUnion (A : Set PopState) :
    {ω : ℕ → PopState | nsdStopOutcome A ω} =
      ⋃ N : ℕ, {ω | nsdStopOutcomeBy A N ω} := by
  ext ω
  simp [nsdStopOutcome]

private lemma nsd_boundary_payoff_le
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (a b : ℕ)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
          {ω | nsdStopOutcome {s | 0 < s.1 ∧ s.2 = 0} ω} +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure .nonSelfDestructive params (a, b)
            {ω | nsdStopOutcome
              {s | s.1 = s.2 ∧ 0 < s.1} ω} ≤
      ENNReal.ofReal (nsdRatio (a, b)) := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let A : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  let D : Set PopState := {s | s.1 = s.2 ∧ 0 < s.1}
  let EA : ℕ → Set (ℕ → PopState) :=
    fun N => {ω | nsdStopOutcomeBy A N ω}
  let ED : ℕ → Set (ℕ → PopState) :=
    fun N => {ω | nsdStopOutcomeBy D N ω}
  have hAB : A ⊆ {s | nsdMajorityBoundary s} := by
    intro s hs
    exact Or.inl hs.2
  have hDB : D ⊆ {s | nsdMajorityBoundary s} := by
    intro s hs
    exact Or.inr (le_of_eq hs.1)
  have hEA : Monotone EA := by
    simpa only [EA] using nsdStopOutcomeBy_monotone A hAB
  have hED : Monotone ED := by
    simpa only [ED] using nsdStopOutcomeBy_monotone D hDB
  have hf : Monotone (fun N => P (EA N)) :=
    fun _ _ hNM => measure_mono (hEA hNM)
  have hg : Monotone
      (fun N => ENNReal.ofReal (1 / 2) * P (ED N)) :=
    fun _ _ hNM => mul_le_mul_left' (measure_mono (hED hNM)) _
  rw [show {s : PopState | 0 < s.1 ∧ s.2 = 0} = A from rfl,
    show {s : PopState | s.1 = s.2 ∧ 0 < s.1} = D from rfl,
    nsdStopOutcome_eq_iUnion A, nsdStopOutcome_eq_iUnion D,
    show (⋃ N, {ω | nsdStopOutcomeBy A N ω}) =
      ⋃ N, EA N from rfl,
    show (⋃ N, {ω | nsdStopOutcomeBy D N ω}) =
      ⋃ N, ED N from rfl,
    hEA.measure_iUnion, hED.measure_iUnion, ENNReal.mul_iSup,
    ENNReal.iSup_add_iSup_of_monotone hf hg]
  apply iSup_le
  intro N
  simpa only [P, EA, ED, A, D] using
    nsd_boundary_payoff_by_le
      params hAlpha hNeutral hGamma hGe a b N

private def nsdMajoritySide (s : PopState) : Prop :=
  s.2 = 0 ∨ s.2 ≤ s.1

private lemma nsdMajorityStoppedKernel_side_support
    (params : LVParams) (s : PopState)
    (hsSide : nsdMajoritySide s)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    nsdMajorityStoppedKernel params s
      {x | ¬nsdMajoritySide x} = 0 := by
  by_cases hsB : nsdMajorityBoundary s
  · rw [nsdMajorityStoppedKernel_boundary params s hsB,
      Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
    simp [hsSide]
  · rw [nsdMajorityStoppedKernel_open params s hsB]
    rcases s with ⟨a, b⟩
    have hb : 0 < b := by
      have : b ≠ 0 := fun h => hsB (Or.inl h)
      exact Nat.pos_of_ne_zero this
    have hba : b < a := by
      have : ¬a ≤ b := fun h => hsB (Or.inr h)
      omega
    by_cases hφ : lvTotalPropensity params (a, b) = 0
    · rw [lvKernel_apply_zero_propensity
        .nonSelfDestructive params (a, b) hφ,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
      simp [nsdMajoritySide, hba.le]
    · rw [lvKernel_nsd_apply params a b hφ]
      simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]
      have h1 :
          (a + 1, b) ∉ {x : PopState | ¬nsdMajoritySide x} := by
        simp [nsdMajoritySide]
        omega
      have h2 :
          (a, b + 1) ∉ {x : PopState | ¬nsdMajoritySide x} := by
        simp [nsdMajoritySide]
        omega
      have h3 :
          (a - 1, b) ∉ {x : PopState | ¬nsdMajoritySide x} := by
        simp [nsdMajoritySide]
        omega
      have h4 :
          (a, b - 1) ∉ {x : PopState | ¬nsdMajoritySide x} := by
        simp [nsdMajoritySide]
        omega
      rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
      simp [h1, h2, h3, h4]

private lemma nsdMajorityStoppedKernel_iter_side
    (params : LVParams) (s : PopState)
    (hsSide : nsdMajoritySide s)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∀ N : ℕ,
      kernelIter (nsdMajorityStoppedKernel params) N s
        {x | ¬nsdMajoritySide x} = 0 := by
  intro N
  induction N with
  | zero =>
      rw [kernelIter_zero, Kernel.id_apply,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
      simp [hsSide]
  | succ N ih =>
      rw [kernelIter_succ, Kernel.comp_apply' _ _ _
        (Set.to_countable _).measurableSet]
      have hae :
          ∀ᵐ x ∂kernelIter (nsdMajorityStoppedKernel params) N s,
            nsdMajoritySide x := by
        rw [ae_iff]
        simpa only [Set.compl_setOf] using ih
      calc
        ∫⁻ x, nsdMajorityStoppedKernel params x
              {y | ¬nsdMajoritySide y}
            ∂kernelIter (nsdMajorityStoppedKernel params) N s
            = ∫⁻ _x, 0
                ∂kernelIter (nsdMajorityStoppedKernel params) N s := by
              apply lintegral_congr_ae
              filter_upwards [hae] with x hx
              exact nsdMajorityStoppedKernel_side_support params x hx
        _ = 0 := by simp

private lemma nsd_strict_minority_stop_null
    (params : LVParams) (a b : ℕ) (hba : b ≤ a)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | nsdStopOutcome {s | 0 < s.2 ∧ s.1 < s.2} ω} = 0 := by
  let C : Set PopState := {s | 0 < s.2 ∧ s.1 < s.2}
  let EC : ℕ → Set (ℕ → PopState) :=
    fun N => {ω | nsdStopOutcomeBy C N ω}
  have hCB : C ⊆ {s | nsdMajorityBoundary s} := by
    intro s hs
    exact Or.inr hs.2.le
  have hEC : Monotone EC := by
    simpa only [EC] using nsdStopOutcomeBy_monotone C hCB
  have hEach : ∀ N,
      lvPathMeasure .nonSelfDestructive params (a, b) (EC N) = 0 := by
    intro N
    rw [← nsdMajorityStoppedKernel_outcomeBy_eq
      params C (Set.to_countable C).measurableSet hCB N (a, b)]
    apply measure_mono_null
    · intro s hs
      change ¬nsdMajoritySide s
      simp only [C, Set.mem_setOf_eq] at hs
      intro hside
      rcases hside with h0 | hle
      · omega
      · omega
    · exact nsdMajorityStoppedKernel_iter_side
        params (a, b) (Or.inr hba) N
  rw [show {s : PopState | 0 < s.2 ∧ s.1 < s.2} = C from rfl,
    nsdStopOutcome_eq_iUnion C,
    show (⋃ N, {ω | nsdStopOutcomeBy C N ω}) =
      ⋃ N, EC N from rfl,
    hEC.measure_iUnion]
  simp [hEach]

private lemma nsdStopOutcomeBy_iff_first
    (A : Set PopState)
    (hAB : A ⊆ {s | nsdMajorityBoundary s})
    (N : ℕ) (ω : ℕ → PopState) :
    nsdStopOutcomeBy A N ω ↔
      ∃ k : ℕ, k ≤ N ∧ ω k ∈ A ∧
        ∀ j : ℕ, j < k → ¬nsdMajorityBoundary (ω j) := by
  induction N generalizing ω with
  | zero =>
      constructor
      · intro h
        exact ⟨0, le_rfl, h, by omega⟩
      · rintro ⟨k, hk, hA, hfirst⟩
        have : k = 0 := by omega
        simpa [this, nsdStopOutcomeBy] using hA
  | succ N ih =>
      by_cases hB : nsdMajorityBoundary (ω 0)
      · constructor
        · intro h
          have hA : ω 0 ∈ A := by
            simpa [nsdStopOutcomeBy, hB] using h
          exact ⟨0, by omega, hA, by omega⟩
        · rintro ⟨k, hk, hA, hfirst⟩
          have hk0 : k = 0 := by
            by_contra hkne
            have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
            exact (hfirst 0 hkpos) hB
          subst k
          simpa [nsdStopOutcomeBy, hB] using hA
      · constructor
        · intro h
          have hshift :
              nsdStopOutcomeBy A N (pathShift 1 ω) := by
            simpa [nsdStopOutcomeBy, hB] using h
          rcases (ih (pathShift 1 ω)).mp hshift with
            ⟨k, hk, hA, hfirst⟩
          refine ⟨k + 1, by omega, ?_, ?_⟩
          · simpa [pathShift, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hA
          · intro j hj
            rcases j with _ | j
            · simpa using hB
            · have hjk : j < k := by omega
              simpa [pathShift, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using hfirst j hjk
        · rintro ⟨k, hk, hA, hfirst⟩
          have hkpos : 0 < k := by
            by_contra hk0
            have : k = 0 := Nat.eq_zero_of_not_pos hk0
            subst k
            exact hB (hAB hA)
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
          have hshiftA :
              pathShift 1 ω k ∈ A := by
            simpa [pathShift, Nat.add_comm] using hA
          have hshiftFirst :
              ∀ j : ℕ, j < k →
                ¬nsdMajorityBoundary (pathShift 1 ω j) := by
            intro j hj
            simpa [pathShift, Nat.add_comm] using hfirst (j + 1) (by omega)
          have hshift :
              nsdStopOutcomeBy A N (pathShift 1 ω) :=
            (ih (pathShift 1 ω)).mpr
              ⟨k, by omega, hshiftA, hshiftFirst⟩
          simpa [nsdStopOutcomeBy, hB] using hshift

private lemma majorityConsensusEvent_shift_of_no_consensus
    (s0 : PopState) (ω : ℕ → PopState) (k : ℕ)
    (hpre : ∀ j : ℕ, j < k → ¬reachedConsensus (ω j))
    (hMC : majorityConsensusEvent s0 ω) :
    majorityConsensusEvent s0 (pathShift k ω) := by
  unfold majorityConsensusEvent at hMC
  cases hct : consensusTime ω with
  | top =>
      simp [hct] at hMC
  | coe t =>
      simp only [hct] at hMC
      have htReach : reachedConsensus (ω t) :=
        reachedConsensus_at_consensusTime' ω t hct
      have hkt : k ≤ t := by
        by_contra h
        push_neg at h
        exact hpre t h htReach
      have hshift :
          consensusTime (pathShift k ω) = ↑(t - k) := by
        rw [consensusTime_eq_coe_iff]
        constructor
        · show reachedConsensus (ω (k + (t - k)))
          rw [Nat.add_sub_of_le hkt]
          exact htReach
        · intro j hj
          show ¬reachedConsensus (ω (k + j))
          exact ((consensusTime_eq_coe_iff ω t).mp hct).2
            (k + j) (by omega)
      unfold majorityConsensusEvent
      rw [hshift]
      simpa [pathShift, Nat.add_sub_of_le hkt] using hMC

private lemma mc_cap_first_boundary_diagonal_le
    (params : LVParams) (s s0 : PopState)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (k : ℕ)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s
        ({ω | majorityConsensusEvent s0 ω} ∩
          {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
            ∀ j : ℕ, j < k →
              ¬nsdMajorityBoundary (ω j)}) ≤
      ENNReal.ofReal (1 / 2) *
        lvPathMeasure .nonSelfDestructive params s
          {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
            ∀ j : ℕ, j < k →
              ¬nsdMajorityBoundary (ω j)} := by
  let P := lvPathMeasure .nonSelfDestructive params s
  let MC : Set (ℕ → PopState) :=
    {ω | majorityConsensusEvent s0 ω}
  let H : Set (ℕ → PopState) :=
    {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
      ∀ j : ℕ, j < k → ¬nsdMajorityBoundary (ω j)}
  have hH_meas : MeasurableSet H := by
    have hEq :
        H =
          ((fun ω : ℕ → PopState => ω k) ⁻¹'
            {x : PopState | x.1 = x.2 ∧ 0 < x.1}) ∩
          ⋂ j ∈ Finset.range k,
            ((fun ω : ℕ → PopState => ω j) ⁻¹'
              {x : PopState | nsdMajorityBoundary x})ᶜ := by
      ext ω
      simp only [H, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
        Set.mem_compl_iff]
      tauto
    rw [hEq]
    exact ((Set.to_countable _).measurableSet.preimage
        (measurable_pi_apply k)).inter
      (MeasurableSet.biInter (Finset.range k).countable_toSet
        fun j _ => ((Set.to_countable _).measurableSet.preimage
          (measurable_pi_apply j)).compl)
  have hMC_meas : MeasurableSet MC := by
    simpa [MC] using measurableSet_majorityConsensusEvent s0
  have hSub : MC ∩ H ⊆ H ∩ (pathShift k) ⁻¹' MC := by
    intro ω hω
    refine ⟨hω.2, ?_⟩
    exact majorityConsensusEvent_shift_of_no_consensus
      s0 ω k (fun j hj hcons => by
        have hB : nsdMajorityBoundary (ω j) := by
          rcases hcons with h0 | h0
          · exact Or.inr (by simp [h0])
          · exact Or.inl h0
        exact hω.2.2.2 j hj hB) hω.1
  calc
    P (MC ∩ H) ≤ P (H ∩ (pathShift k) ⁻¹' MC) :=
      measure_mono hSub
    _ ≤ ENNReal.ofReal (1 / 2) * P H := by
      dsimp [P]
      exact homogeneousPathMeasure_markov_bound
        (lvKernel .nonSelfDestructive params) s k
        (ENNReal.ofReal (1 / 2)) H MC
        hH_meas hMC_meas
        (by
          intro ω ω' hagree hω
          refine ⟨by rw [← hagree k le_rfl]; exact hω.1,
            by rw [← hagree k le_rfl]; exact hω.2.1, ?_⟩
          intro j hj
          rw [← hagree j (le_of_lt hj)]
          exact hω.2.2 j hj)
        (by
          intro ω hω
          have heq :
              ω k = ((ω k).1, (ω k).1) := by
            ext <;> simp [hω.1]
          rw [heq]
          exact mc_any_from_diagonal_le_half
            .nonSelfDestructive params s0 (ω k).1
              hNeutral hGamma)

private lemma mc_cap_stop_diagonal_le
    (params : LVParams) (s s0 : PopState)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s
        ({ω | majorityConsensusEvent s0 ω} ∩
          {ω | nsdStopOutcome
            {x | x.1 = x.2 ∧ 0 < x.1} ω}) ≤
      ENNReal.ofReal (1 / 2) *
        lvPathMeasure .nonSelfDestructive params s
          {ω | nsdStopOutcome
            {x | x.1 = x.2 ∧ 0 < x.1} ω} := by
  let P := lvPathMeasure .nonSelfDestructive params s
  let MC : Set (ℕ → PopState) :=
    {ω | majorityConsensusEvent s0 ω}
  let D : Set (ℕ → PopState) :=
    {ω | nsdStopOutcome {x | x.1 = x.2 ∧ 0 < x.1} ω}
  let H : ℕ → Set (ℕ → PopState) :=
    fun k => {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
      ∀ j : ℕ, j < k → ¬nsdMajorityBoundary (ω j)}
  have hTargetB :
      {x : PopState | x.1 = x.2 ∧ 0 < x.1} ⊆
        {x | nsdMajorityBoundary x} := by
    intro x hx
    exact Or.inr hx.1.le
  have hD_eq : D = ⋃ k, H k := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨N, hN⟩
      rcases (nsdStopOutcomeBy_iff_first
        {x : PopState | x.1 = x.2 ∧ 0 < x.1}
        hTargetB N ω).mp hN with ⟨k, hkN, hk, hfirst⟩
      exact Set.mem_iUnion.mpr
        ⟨k, hk.1, hk.2, hfirst⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with
        ⟨k, hkdiag, hkpos, hfirst⟩
      exact ⟨k, (nsdStopOutcomeBy_iff_first
        {x : PopState | x.1 = x.2 ∧ 0 < x.1}
        hTargetB k ω).mpr
          ⟨k, le_rfl, ⟨hkdiag, hkpos⟩, hfirst⟩⟩
  have hH_disj : Pairwise (Function.onFun Disjoint H) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω hi hj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hiB : nsdMajorityBoundary (ω i) :=
        Or.inr hi.1.le
      exact hj.2.2 i hij hiB
    · have hjB : nsdMajorityBoundary (ω j) :=
        Or.inr hj.1.le
      exact hi.2.2 j hji hjB
  have hH_meas : ∀ k, MeasurableSet (H k) := fun k => by
    have hEq :
        H k =
          ((fun ω : ℕ → PopState => ω k) ⁻¹'
            {x : PopState | x.1 = x.2 ∧ 0 < x.1}) ∩
          ⋂ j ∈ Finset.range k,
            ((fun ω : ℕ → PopState => ω j) ⁻¹'
              {x : PopState | nsdMajorityBoundary x})ᶜ := by
      ext ω
      simp only [H, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
        Set.mem_compl_iff]
      tauto
    rw [hEq]
    exact ((Set.to_countable _).measurableSet.preimage
        (measurable_pi_apply k)).inter
      (MeasurableSet.biInter (Finset.range k).countable_toSet
        fun j _ => ((Set.to_countable _).measurableSet.preimage
          (measurable_pi_apply j)).compl)
  have hMC_meas : MeasurableSet MC := by
    simpa [MC] using measurableSet_majorityConsensusEvent s0
  have hSum :
      P (MC ∩ D) = ∑' k, P (MC ∩ H k) := by
    rw [hD_eq, Set.inter_iUnion]
    exact measure_iUnion
      (fun i j hij => (hH_disj hij).mono
        Set.inter_subset_right Set.inter_subset_right)
      (fun k => hMC_meas.inter (hH_meas k))
  have hBound : ∀ k,
      P (MC ∩ H k) ≤ ENNReal.ofReal (1 / 2) * P (H k) := by
    intro k
    simpa only [P, MC, H] using
      mc_cap_first_boundary_diagonal_le
        params s s0 hNeutral hGamma k
  calc
    P (MC ∩ D) = ∑' k, P (MC ∩ H k) := hSum
    _ ≤ ∑' k, ENNReal.ofReal (1 / 2) * P (H k) :=
      ENNReal.tsum_le_tsum hBound
    _ = ENNReal.ofReal (1 / 2) * ∑' k, P (H k) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 / 2) * P (⋃ k, H k) := by
      rw [measure_iUnion hH_disj hH_meas]
    _ = ENNReal.ofReal (1 / 2) * P D := by rw [hD_eq]

private lemma nsdMajorityStoppedKernel_zero_support
    (params : LVParams) (s : PopState)
    (hs0 : s ≠ (0, 0))
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    nsdMajorityStoppedKernel params s {(0, 0)} = 0 := by
  by_cases hsB : nsdMajorityBoundary s
  · rw [nsdMajorityStoppedKernel_boundary params s hsB,
      Measure.dirac_apply' _ (measurableSet_singleton _)]
    rw [Set.indicator_of_notMem (by simpa using hs0)]
  · rw [nsdMajorityStoppedKernel_open params s hsB]
    rcases s with ⟨a, b⟩
    have hb : 0 < b := by
      have : b ≠ 0 := fun h => hsB (Or.inl h)
      exact Nat.pos_of_ne_zero this
    have hba : b < a := by
      have : ¬a ≤ b := fun h => hsB (Or.inr h)
      omega
    by_cases hφ : lvTotalPropensity params (a, b) = 0
    · rw [lvKernel_apply_zero_propensity
        .nonSelfDestructive params (a, b) hφ,
        Measure.dirac_apply' _ (measurableSet_singleton _)]
      rw [Set.indicator_of_notMem (by
        simpa using (show (a, b) ≠ (0, 0) from by
          intro h
          have : b = 0 := congrArg Prod.snd h
          omega))]
    · rw [lvKernel_nsd_apply params a b hφ]
      have h1 : (a + 1, b) ≠ (0, 0) := by
        intro h
        have : b = 0 := congrArg Prod.snd h
        omega
      have h2 : (a, b + 1) ≠ (0, 0) := by
        intro h
        have : b + 1 = 0 := congrArg Prod.snd h
        omega
      have h3 : (a - 1, b) ≠ (0, 0) := by
        intro h
        have : b = 0 := congrArg Prod.snd h
        omega
      have h4 : (a, b - 1) ≠ (0, 0) := by
        intro h
        have : a = 0 := congrArg Prod.fst h
        omega
      simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]
      rw [Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Measure.dirac_apply' _ (measurableSet_singleton _)]
      simp [h1, h2, h3, h4]

private lemma nsdMajorityStoppedKernel_iter_zero
    (params : LVParams) (s : PopState)
    (hs0 : s ≠ (0, 0))
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∀ N : ℕ,
      kernelIter (nsdMajorityStoppedKernel params) N s
        {(0, 0)} = 0 := by
  intro N
  induction N with
  | zero =>
      rw [kernelIter_zero, Kernel.id_apply,
        Measure.dirac_apply' _ (measurableSet_singleton _)]
      simp [hs0]
  | succ N ih =>
      rw [kernelIter_succ, Kernel.comp_apply' _ _ _
        (measurableSet_singleton _)]
      have hae :
          ∀ᵐ x ∂kernelIter (nsdMajorityStoppedKernel params) N s,
            x ≠ (0, 0) := by
        rw [ae_iff]
        have hset :
            {x : PopState | ¬x ≠ (0, 0)} = {(0, 0)} := by
          ext x
          simp
        rw [hset]
        exact ih
      calc
        ∫⁻ x, nsdMajorityStoppedKernel params x {(0, 0)}
            ∂kernelIter (nsdMajorityStoppedKernel params) N s
            = ∫⁻ _x, 0
                ∂kernelIter (nsdMajorityStoppedKernel params) N s := by
              apply lintegral_congr_ae
              filter_upwards [hae] with x hx
              exact nsdMajorityStoppedKernel_zero_support params x hx
        _ = 0 := by simp

private lemma nsd_zero_stop_null
    (params : LVParams) (a b : ℕ) (ha : 0 < a)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | nsdStopOutcome ({(0, 0)} : Set PopState) ω} = 0 := by
  let Z : Set PopState := {(0, 0)}
  let EZ : ℕ → Set (ℕ → PopState) :=
    fun N => {ω | nsdStopOutcomeBy Z N ω}
  have hZB : Z ⊆ {s | nsdMajorityBoundary s} := by
    intro s hs
    subst s
    exact Or.inl rfl
  have hEZ : Monotone EZ := by
    simpa only [EZ] using nsdStopOutcomeBy_monotone Z hZB
  have hEach : ∀ N,
      lvPathMeasure .nonSelfDestructive params (a, b) (EZ N) = 0 := by
    intro N
    rw [← nsdMajorityStoppedKernel_outcomeBy_eq
      params Z (measurableSet_singleton _) hZB N (a, b)]
    exact nsdMajorityStoppedKernel_iter_zero
      params (a, b) (by
        intro h
        have : a = 0 := congrArg Prod.fst h
        omega) N
  rw [show ({(0, 0)} : Set PopState) = Z from rfl,
    nsdStopOutcome_eq_iUnion Z,
    show (⋃ N, {ω | nsdStopOutcomeBy Z N ω}) =
      ⋃ N, EZ N from rfl,
    hEZ.measure_iUnion]
  simp [hEach]

private lemma measurableSet_nsdStopOutcome
    (A : Set PopState) (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → PopState | nsdStopOutcome A ω} := by
  rw [nsdStopOutcome_eq_iUnion A]
  exact MeasurableSet.iUnion fun N =>
    measurableSet_nsdStopOutcomeBy A hA N

private lemma nsd_mce_stop_classification
    (a b : ℕ) (hba : b < a)
    (ω : ℕ → PopState)
    (hMC : majorityConsensusEvent (a, b) ω) :
    nsdStopOutcome {s | 0 < s.1 ∧ s.2 = 0} ω ∨
      nsdStopOutcome {s | s.1 = s.2 ∧ 0 < s.1} ω ∨
      nsdStopOutcome {s | 0 < s.2 ∧ s.1 < s.2} ω ∨
      nsdStopOutcome ({(0, 0)} : Set PopState) ω := by
  have hMaj : species0Majority (a, b) := by
    simp [species0Majority, hba]
  unfold majorityConsensusEvent at hMC
  cases hct : consensusTime ω with
  | top =>
      simp [hct] at hMC
  | coe t =>
      simp only [hct] at hMC
      have htA : 0 < (ω t).1 ∧ (ω t).2 = 0 := by
        rcases hMC with hMC | hMC
        · exact ⟨hMC.2.1, hMC.2.2⟩
        · exact (hMC.1 hMaj).elim
      have hex :
          ∃ k : ℕ, k ≤ t ∧ nsdMajorityBoundary (ω k) :=
        ⟨t, le_rfl, Or.inl htA.2⟩
      let k := Nat.find hex
      have hk := Nat.find_spec hex
      have hfirst :
          ∀ j : ℕ, j < k →
            ¬nsdMajorityBoundary (ω j) := by
        intro j hj hBj
        exact Nat.find_min hex hj
          ⟨(Nat.le_of_lt hj).trans hk.1, hBj⟩
      have hmkOutcome :
          ∀ (A : Set PopState),
            A ⊆ {s | nsdMajorityBoundary s} →
            ω k ∈ A → nsdStopOutcome A ω := by
        intro A hAB hkA
        exact ⟨k, (nsdStopOutcomeBy_iff_first A hAB k ω).mpr
          ⟨k, le_rfl, hkA, hfirst⟩⟩
      rcases hk.2 with hk0 | hkle
      · by_cases hpos : 0 < (ω k).1
        · exact Or.inl (hmkOutcome
            {s | 0 < s.1 ∧ s.2 = 0}
            (fun s hs => Or.inl hs.2) ⟨hpos, hk0⟩)
        · have hz : ω k = (0, 0) := by
            apply Prod.ext
            · simp only [Prod.fst]
              exact Nat.eq_zero_of_not_pos hpos
            · simpa only [Prod.snd] using hk0
          exact Or.inr (Or.inr (Or.inr
            (hmkOutcome ({(0, 0)} : Set PopState)
              (by intro s hs; subst s; exact Or.inl rfl) hz)))
      · by_cases heq : (ω k).1 = (ω k).2
        · by_cases hpos : 0 < (ω k).1
          · exact Or.inr (Or.inl (hmkOutcome
              {s | s.1 = s.2 ∧ 0 < s.1}
              (fun s hs => Or.inr hs.1.le) ⟨heq, hpos⟩))
          · have hz : ω k = (0, 0) := by
              apply Prod.ext
              · simp only [Prod.fst]
                exact Nat.eq_zero_of_not_pos hpos
              · simp only [Prod.snd]
                rw [← heq]
                exact Nat.eq_zero_of_not_pos hpos
            exact Or.inr (Or.inr (Or.inr
              (hmkOutcome ({(0, 0)} : Set PopState)
                (by intro s hs; subst s; exact Or.inl rfl) hz)))
        · have hlt : (ω k).1 < (ω k).2 :=
            lt_of_le_of_ne hkle heq
          have hpos2 : 0 < (ω k).2 := by omega
          exact Or.inr (Or.inr (Or.inl
            (hmkOutcome {s | 0 < s.2 ∧ s.1 < s.2}
              (fun s hs => Or.inr hs.2.le) ⟨hpos2, hlt⟩)))

/-- Corollary of `thm:nsd-intra` for `γ ≥ 2α`, with arbitrary common
    demographic rates.  The proof stops at the first diagonal or majority
    extinction.  Before that stopping time, `a/(a+b)` is superharmonic; at a
    diagonal, swap symmetry bounds the subsequent majority-win probability
    by one half. -/
theorem cor_nsd_intra
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe0 : 2 * params.alpha0 ≤ params.gamma0)
    (_hGe1 : 2 * params.alpha1 ≤ params.gamma1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    majorityConsensusProb LVVariant.nonSelfDestructive params (a, b) ≤
      ENNReal.ofReal ((a : Real) / (a + b)) := by
  rcases eq_or_lt_of_le hba with hab | hba_lt
  · subst a
    have hhalf :=
      lemma_identical_gap_fail .nonSelfDestructive params
        hNeutral hGamma b
    have hratio :
        (b : ℝ) / ((b : ℝ) + b) = 1 / 2 := by
      have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hposB
      field_simp
      ring
    simpa only [Nat.cast_add, hratio] using hhalf
  · let P := lvPathMeasure .nonSelfDestructive params (a, b)
    let MC : Set (ℕ → PopState) :=
      {ω | majorityConsensusEvent (a, b) ω}
    let A : Set (ℕ → PopState) :=
      {ω | nsdStopOutcome {s | 0 < s.1 ∧ s.2 = 0} ω}
    let D : Set (ℕ → PopState) :=
      {ω | nsdStopOutcome {s | s.1 = s.2 ∧ 0 < s.1} ω}
    let C : Set (ℕ → PopState) :=
      {ω | nsdStopOutcome {s | 0 < s.2 ∧ s.1 < s.2} ω}
    let Z : Set (ℕ → PopState) :=
      {ω | nsdStopOutcome ({(0, 0)} : Set PopState) ω}
    have hD_meas : MeasurableSet D := by
      exact measurableSet_nsdStopOutcome _
        (Set.to_countable _).measurableSet
    have hC_zero : P C = 0 := by
      simpa only [P, C] using
        nsd_strict_minority_stop_null params a b hba
    have hZ_zero : P Z = 0 := by
      simpa only [P, Z] using
        nsd_zero_stop_null params a b hposA
    have hOutsideSub :
        MC ∩ Dᶜ ⊆ (A ∪ C) ∪ Z := by
      intro ω hω
      rcases nsd_mce_stop_classification
        a b hba_lt ω hω.1 with hA | hD | hC | hZ
      · exact Or.inl (Or.inl hA)
      · exact (hω.2 hD).elim
      · exact Or.inl (Or.inr hC)
      · exact Or.inr hZ
    have hOutside : P (MC ∩ Dᶜ) ≤ P A := by
      calc
        P (MC ∩ Dᶜ) ≤ P ((A ∪ C) ∪ Z) :=
          measure_mono hOutsideSub
        _ ≤ P (A ∪ C) + P Z := measure_union_le _ _
        _ ≤ (P A + P C) + P Z :=
          add_le_add (measure_union_le A C) le_rfl
        _ = P A := by rw [hC_zero, hZ_zero, add_zero, add_zero]
    have hDiag :
        P (MC ∩ D) ≤ ENNReal.ofReal (1 / 2) * P D := by
      simpa only [P, MC, D] using
        mc_cap_stop_diagonal_le
          params (a, b) (a, b) hNeutral hGamma
    have hPayoff :
        P A + ENNReal.ofReal (1 / 2) * P D ≤
          ENNReal.ofReal (nsdRatio (a, b)) := by
      simpa only [P, A, D] using
        nsd_boundary_payoff_le
          params hAlpha hNeutral hGamma hGe0 a b
    have hSplit :
        MC ⊆ (MC ∩ D) ∪ (MC ∩ Dᶜ) := by
      intro ω hω
      by_cases hD : ω ∈ D
      · exact Or.inl ⟨hω, hD⟩
      · exact Or.inr ⟨hω, hD⟩
    calc
      P MC ≤ P ((MC ∩ D) ∪ (MC ∩ Dᶜ)) :=
        measure_mono hSplit
      _ ≤ P (MC ∩ D) + P (MC ∩ Dᶜ) :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 2) * P D + P A :=
        add_le_add hDiag hOutside
      _ = P A + ENNReal.ofReal (1 / 2) * P D := add_comm _ _
      _ ≤ ENNReal.ofReal (nsdRatio (a, b)) := hPayoff
      _ = ENNReal.ofReal ((a : ℝ) / (a + b)) := by
        congr 1
        rw [nsdRatio_of_ne (a, b) (by
          intro h
          have : a = 0 := congrArg Prod.fst h
          omega)]

/-- Paper corollary with arbitrary common demographic rates.  Consensus is
almost sure and `γᵢ ≥ 2αᵢ` gives the majority-probability upper bound. -/
theorem cor_nsd_intra_full
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe0 : 2 * params.alpha0 ≤ params.gamma0)
    (hGe1 : 2 * params.alpha1 ≤ params.gamma1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
          {ω | consensusReachedEvent ω} = 1 ∧
      majorityConsensusProb LVVariant.nonSelfDestructive params (a, b) ≤
        ENNReal.ofReal ((a : Real) / (a + b)) := by
  exact
    ⟨nsd_consensus_almost_sure_gamma_ge params hAlpha hNeutral hGamma
        hGe0 a b hposA hposB,
      cor_nsd_intra params hAlpha hNeutral hGamma
        hGe0 hGe1 a b hposA hposB hba⟩

end LVConsensus
