import LVConsensus.MarkovLib
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

private def nonholdingUpTo (ω : ℕ → ℕ) (t : ℕ) : ℕ :=
  Finset.sum (Finset.range t) fun i => if ω (i + 1) ≠ ω i then 1 else 0

private lemma measurable_nonholdingUpTo (t : ℕ) :
    Measurable (fun ω : ℕ → ℕ => nonholdingUpTo ω t) := by
  unfold nonholdingUpTo
  apply Finset.measurable_fun_sum
  intro i hi
  have hne : MeasurableSet {ω : ℕ → ℕ | ω (i + 1) ≠ ω i} := by
    measurability
  exact Measurable.ite hne measurable_const measurable_const

private def nonholdingEpoch (r t : ℕ) (ω : ℕ → ℕ) : Prop :=
  (r = 0 ∧ t = 0) ∨
    (0 < r ∧ 0 < t ∧ nonholdingUpTo ω (t - 1) = r - 1 ∧
      ω t ≠ ω (t - 1))

private lemma measurableSet_nonholdingEpoch (r t : ℕ) :
    MeasurableSet {ω : ℕ → ℕ | nonholdingEpoch r t ω} := by
  by_cases hzero : r = 0 ∧ t = 0
  · convert MeasurableSet.univ
    ext ω
    simp [nonholdingEpoch, hzero]
  · by_cases hpos : 0 < r ∧ 0 < t
    · have hc : MeasurableSet
          {ω : ℕ → ℕ | nonholdingUpTo ω (t - 1) = r - 1} := by
        exact (measurable_nonholdingUpTo (t - 1)) (measurableSet_singleton _)
      have hm : MeasurableSet {ω : ℕ → ℕ | ω t ≠ ω (t - 1)} := by
        measurability
      rw [show {ω : ℕ → ℕ | nonholdingEpoch r t ω} =
          {ω | nonholdingUpTo ω (t - 1) = r - 1} ∩
            {ω | ω t ≠ ω (t - 1)} by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · intro h
          rcases h with hz | h
          · exact absurd hz hzero
          · exact ⟨h.2.2.1, h.2.2.2⟩
        · intro h
          exact Or.inr ⟨hpos.1, hpos.2, h⟩]
      exact hc.inter hm
    · rw [show {ω : ℕ → ℕ | nonholdingEpoch r t ω} = ∅ by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        rcases h with hz | h
        · exact hzero hz
        · exact hpos ⟨h.1, h.2.1⟩]
      exact MeasurableSet.empty

private lemma nonholdingEpoch_cylinder (r t : ℕ) :
    isCylinderUpTo t {ω : ℕ → ℕ | nonholdingEpoch r t ω} := by
  intro ω ω' heq hω
  rcases hω with hzero | ⟨hr, ht, hcount, hmove⟩
  · exact Or.inl hzero
  · right
    refine ⟨hr, ht, ?_, ?_⟩
    · unfold nonholdingUpTo at hcount ⊢
      rw [← hcount]
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i + 1 ≤ t := by
        simp only [Finset.mem_range] at hi
        omega
      rw [heq i (by omega), heq (i + 1) hit]
    · rw [← heq t le_rfl, ← heq (t - 1) (by omega)]
      exact hmove

private lemma nonholdingUpTo_succ (ω : ℕ → ℕ) (t : ℕ) :
    nonholdingUpTo ω (t + 1) =
      nonholdingUpTo ω t + if ω (t + 1) ≠ ω t then 1 else 0 := by
  simp [nonholdingUpTo, Finset.sum_range_succ]

private lemma nonholdingUpTo_mono (ω : ℕ → ℕ) :
    Monotone (nonholdingUpTo ω) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [nonholdingUpTo_succ]
  omega

private lemma nonholdingEpoch_count {r t : ℕ} {ω : ℕ → ℕ}
    (h : nonholdingEpoch r t ω) :
    nonholdingUpTo ω t = r := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hr, ht, hcount, hmove⟩
  · simp [nonholdingUpTo]
  · have htform : t = (t - 1) + 1 := by omega
    rw [htform, nonholdingUpTo_succ, hcount,
      show t - 1 + 1 = t from by omega, if_pos hmove]
    omega

private lemma nonholdingEpoch_unique {r t u : ℕ} {ω : ℕ → ℕ}
    (ht : nonholdingEpoch r t ω) (hu : nonholdingEpoch r u ω) :
    t = u := by
  rcases ht with htz | htp
  · exact htz.2.trans (by
      rcases hu with huz | hup
      · exact huz.2.symm
      · omega)
  rcases hu with huz | hup
  · omega
  have hct : nonholdingUpTo ω t = r :=
    nonholdingEpoch_count (Or.inr htp)
  have hcu : nonholdingUpTo ω u = r :=
    nonholdingEpoch_count (Or.inr hup)
  rcases lt_trichotomy t u with hlt | heq | hgt
  · have hm := nonholdingUpTo_mono ω (show t ≤ u - 1 by omega)
    rw [hct, hup.2.2.1] at hm
    omega
  · exact heq
  · have hm := nonholdingUpTo_mono ω (show u ≤ t - 1 by omega)
    rw [hcu, htp.2.2.1] at hm
    omega

private lemma nonholdingEpoch_exists_of_le_count
    (ω : ℕ → ℕ) (r t : ℕ) (hr : r ≤ nonholdingUpTo ω t) :
    ∃ u ≤ t, nonholdingEpoch r u ω := by
  induction t with
  | zero =>
      have hr0 : r = 0 := by
        simpa [nonholdingUpTo] using hr
      subst r
      exact ⟨0, le_rfl, Or.inl ⟨rfl, rfl⟩⟩
  | succ t ih =>
      by_cases hprev : r ≤ nonholdingUpTo ω t
      · obtain ⟨u, hu, hepoch⟩ := ih hprev
        exact ⟨u, hu.trans (Nat.le_succ t), hepoch⟩
      · have hrpos : 0 < r := by omega
        have hmove : ω (t + 1) ≠ ω t := by
          intro heq
          rw [nonholdingUpTo_succ,
            if_neg (not_not.mpr heq)] at hr
          omega
        have hcount : nonholdingUpTo ω t = r - 1 := by
          rw [nonholdingUpTo_succ, if_pos hmove] at hr
          omega
        refine ⟨t + 1, le_rfl, Or.inr ⟨hrpos, by omega, ?_, ?_⟩⟩
        · simpa using hcount
        · simpa using hmove

private lemma nonholdingEpoch_exists_before
    {n T : ℕ} {ω : ℕ → ℕ} (hT : nonholdingEpoch n T ω)
    (r : ℕ) (hr : r ≤ n) :
    ∃ u ≤ T, nonholdingEpoch r u ω := by
  apply nonholdingEpoch_exists_of_le_count
  rw [nonholdingEpoch_count hT]
  exact hr

private lemma shifted_firstDeparture_iff_up_of_consecutive_epochs
    {r u v : ℕ} {ω : ℕ → ℕ}
    (hu : nonholdingEpoch r u ω)
    (hv : nonholdingEpoch (r + 1) v ω) :
    pathShift u ω ∈ firstDepartureBirthFrom (ω u) ↔
      ω v = ω (v - 1) + 1 := by
  have hcu : nonholdingUpTo ω u = r := nonholdingEpoch_count hu
  have hcv : nonholdingUpTo ω v = r + 1 := nonholdingEpoch_count hv
  have huv : u < v := by
    by_contra h
    have hm := nonholdingUpTo_mono ω (show v ≤ u by omega)
    rw [hcv, hcu] at hm
    omega
  have hvpos : 0 < v := by omega
  have hbefore : nonholdingUpTo ω (v - 1) = r := by
    rcases hv with hz | hp
    · omega
    · simpa using hp.2.2.1
  have hcount_between :
      ∀ s, u ≤ s → s < v → nonholdingUpTo ω s = r := by
    intro s hus hsv
    have hleft := nonholdingUpTo_mono ω hus
    have hright := nonholdingUpTo_mono ω
      (show s ≤ v - 1 by omega)
    rw [hcu] at hleft
    rw [hbefore] at hright
    omega
  have hconst :
      ∀ i, i ≤ v - u - 1 → ω (u + i) = ω u := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hi : i ≤ v - u - 1 := by omega
        have hlt : u + i + 1 < v := by omega
        have hc0 := hcount_between (u + i) (by omega) (by omega)
        have hc1 := hcount_between (u + i + 1) (by omega) hlt
        have hhold : ω (u + i + 1) = ω (u + i) := by
          rw [show u + i + 1 = (u + i) + 1 by omega,
            nonholdingUpTo_succ] at hc1
          by_contra hm
          rw [if_pos hm, hc0] at hc1
          omega
        exact hhold.trans (ih hi)
  constructor
  · intro hbirth
    unfold firstDepartureBirthFrom at hbirth
    rcases hbirth with ⟨s, hpref, hstep⟩
    have hcount_prefix :
        nonholdingUpTo ω (u + s) = r := by
      clear hstep
      induction s with
      | zero => simpa using hcu
      | succ s ih =>
          have hpj := hpref s (by omega)
          have hpjs := hpref (s + 1) le_rfl
          have hhold : ω (u + s + 1) = ω (u + s) := by
            simpa only [pathShift, Nat.add_assoc] using hpjs.trans hpj.symm
          have hpref' :
              ∀ i, i ≤ s → pathShift u ω i = ω u :=
            fun i hi => hpref i (by omega)
          rw [show u + (s + 1) = (u + s) + 1 by omega,
            nonholdingUpTo_succ, if_neg (not_not.mpr hhold), ih hpref']
          simp
    have hstep' : ω (u + s + 1) = ω (u + s) + 1 := by
      have hps := hpref s le_rfl
      simpa only [pathShift, Nat.add_assoc] using hstep.trans
        (congrArg (· + 1) hps.symm)
    have hepoch :
        nonholdingEpoch (r + 1) (u + s + 1) ω := by
      right
      refine ⟨by omega, by omega, ?_, ?_⟩
      · simpa [show u + s + 1 - 1 = u + s by omega] using
          hcount_prefix
      · simpa [show u + s + 1 - 1 = u + s by omega] using
          (show ω (u + s + 1) ≠ ω (u + s) by omega)
    have heq : u + s + 1 = v :=
      nonholdingEpoch_unique hepoch hv
    rw [← heq]
    simpa [show u + s + 1 - 1 = u + s by omega] using hstep'
  · intro hstep
    unfold firstDepartureBirthFrom
    refine ⟨v - u - 1, ?_, ?_⟩
    · intro i hi
      simp only [pathShift]
      exact hconst i hi
    · simp only [pathShift]
      have hend := hconst (v - u - 1) le_rfl
      have hidx : u + (v - u - 1) = v - 1 := by omega
      have hnext : u + (v - u - 1 + 1) = v := by omega
      rw [hnext, hstep, ← hidx, hend]

private lemma birthsUpTo_consecutive_epochs
    {r u v : ℕ} {ω : ℕ → ℕ}
    (hu : nonholdingEpoch r u ω)
    (hv : nonholdingEpoch (r + 1) v ω) :
    birthsUpTo ω v =
      birthsUpTo ω u + if ω v = ω (v - 1) + 1 then 1 else 0 := by
  have hcu : nonholdingUpTo ω u = r := nonholdingEpoch_count hu
  have hcv : nonholdingUpTo ω v = r + 1 := nonholdingEpoch_count hv
  have huv : u < v := by
    by_contra h
    have hm := nonholdingUpTo_mono ω (show v ≤ u by omega)
    rw [hcv, hcu] at hm
    omega
  have hvpos : 0 < v := by omega
  have hbefore : nonholdingUpTo ω (v - 1) = r := by
    rcases hv with hz | hp
    · omega
    · simpa using hp.2.2.1
  have hhold :
      ∀ i, u ≤ i → i + 1 < v → ω (i + 1) = ω i := by
    intro i hui hiv
    have hc0 : nonholdingUpTo ω i = r := by
      have hl := nonholdingUpTo_mono ω hui
      have hr := nonholdingUpTo_mono ω (show i ≤ v - 1 by omega)
      rw [hcu] at hl
      rw [hbefore] at hr
      omega
    have hc1 : nonholdingUpTo ω (i + 1) = r := by
      have hl := nonholdingUpTo_mono ω (show u ≤ i + 1 by omega)
      have hr := nonholdingUpTo_mono ω (show i + 1 ≤ v - 1 by omega)
      rw [hcu] at hl
      rw [hbefore] at hr
      omega
    rw [nonholdingUpTo_succ] at hc1
    by_contra hm
    rw [if_pos hm, hc0] at hc1
    omega
  unfold birthsUpTo
  rw [← Finset.sum_range_add_sum_Ico
    (fun i => if ω (i + 1) = ω i + 1 then 1 else 0) huv.le]
  congr 1
  rw [Finset.sum_eq_single (v - 1)]
  · rw [show v - 1 + 1 = v by omega]
  · intro i hi hne
    simp only [Finset.mem_Ico] at hi
    rw [if_neg]
    intro hup
    have hh := hhold i hi.1 (by omega)
    omega
  · intro hnot
    exfalso
    apply hnot
    simp [Finset.mem_Ico]
    omega

def validBdPath (ω : ℕ → ℕ) : Prop :=
  ∀ t, ω (t + 1) = ω t + 1 ∨ ω (t + 1) = ω t - 1 ∨ ω (t + 1) = ω t

private lemma birthsUpTo_succ (ω : ℕ → ℕ) (t : ℕ) :
    birthsUpTo ω (t + 1) =
      birthsUpTo ω t + if ω (t + 1) = ω t + 1 then 1 else 0 := by
  unfold birthsUpTo
  rw [Finset.sum_range_succ]

lemma state_count_birth_invariant
    (n : ℕ) (ω : ℕ → ℕ) (h0 : ω 0 = n) (hvalid : validBdPath ω) :
    ∀ t, ω t + nonholdingUpTo ω t =
      n + 2 * birthsUpTo ω t := by
  intro t
  induction t with
  | zero =>
      simp [nonholdingUpTo, birthsUpTo, h0]
  | succ t ih =>
      rw [nonholdingUpTo_succ, birthsUpTo_succ]
      rcases hvalid t with hup | hdown | hhold
      · rw [hup]
        simp
        omega
      · rw [hdown]
        by_cases hz : ω t = 0
        · simp [hz]
          simpa [hz] using ih
        · have hpos : 0 < ω t := Nat.pos_of_ne_zero hz
          have hne : ω t - 1 ≠ ω t := by omega
          have hnup : ω t - 1 ≠ ω t + 1 := by omega
          rw [if_pos hne, if_neg hnup]
          omega
      · rw [hhold]
        simp
        exact ih

lemma state_le_initial_add_births
    (n t : ℕ) (ω : ℕ → ℕ)
    (h0 : ω 0 = n) (hvalid : validBdPath ω) :
    ω t ≤ n + birthsUpTo ω t := by
  have hinv := state_count_birth_invariant n ω h0 hvalid t
  have hbirth_nonholding :
      birthsUpTo ω t ≤ nonholdingUpTo ω t := by
    unfold birthsUpTo nonholdingUpTo
    apply Finset.sum_le_sum
    intro i hi
    by_cases hb : ω (i + 1) = ω i + 1
    · rw [if_pos hb, if_pos (by omega)]
    · rw [if_neg hb]
      exact Nat.zero_le _
  omega

private lemma state_lower_of_valid
    (n : ℕ) (ω : ℕ → ℕ) (h0 : ω 0 = n) (hvalid : validBdPath ω) :
    ∀ t, n - nonholdingUpTo ω t ≤ ω t := by
  intro t
  induction t with
  | zero =>
      simp [nonholdingUpTo, h0]
  | succ t ih =>
      rw [nonholdingUpTo_succ]
      rcases hvalid t with hup | hdown | hhold
      · rw [hup]
        simp only [ne_eq, Nat.add_left_cancel_iff, one_ne_zero, not_false_eq_true, if_true]
        omega
      · rw [hdown]
        by_cases hm : ω t - 1 = ω t
        · rw [if_neg (not_not.mpr hm), hm]
          exact ih
        · rw [if_pos hm]
          omega
      · rw [hhold, if_neg (by simp)]
        exact ih

private lemma epoch_state_lower
    (n r t : ℕ) (ω : ℕ → ℕ) (h0 : ω 0 = n) (hvalid : validBdPath ω)
    (hepoch : nonholdingEpoch r t ω) :
    n - r ≤ ω t := by
  have hstate := state_lower_of_valid n ω h0 hvalid t
  rcases hepoch with ⟨rfl, rfl⟩ | ⟨hr, ht, hcount, hmove⟩
  · simpa [nonholdingUpTo, h0] using hstate
  · have hcnt : nonholdingUpTo ω t = r :=
      nonholdingEpoch_count (Or.inr ⟨hr, ht, hcount, hmove⟩)
    rwa [hcnt] at hstate

private lemma bdKernel_valid_support (N : BirthDeathChain) (x : ℕ) :
    bdKernel N x {y | y ≠ x + 1 ∧ y ≠ x - 1 ∧ y ≠ x} = 0 := by
  rw [bdKernel_apply]
  simp [Measure.smul_apply, smul_eq_mul, Measure.add_apply]

private lemma bdPathMeasure_invalid_step
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n t : ℕ) :
    bdPathMeasure N n
      {ω | ω (t + 1) ≠ ω t + 1 ∧ ω (t + 1) ≠ ω t - 1 ∧
        ω (t + 1) ≠ ω t} = 0 := by
  let P := bdPathMeasure N n
  let Bad : ℕ → Set ℕ := fun x => {y | y ≠ x + 1 ∧ y ≠ x - 1 ∧ y ≠ x}
  have hsub :
      {ω : ℕ → ℕ | ω (t + 1) ≠ ω t + 1 ∧ ω (t + 1) ≠ ω t - 1 ∧
        ω (t + 1) ≠ ω t} ⊆
        ⋃ x : ℕ, {ω | ω t = x} ∩ {ω | ω (t + 1) ∈ Bad x} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨ω t, rfl, hω⟩
  have hzero : ∀ x : ℕ,
      P ({ω | ω t = x} ∩ {ω | ω (t + 1) ∈ Bad x}) = 0 := by
    intro x
    let g : ℕ → ℝ≥0∞ := fun y => if y = x then 1 else 0
    let φ : ℕ → ℝ≥0∞ := fun y => if y ∈ Bad x then 1 else 0
    have hmeas : MeasurableSet
        ({ω : ℕ → ℕ | ω t = x} ∩ {ω | ω (t + 1) ∈ Bad x}) := by
      measurability
    rw [← lintegral_indicator_one hmeas]
    change (∫⁻ ω, ({ω : ℕ → ℕ | ω t = x} ∩
      {ω | ω (t + 1) ∈ Bad x}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂P) = 0
    have heq : ∀ ω : ℕ → ℕ,
        ({ω : ℕ → ℕ | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω =
          g (ω t) * φ (ω (t + 1)) := by
      intro ω
      by_cases h1 : ω t = x <;> by_cases h2 : ω (t + 1) ∈ Bad x <;>
        simp [g, φ, Set.indicator, h1, h2]
    rw [show ∫⁻ ω, ({ω : ℕ → ℕ | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂P =
        ∫⁻ ω, g (ω t) * φ (ω (t + 1)) ∂P by
      congr 1
      funext ω
      exact heq ω]
    change (∫⁻ ω, g (ω t) * φ (ω (t + 1))
      ∂homogeneousPathMeasure (Measure.dirac n) (bdKernel N)) = 0
    rw [homogeneousPathMeasure_joint_lintegral (bdKernel N) n t g φ
      (measurable_of_countable _) (measurable_of_countable _)]
    have hz : ∀ y : ℕ, g y * ∫⁻ z, φ z ∂bdKernel N y = 0 := by
      intro y
      by_cases hy : y = x
      · subst y
        simp only [g, φ, ↓reduceIte, one_mul]
        rw [show ∫⁻ z, φ z ∂bdKernel N x =
            bdKernel N x (Bad x) by
          rw [← lintegral_indicator_one ((Set.to_countable _).measurableSet)]
          congr 1
          funext z
          simp [φ, Set.indicator]]
        exact bdKernel_valid_support N x
      · simp [g, hy]
    simp_rw [hz, lintegral_zero]
  apply le_antisymm _ zero_le
  calc
    P {ω | ω (t + 1) ≠ ω t + 1 ∧ ω (t + 1) ≠ ω t - 1 ∧
        ω (t + 1) ≠ ω t}
        ≤ P (⋃ x : ℕ, {ω | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x}) := measure_mono hsub
    _ ≤ ∑' x, P ({ω | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x}) := measure_iUnion_le _
    _ = 0 := ENNReal.tsum_eq_zero.mpr hzero

lemma bdPathMeasure_invalid_path
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    bdPathMeasure N n {ω | ¬validBdPath ω} = 0 := by
  have heq :
      {ω : ℕ → ℕ | ¬validBdPath ω} =
        ⋃ t : ℕ, {ω | ω (t + 1) ≠ ω t + 1 ∧
          ω (t + 1) ≠ ω t - 1 ∧ ω (t + 1) ≠ ω t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, validBdPath, not_forall, not_or]
  rw [heq]
  exact measure_iUnion_null fun t => bdPathMeasure_invalid_step N n t

lemma bdPathMeasure_initial_ne
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    bdPathMeasure N n {ω | ω 0 ≠ n} = 0 := by
  rw [show {ω : ℕ → ℕ | ω 0 ≠ n} =
      {ω | ω 0 ∈ ({n} : Set ℕ)ᶜ} by ext ω; simp]
  rw [bdPathMeasure_coord_eq N n 0 {n}ᶜ (measurableSet_singleton n).compl]
  simp [kernelIter_zero, Kernel.id_apply]

private def epochStateEvent (r t x : ℕ) : Set (ℕ → ℕ) :=
  {ω | nonholdingEpoch r t ω ∧ ω t = x}

private lemma measurableSet_epochStateEvent (r t x : ℕ) :
    MeasurableSet (epochStateEvent r t x) := by
  change MeasurableSet
    ({ω : ℕ → ℕ | nonholdingEpoch r t ω} ∩ {ω | ω t = x})
  exact (measurableSet_nonholdingEpoch r t).inter (by measurability)

private lemma epochStateEvent_cylinder (r t x : ℕ) :
    isCylinderUpTo t (epochStateEvent r t x) := by
  intro ω ω' heq hω
  exact ⟨nonholdingEpoch_cylinder r t ω ω' heq hω.1,
    (heq t le_rfl).symm.trans hω.2⟩

private lemma epochStateEvent_pairwise (r : ℕ) :
    Pairwise (fun z z' : ℕ × ℕ =>
      Disjoint (epochStateEvent r z.1 z.2) (epochStateEvent r z'.1 z'.2)) := by
  intro ⟨t, x⟩ ⟨u, y⟩ hne
  rw [Set.disjoint_left]
  intro ω htx huy
  change nonholdingEpoch r t ω ∧ ω t = x at htx
  change nonholdingEpoch r u ω ∧ ω u = y at huy
  have htu := nonholdingEpoch_unique htx.1 huy.1
  subst u
  have hxy : x = y := htx.2.symm.trans huy.2
  exact hne (Prod.ext rfl hxy)

private lemma epochStateEvent_low_null
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n r t x : ℕ) (hx : x < n - r) :
    bdPathMeasure N n (epochStateEvent r t x) = 0 := by
  let P := bdPathMeasure N n
  have hsub : epochStateEvent r t x ⊆
      {ω | ω 0 ≠ n} ∪ {ω | ¬validBdPath ω} := by
    intro ω hω
    by_cases h0 : ω 0 = n
    · by_cases hv : validBdPath ω
      · exfalso
        have hlower := epoch_state_lower n r t ω h0 hv hω.1
        rw [hω.2] at hlower
        omega
      · right; exact hv
    · left; exact h0
  apply le_antisymm _ zero_le
  calc
    P (epochStateEvent r t x)
        ≤ P ({ω | ω 0 ≠ n} ∪ {ω | ¬validBdPath ω}) := measure_mono hsub
    _ ≤ P {ω | ω 0 ≠ n} + P {ω | ¬validBdPath ω} := measure_union_le _ _
    _ = 0 := by
      rw [bdPathMeasure_initial_ne N n, bdPathMeasure_invalid_path N n]
      exact add_zero 0

private lemma nice_birth_ratio_le
    (N : BirthDeathChain) (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m)
    (x l : ℕ) (hl : 0 < l) (hlx : l ≤ x) :
    N.p x / (N.p x + N.q x) ≤ C / (D * (l : ℝ)) := by
  have hx : 0 < x := lt_of_lt_of_le hl hlx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hpnn := N.p_nonneg x
  have hqD := hq x hx
  have hqpos : 0 < N.q x := lt_of_lt_of_le hD hqD
  have hpqpos : 0 < N.p x + N.q x := by linarith
  have hpx : N.p x * (x : ℝ) ≤ C := by
    exact (le_div_iff₀ hxR).mp (hp x hx)
  have hcross1 : N.p x * (D * (x : ℝ)) ≤ C * N.q x := by
    calc
      N.p x * (D * (x : ℝ)) = D * (N.p x * (x : ℝ)) := by ring
      _ ≤ D * C := mul_le_mul_of_nonneg_left hpx hD.le
      _ ≤ N.q x * C := mul_le_mul_of_nonneg_right hqD hC.le
      _ = C * N.q x := by ring
  have hratio_x :
      N.p x / (N.p x + N.q x) ≤ C / (D * (x : ℝ)) := by
    rw [div_le_div_iff₀ hpqpos (mul_pos hD hxR)]
    calc
      N.p x * (D * (x : ℝ)) ≤ C * N.q x := hcross1
      _ ≤ C * (N.p x + N.q x) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        linarith
  calc
    N.p x / (N.p x + N.q x) ≤ C / (D * (x : ℝ)) := hratio_x
    _ ≤ C / (D * (l : ℝ)) := by
      apply div_le_div_of_nonneg_left hC.le (mul_pos hD hlR)
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact_mod_cast hlx

private def nextNonholdingBirthEvent (r : ℕ) : Set (ℕ → ℕ) :=
  ⋃ t : ℕ, ⋃ x : ℕ,
    epochStateEvent r t x ∩ (pathShift t) ⁻¹' firstDepartureBirthFrom x

private lemma measurableSet_nextNonholdingBirthEvent (r : ℕ) :
    MeasurableSet (nextNonholdingBirthEvent r) := by
  unfold nextNonholdingBirthEvent
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.iUnion
  intro x
  exact (measurableSet_epochStateEvent r t x).inter
    ((measurableSet_firstDepartureBirthFrom x).preimage
      (measurable_pi_lambda _ fun i => measurable_pi_apply _))

private lemma nextNonholdingBirth_prob_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m)
    (n r : ℕ) (hr : r < n) :
    bdPathMeasure N n (nextNonholdingBirthEvent r) ≤
      ENNReal.ofReal (C / (D * ((n - r : ℕ) : ℝ))) := by
  let P := bdPathMeasure N n
  let L := ENNReal.ofReal (C / (D * ((n - r : ℕ) : ℝ)))
  let c : ℕ → ℕ → ℝ≥0∞ := fun _t x =>
    bdPathMeasure N x (firstDepartureBirthFrom x)
  letI : IsProbabilityMeasure P := by
    simp only [P, bdPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hmarkov :
      P (nextNonholdingBirthEvent r) ≤
        ∑' t, ∑' x, c t x * P (epochStateEvent r t x) := by
    exact homogeneousPathMeasure_markov_bound_countable
      (bdKernel N) n
      (fun t x => epochStateEvent r t x)
      (fun _t x => firstDepartureBirthFrom x)
      c
      (fun t x => measurableSet_epochStateEvent r t x)
      (fun _t x => measurableSet_firstDepartureBirthFrom x)
      (fun t x => epochStateEvent_cylinder r t x)
      (fun t x ω hω => by
        change bdPathMeasure N (ω t) (firstDepartureBirthFrom x) ≤
          bdPathMeasure N x (firstDepartureBirthFrom x)
        rw [hω.2])
  have hlpos : 0 < n - r := Nat.sub_pos_of_lt hr
  have hterm : ∀ t x,
      c t x * P (epochStateEvent r t x) ≤
        L * P (epochStateEvent r t x) := by
    intro t x
    by_cases hx : n - r ≤ x
    · have hxpos : 0 < x := lt_of_lt_of_le hlpos hx
      have hqpos : 0 < N.q x := lt_of_lt_of_le hD (hq x hxpos)
      have hbase := firstDepartureBirthFrom_prob_le N x hxpos hqpos
      have hratio := nice_birth_ratio_le N C D hC hD hp hq x (n - r) hlpos hx
      apply mul_le_mul_of_nonneg_right _ zero_le
      calc
        c t x ≤ ENNReal.ofReal (N.p x / (N.p x + N.q x)) := hbase
        _ ≤ L := ENNReal.ofReal_le_ofReal hratio
    · have hlow : x < n - r := by omega
      rw [epochStateEvent_low_null N n r t x hlow, mul_zero, mul_zero]
  have hsum_le :
      (∑' t, ∑' x, P (epochStateEvent r t x)) ≤ 1 := by
    rw [← ENNReal.tsum_prod]
    rw [← measure_iUnion (epochStateEvent_pairwise r)
      (fun z => measurableSet_epochStateEvent r z.1 z.2)]
    calc
      P (⋃ z : ℕ × ℕ, epochStateEvent r z.1 z.2) ≤ P Set.univ :=
        measure_mono (fun _ _ => Set.mem_univ _)
      _ = 1 := measure_univ
  calc
    P (nextNonholdingBirthEvent r)
        ≤ ∑' t, ∑' x, c t x * P (epochStateEvent r t x) := hmarkov
    _ ≤ ∑' t, ∑' x, L * P (epochStateEvent r t x) := by
      apply ENNReal.tsum_le_tsum
      intro t
      apply ENNReal.tsum_le_tsum
      exact hterm t
    _ = L * (∑' t, ∑' x, P (epochStateEvent r t x)) := by
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ L * 1 := mul_le_mul_of_nonneg_left hsum_le zero_le
    _ = ENNReal.ofReal (C / (D * ((n - r : ℕ) : ℝ))) := by
      simp [L]

private lemma mem_nextNonholdingBirthEvent_iff_up
    {r u v : ℕ} {ω : ℕ → ℕ}
    (hu : nonholdingEpoch r u ω)
    (hv : nonholdingEpoch (r + 1) v ω) :
    ω ∈ nextNonholdingBirthEvent r ↔
      ω v = ω (v - 1) + 1 := by
  have hnext :
      ω ∈ nextNonholdingBirthEvent r ↔
        pathShift u ω ∈ firstDepartureBirthFrom (ω u) := by
    unfold nextNonholdingBirthEvent
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      epochStateEvent, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, x, ⟨ht, htx⟩, hbirth⟩
      have htu : t = u := nonholdingEpoch_unique ht hu
      subst t
      have hxu : x = ω u := htx.symm
      subst x
      exact hbirth
    · intro hbirth
      exact ⟨u, ω u, ⟨hu, rfl⟩, hbirth⟩
  exact hnext.trans
    (shifted_firstDeparture_iff_up_of_consecutive_epochs hu hv)

private noncomputable def nonholdingBirthIndicator
    (r : ℕ) (ω : ℕ → ℕ) : ℕ :=
  @ite ℕ (ω ∈ nextNonholdingBirthEvent r) (Classical.propDecidable _) 1 0

private noncomputable def birthsInFirstNonholding (n : ℕ) (ω : ℕ → ℕ) : ℕ :=
  ∑ r ∈ Finset.range n, nonholdingBirthIndicator r ω

private lemma measurable_nonholdingBirthIndicator (r : ℕ) :
    Measurable (nonholdingBirthIndicator r) := by
  unfold nonholdingBirthIndicator
  exact Measurable.ite (measurableSet_nextNonholdingBirthEvent r)
    measurable_const measurable_const

private lemma measurable_birthsInFirstNonholding (n : ℕ) :
    Measurable (birthsInFirstNonholding n) := by
  unfold birthsInFirstNonholding
  apply Finset.measurable_fun_sum
  intro r hr
  exact measurable_nonholdingBirthIndicator r

private lemma birthsInFirstNonholding_eq_birthsUpTo_epoch
    (n T : ℕ) (ω : ℕ → ℕ) (hT : nonholdingEpoch n T ω) :
    birthsInFirstNonholding n ω = birthsUpTo ω T := by
  induction n generalizing T with
  | zero =>
      rcases hT with hz | hp
      · rw [hz.2]
        simp [birthsInFirstNonholding, birthsUpTo]
      · omega
  | succ n ih =>
      obtain ⟨u, huT, hu⟩ :=
        nonholdingEpoch_exists_before hT n (by omega)
      have hprev : nonholdingEpoch n u ω := hu
      have ihU := ih u hprev
      have hbirths := birthsUpTo_consecutive_epochs hprev hT
      have hevent := mem_nextNonholdingBirthEvent_iff_up hprev hT
      rw [birthsInFirstNonholding, Finset.sum_range_succ]
      change birthsInFirstNonholding n ω +
          nonholdingBirthIndicator n ω = birthsUpTo ω T
      rw [ihU, hbirths]
      by_cases hup : ω T = ω (T - 1) + 1
      · have hmem : ω ∈ nextNonholdingBirthEvent n := hevent.mpr hup
        simp [nonholdingBirthIndicator, hup, hmem]
      · have hmem : ω ∉ nextNonholdingBirthEvent n :=
          fun h => hup (hevent.mp h)
        simp [nonholdingBirthIndicator, hup, hmem]

private lemma epoch_state_eq_twice_first_births
    (n T : ℕ) (ω : ℕ → ℕ) (h0 : ω 0 = n)
    (hvalid : validBdPath ω) (hT : nonholdingEpoch n T ω) :
    ω T = 2 * birthsInFirstNonholding n ω := by
  have hinv := state_count_birth_invariant n ω h0 hvalid T
  rw [nonholdingEpoch_count hT,
    ← birthsInFirstNonholding_eq_birthsUpTo_epoch n T ω hT] at hinv
  omega

private lemma bd_harmonic_cast_eq_sum_real (n : ℕ) :
    (harmonic n : ℝ) =
      ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
  have heq : (harmonic n : ℝ) =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)⁻¹ := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq]
  congr 1
  ext k
  push_cast
  ring

private lemma bd_remaining_harmonic_sum_le
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D) (n : ℕ) :
    ∑ r ∈ Finset.range n, C / (D * ((n - r : ℕ) : ℝ)) ≤
      (C / D) * (Real.log n + 1) := by
  have hreindex :
      ∑ r ∈ Finset.range n, (1 : ℝ) / ((n - r : ℕ) : ℝ) =
        ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect
      (fun k => (1 : ℝ) / ((k : ℝ) + 1)) n]
    apply Finset.sum_congr rfl
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    congr 1
    norm_cast
    omega
  have hharm :
      ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) ≤
        Real.log n + 1 := by
    rw [← bd_harmonic_cast_eq_sum_real]
    have h := harmonic_le_one_add_log n
    linarith
  calc
    ∑ r ∈ Finset.range n, C / (D * ((n - r : ℕ) : ℝ))
        = (C / D) *
            ∑ r ∈ Finset.range n, (1 : ℝ) / ((n - r : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          have hrem : (0 : ℝ) < (n - r : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt (Finset.mem_range.mp hr)
          field_simp
    _ = (C / D) *
          ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
          rw [hreindex]
    _ ≤ (C / D) * (Real.log n + 1) :=
      mul_le_mul_of_nonneg_left hharm (div_nonneg hC.le hD.le)

private lemma birthsInFirstNonholding_lintegral_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m)
    (n : ℕ) :
    ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂bdPathMeasure N n ≤
      ENNReal.ofReal ((C / D) * (Real.log n + 1)) := by
  let P := bdPathMeasure N n
  have hpoint : ∀ ω : ℕ → ℕ,
      (birthsInFirstNonholding n ω : ℝ≥0∞) =
        ∑ r ∈ Finset.range n,
          (nextNonholdingBirthEvent r).indicator
            (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [birthsInFirstNonholding, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hmem : ω ∈ nextNonholdingBirthEvent r
    · simp [nonholdingBirthIndicator, Set.indicator, hmem]
    · simp [nonholdingBirthIndicator, Set.indicator, hmem]
  calc
    ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P
        = ∫⁻ ω, ∑ r ∈ Finset.range n,
            (nextNonholdingBirthEvent r).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
          congr 1
          funext ω
          exact hpoint ω
    _ = ∑ r ∈ Finset.range n, P (nextNonholdingBirthEvent r) := by
          rw [lintegral_finset_sum]
          · apply Finset.sum_congr rfl
            intro r hr
            exact lintegral_indicator_one
              (measurableSet_nextNonholdingBirthEvent r)
          · intro r hr
            exact measurable_const.indicator
              (measurableSet_nextNonholdingBirthEvent r)
    _ ≤ ∑ r ∈ Finset.range n,
          ENNReal.ofReal (C / (D * ((n - r : ℕ) : ℝ))) := by
          apply Finset.sum_le_sum
          intro r hr
          exact nextNonholdingBirth_prob_le N C D hC hD hp hq n r
            (Finset.mem_range.mp hr)
    _ = ENNReal.ofReal
          (∑ r ∈ Finset.range n, C / (D * ((n - r : ℕ) : ℝ))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro r hr
          positivity
    _ ≤ ENNReal.ofReal ((C / D) * (Real.log n + 1)) :=
      ENNReal.ofReal_le_ofReal (bd_remaining_harmonic_sum_le C D hC hD n)

lemma extinctionTime_measurable :
    Measurable extinctionTime := by
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℕ)) :=
    Filtration.piLE (X := fun _ : ℕ => ℕ)
  have hadapt : StronglyAdapted ℱ natCoord := by
    intro t
    have hrestrict :
        Measurable[ℱ t] (frestrictLe t : (ℕ → ℕ) → ∀ i : Finset.Iic t, ℕ) := by
      change Measurable[
        Filtration.piLE (X := fun _ : ℕ => ℕ) t] (frestrictLe t)
      rw [Filtration.piLE_eq_comap_frestrictLe
        (X := fun _ : ℕ => ℕ)]
      exact comap_measurable _
    exact ((measurable_pi_apply
      (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t)).comp
        hrestrict).stronglyMeasurable
  have hstop : IsStoppingTime ℱ extinctionTime := by
    exact hadapt.adapted.isStoppingTime_hittingAfter
      (measurableSet_singleton 0)
  exact hstop.measurable'

lemma extinctionTimeUntop_measurable :
    Measurable (fun ω : ℕ → ℕ => (extinctionTime ω).untopD 0) :=
  extinctionTime_measurable.untopD 0

lemma extinctionTime_pathShift_eq_sub
    (ω : ℕ → ℕ) (T τ : ℕ) (hTτ : T ≤ τ)
    (hτ : extinctionTime ω = (τ : WithTop ℕ)) :
    extinctionTime (pathShift T ω) = ((τ - T : ℕ) : WithTop ℕ) := by
  have hzero : ω τ = 0 := by
    have hne : extinctionTime ω ≠ ⊤ := by rw [hτ]; simp
    have hmem := hittingAfter_mem_set_of_ne_top
      (u := natCoord) (s := ({0} : Set ℕ)) (n := 0) (ω := ω) hne
    have huntop : (extinctionTime ω).untopA = τ := by
      rw [hτ]
      rfl
    change natCoord (extinctionTime ω).untopA ω ∈ ({0} : Set ℕ) at hmem
    rw [huntop] at hmem
    simpa [natCoord] using hmem
  have hshiftZero : pathShift T ω (τ - T) = 0 := by
    simp only [pathShift]
    rw [show T + (τ - T) = τ by omega, hzero]
  have hle :
      extinctionTime (pathShift T ω) ≤ (τ - T : ℕ) :=
    ext_time_le_of_zero (pathShift T ω) (τ - T) hshiftZero
  have hne : extinctionTime (pathShift T ω) ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top) hle
  lift extinctionTime (pathShift T ω) to ℕ using hne with σ hσ
  have hσle : σ ≤ τ - T := by
    exact WithTop.coe_le_coe.mp hle
  have hσzero : pathShift T ω σ = 0 := by
    have hne' : extinctionTime (pathShift T ω) ≠ ⊤ := by
      rw [← hσ]
      simp
    have hmem := hittingAfter_mem_set_of_ne_top
      (u := natCoord) (s := ({0} : Set ℕ)) (n := 0)
      (ω := pathShift T ω) hne'
    have huntop :
        (extinctionTime (pathShift T ω)).untopA = σ := by
      rw [← hσ]
      rfl
    change natCoord (extinctionTime (pathShift T ω)).untopA
      (pathShift T ω) ∈ ({0} : Set ℕ) at hmem
    rw [huntop] at hmem
    simpa [natCoord] using hmem
  have hglobal : extinctionTime ω ≤ (T + σ : ℕ) := by
    apply ext_time_le_of_zero
    simpa [pathShift] using hσzero
  have hτle : τ ≤ T + σ := by
    rw [hτ] at hglobal
    exact WithTop.coe_le_coe.mp hglobal
  have hστ : σ = τ - T := by omega
  exact congrArg (fun m : ℕ => (m : WithTop ℕ)) hστ

lemma birthsUpTo_add_shift
    (ω : ℕ → ℕ) (T s : ℕ) :
    birthsUpTo ω (T + s) =
      birthsUpTo ω T + birthsUpTo (pathShift T ω) s := by
  unfold birthsUpTo
  rw [Finset.sum_range_add]
  congr 1

private lemma birthsUpTo_le_time (ω : ℕ → ℕ) (t : ℕ) :
    birthsUpTo ω t ≤ t := by
  unfold birthsUpTo
  calc
    ∑ i ∈ Finset.range t,
        (if ω (i + 1) = ω i + 1 then 1 else 0)
        ≤ ∑ _i ∈ Finset.range t, 1 := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs <;> omega
    _ = t := by simp

private noncomputable def epochFutureExtinction
    (n : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' z : ℕ × ℕ,
    (epochStateEvent n z.1 z.2).indicator
      (fun η =>
        (((extinctionTime (pathShift z.1 η)).untopD 0 : ℕ) : ℝ≥0∞)) ω

private lemma measurable_epochFutureExtinction (n : ℕ) :
    Measurable (epochFutureExtinction n) := by
  unfold epochFutureExtinction
  apply Measurable.ennreal_tsum
  intro z
  apply Measurable.indicator
  · have hshift : Measurable
        (pathShift z.1 : (ℕ → ℕ) → ℕ → ℕ) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply _
    exact (measurable_of_countable
      (fun m : ℕ => (m : ℝ≥0∞))).comp
        (extinctionTimeUntop_measurable.comp hshift)
  · exact measurableSet_epochStateEvent n z.1 z.2

private lemma birthsBeforeExtinction_le_epoch_restart
    (n : ℕ) (ω : ℕ → ℕ) (h0 : ω 0 = n)
    (hvalid : validBdPath ω) :
    (birthsBeforeExtinction ω : ℝ≥0∞) ≤
      (birthsInFirstNonholding n ω : ℝ≥0∞) +
        epochFutureExtinction n ω := by
  by_cases htop : extinctionTime ω = ⊤
  · simp [birthsBeforeExtinction, htop]
  · lift extinctionTime ω to ℕ using htop with τ hτ
    have hzero : ω τ = 0 := by
      have htop' : extinctionTime ω ≠ ⊤ := by
        rw [← hτ]
        simp
      have hmem := hittingAfter_mem_set_of_ne_top
        (u := natCoord) (s := ({0} : Set ℕ)) (n := 0) (ω := ω) htop'
      have huntop : (extinctionTime ω).untopA = τ := by
        rw [← hτ]
        rfl
      change natCoord (extinctionTime ω).untopA ω ∈ ({0} : Set ℕ) at hmem
      rw [huntop] at hmem
      simpa [natCoord] using hmem
    have hcount : n ≤ nonholdingUpTo ω τ := by
      have hlower := state_lower_of_valid n ω h0 hvalid τ
      rw [hzero] at hlower
      omega
    obtain ⟨T, hTτ, hT⟩ :=
      nonholdingEpoch_exists_of_le_count ω n τ hcount
    have hprefix :
        birthsUpTo ω T = birthsInFirstNonholding n ω :=
      (birthsInFirstNonholding_eq_birthsUpTo_epoch n T ω hT).symm
    have hshift :=
      extinctionTime_pathShift_eq_sub ω T τ hTτ hτ.symm
    have hsplit :
        birthsUpTo ω τ =
          birthsUpTo ω T + birthsUpTo (pathShift T ω) (τ - T) := by
      calc
        birthsUpTo ω τ =
            birthsUpTo ω (T + (τ - T)) := by
              congr 1
              omega
        _ = birthsUpTo ω T +
            birthsUpTo (pathShift T ω) (τ - T) :=
          birthsUpTo_add_shift ω T (τ - T)
    have hnat :
        birthsBeforeExtinction ω ≤
          birthsInFirstNonholding n ω +
            (extinctionTime (pathShift T ω)).untopD 0 := by
      simp only [birthsBeforeExtinction, ← hτ, hsplit, hprefix, hshift,
        WithTop.untopD_coe]
      exact Nat.add_le_add_left
        (birthsUpTo_le_time (pathShift T ω) (τ - T)) _
    have hterm :
        (((extinctionTime (pathShift T ω)).untopD 0 : ℕ) : ℝ≥0∞) ≤
          epochFutureExtinction n ω := by
      unfold epochFutureExtinction
      have hle := ENNReal.le_tsum
        (f := fun z : ℕ × ℕ =>
          (epochStateEvent n z.1 z.2).indicator
            (fun ω =>
              (((extinctionTime (pathShift z.1 ω)).untopD 0 : ℕ) :
                ℝ≥0∞)) ω)
        (T, ω T)
      simpa [epochStateEvent, hT] using hle
    exact (show
        (birthsBeforeExtinction ω : ℝ≥0∞) ≤
          (birthsInFirstNonholding n ω : ℝ≥0∞) +
            (((extinctionTime (pathShift T ω)).untopD 0 : ℕ) : ℝ≥0∞)
        by exact_mod_cast hnat).trans
      (add_le_add (le_refl _) hterm)

private noncomputable def epochStateAt
    (n : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' z : ℕ × ℕ,
    (epochStateEvent n z.1 z.2).indicator
      (fun _ => (z.2 : ℝ≥0∞)) ω

private lemma measurable_epochStateAt (n : ℕ) :
    Measurable (epochStateAt n) := by
  unfold epochStateAt
  apply Measurable.ennreal_tsum
  intro z
  exact measurable_const.indicator
    (measurableSet_epochStateEvent n z.1 z.2)

private lemma epochStateAt_eq_of_epoch
    {n T : ℕ} {ω : ℕ → ℕ} (hT : nonholdingEpoch n T ω) :
    epochStateAt n ω = (ω T : ℝ≥0∞) := by
  unfold epochStateAt
  rw [tsum_eq_single (T, ω T)]
  · simp [epochStateEvent, hT]
  · intro z hzne
    rw [Set.indicator_of_notMem]
    intro hz
    have ht : z.1 = T := nonholdingEpoch_unique hz.1 hT
    have hx : z.2 = ω T := by
      rw [← hz.2, ht]
    exact hzne (Prod.ext ht hx)

private lemma epochStateAt_le_twice_births
    (n : ℕ) (ω : ℕ → ℕ) (h0 : ω 0 = n)
    (hvalid : validBdPath ω) :
    epochStateAt n ω ≤
      (2 * birthsInFirstNonholding n ω : ℕ) := by
  by_cases hex : ∃ T, nonholdingEpoch n T ω
  · obtain ⟨T, hT⟩ := hex
    rw [epochStateAt_eq_of_epoch hT,
      epoch_state_eq_twice_first_births n T ω h0 hvalid hT]
  · unfold epochStateAt
    have hz :
        (∑' z : ℕ × ℕ,
          (epochStateEvent n z.1 z.2).indicator
            (fun _ => (z.2 : ℝ≥0∞)) ω) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro z
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hex ⟨z.1, hmem.1⟩
    rw [hz]
    exact zero_le

private lemma epochStateAt_lintegral_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    ∫⁻ ω, epochStateAt n ω ∂bdPathMeasure N n ≤
      2 * ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞)
        ∂bdPathMeasure N n := by
  let P := bdPathMeasure N n
  have hae0 : ∀ᵐ ω ∂P, ω 0 = n := by
    have h := compl_mem_ae_iff.mpr (bdPathMeasure_initial_ne N n)
    filter_upwards [h] with ω hω
    simpa using hω
  have haevalid : ∀ᵐ ω ∂P, validBdPath ω := by
    have h := compl_mem_ae_iff.mpr (bdPathMeasure_invalid_path N n)
    filter_upwards [h] with ω hω
    simpa using hω
  calc
    ∫⁻ ω, epochStateAt n ω ∂P
        ≤ ∫⁻ ω, 2 * (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hae0, haevalid] with ω h0 hv
          simpa [Nat.cast_mul] using
            epochStateAt_le_twice_births n ω h0 hv
    _ = 2 * ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P := by
          rw [lintegral_const_mul]
          exact (measurable_of_countable
            (fun m : ℕ => (m : ℝ≥0∞))).comp
              (measurable_birthsInFirstNonholding n)

private lemma bd_drift_neg_from_inverse_birth_bound
    (N : BirthDeathChain) (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m) :
    ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → 0 < m →
      N.p m - N.q m ≤ -(D / 2) := by
  refine ⟨Nat.ceil (2 * C / D) + 1, ?_⟩
  intro m hm hmpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hratio : C / (m : ℝ) ≤ D / 2 := by
    rw [div_le_div_iff₀ hmR (by positivity)]
    have h1 : (Nat.ceil (2 * C / D) : ℝ) + 1 ≤ m := by
      exact_mod_cast hm
    have h2 : 2 * C / D ≤ Nat.ceil (2 * C / D) := Nat.le_ceil _
    have h3 : 2 * C / D ≤ (m : ℝ) - 1 := by linarith
    have h4 : 2 * C ≤ D * ((m : ℝ) - 1) := by
      have := (div_le_iff₀ hD).mp h3
      linarith
    linarith
  linarith [hp m hmpos, hq m hmpos]

private lemma epochStateAt_lintegral_eq_mass
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    ∫⁻ ω, epochStateAt n ω ∂bdPathMeasure N n =
      ∑' z : ℕ × ℕ,
        (z.2 : ℝ≥0∞) *
          bdPathMeasure N n (epochStateEvent n z.1 z.2) := by
  unfold epochStateAt
  rw [lintegral_tsum]
  · apply tsum_congr
    intro z
    rw [lintegral_indicator
      (measurableSet_epochStateEvent n z.1 z.2)]
    simp
  · intro z
    exact (measurable_const.indicator
      (measurableSet_epochStateEvent n z.1 z.2)).aemeasurable

private lemma epochFutureExtinction_lintegral_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      ∫⁻ ω, epochFutureExtinction n ω ∂bdPathMeasure N n ≤
        ENNReal.ofReal K * 2 *
          ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞)
            ∂bdPathMeasure N n := by
  obtain ⟨n₀, hdrift⟩ :=
    bd_drift_neg_from_inverse_birth_bound N C D hC hD hp hq
  obtain ⟨K, hK, hExt⟩ :=
    bd_expected_extinction_linear_ennreal N (D / 2) (by positivity)
      n₀ hdrift D hD hq
  refine ⟨K, hK, fun n => ?_⟩
  let P := bdPathMeasure N n
  have hsum :
      ∫⁻ ω, epochFutureExtinction n ω ∂P =
        ∑' z : ℕ × ℕ,
          ∫⁻ ω,
            (epochStateEvent n z.1 z.2).indicator
              (fun η =>
                (((extinctionTime (pathShift z.1 η)).untopD 0 : ℕ) :
                  ℝ≥0∞)) ω ∂P := by
    unfold epochFutureExtinction
    rw [lintegral_tsum]
    intro z
    apply AEMeasurable.indicator
    · have hshift : Measurable
          (pathShift z.1 : (ℕ → ℕ) → ℕ → ℕ) :=
        measurable_pi_lambda _ fun i => measurable_pi_apply _
      exact ((measurable_of_countable
        (fun m : ℕ => (m : ℝ≥0∞))).comp
          (extinctionTimeUntop_measurable.comp hshift)).aemeasurable
    · exact measurableSet_epochStateEvent n z.1 z.2
  rw [hsum]
  calc
    (∑' z : ℕ × ℕ,
        ∫⁻ ω,
          (epochStateEvent n z.1 z.2).indicator
            (fun η =>
              (((extinctionTime (pathShift z.1 η)).untopD 0 : ℕ) :
                ℝ≥0∞)) ω ∂P)
        ≤ ∑' z : ℕ × ℕ,
            expectedExtinctionTime N z.2 *
              P (epochStateEvent n z.1 z.2) := by
          apply ENNReal.tsum_le_tsum
          intro z
          rw [lintegral_indicator
            (measurableSet_epochStateEvent n z.1 z.2)]
          exact homogeneousPathMeasure_markov_lintegral_nat
            (bdKernel N) n z.2 z.1
            (epochStateEvent n z.1 z.2)
            (fun η => (extinctionTime η).untopD 0)
            (measurableSet_epochStateEvent n z.1 z.2)
            (epochStateEvent_cylinder n z.1 z.2)
            extinctionTimeUntop_measurable
            (fun ω hω => hω.2)
    _ ≤ ∑' z : ℕ × ℕ,
          ENNReal.ofReal (K * (z.2 : ℝ)) *
            P (epochStateEvent n z.1 z.2) := by
          apply ENNReal.tsum_le_tsum
          intro z
          exact mul_le_mul_of_nonneg_right (hExt z.2) zero_le
    _ = ENNReal.ofReal K *
          (∑' z : ℕ × ℕ, (z.2 : ℝ≥0∞) *
            P (epochStateEvent n z.1 z.2)) := by
          simp_rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_natCast,
            mul_assoc, ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal K *
          (∫⁻ ω, epochStateAt n ω ∂P) := by
          rw [epochStateAt_lintegral_eq_mass N n]
    _ ≤ ENNReal.ofReal K *
          (2 * ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P) := by
          apply mul_le_mul_of_nonneg_left
          exact epochStateAt_lintegral_le N n
          exact zero_le
    _ = ENNReal.ofReal K * 2 *
          ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P := by
          rw [mul_assoc]

lemma expectedBirthsBeforeExtinction_ennreal_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ n,
      expectedBirthsBeforeExtinction N n ≤
        A * ENNReal.ofReal ((C / D) * (Real.log n + 1)) := by
  obtain ⟨K, hK, hfuture⟩ :=
    epochFutureExtinction_lintegral_le N C D hC hD hp hq
  let A : ℝ≥0∞ := 1 + ENNReal.ofReal K * 2
  refine ⟨A, ?_, fun n => ?_⟩
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by norm_num)⟩
  let P := bdPathMeasure N n
  have hmeasB : Measurable
      (fun ω : ℕ → ℕ =>
        (birthsInFirstNonholding n ω : ℝ≥0∞)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ≥0∞))).comp
      (measurable_birthsInFirstNonholding n)
  have hae0 : ∀ᵐ ω ∂P, ω 0 = n := by
    have h := compl_mem_ae_iff.mpr (bdPathMeasure_initial_ne N n)
    filter_upwards [h] with ω hω
    simpa using hω
  have haevalid : ∀ᵐ ω ∂P, validBdPath ω := by
    have h := compl_mem_ae_iff.mpr (bdPathMeasure_invalid_path N n)
    filter_upwards [h] with ω hω
    simpa using hω
  calc
    expectedBirthsBeforeExtinction N n
        ≤ ∫⁻ ω,
            (birthsInFirstNonholding n ω : ℝ≥0∞) +
              epochFutureExtinction n ω ∂P := by
          unfold expectedBirthsBeforeExtinction
          apply lintegral_mono_ae
          filter_upwards [hae0, haevalid] with ω h0 hv
          exact birthsBeforeExtinction_le_epoch_restart n ω h0 hv
    _ = (∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P) +
          ∫⁻ ω, epochFutureExtinction n ω ∂P := by
          rw [lintegral_add_left hmeasB]
    _ ≤ (∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P) +
          ENNReal.ofReal K * 2 *
            ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P := by
          exact add_le_add (le_refl _) (hfuture n)
    _ = A * ∫⁻ ω, (birthsInFirstNonholding n ω : ℝ≥0∞) ∂P := by
          simp [A]
          ring
    _ ≤ A * ENNReal.ofReal ((C / D) * (Real.log n + 1)) := by
          apply mul_le_mul_of_nonneg_left
          exact birthsInFirstNonholding_lintegral_le N C D hC hD hp hq n
          exact zero_le

theorem bd_expected_births_logarithmic_unconditional
    (N : BirthDeathChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)]
    (C : ℝ) (hC : 0 < C)
    (hp : ∀ n, 0 < n → N.p n ≤ C / ↑n)
    (D : ℝ) (hD : 0 < D) (hq : ∀ n, 0 < n → D ≤ N.q n) :
    IsBigOEventuallyENN
      (fun n => expectedBirthsBeforeExtinction N n)
      logScale := by
  obtain ⟨A, hA, hbound⟩ :=
    expectedBirthsBeforeExtinction_ennreal_le N C D hC hD hp hq
  let L : ℝ := 1 + 1 / Real.log 2
  let M : ℝ := A.toReal * (C / D) * L
  refine ⟨M, 1, ?_, fun n hn => ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [M, L]
    positivity
  · have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by
      exact_mod_cast hn)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hnplus : (2 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show 2 ≤ n + 1 by omega)
    have hlog2le :
        Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by norm_num) hnplus
    have hlognle :
        Real.log n ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hnR (by linarith)
    have hone :
        1 ≤ (1 / Real.log 2) * Real.log ((n : ℝ) + 1) := by
      have hdiv :
          1 ≤ Real.log ((n : ℝ) + 1) / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr (by simpa using hlog2le)
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    have hbridge :
        Real.log n + 1 ≤
          L * Real.log ((n : ℝ) + 1) := by
      dsimp [L]
      nlinarith
    have hscale : logScale n = Real.log ((n : ℝ) + 1) := by
      simp [logScale]
    have hmul :
        A * ENNReal.ofReal ((C / D) * (Real.log n + 1)) =
          ENNReal.ofReal (A.toReal * ((C / D) * (Real.log n + 1))) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hA]
    refine (hbound n).trans ?_
    rw [hmul, hscale]
    refine ENNReal.ofReal_le_ofReal ?_
    dsimp [M]
    have hfac : 0 ≤ A.toReal * (C / D) := by positivity
    calc
      A.toReal * ((C / D) * (Real.log n + 1))
          = (A.toReal * (C / D)) * (Real.log n + 1) := by ring
      _ ≤ (A.toReal * (C / D)) *
          (L * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hbridge hfac
      _ = A.toReal * (C / D) * L *
          Real.log ((n : ℝ) + 1) := by ring

end LVConsensus
