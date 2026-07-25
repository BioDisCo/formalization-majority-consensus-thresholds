import LVConsensus.ExpectedBirthsProof

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal BigOperators

namespace LVConsensus

/-!
# High-probability birth bound for nice chains

This file formalizes the corrected block/restart proof from the paper.  A
block ends at the first time a prescribed number of new births has occurred.
The strong Markov bound is then applied to the countable partition by that
time and the state at the end of the block.
-/

private lemma measurable_birthsUpTo (t : ℕ) :
    Measurable (fun ω : ℕ → ℕ => birthsUpTo ω t) := by
  unfold birthsUpTo
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · have hp : Measurable
        (fun ω : ℕ → ℕ => (ω (i + 1), ω i)) :=
      (measurable_pi_apply (i + 1)).prodMk
        (measurable_pi_apply i)
    exact hp ((Set.to_countable
      {z : ℕ × ℕ | z.1 = z.2 + 1}).measurableSet)
  · exact measurable_const
  · exact measurable_const

private lemma birthsUpTo_congr
    (t : ℕ) (ω η : ℕ → ℕ)
    (h : ∀ i, i ≤ t → ω i = η i) :
    birthsUpTo ω t = birthsUpTo η t := by
  unfold birthsUpTo
  apply Finset.sum_congr rfl
  intro i hi
  have hit : i < t := Finset.mem_range.mp hi
  rw [h i (by omega), h (i + 1) (by omega)]

/-- The first time the running birth count reaches `r`, together with the
state at that time. -/
private def firstBirthBlock (r t x : ℕ) : Set (ℕ → ℕ) :=
  {ω | r ≤ birthsUpTo ω t ∧
    (∀ u < t, birthsUpTo ω u < r) ∧ ω t = x}

private lemma measurableSet_firstBirthBlock (r t x : ℕ) :
    MeasurableSet (firstBirthBlock r t x) := by
  have hall :
      MeasurableSet {ω : ℕ → ℕ |
        ∀ u < t, birthsUpTo ω u < r} := by
    rw [show {ω : ℕ → ℕ | ∀ u < t, birthsUpTo ω u < r} =
        ⋂ u : Fin t, {ω | birthsUpTo ω u < r} by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h u
        exact h u u.2
      · intro h u hu
        exact h ⟨u, hu⟩]
    exact MeasurableSet.iInter fun u =>
      measurable_birthsUpTo u measurableSet_Iio
  unfold firstBirthBlock
  exact (measurable_birthsUpTo t measurableSet_Ici).inter
    (hall.inter
      (by
        have heval :
            Measurable (fun ω : ℕ → ℕ => ω t) :=
          measurable_pi_apply t
        have hm := heval (measurableSet_singleton x)
        convert hm using 1
        ext ω
        rfl))

private lemma firstBirthBlock_cylinder (r t x : ℕ) :
    isCylinderUpTo t (firstBirthBlock r t x) := by
  intro ω η h hω
  change r ≤ birthsUpTo ω t ∧
    (∀ u < t, birthsUpTo ω u < r) ∧ ω t = x at hω
  change r ≤ birthsUpTo η t ∧
    (∀ u < t, birthsUpTo η u < r) ∧ η t = x
  refine ⟨?_, ?_, h t le_rfl ▸ hω.2.2⟩
  · have heq := birthsUpTo_congr t ω η h
    omega
  · intro u hu
    have heq := birthsUpTo_congr u ω η
      (fun i hi => h i (le_trans hi (Nat.le_of_lt hu)))
    have hprev := hω.2.1 u hu
    omega

private lemma firstBirthBlock_unique_time
    (r t u x y : ℕ) (ω : ℕ → ℕ)
    (ht : ω ∈ firstBirthBlock r t x)
    (hu : ω ∈ firstBirthBlock r u y) :
    t = u := by
  rcases lt_trichotomy t u with htu | htu | htu
  · exact absurd ht.1 (Nat.not_le_of_lt (hu.2.1 t htu))
  · exact htu
  · exact absurd hu.1 (Nat.not_le_of_lt (ht.2.1 u htu))

private lemma firstBirthBlock_pairwise (r : ℕ) :
    Pairwise fun z z' : ℕ × ℕ =>
      Disjoint (firstBirthBlock r z.1 z.2)
        (firstBirthBlock r z'.1 z'.2) := by
  intro ⟨t, x⟩ ⟨u, y⟩ hne
  rw [Set.disjoint_left]
  intro ω ht hu
  have htu := firstBirthBlock_unique_time r t u x y ω ht hu
  subst u
  have hxy : x = y := ht.2.2.symm.trans hu.2.2
  exact hne (Prod.ext rfl hxy)

private lemma exists_firstBirthBlock
    (r T : ℕ) (ω : ℕ → ℕ)
    (h : r ≤ birthsUpTo ω T) :
    ∃ t ≤ T, ω ∈ firstBirthBlock r t (ω t) := by
  let hex : ∃ u, r ≤ birthsUpTo ω u := ⟨T, h⟩
  let t := Nat.find hex
  have ht : r ≤ birthsUpTo ω t :=
    Nat.find_spec hex
  have htT : t ≤ T :=
    Nat.find_min' hex h
  refine ⟨t, htT, ht, ?_, rfl⟩
  intro u hu
  exact Nat.lt_of_not_ge
    (fun hur => Nat.find_min hex hu hur)

private lemma birthsUpTo_eq_threshold_at_first
    (r t x : ℕ) (ω : ℕ → ℕ) (hr : 0 < r)
    (h : ω ∈ firstBirthBlock r t x) :
    birthsUpTo ω t = r := by
  change r ≤ birthsUpTo ω t ∧
    (∀ u < t, birthsUpTo ω u < r) ∧ ω t = x at h
  by_cases ht : t = 0
  · subst t
    simp [birthsUpTo] at h
    omega
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
    have hprev := h.2.1 u (Nat.lt_succ_self u)
    unfold birthsUpTo at hprev h ⊢
    rw [Finset.sum_range_succ] at h ⊢
    split_ifs at h ⊢ <;> omega

lemma measurableSet_birthTailEvent (L : ℕ) :
    MeasurableSet {ω : ℕ → ℕ | L ≤ birthsBeforeExtinction ω} := by
  by_cases hL : L = 0
  · subst L
    simp
  rw [show {ω : ℕ → ℕ | L ≤ birthsBeforeExtinction ω} =
      ⋃ τ : ℕ, {ω | extinctionTime ω = (τ : WithTop ℕ)} ∩
        {ω | L ≤ birthsUpTo ω τ} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      cases hτ : extinctionTime ω with
      | top =>
          simp [birthsBeforeExtinction, hτ] at h
          exact (hL h).elim
      | coe τ =>
          refine ⟨τ, ?_, ?_⟩
          · rfl
          · simpa [birthsBeforeExtinction, hτ] using h
    · rintro ⟨τ, hτ, hbirth⟩
      simpa [birthsBeforeExtinction, hτ] using hbirth]
  exact MeasurableSet.iUnion fun τ =>
    (extinctionTime_measurable
      (measurableSet_singleton (τ : WithTop ℕ))).inter
      (measurable_birthsUpTo τ measurableSet_Ici)

private lemma later_birth_block
    (r L t x : ℕ) (ω : ℕ → ℕ)
    (hr : 0 < r)
    (hblock : ω ∈ firstBirthBlock r t x)
    (htotal : r + L ≤ birthsBeforeExtinction ω) :
    L ≤ birthsBeforeExtinction (pathShift t ω) := by
  cases hτ : extinctionTime ω with
  | top =>
      simp [birthsBeforeExtinction, hτ] at htotal
      omega
  | coe τ =>
      have hrt : birthsUpTo ω t = r :=
        birthsUpTo_eq_threshold_at_first r t x ω hr hblock
      have htτ : t ≤ τ := by
        by_contra hnot
        have hτt : τ < t := Nat.lt_of_not_ge hnot
        have hbefore := hblock.2.1 τ hτt
        have htotal' : r + L ≤ birthsUpTo ω τ := by
          simpa [birthsBeforeExtinction, hτ] using htotal
        omega
      have hshift :=
        extinctionTime_pathShift_eq_sub ω t τ htτ hτ
      have hsplit := birthsUpTo_add_shift ω t (τ - t)
      rw [show t + (τ - t) = τ by omega] at hsplit
      have hfuture :
          birthsBeforeExtinction (pathShift t ω) =
            birthsUpTo (pathShift t ω) (τ - t) := by
        simp [birthsBeforeExtinction, hshift]
      rw [hfuture]
      have htotal' : r + L ≤ birthsUpTo ω τ := by
        simpa [birthsBeforeExtinction, hτ] using htotal
      rw [hrt] at hsplit
      omega

private def zeroAbsorbingPath (ω : ℕ → ℕ) : Prop :=
  ∀ t, ω t = 0 → ω (t + 1) = 0

private lemma zeroAbsorbingPath_of_step
    (ω : ℕ → ℕ) (h : zeroAbsorbingPath ω)
    {s t : ℕ} (hst : s ≤ t) (hs : ω s = 0) :
    ω t = 0 := by
  induction t, hst using Nat.le_induction with
  | base => exact hs
  | succ t hst ih => exact h t ih

private lemma bdPathMeasure_not_zeroAbsorbing
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n : ℕ) :
    bdPathMeasure N n {ω | ¬zeroAbsorbingPath ω} = 0 := by
  rw [show {ω : ℕ → ℕ | ¬zeroAbsorbingPath ω} =
      ⋃ t : ℕ, {ω | ω t = 0 ∧ ω (t + 1) ≠ 0} by
    ext ω
    simp [zeroAbsorbingPath]]
  exact measure_iUnion_null fun t =>
    bdPathMeasure_absorbing_step N n t

private lemma firstBirthBlocks_le_birthTail
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n r : ℕ) (hr : 0 < r)
    (hExt : bdPathMeasure N n
      {ω | extinctionTime ω = ⊤} = 0) :
    bdPathMeasure N n
        (⋃ t, ⋃ x, firstBirthBlock r t x) ≤
      birthTail N n r := by
  let P := bdPathMeasure N n
  let U : Set (ℕ → ℕ) :=
    ⋃ t, ⋃ x, firstBirthBlock r t x
  let E : Set (ℕ → ℕ) :=
    {ω | r ≤ birthsBeforeExtinction ω}
  let Z : Set (ℕ → ℕ) :=
    {ω | ¬zeroAbsorbingPath ω}
  have hsubset :
      U ⊆ E ∪ {ω | extinctionTime ω = ⊤} ∪ Z := by
    intro ω hω
    simp only [U, Set.mem_iUnion] at hω
    obtain ⟨t, x, hblock⟩ := hω
    by_cases htop : extinctionTime ω = ⊤
    · exact Or.inl (Or.inr htop)
    lift extinctionTime ω to ℕ using htop with τ hτ
    by_cases hz : zeroAbsorbingPath ω
    · apply Or.inl
      apply Or.inl
      change r ≤ birthsBeforeExtinction ω
      simp only [birthsBeforeExtinction, ← hτ]
      by_cases htτ : t ≤ τ
      · exact le_trans hblock.1
          (by
            unfold birthsUpTo
            apply Finset.sum_le_sum_of_subset
            exact Finset.range_mono htτ)
      · have hτt : τ < t := Nat.lt_of_not_ge htτ
        have hzero : ω τ = 0 := by
          have hne : extinctionTime ω ≠ ⊤ := by
            rw [← hτ]
            simp
          have hmem := hittingAfter_mem_set_of_ne_top
            (u := natCoord) (s := ({0} : Set ℕ))
            (n := 0) (ω := ω) hne
          have huntop : (extinctionTime ω).untopA = τ := by
            rw [← hτ]
            rfl
          change natCoord (extinctionTime ω).untopA ω ∈
            ({0} : Set ℕ) at hmem
          rw [huntop] at hmem
          simpa [natCoord] using hmem
        have hstay : ∀ u, τ ≤ u → ω u = 0 :=
          fun u hu => zeroAbsorbingPath_of_step ω hz hu hzero
        have hcount : birthsUpTo ω t = birthsUpTo ω τ := by
          have hsplit :=
            birthsUpTo_add_shift ω τ (t - τ)
          rw [show τ + (t - τ) = t by omega] at hsplit
          have htail :
              birthsUpTo (pathShift τ ω) (t - τ) = 0 := by
            unfold birthsUpTo
            apply Finset.sum_eq_zero
            intro i hi
            rw [if_neg]
            simp only [pathShift]
            rw [hstay (τ + i) (by omega),
              hstay (τ + (i + 1)) (by omega)]
            omega
          omega
        rw [← hcount]
        exact hblock.1
    · exact Or.inr hz
  calc
    P U ≤ P (E ∪ {ω | extinctionTime ω = ⊤} ∪ Z) :=
      measure_mono hsubset
    _ ≤ P E + P {ω | extinctionTime ω = ⊤} + P Z := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ = P E := by
      rw [hExt, bdPathMeasure_not_zeroAbsorbing N n]
      simp
    _ = birthTail N n r := rfl

/-- Strong-Markov restart inequality for birth-count tails.  Reaching
`r + L` births requires first reaching `r`, then producing another `L` from a
state no larger than `n + r`. -/
private lemma birthTail_add_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n r L : ℕ) (hr : 0 < r) (q : ℝ≥0∞)
    (hExt : ∀ x, bdPathMeasure N x
      {ω | extinctionTime ω = ⊤} = 0)
    (hfresh : ∀ x, x ≤ n + r → birthTail N x L ≤ q) :
    birthTail N n (r + L) ≤ q * birthTail N n r := by
  let P := bdPathMeasure N n
  let B : ℕ → ℕ → Set (ℕ → ℕ) :=
    fun t x => firstBirthBlock r t x
  let C : ℕ → ℕ → Set (ℕ → ℕ) :=
    fun _t x =>
      if x ≤ n + r then
        {η | L ≤ birthsBeforeExtinction η}
      else
        ∅
  let R : Set (ℕ → ℕ) :=
    ⋃ t, ⋃ x, B t x ∩ (pathShift t) ⁻¹' C t x
  have hBmeas : ∀ t x, MeasurableSet (B t x) :=
    fun t x => measurableSet_firstBirthBlock r t x
  have hCmeas : ∀ t x, MeasurableSet (C t x) := by
    intro t x
    by_cases hx : x ≤ n + r
    · simp only [C, if_pos hx]
      exact measurableSet_birthTailEvent L
    · simp [C, hx]
  have hBcyl : ∀ t x, isCylinderUpTo t (B t x) :=
    fun t x => firstBirthBlock_cylinder r t x
  have hbound :
      ∀ t x (ω : ℕ → ℕ), ω ∈ B t x →
        homogeneousPathMeasure (Measure.dirac (ω t))
            (bdKernel N) (C t x) ≤ q := by
    intro t x ω hω
    by_cases hx : x ≤ n + r
    · simp only [C, if_pos hx]
      change birthTail N (ω t) L ≤ q
      rw [hω.2.2]
      exact hfresh x hx
    · simp [C, hx]
  have hmarkov :
      P R ≤
        ∑' t, ∑' x, q * P (B t x) := by
    exact homogeneousPathMeasure_markov_bound_countable
      (bdKernel N) n B C (fun _ _ => q)
      hBmeas hCmeas hBcyl hbound
  have htotal_subset :
      {ω | r + L ≤ birthsBeforeExtinction ω} ⊆
        {ω | ω 0 ≠ n} ∪
          {ω | ¬validBdPath ω} ∪ R := by
    intro ω htotal
    by_cases h0 : ω 0 = n
    · by_cases hv : validBdPath ω
      · cases hτ : extinctionTime ω with
        | top =>
            simp [birthsBeforeExtinction, hτ] at htotal
            omega
        | coe τ =>
            have hrτ : r ≤ birthsUpTo ω τ := by
              have : r + L ≤ birthsUpTo ω τ := by
                simpa [birthsBeforeExtinction, hτ] using htotal
              omega
            obtain ⟨t, htτ, hblock⟩ :=
              exists_firstBirthBlock r τ ω hrτ
            have hcount :
                birthsUpTo ω t = r :=
              birthsUpTo_eq_threshold_at_first r t (ω t)
                ω hr hblock
            have hstate : ω t ≤ n + r := by
              have hs :=
                state_le_initial_add_births n t ω h0 hv
              omega
            apply Or.inr
            simp only [R, Set.mem_iUnion, Set.mem_inter_iff,
              Set.mem_preimage]
            refine ⟨t, ω t, hblock, ?_⟩
            simp only [C, if_pos hstate]
            exact later_birth_block r L t (ω t) ω hr
              hblock htotal
      · exact Or.inl (Or.inr hv)
    · exact Or.inl (Or.inl h0)
  have hsum_eq :
      (∑' t, ∑' x, P (B t x)) =
        P (⋃ t, ⋃ x, B t x) := by
    rw [← ENNReal.tsum_prod]
    rw [← MeasureTheory.measure_iUnion
      (firstBirthBlock_pairwise r)
      (fun z => hBmeas z.1 z.2)]
    congr 1
    ext ω
    simp only [B, Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z.1, z.2, hz⟩
    · rintro ⟨t, x, hx⟩
      exact ⟨(t, x), hx⟩
  calc
    birthTail N n (r + L)
        ≤ P ({ω | ω 0 ≠ n} ∪
          {ω | ¬validBdPath ω} ∪ R) :=
      measure_mono htotal_subset
    _ ≤ P {ω | ω 0 ≠ n} +
          P {ω | ¬validBdPath ω} + P R := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ = P R := by
      rw [bdPathMeasure_initial_ne N n,
        bdPathMeasure_invalid_path N n]
      simp
    _ ≤ ∑' t, ∑' x, q * P (B t x) := hmarkov
    _ = q * (∑' t, ∑' x, P (B t x)) := by
      simp_rw [ENNReal.tsum_mul_left]
    _ = q * P (⋃ t, ⋃ x, B t x) := by
      rw [hsum_eq]
    _ ≤ q * birthTail N n r := by
      exact mul_le_mul_left'
        (firstBirthBlocks_le_birthTail N n r hr
          (hExt n)) q

lemma measurable_birthsBeforeExtinction :
    Measurable (fun ω : ℕ → ℕ => birthsBeforeExtinction ω) := by
  apply measurable_of_Ici
  intro L
  exact measurableSet_birthTailEvent L

private lemma birthTail_le_expected_div
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n L : ℕ) (hL : 0 < L) :
    birthTail N n L ≤
      expectedBirthsBeforeExtinction N n / (L : ℝ≥0∞) := by
  unfold birthTail expectedBirthsBeforeExtinction
  have hevent :
      {ω : ℕ → ℕ | L ≤ birthsBeforeExtinction ω} =
        {ω | (L : ℝ≥0∞) ≤
          (birthsBeforeExtinction ω : ℝ≥0∞)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    norm_cast
  rw [hevent]
  simpa only [Function.comp_apply] using
    (meas_ge_le_lintegral_div
      (μ := bdPathMeasure N n)
      ((measurable_of_countable
        (fun m : ℕ => (m : ℝ≥0∞))).comp
          measurable_birthsBeforeExtinction).aemeasurable
      (by exact_mod_cast (Nat.ne_of_gt hL))
      (ENNReal.natCast_ne_top L))

private lemma birthTail_le_half
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n L : ℕ) (hL : 0 < L)
    (hmean :
      expectedBirthsBeforeExtinction N n ≤
        (L : ℝ≥0∞) / 2) :
    birthTail N n L ≤ (2 : ℝ≥0∞)⁻¹ := by
  calc
    birthTail N n L
        ≤ expectedBirthsBeforeExtinction N n /
            (L : ℝ≥0∞) :=
      birthTail_le_expected_div N n L hL
    _ ≤ ((L : ℝ≥0∞) / 2) / (L : ℝ≥0∞) :=
      ENNReal.div_le_div_right hmean (L : ℝ≥0∞)
    _ ≤ (2 : ℝ≥0∞)⁻¹ := by
      apply (ENNReal.div_le_iff_le_mul
        (Or.inl (by exact_mod_cast (Nat.ne_of_gt hL)))
        (Or.inl (ENNReal.natCast_ne_top L))).2
      rw [ENNReal.div_eq_inv_mul]

/-- Iterating the restart inequality gives a geometric bound in the number
of birth blocks. -/
private lemma birthTail_blocks_le_pow
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n L K : ℕ) (hL : 0 < L) (q : ℝ≥0∞)
    (hExt : ∀ x, bdPathMeasure N x
      {ω | extinctionTime ω = ⊤} = 0)
    (hfresh : ∀ x, x ≤ n + K * L →
      birthTail N x L ≤ q) :
    birthTail N n (K * L) ≤ q ^ K := by
  haveI : IsProbabilityMeasure (bdPathMeasure N n) := by
    unfold bdPathMeasure homogeneousPathMeasure
    infer_instance
  induction K with
  | zero =>
      simp only [Nat.zero_mul, pow_zero]
      unfold birthTail
      change bdPathMeasure N n
        {ω | 0 ≤ birthsBeforeExtinction ω} ≤ 1
      rw [show {ω : ℕ → ℕ |
          0 ≤ birthsBeforeExtinction ω} = Set.univ by
        ext ω
        simp]
      simp
  | succ K ih =>
      rcases K with _ | K
      · simpa using hfresh n (by omega)
      · have hprev :
            birthTail N n ((K + 1) * L) ≤
              q ^ (K + 1) := by
          apply ih
          intro x hx
          apply hfresh x
          exact hx.trans
            (Nat.add_le_add_left
              (Nat.mul_le_mul_right L (by omega)) n)
        calc
          birthTail N n ((K + 2) * L)
              = birthTail N n ((K + 1) * L + L) := by
                  congr 2
                  simp [Nat.add_mul, two_mul, Nat.add_assoc]
          _ ≤ q * birthTail N n ((K + 1) * L) := by
            apply birthTail_add_le N n ((K + 1) * L) L
              (by positivity) q hExt
            intro x hx
            apply hfresh x
            exact hx.trans
              (Nat.add_le_add_left
                (Nat.mul_le_mul_right L (by omega)) n)
          _ ≤ q * q ^ (K + 1) :=
            mul_le_mul_left' hprev q
          _ = q ^ (K + 2) := by
            simp [pow_succ, mul_comm]

private lemma logScale_nonneg (n : ℕ) :
    0 ≤ logScale n := by
  unfold logScale
  exact Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n + 1 by omega))

private lemma logScale_le_logScaleNat (n : ℕ) :
    logScale n ≤ (logScaleNat n : ℝ) := by
  unfold logScaleNat
  have hnonneg : 0 ≤ Int.ceil (logScale n) :=
    Int.ceil_nonneg (logScale_nonneg n)
  calc
    logScale n ≤ (Int.ceil (logScale n) : ℝ) :=
      Int.le_ceil _
    _ = (Int.toNat (Int.ceil (logScale n)) : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm

private lemma logSqScaleNat_le_sq (n : ℕ) :
    logSqScaleNat n ≤ n ^ 2 := by
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hlog_le : logScale n ≤ n := by
    unfold logScale
    have h := Real.log_le_sub_one_of_pos hnpos
    norm_num at h ⊢
    linarith
  have hsq :
      logSqScale n ≤ (n ^ 2 : ℕ) := by
    unfold logSqScale
    rw [show ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 by
      norm_num]
    have hnnonneg : (0 : ℝ) ≤ n := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog_le)
      (add_nonneg hnnonneg (logScale_nonneg n))]
  unfold logSqScaleNat
  have hceil :
      Int.ceil (logSqScale n) ≤ (n ^ 2 : ℤ) := by
    rw [Int.ceil_le]
    exact_mod_cast hsq
  have hceil_nonneg : 0 ≤ Int.ceil (logSqScale n) :=
    Int.ceil_nonneg (by
      unfold logSqScale
      positivity)
  exact_mod_cast
    (show Int.toNat (Int.ceil (logSqScale n)) ≤ n ^ 2 by
      rw [Int.toNat_le]
      exact_mod_cast hceil)

private lemma one_lt_logScale (n : ℕ) (hn : 2 ≤ n) :
    1 < logScale n := by
  unfold logScale
  have hthree : (3 : ℝ) ≤ n + 1 := by
    exact_mod_cast (show 3 ≤ n + 1 by omega)
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2
      Real.exp_one_lt_three
  exact hlog3.trans_le
    (Real.log_le_log (by norm_num) hthree)

private lemma logScaleNat_sq_le_logSq (n : ℕ) (hn : 2 ≤ n) :
    logScaleNat n ^ 2 ≤ 4 * logSqScaleNat n := by
  have hlog : 1 ≤ logScale n :=
    (one_lt_logScale n hn).le
  have hceil_upper :
      (logScaleNat n : ℝ) ≤ logScale n + 1 := by
    unfold logScaleNat
    have hnonneg : 0 ≤ Int.ceil (logScale n) :=
      Int.ceil_nonneg (logScale_nonneg n)
    rw [show (Int.toNat (Int.ceil (logScale n)) : ℝ) =
        (Int.ceil (logScale n) : ℝ) by
      exact_mod_cast (Int.toNat_of_nonneg hnonneg)]
    exact_mod_cast Int.ceil_lt_add_one (logScale n) |>.le
  have hs_le : (logScaleNat n : ℝ) ≤ 2 * logScale n := by
    linarith
  have hsq_le :
      ((logScaleNat n : ℝ) ^ 2) ≤
        4 * logSqScaleNat n := by
    have hlogsq :
        logScale n ^ 2 ≤ (logSqScaleNat n : ℝ) := by
      unfold logSqScaleNat logSqScale
      have hnonneg : 0 ≤ Int.ceil (logScale n ^ 2) :=
        Int.ceil_nonneg (sq_nonneg _)
      calc
        logScale n ^ 2 ≤
            (Int.ceil (logScale n ^ 2) : ℝ) :=
          Int.le_ceil _
        _ = (Int.toNat
              (Int.ceil (logScale n ^ 2)) : ℝ) := by
          exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm
    nlinarith [sq_nonneg
      ((logScaleNat n : ℝ) - 2 * logScale n)]
  exact_mod_cast hsq_le

private lemma log_state_le_three
    (n C₀ x : ℕ) (hn : 2 ≤ n) (hC₀ : C₀ ≤ n)
    (hx : x ≤ n + C₀ * logSqScaleNat n) :
    Real.log x ≤ 3 * logScale n := by
  have hM := logSqScaleNat_le_sq n
  have hx₁ : x ≤ n + C₀ * n ^ 2 :=
    hx.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left C₀ hM) n)
  have hx₂ : x ≤ n + n * n ^ 2 :=
    hx₁.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (n ^ 2) hC₀) n)
  have hcube : x ≤ (n + 1) ^ 3 := by
    exact hx₂.trans (by nlinarith [Nat.zero_le n])
  rcases x.eq_zero_or_pos with rfl | hxpos
  · rw [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by norm_num) (logScale_nonneg n)
  · calc
      Real.log x ≤ Real.log ((n + 1) ^ 3) :=
        Real.log_le_log
          (by exact_mod_cast hxpos)
          (by exact_mod_cast hcube)
      _ = 3 * logScale n := by
        unfold logScale
        rw [Real.log_pow]
        norm_num

private lemma expected_le_half_block
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (hp : ∀ m, 0 < m → N.p m ≤ C / (m : ℝ))
    (hq : ∀ m, 0 < m → D ≤ N.q m)
    (A : ℝ≥0∞) (hA : A ≠ ⊤)
    (hmean : ∀ x,
      expectedBirthsBeforeExtinction N x ≤
        A * ENNReal.ofReal
          ((C / D) * (Real.log x + 1)))
    (Q n C₀ x : ℕ)
    (hQ : 8 * A.toReal * (C / D) ≤ Q)
    (hn : 2 ≤ n) (hC₀ : C₀ ≤ n)
    (hx : x ≤ n + C₀ * logSqScaleNat n) :
    expectedBirthsBeforeExtinction N x ≤
      (Q * logScaleNat n : ℕ) / (2 : ℝ≥0∞) := by
  have hCD : 0 < C / D := div_pos hC hD
  have hlogx := log_state_le_three n C₀ x hn hC₀ hx
  have hlogn : 1 ≤ logScale n :=
    (one_lt_logScale n hn).le
  have harg_nonneg :
      0 ≤ (C / D) * (Real.log x + 1) := by
    have hlogx_nonneg : 0 ≤ Real.log x := by
      rcases x.eq_zero_or_pos with rfl | hxpos
      · simp
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ x by omega))
    positivity
  have hRhsNe :
      A * ENNReal.ofReal
        ((C / D) * (Real.log x + 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top hA ENNReal.ofReal_ne_top
  have hENe :
      expectedBirthsBeforeExtinction N x ≠ ⊤ :=
    ne_top_of_le_ne_top hRhsNe (hmean x)
  have hblockNe :
      ((Q * logScaleNat n : ℕ) : ℝ≥0∞) /
          (2 : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.div_ne_top
      (ENNReal.natCast_ne_top _) (by norm_num)
  rw [← ENNReal.toReal_le_toReal hENe hblockNe]
  have hreal := ENNReal.toReal_mono hRhsNe (hmean x)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal harg_nonneg] at hreal
  rw [ENNReal.toReal_div]
  norm_num
  norm_num at hreal
  have hS := logScale_le_logScaleNat n
  have hQreal : 8 * A.toReal * (C / D) ≤ (Q : ℝ) := by
    exact_mod_cast hQ
  norm_num
  nlinarith [mul_nonneg
    (show 0 ≤ A.toReal by positivity)
    (show 0 ≤ C / D by positivity)]

private lemma real_pow_eq_exp_mul_log
    (x : ℝ) (hx : 0 < x) (m : ℕ) :
    x ^ m = Real.exp ((m : ℝ) * Real.log x) := by
  conv_lhs => rw [(Real.exp_log hx).symm]
  exact (Real.exp_nat_mul (Real.log x) m).symm

private lemma half_pow_logScale_le_poly
    (n k : ℕ) :
    ((2 : ℝ≥0∞)⁻¹) ^
        (2 * k * logScaleNat n) ≤
      ((n + 1 : ℝ≥0∞) ^ k)⁻¹ := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith)
  have htwolog : (1 : ℝ) ≤ 2 * Real.log 2 := by
    linarith
  have hS : logScale n ≤ (logScaleNat n : ℝ) :=
    logScale_le_logScaleNat n
  have hk : (0 : ℝ) ≤ k := by positivity
  have hlog_nonneg := logScale_nonneg n
  have hkS :
      (k : ℝ) * logScale n ≤
        (k : ℝ) * logScaleNat n :=
    mul_le_mul_of_nonneg_left hS hk
  have hscale_nonneg :
      0 ≤ (k : ℝ) * logScaleNat n := by positivity
  have htwice :
      (k : ℝ) * logScaleNat n ≤
        (2 * Real.log 2) *
          ((k : ℝ) * logScaleNat n) :=
    by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right htwolog hscale_nonneg)
  have hexponent :
      ((2 * k * logScaleNat n : ℕ) : ℝ) *
          Real.log (1 / 2) ≤
        -(k : ℝ) * logScale n := by
    have hloghalf :
        Real.log (1 / 2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hloghalf]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hreal :
      (1 / 2 : ℝ) ^ (2 * k * logScaleNat n) ≤
        1 / ((n + 1 : ℝ) ^ k) := by
    rw [real_pow_eq_exp_mul_log (1 / 2) (by positivity)]
    rw [show 1 / ((n + 1 : ℝ) ^ k) =
        Real.exp (-(k : ℝ) * logScale n) by
      unfold logScale
      rw [show -(k : ℝ) * Real.log ((n : ℝ) + 1) =
          -((k : ℝ) * Real.log ((n : ℝ) + 1)) by ring,
        Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
      simp [one_div]]
    exact Real.exp_le_exp.mpr hexponent
  rw [show (2 : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (1 / 2 : ℝ) by
    calc
      (2 : ℝ≥0∞)⁻¹ =
          (ENNReal.ofReal (2 : ℝ))⁻¹ := by norm_num
      _ = ENNReal.ofReal (2 : ℝ)⁻¹ :=
        (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by norm_num]
  rw [← ENNReal.ofReal_pow (by positivity)]
  rw [show ((n + 1 : ℝ≥0∞) ^ k)⁻¹ =
      ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ k)) by
    calc
      ((n + 1 : ℝ≥0∞) ^ k)⁻¹ =
          (ENNReal.ofReal ((n + 1 : ℝ)) ^ k)⁻¹ := by
            rw [show (n + 1 : ℝ) =
                ((n + 1 : ℕ) : ℝ) by norm_num,
              ENNReal.ofReal_natCast]
            norm_num
      _ = (ENNReal.ofReal ((n + 1 : ℝ) ^ k))⁻¹ := by
            rw [ENNReal.ofReal_pow (by positivity)]
      _ = ENNReal.ofReal (((n + 1 : ℝ) ^ k)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos
          (pow_pos (by positivity : (0 : ℝ) < n + 1) k)).symm
      _ = ENNReal.ofReal
          (1 / ((n + 1 : ℝ) ^ k)) := by
            rw [one_div]]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Uniform form of the corrected block/restart proof: the same threshold
works for every initial state `x ≤ n`. -/
theorem nice_whp_births_logsq_uniform_unconditional
    (N : NiceChain)
    [IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    ∀ k : ℕ, ∃ C n₀ : ℕ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ x : ℕ, x ≤ n →
        birthTail N.toBirthDeathChain x (C * logSqScaleNat n) ≤
          ((n + 1 : ℝ≥0∞) ^ k)⁻¹ := by
  let bd := N.toBirthDeathChain
  obtain ⟨A, hA, hmean⟩ :=
    expectedBirthsBeforeExtinction_ennreal_le
      bd N.C N.D N.C_pos N.D_pos N.p_le N.q_ge
  let B : ℝ :=
    8 * A.toReal * (N.C / N.D)
  let Q : ℕ := Nat.ceil B + 1
  have hQpos : 0 < Q := by
    simp [Q]
  have hQbound :
      8 * A.toReal * (N.C / N.D) ≤ (Q : ℝ) := by
    change B ≤ (Q : ℝ)
    calc
      B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
      _ ≤ (Q : ℝ) := by
        exact_mod_cast
          (show Nat.ceil B ≤ Q by simp [Q])
  obtain ⟨nDrift, hDrift⟩ := nice_drift_neg N
  have hExt :
      ∀ x, bdPathMeasure bd x
        {ω | extinctionTime ω = ⊤} = 0 := by
    intro x
    have hDrift' :
        ∀ m, nDrift ≤ m → 0 < m →
          bd.p m - bd.q m ≤ -(N.D / 2) := by
      intro m hm hmp
      have h := hDrift m hm hmp
      linarith
    exact bd_extinction_almost_sure bd
      (N.D / 2) (half_pos N.D_pos) nDrift
      hDrift' N.D N.D_pos N.q_ge x
  intro k
  let C₀ : ℕ := 8 * (k + 1) * Q
  refine ⟨C₀, max 2 C₀, ?_, ?_⟩
  · dsimp [C₀]
    positivity
  intro n hn
  intro x hx
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hC₀n : C₀ ≤ n :=
    le_trans (le_max_right _ _) hn
  let S := logScaleNat n
  let M := logSqScaleNat n
  let L := Q * S
  let K := 2 * k * S
  have hSpos : 0 < S := by
    have hsreal :
        (1 : ℝ) < (S : ℝ) :=
      (one_lt_logScale n hn2).trans_le
        (by simpa only [S] using
          logScale_le_logScaleNat n)
    by_contra h
    have hzero : S = 0 := Nat.eq_zero_of_not_pos h
    rw [hzero] at hsreal
    norm_num at hsreal
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.mul_pos hQpos hSpos
  have hscale :
      S ^ 2 ≤ 4 * M := by
    simpa only [S, M] using
      logScaleNat_sq_le_logSq n hn2
  have hthreshold :
      K * L ≤ C₀ * M := by
    calc
      K * L = (2 * k * Q) * S ^ 2 := by
        simp only [K, L]
        ring
      _ ≤ (2 * k * Q) * (4 * M) :=
        Nat.mul_le_mul_left _ hscale
      _ = 8 * k * Q * M := by ring
      _ ≤ 8 * (k + 1) * Q * M := by
        gcongr
        omega
      _ = C₀ * M := by
        simp only [C₀]
  have hfresh :
      ∀ x, x ≤ n + K * L →
        birthTail bd x L ≤ (2 : ℝ≥0∞)⁻¹ := by
    intro x hx
    have hx' :
        x ≤ n + C₀ * logSqScaleNat n := by
      exact hx.trans
        (Nat.add_le_add_left
          (by simpa only [M] using hthreshold) n)
    apply birthTail_le_half bd x L hLpos
    exact expected_le_half_block
      bd N.C N.D N.C_pos N.D_pos N.p_le N.q_ge
      A hA hmean Q n C₀ x hQbound hn2 hC₀n hx'
  calc
    birthTail bd x (C₀ * logSqScaleNat n)
        ≤ birthTail bd x (K * L) := by
      unfold birthTail
      apply measure_mono
      intro ω hω
      exact hthreshold.trans hω
    _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ K :=
      birthTail_blocks_le_pow bd x L K hLpos
        (2 : ℝ≥0∞)⁻¹ hExt (fun y hy =>
          hfresh y (hy.trans (Nat.add_le_add_right hx _)))
    _ ≤ ((n + 1 : ℝ≥0∞) ^ k)⁻¹ := by
      simpa only [K, S] using
        half_pow_logScale_le_poly n k

/-- Corrected block/restart proof of paper `lemma:nice-whp-births`. -/
theorem nice_whp_births_logsq_unconditional
    (N : NiceChain)
    [IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    WhpTailBound
      (fun n t =>
        birthTail N.toBirthDeathChain n t)
      logSqScaleNat := by
  intro k
  obtain ⟨C, n₀, hC, h⟩ :=
    nice_whp_births_logsq_uniform_unconditional N k
  exact ⟨C, n₀, hC, fun n hn => h n hn n le_rfl⟩

end LVConsensus
