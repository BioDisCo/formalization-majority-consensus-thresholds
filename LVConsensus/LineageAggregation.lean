import LVConsensus.NsdIntra
import LVConsensus.KernelPathMap

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LVConsensus

/-- Aggregate lineage counts according to whether the initial lineage index is
strictly smaller than `a`. -/
def lineageAggregate (a : Nat) {n : Nat} (L : LinState n) : PopState :=
  (∑ i : Lineage n, if (i : Nat) < a then L i else 0,
    ∑ i : Lineage n, if a ≤ (i : Nat) then L i else 0)

private lemma sum_update_univ
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Nat) (i : α) (v : Nat) :
    (∑ x, Function.update f i v x) =
      v + ∑ x ∈ (Finset.univ.erase i), f x := by
  simpa only [Finset.sdiff_singleton_eq_erase] using
    Finset.sum_update_of_mem (Finset.mem_univ i) f v

private lemma sum_update_add_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Nat) (i : α) :
    (∑ x, Function.update f i (f i + 1) x) = (∑ x, f x) + 1 := by
  rw [sum_update_univ]
  have h := Finset.sum_erase_add (Finset.univ : Finset α) f (Finset.mem_univ i)
  omega

private lemma sum_update_sub_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Nat) (i : α) (hi : 0 < f i) :
    (∑ x, Function.update f i (f i - 1) x) = (∑ x, f x) - 1 := by
  rw [sum_update_univ]
  have h := Finset.sum_erase_add (Finset.univ : Finset α) f (Finset.mem_univ i)
  omega

lemma lineageAggregate_birth
    (a : Nat) {n : Nat} (L : LinState n) (i : Lineage n) :
    lineageAggregate a (lineageBirth L i) =
      if (i : Nat) < a then
        ((lineageAggregate a L).1 + 1, (lineageAggregate a L).2)
      else
        ((lineageAggregate a L).1, (lineageAggregate a L).2 + 1) := by
  classical
  by_cases hi : (i : Nat) < a
  · simp only [hi, if_pos]
    apply Prod.ext
    · change
        (∑ x : Lineage n,
          if (x : Nat) < a then Function.update L i (L i + 1) x else 0) =
          (∑ x : Lineage n, if (x : Nat) < a then L x else 0) + 1
      have hfun :
          (fun x : Lineage n =>
            if (x : Nat) < a then Function.update L i (L i + 1) x else 0) =
            Function.update
              (fun x : Lineage n => if (x : Nat) < a then L x else 0)
              i (L i + 1) := by
        funext x
        by_cases hxi : x = i
        · subst x
          simp [hi]
        · simp [hxi]
      rw [hfun]
      simpa [hi] using
        sum_update_add_one
          (fun x : Lineage n => if (x : Nat) < a then L x else 0) i
    · change
        (∑ x : Lineage n,
          if a ≤ (x : Nat) then Function.update L i (L i + 1) x else 0) =
          ∑ x : Lineage n, if a ≤ (x : Nat) then L x else 0
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxi : x = i
      · subst x
        have hnot : ¬a ≤ (i : Nat) := Nat.not_le_of_gt hi
        simp [hnot]
      · simp [hxi]
  · have hai : a ≤ (i : Nat) := Nat.le_of_not_gt hi
    simp only [hi, if_false]
    apply Prod.ext
    · change
        (∑ x : Lineage n,
          if (x : Nat) < a then Function.update L i (L i + 1) x else 0) =
          ∑ x : Lineage n, if (x : Nat) < a then L x else 0
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxi : x = i
      · subst x
        simp [hi]
      · simp [hxi]
    · change
        (∑ x : Lineage n,
          if a ≤ (x : Nat) then Function.update L i (L i + 1) x else 0) =
          (∑ x : Lineage n, if a ≤ (x : Nat) then L x else 0) + 1
      have hfun :
          (fun x : Lineage n =>
            if a ≤ (x : Nat) then Function.update L i (L i + 1) x else 0) =
            Function.update
              (fun x : Lineage n => if a ≤ (x : Nat) then L x else 0)
              i (L i + 1) := by
        funext x
        by_cases hxi : x = i
        · subst x
          simp [hai]
        · simp [hxi]
      rw [hfun]
      simpa [hai] using
        sum_update_add_one
          (fun x : Lineage n => if a ≤ (x : Nat) then L x else 0) i

lemma lineageAggregate_death
    (a : Nat) {n : Nat} (L : LinState n) (i : Lineage n)
    (hiPos : 0 < L i) :
    lineageAggregate a (lineageDeath L i) =
      if (i : Nat) < a then
        ((lineageAggregate a L).1 - 1, (lineageAggregate a L).2)
      else
        ((lineageAggregate a L).1, (lineageAggregate a L).2 - 1) := by
  classical
  by_cases hi : (i : Nat) < a
  · simp only [hi, if_pos]
    apply Prod.ext
    · change
        (∑ x : Lineage n,
          if (x : Nat) < a then Function.update L i (L i - 1) x else 0) =
          (∑ x : Lineage n, if (x : Nat) < a then L x else 0) - 1
      have hfun :
          (fun x : Lineage n =>
            if (x : Nat) < a then Function.update L i (L i - 1) x else 0) =
            Function.update
              (fun x : Lineage n => if (x : Nat) < a then L x else 0)
              i (L i - 1) := by
        funext x
        by_cases hxi : x = i
        · subst x
          simp [hi]
        · simp [hxi]
      rw [hfun]
      simpa [hi] using
        sum_update_sub_one
          (fun x : Lineage n => if (x : Nat) < a then L x else 0)
          i (by simpa [hi])
    · change
        (∑ x : Lineage n,
          if a ≤ (x : Nat) then Function.update L i (L i - 1) x else 0) =
          ∑ x : Lineage n, if a ≤ (x : Nat) then L x else 0
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxi : x = i
      · subst x
        have hnot : ¬a ≤ (i : Nat) := Nat.not_le_of_gt hi
        simp [hnot]
      · simp [hxi]
  · have hai : a ≤ (i : Nat) := Nat.le_of_not_gt hi
    simp only [hi, if_false]
    apply Prod.ext
    · change
        (∑ x : Lineage n,
          if (x : Nat) < a then Function.update L i (L i - 1) x else 0) =
          ∑ x : Lineage n, if (x : Nat) < a then L x else 0
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxi : x = i
      · subst x
        simp [hi]
      · simp [hxi]
    · change
        (∑ x : Lineage n,
          if a ≤ (x : Nat) then Function.update L i (L i - 1) x else 0) =
          (∑ x : Lineage n, if a ≤ (x : Nat) then L x else 0) - 1
      have hfun :
          (fun x : Lineage n =>
            if a ≤ (x : Nat) then Function.update L i (L i - 1) x else 0) =
            Function.update
              (fun x : Lineage n => if a ≤ (x : Nat) then L x else 0)
              i (L i - 1) := by
        funext x
        by_cases hxi : x = i
        · subst x
          simp [hai]
        · simp [hxi]
      rw [hfun]
      simpa [hai] using
        sum_update_sub_one
          (fun x : Lineage n => if a ≤ (x : Nat) then L x else 0)
          i (by simpa [hai])

lemma lineageTotal_eq_aggregate_total
    (a : Nat) {n : Nat} (L : LinState n) :
    lineageTotal L = (lineageAggregate a L).1 + (lineageAggregate a L).2 := by
  classical
  simp only [lineageTotal, lineageAggregate, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Nat) < a
  · simp [hi, Nat.not_le_of_gt hi]
  · simp [hi, Nat.le_of_not_gt hi]

lemma lineageBirthMass_sum_species0
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    (∑ i : Lineage n,
        if (i : Nat) < a then lineageBirthMass params L i else 0) =
      ENNReal.ofReal (params.beta * (lineageAggregate a L).1) := by
  classical
  rw [show
      (∑ i : Lineage n,
          if (i : Nat) < a then lineageBirthMass params L i else 0) =
        ∑ i : Lineage n,
          ENNReal.ofReal
            (if (i : Nat) < a then params.beta * L i else 0) by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : Nat) < a <;>
        simp [lineageBirthMass, hi]]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    simp only [lineageAggregate]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Nat) < a <;> simp [hi]
  · intro i _
    split_ifs
    · exact mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    · simp

lemma lineageBirthMass_sum_species1
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    (∑ i : Lineage n,
        if a ≤ (i : Nat) then lineageBirthMass params L i else 0) =
      ENNReal.ofReal (params.beta * (lineageAggregate a L).2) := by
  classical
  rw [show
      (∑ i : Lineage n,
          if a ≤ (i : Nat) then lineageBirthMass params L i else 0) =
        ∑ i : Lineage n,
          ENNReal.ofReal
            (if a ≤ (i : Nat) then params.beta * L i else 0) by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a ≤ (i : Nat) <;>
        simp [lineageBirthMass, hi]]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    simp only [lineageAggregate]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a ≤ (i : Nat) <;> simp [hi]
  · intro i _
    split_ifs
    · exact mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    · simp

lemma lineageDeathMass_sum_species0
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    (∑ i : Lineage n,
        if (i : Nat) < a then lineageDeathMass params L i else 0) =
      ENNReal.ofReal
        ((params.delta +
            params.alpha0 * (lineageTotal L - 1 : Nat)) *
          (lineageAggregate a L).1) := by
  classical
  rw [show
      (∑ i : Lineage n,
          if (i : Nat) < a then lineageDeathMass params L i else 0) =
        ∑ i : Lineage n,
          ENNReal.ofReal
            (if (i : Nat) < a then
              (params.delta +
                  params.alpha0 * (lineageTotal L - 1 : Nat)) * L i
            else 0) by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (i : Nat) < a <;>
        simp [lineageDeathMass, hi]]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    simp only [lineageAggregate]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : Nat) < a <;> simp [hi]
  · intro i _
    split_ifs
    · exact mul_nonneg
        (add_nonneg params.delta_nonneg
          (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _)))
        (Nat.cast_nonneg _)
    · simp

lemma lineageDeathMass_sum_species1
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    (∑ i : Lineage n,
        if a ≤ (i : Nat) then lineageDeathMass params L i else 0) =
      ENNReal.ofReal
        ((params.delta +
            params.alpha0 * (lineageTotal L - 1 : Nat)) *
          (lineageAggregate a L).2) := by
  classical
  rw [show
      (∑ i : Lineage n,
          if a ≤ (i : Nat) then lineageDeathMass params L i else 0) =
        ∑ i : Lineage n,
          ENNReal.ofReal
            (if a ≤ (i : Nat) then
              (params.delta +
                  params.alpha0 * (lineageTotal L - 1 : Nat)) * L i
            else 0) by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : a ≤ (i : Nat) <;>
        simp [lineageDeathMass, hi]]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    simp only [lineageAggregate]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a ≤ (i : Nat) <;> simp [hi]
  · intro i _
    split_ifs
    · exact mul_nonneg
        (add_nonneg params.delta_nonneg
          (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _)))
        (Nat.cast_nonneg _)
    · simp

lemma initialLineages_aggregate (a b : Nat) :
    lineageAggregate a (initialLineages (a + b)) = (a, b) := by
  classical
  apply Prod.ext <;>
    simp only [lineageAggregate, initialLineages]
  · rw [show
      (∑ i : Lineage (a + b), if (i : Nat) < a then 1 else 0) =
        ((Finset.univ.filter fun i : Lineage (a + b) => (i : Nat) < a).card) by
      simp]
    simpa [Nat.min_eq_left (Nat.le_add_right a b)] using
      (Fin.card_filter_val_lt (n := a + b) (m := a))
  · rw [show
      (∑ i : Lineage (a + b), if a ≤ (i : Nat) then 1 else 0) =
        ((Finset.univ.filter fun i : Lineage (a + b) => a ≤ (i : Nat)).card) by
      simp]
    have hpartition :
        (Finset.univ.filter fun i : Lineage (a + b) => (i : Nat) < a).card +
          (Finset.univ.filter fun i : Lineage (a + b) => a ≤ (i : Nat)).card =
            a + b := by
      let A := Finset.univ.filter fun i : Lineage (a + b) => (i : Nat) < a
      let B := Finset.univ.filter fun i : Lineage (a + b) => a ≤ (i : Nat)
      have hdis : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro i hiA hiB
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hiA
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hiB
        omega
      have hunion : A ∪ B = Finset.univ := by
        ext i
        simp [A, B]
        omega
      change A.card + B.card = a + b
      calc
        A.card + B.card = (A ∪ B).card :=
          (Finset.card_union_of_disjoint hdis).symm
        _ = a + b := by simp [hunion]
    have hfirst :
        (Finset.univ.filter fun i : Lineage (a + b) => (i : Nat) < a).card = a := by
      simpa [Nat.min_eq_left (Nat.le_add_right a b)] using
        (Fin.card_filter_val_lt (n := a + b) (m := a))
    omega

private lemma lineageAggregate_measurable (a : Nat) {n : Nat} :
    Measurable (lineageAggregate a : LinState n → PopState) :=
  measurable_of_countable _

/-- The four-target unnormalised population measure obtained by aggregating
the neutral lineage birth and death rates. -/
noncomputable def aggregatedLineageRawMeasure
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    Measure PopState :=
  let x := lineageAggregate a L
  let d := params.delta + params.alpha0 * (lineageTotal L - 1 : Nat)
  ENNReal.ofReal (params.beta * x.1) • Measure.dirac (x.1 + 1, x.2) +
    ENNReal.ofReal (params.beta * x.2) • Measure.dirac (x.1, x.2 + 1) +
    ENNReal.ofReal (d * x.1) • Measure.dirac (x.1 - 1, x.2) +
    ENNReal.ofReal (d * x.2) • Measure.dirac (x.1, x.2 - 1)

lemma lineageRawMeasure_map_aggregate
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    (lineageRawMeasure params L).map (lineageAggregate a) =
      aggregatedLineageRawMeasure params a L := by
  classical
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (lineageAggregate_measurable a)
    (measurableSet_singleton x)]
  simp only [lineageRawMeasure, aggregatedLineageRawMeasure,
    Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply]
  simp only [mul_ite, mul_one, mul_zero]
  let s := lineageAggregate a L
  have hBirthSplit :
      (∑ i : Lineage n,
          if lineageAggregate a (lineageBirth L i) = x then
            lineageBirthMass params L i
          else 0) =
        (∑ i : Lineage n,
            if (i : Nat) < a then
              if (s.1 + 1, s.2) = x then lineageBirthMass params L i else 0
            else 0) +
          ∑ i : Lineage n,
            if a ≤ (i : Nat) then
              if (s.1, s.2 + 1) = x then lineageBirthMass params L i else 0
            else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [lineageAggregate_birth]
    by_cases hi : (i : Nat) < a
    · have hnot : ¬a ≤ (i : Nat) := Nat.not_le_of_gt hi
      simp [s, hi, hnot]
    · have hai : a ≤ (i : Nat) := Nat.le_of_not_gt hi
      simp [s, hi, hai]
  have hDeathSplit :
      (∑ i : Lineage n,
          if lineageAggregate a (lineageDeath L i) = x then
            lineageDeathMass params L i
          else 0) =
        (∑ i : Lineage n,
            if (i : Nat) < a then
              if (s.1 - 1, s.2) = x then lineageDeathMass params L i else 0
            else 0) +
          ∑ i : Lineage n,
            if a ≤ (i : Nat) then
              if (s.1, s.2 - 1) = x then lineageDeathMass params L i else 0
            else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hzero : L i = 0
    · simp [lineageDeathMass, hzero]
    · have hpos : 0 < L i := Nat.pos_of_ne_zero hzero
      rw [lineageAggregate_death a L i hpos]
      by_cases hi : (i : Nat) < a
      · have hnot : ¬a ≤ (i : Nat) := Nat.not_le_of_gt hi
        simp [s, hi, hnot]
      · have hai : a ≤ (i : Nat) := Nat.le_of_not_gt hi
        simp [s, hi, hai]
  rw [hBirthSplit, hDeathSplit]
  dsimp only [s]
  by_cases hb0 : ((lineageAggregate a L).1 + 1,
      (lineageAggregate a L).2) = x <;>
    by_cases hb1 : ((lineageAggregate a L).1,
      (lineageAggregate a L).2 + 1) = x <;>
    by_cases hd0 : ((lineageAggregate a L).1 - 1,
      (lineageAggregate a L).2) = x <;>
    by_cases hd1 : ((lineageAggregate a L).1,
      (lineageAggregate a L).2 - 1) = x <;>
    simp [hb0, hb1, hd0, hd1,
      lineageBirthMass_sum_species0, lineageBirthMass_sum_species1,
      lineageDeathMass_sum_species0, lineageDeathMass_sum_species1] <;>
    ac_rfl

lemma aggregate_species0_death_rate
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (a : Nat) {n : Nat} (L : LinState n) :
    (params.delta + params.alpha0 * (lineageTotal L - 1 : Nat)) *
        (lineageAggregate a L).1 =
      params.delta * (lineageAggregate a L).1 +
        params.alpha1 * (lineageAggregate a L).1 *
          (lineageAggregate a L).2 +
        params.gamma0 *
          ((lineageAggregate a L).1 *
            ((lineageAggregate a L).1 - 1) / 2) := by
  let x0 := (lineageAggregate a L).1
  let x1 := (lineageAggregate a L).2
  have htotal : lineageTotal L = x0 + x1 :=
    lineageTotal_eq_aggregate_total a L
  rw [htotal]
  by_cases hx0 : x0 = 0
  · simp [x0, x1, hx0]
  · have hOne : 1 ≤ x0 + x1 := by
      have : 0 < x0 := Nat.pos_of_ne_zero hx0
      omega
    rw [Nat.cast_sub hOne]
    norm_num
    exact (nsd_neutral_sp0_death_rate
      params hNeutral hEq0 x0 x1).symm

lemma aggregate_species1_death_rate
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a : Nat) {n : Nat} (L : LinState n) :
    (params.delta + params.alpha0 * (lineageTotal L - 1 : Nat)) *
        (lineageAggregate a L).2 =
      params.delta * (lineageAggregate a L).2 +
        params.alpha0 * (lineageAggregate a L).1 *
          (lineageAggregate a L).2 +
        params.gamma1 *
          ((lineageAggregate a L).2 *
            ((lineageAggregate a L).2 - 1) / 2) := by
  let x0 := (lineageAggregate a L).1
  let x1 := (lineageAggregate a L).2
  have htotal : lineageTotal L = x0 + x1 :=
    lineageTotal_eq_aggregate_total a L
  rw [htotal]
  by_cases hx1 : x1 = 0
  · simp [x0, x1, hx1]
  · have hOne : 1 ≤ x0 + x1 := by
      have : 0 < x1 := Nat.pos_of_ne_zero hx1
      omega
    rw [Nat.cast_sub hOne]
    norm_num
    exact (nsd_neutral_sp1_death_rate
      params hNeutral hEq1 x0 x1).symm

/-- The eight reaction masses of the NSD population chain, before
normalisation. Reactions with the same population target are kept separate. -/
noncomputable def nsdRawMeasure (params : LVParams) (s : PopState) :
    Measure PopState :=
  ENNReal.ofReal (params.beta * s.1) • Measure.dirac (s.1 + 1, s.2) +
    ENNReal.ofReal (params.beta * s.2) • Measure.dirac (s.1, s.2 + 1) +
    ENNReal.ofReal (params.delta * s.1) • Measure.dirac (s.1 - 1, s.2) +
    ENNReal.ofReal (params.delta * s.2) • Measure.dirac (s.1, s.2 - 1) +
    ENNReal.ofReal (params.alpha0 * s.1 * s.2) •
      Measure.dirac (s.1, s.2 - 1) +
    ENNReal.ofReal (params.alpha1 * s.1 * s.2) •
      Measure.dirac (s.1 - 1, s.2) +
    ENNReal.ofReal (params.gamma0 * (s.1 * (s.1 - 1) / 2)) •
      Measure.dirac (s.1 - 1, s.2) +
    ENNReal.ofReal (params.gamma1 * (s.2 * (s.2 - 1) / 2)) •
      Measure.dirac (s.1, s.2 - 1)

lemma aggregatedLineageRawMeasure_eq_nsdRawMeasure
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a : Nat) {n : Nat} (L : LinState n) :
    aggregatedLineageRawMeasure params a L =
      nsdRawMeasure params (lineageAggregate a L) := by
  let x := lineageAggregate a L
  have hδ0 : 0 ≤ params.delta * (x.1 : Real) :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  have hδ1 : 0 ≤ params.delta * (x.2 : Real) :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  have hα0 : 0 ≤ params.alpha0 * (x.1 : Real) * (x.2 : Real) :=
    mul_nonneg (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hα1 : 0 ≤ params.alpha1 * (x.1 : Real) * (x.2 : Real) :=
    mul_nonneg (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hγ0 :
      0 ≤ params.gamma0 * ((x.1 : Real) * ((x.1 : Real) - 1) / 2) := by
    have hprod : 0 ≤ (x.1 : Real) * ((x.1 : Real) - 1) := by
      have : x.1 = 0 ∨ 1 ≤ x.1 := by omega
      rcases this with hx | hx
      · simp [hx]
      · exact mul_nonneg (Nat.cast_nonneg _)
          (sub_nonneg.mpr (by exact_mod_cast hx))
    exact mul_nonneg params.gamma0_nonneg (div_nonneg hprod (by norm_num))
  have hγ1 :
      0 ≤ params.gamma1 * ((x.2 : Real) * ((x.2 : Real) - 1) / 2) := by
    have hprod : 0 ≤ (x.2 : Real) * ((x.2 : Real) - 1) := by
      have : x.2 = 0 ∨ 1 ≤ x.2 := by omega
      rcases this with hx | hx
      · simp [hx]
      · exact mul_nonneg (Nat.cast_nonneg _)
          (sub_nonneg.mpr (by exact_mod_cast hx))
    exact mul_nonneg params.gamma1_nonneg (div_nonneg hprod (by norm_num))
  have hcoeff0 :
      ENNReal.ofReal
          ((params.delta +
              params.alpha0 * (lineageTotal L - 1 : Nat)) * x.1) =
        ENNReal.ofReal (params.delta * x.1) +
          ENNReal.ofReal (params.alpha1 * x.1 * x.2) +
          ENNReal.ofReal
            (params.gamma0 * (x.1 * (x.1 - 1) / 2)) := by
    rw [aggregate_species0_death_rate params hNeutral hEq0 a L]
    rw [ENNReal.ofReal_add (add_nonneg hδ0 hα1) hγ0,
      ENNReal.ofReal_add hδ0 hα1]
  have hcoeff1 :
      ENNReal.ofReal
          ((params.delta +
              params.alpha0 * (lineageTotal L - 1 : Nat)) * x.2) =
        ENNReal.ofReal (params.delta * x.2) +
          ENNReal.ofReal (params.alpha0 * x.1 * x.2) +
          ENNReal.ofReal
            (params.gamma1 * (x.2 * (x.2 - 1) / 2)) := by
    rw [aggregate_species1_death_rate params hNeutral hEq1 a L]
    rw [ENNReal.ofReal_add (add_nonneg hδ1 hα0) hγ1,
      ENNReal.ofReal_add hδ1 hα0]
  unfold aggregatedLineageRawMeasure nsdRawMeasure
  dsimp only [x] at hcoeff0 hcoeff1 ⊢
  rw [hcoeff0, hcoeff1, add_smul, add_smul, add_smul, add_smul]
  simp only [mul_assoc]
  abel

private lemma lineage_sum_split
    {n : Nat} (a : Nat) (f : Lineage n → ENNReal) :
    (∑ i : Lineage n, f i) =
      (∑ i : Lineage n, if (i : Nat) < a then f i else 0) +
        ∑ i : Lineage n, if a ≤ (i : Nat) then f i else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : Nat) < a
  · simp [hi, Nat.not_le_of_gt hi]
  · simp [hi, Nat.le_of_not_gt hi]

lemma lineageTotalMass_eq_four_rates
    (params : LVParams) (a : Nat) {n : Nat} (L : LinState n) :
    lineageTotalMass params L =
      ENNReal.ofReal (params.beta * (lineageAggregate a L).1) +
        ENNReal.ofReal (params.beta * (lineageAggregate a L).2) +
        ENNReal.ofReal
          ((params.delta +
              params.alpha0 * (lineageTotal L - 1 : Nat)) *
            (lineageAggregate a L).1) +
        ENNReal.ofReal
          ((params.delta +
              params.alpha0 * (lineageTotal L - 1 : Nat)) *
            (lineageAggregate a L).2) := by
  unfold lineageTotalMass
  rw [Finset.sum_add_distrib]
  rw [lineage_sum_split a (lineageBirthMass params L)]
  rw [lineage_sum_split a (lineageDeathMass params L)]
  rw [lineageBirthMass_sum_species0, lineageBirthMass_sum_species1,
    lineageDeathMass_sum_species0, lineageDeathMass_sum_species1]
  ac_rfl

lemma lvTotalPropensity_eq_lineage_rates
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a : Nat) {n : Nat} (L : LinState n) :
    lvTotalPropensity params (lineageAggregate a L) =
      params.beta * (lineageAggregate a L).1 +
        params.beta * (lineageAggregate a L).2 +
        (params.delta +
            params.alpha0 * (lineageTotal L - 1 : Nat)) *
          (lineageAggregate a L).1 +
        (params.delta +
            params.alpha0 * (lineageTotal L - 1 : Nat)) *
          (lineageAggregate a L).2 := by
  let x := lineageAggregate a L
  have h0 := aggregate_species0_death_rate params hNeutral hEq0 a L
  have h1 := aggregate_species1_death_rate params hNeutral hEq1 a L
  calc
    lvTotalPropensity params x =
        params.beta * x.1 + params.beta * x.2 +
          (params.delta * x.1 + params.alpha1 * x.1 * x.2 +
            params.gamma0 * (x.1 * (x.1 - 1) / 2)) +
          (params.delta * x.2 + params.alpha0 * x.1 * x.2 +
            params.gamma1 * (x.2 * (x.2 - 1) / 2)) := by
      unfold lvTotalPropensity
      ring
    _ = params.beta * x.1 + params.beta * x.2 +
          (params.delta +
              params.alpha0 * (lineageTotal L - 1 : Nat)) * x.1 +
          (params.delta +
              params.alpha0 * (lineageTotal L - 1 : Nat)) * x.2 := by
      rw [← h0, ← h1]

lemma lineageTotalMass_eq_lvTotalPropensity
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a : Nat) {n : Nat} (L : LinState n) :
    lineageTotalMass params L =
      ENNReal.ofReal (lvTotalPropensity params (lineageAggregate a L)) := by
  rw [lineageTotalMass_eq_four_rates params a L]
  have hb0 :
      0 ≤ params.beta * ((lineageAggregate a L).1 : Real) :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  have hb1 :
      0 ≤ params.beta * ((lineageAggregate a L).2 : Real) :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  have hd :
      0 ≤ params.delta +
          params.alpha0 * (lineageTotal L - 1 : Nat) :=
    add_nonneg params.delta_nonneg
      (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
  have hd0 :
      0 ≤ (params.delta +
          params.alpha0 * (lineageTotal L - 1 : Nat)) *
            ((lineageAggregate a L).1 : Real) :=
    mul_nonneg hd (Nat.cast_nonneg _)
  have hd1 :
      0 ≤ (params.delta +
          params.alpha0 * (lineageTotal L - 1 : Nat)) *
            ((lineageAggregate a L).2 : Real) :=
    mul_nonneg hd (Nat.cast_nonneg _)
  rw [← ENNReal.ofReal_add hb0 hb1,
    ← ENNReal.ofReal_add (add_nonneg hb0 hb1) hd0,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hb0 hb1) hd0) hd1]
  congr 1
  exact (lvTotalPropensity_eq_lineage_rates
    params hNeutral hEq0 hEq1 a L).symm

/-- Aggregating the neutral lineage chain by the species of the initial
individuals gives exactly the NSD Lotka--Volterra jump chain. -/
theorem lineageKernel_map_aggregate
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a : Nat) {n : Nat} (L : LinState n) :
    (lineageKernel params n L).map (lineageAggregate a) =
      lvKernel .nonSelfDestructive params (lineageAggregate a L) := by
  let x := lineageAggregate a L
  let φ := lvTotalPropensity params x
  have hmass :
      lineageTotalMass params L = ENNReal.ofReal φ := by
    exact lineageTotalMass_eq_lvTotalPropensity
      params hNeutral hEq0 hEq1 a L
  by_cases hφ : φ = 0
  · have hm0 : lineageTotalMass params L = 0 := by
      rw [hmass, hφ, ENNReal.ofReal_zero]
    rw [lvKernel_apply_zero_propensity .nonSelfDestructive params x hφ]
    simp only [lineageKernel, Kernel.ofFunOfCountable, Kernel.coe_mk,
      hm0, dite_true]
    exact Measure.map_dirac' (lineageAggregate_measurable a) L
  · have hφpos : 0 < φ :=
      lt_of_le_of_ne (lvTotalPropensity_nonneg params x) (Ne.symm hφ)
    have hmne : lineageTotalMass params L ≠ 0 := by
      rw [hmass, ENNReal.ofReal_ne_zero_iff]
      exact hφpos
    simp only [lineageKernel, Kernel.ofFunOfCountable, Kernel.coe_mk,
      hmne, dite_false]
    rw [Measure.map_smul, lineageRawMeasure_map_aggregate,
      aggregatedLineageRawMeasure_eq_nsdRawMeasure
        params hNeutral hEq0 hEq1 a L]
    rw [lvKernel_nsd_apply params x.1 x.2 hφ]
    change
      (lineageTotalMass params L)⁻¹ • nsdRawMeasure params x =
        ENNReal.ofReal (1 / φ) • nsdRawMeasure params x
    congr 1
    rw [hmass, one_div, ENNReal.ofReal_inv_of_pos hφpos]

/-- Path law of the neutral lineage chain started with one descendant in each
initial lineage. -/
noncomputable def lineagePathMeasure (params : LVParams) (n : Nat) :
    Measure (Nat → LinState n) :=
  homogeneousPathMeasure (Measure.dirac (initialLineages n))
    (lineageKernel params n)

/-- The coordinatewise aggregation of the full lineage path has exactly the
Lotka--Volterra path law started from the corresponding two species counts. -/
theorem lineagePathMeasure_map_aggregate
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) :
    (lineagePathMeasure params (a + b)).map
        (pathMap (lineageAggregate a)) =
      lvPathMeasure .nonSelfDestructive params (a, b) := by
  unfold lineagePathMeasure lvPathMeasure
  rw [← initialLineages_aggregate a b]
  exact homogeneousPathMeasure_map_pathMap
    (lineageKernel params (a + b))
    (lvKernel .nonSelfDestructive params)
    (lineageAggregate a)
    (lineageAggregate_measurable a)
    (lineageKernel_map_aggregate params hNeutral hEq0 hEq1 a)
    (initialLineages (a + b))

end LVConsensus
