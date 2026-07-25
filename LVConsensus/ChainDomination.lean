import LVConsensus.Definitions
import LVConsensus.Helpers
import LVConsensus.LabeledDynamics
import LVConsensus.MarkovLib
import LVConsensus.NiceWhpExtinction

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open LVConsensus.Helpers
open scoped ENNReal

namespace LVConsensus

/-- Event-profile abstraction used by domination conditions (D1) and (D2). -/
structure TwoSpeciesEventProfile where
  badNonCompetitive : PopState → Real
  goodEvent : PopState → Real

/-- Domination conditions from the paper. -/
def IsDominatingChain (N : BirthDeathChain) (S : TwoSpeciesEventProfile) : Prop :=
  (∀ a b : Nat, S.badNonCompetitive (a, b) ≤ N.p (Nat.min a b)) ∧
    (∀ a b : Nat, N.q (Nat.min a b) ≤ S.goodEvent (a, b))

/-- Rate that uniformly guarantees a minority-decreasing competitive event. -/
noncomputable def effectiveGoodRate (v : LVVariant) (params : LVParams) : Real :=
  match v with
  | .selfDestructive => params.alpha0 + params.alpha1
  | .nonSelfDestructive => min params.alpha0 params.alpha1

/-- Event profile from LV parameters used in domination inequalities. -/
noncomputable def lvEventProfile (v : LVVariant) (params : LVParams) : TwoSpeciesEventProfile where
  badNonCompetitive := fun s =>
    if Nat.min s.1 s.2 = 0 then
      0
    else
      let a : Real := s.1
      let b : Real := s.2
      let α : Real := params.alpha0 + params.alpha1
      let θ : Real := params.beta + params.delta
      if s.2 < s.1 then
        (params.delta * a + params.beta * b) /
          (α * a * b + θ * (a + b))
      else if s.1 < s.2 then
        (params.delta * b + params.beta * a) /
          (α * a * b + θ * (a + b))
      else
        0
  goodEvent := fun s =>
    if Nat.min s.1 s.2 = 0 then
      0
    else
      let a : Real := s.1
      let b : Real := s.2
      let α : Real := params.alpha0 + params.alpha1
      let αgood : Real := effectiveGoodRate v params
      let θ : Real := params.beta + params.delta
      (αgood * a * b) / (α * a * b + θ * (a + b))

/-- Labelled bad reactions used by the pseudo-coupling. -/
def dominationBadSet (s : PopState) : Set LabeledPopState :=
  {z | isBadNoncompetitiveReaction s z.2}

/-- A competitive reaction which decreases the current minimum.  In the NSD
case the selected reaction is the one which kills the smaller species; at a
tie either competitive label decreases the minimum. -/
def dominationGoodSet (v : LVVariant) (s : PopState) : Set LabeledPopState :=
  {z |
    match v with
    | .selfDestructive =>
        z.2 = .inter0 ∨ z.2 = .inter1
    | .nonSelfDestructive =>
        if s.2 < s.1 then z.2 = .inter0
        else if s.1 < s.2 then z.2 = .inter1
        else z.2 = .inter0 ∨ z.2 = .inter1}

/-- Reactions which belong to neither the bad non-competitive class nor the
chosen good competitive class.  This residual class is essential: the first
two classes do not in general exhaust all reactions. -/
def dominationOtherSet (v : LVVariant) (s : PopState) :
    Set LabeledPopState :=
  (dominationBadSet s ∪ dominationGoodSet v s)ᶜ

lemma dominationBadSet_disjoint_goodSet
    (v : LVVariant) (s : PopState) :
    Disjoint (dominationBadSet s) (dominationGoodSet v s) := by
  apply Set.disjoint_left.2
  intro z hbad hgood
  rcases s with ⟨a, b⟩
  rcases z with ⟨x, r⟩
  cases v <;>
    simp only [dominationBadSet, dominationGoodSet,
      Set.mem_setOf_eq, isBadNoncompetitiveReaction] at hbad hgood
  · split at hbad
    · rcases hbad with rfl | rfl <;> simp at hgood
    · split at hbad
      · rcases hbad with rfl | rfl <;> simp at hgood
      · contradiction
  · split at hbad
    · rcases hbad with rfl | rfl <;> simp at hgood
    · split at hbad
      · rcases hbad with rfl | rfl <;> simp at hgood
      · contradiction

lemma domination_category_partition
    (v : LVVariant) (s : PopState) :
    dominationBadSet s ∪ dominationGoodSet v s ∪
        dominationOtherSet v s = Set.univ := by
  ext z
  simp only [dominationOtherSet, Set.mem_union, Set.mem_compl_iff,
    Set.mem_univ, iff_true]
  tauto

/-- Every reaction can raise the minority population by at most one. -/
lemma lvReactionTarget_min_le_succ
    (v : LVVariant) (s : PopState) (r : LVReaction) :
    Nat.min (lvReactionTarget v s r).1
        (lvReactionTarget v s r).2 ≤ Nat.min s.1 s.2 + 1 := by
  rcases s with ⟨a, b⟩
  have hfst :
      (lvReactionTarget v (a, b) r).1 ≤ a + 1 := by
    cases v <;> cases r <;> simp [lvReactionTarget] <;> omega
  have hsnd :
      (lvReactionTarget v (a, b) r).2 ≤ b + 1 := by
    cases v <;> cases r <;> simp [lvReactionTarget] <;> omega
  have hmin := min_le_min hfst hsnd
  simpa only [min_add_add_right] using hmin

/-- A residual reaction (neither bad nor chosen good) does not increase the
minority population. -/
lemma lvReactionTarget_min_le_of_other
    (v : LVVariant) (s : PopState) (r : LVReaction)
    (hother :
      (lvReactionTarget v s r, r) ∈ dominationOtherSet v s) :
    Nat.min (lvReactionTarget v s r).1
        (lvReactionTarget v s r).2 ≤ Nat.min s.1 s.2 := by
  rcases s with ⟨a, b⟩
  cases v <;> cases r <;>
    simp [lvReactionTarget, dominationOtherSet, dominationBadSet,
      dominationGoodSet, isBadNoncompetitiveReaction] at hother ⊢ <;>
    omega

/-- Each chosen good reaction lowers a positive minority population by
exactly one. -/
lemma lvReactionTarget_min_eq_pred_of_good
    (v : LVVariant) (s : PopState) (r : LVReaction)
    (hminpos : 0 < Nat.min s.1 s.2)
    (hgood :
      (lvReactionTarget v s r, r) ∈ dominationGoodSet v s) :
    Nat.min (lvReactionTarget v s r).1
        (lvReactionTarget v s r).2 = Nat.min s.1 s.2 - 1 := by
  rcases s with ⟨a, b⟩
  cases v with
  | selfDestructive =>
      cases r <;>
        simp [dominationGoodSet] at hgood
      all_goals
        simp only [lvReactionTarget]
        change Nat.min (Nat.pred a) (Nat.pred b) = Nat.pred (Nat.min a b)
        exact (Order.pred_min a b).symm
  | nonSelfDestructive =>
      by_cases hba : b < a
      · have hr : r = .inter0 := by
          simpa [dominationGoodSet, hba, Nat.not_lt_of_ge hba.le] using hgood
        subst r
        simp only [lvReactionTarget]
        simp only [Nat.min_def]
        split <;> split <;> omega
      · by_cases hab : a < b
        · have hr : r = .inter1 := by
            simpa [dominationGoodSet, hba, hab] using hgood
          subst r
          simp only [lvReactionTarget]
          simp only [Nat.min_def]
          split <;> split <;> omega
        · have heq : a = b := by omega
          subst b
          have hr : r = .inter0 ∨ r = .inter1 := by
            simpa [dominationGoodSet] using hgood
          rcases hr with rfl | rfl <;>
            simp [lvReactionTarget, Nat.min_eq_left, Nat.min_eq_right]

/-- The actual labelled one-step probabilities have three disjoint classes.
In particular, no assertion that `bad + good = 1` is used. -/
lemma lvLabeledKernel_domination_partition
    (v : LVVariant) (params : LVParams) (z : LabeledPopState) :
    lvLabeledKernel v params z (dominationBadSet z.1) +
        lvLabeledKernel v params z (dominationOtherSet v z.1) +
        lvLabeledKernel v params z (dominationGoodSet v z.1) = 1 := by
  let μ := lvLabeledKernel v params z
  let bad := dominationBadSet z.1
  let good := dominationGoodSet v z.1
  let other := dominationOtherSet v z.1
  have hbad : MeasurableSet bad := (Set.to_countable _).measurableSet
  have hgood : MeasurableSet good := (Set.to_countable _).measurableSet
  have hother : MeasurableSet other := (Set.to_countable _).measurableSet
  have hdisj : Disjoint bad good :=
    dominationBadSet_disjoint_goodSet v z.1
  have hdisjOther : Disjoint (bad ∪ good) other := by
    dsimp only [bad, good, other]
    exact Set.disjoint_left.2 (by
      intro x hx hxcompl
      exact hxcompl hx)
  have hμuniv : μ Set.univ = 1 := by
    letI : IsProbabilityMeasure μ := by infer_instance
    exact measure_univ
  calc
    μ bad + μ other + μ good = μ bad + μ good + μ other := by
      simp only [add_assoc]
      rw [add_comm (μ other) (μ good)]
    _ = μ (bad ∪ good) + μ other := by
      rw [measure_union hdisj hgood]
    _ = μ ((bad ∪ good) ∪ other) := by
      rw [measure_union hdisjOther hother]
    _ = μ Set.univ := by
      congr 1
      exact domination_category_partition v z.1
    _ = 1 := hμuniv

/-- On an interior state with `γ = 0`, the labelled probability of a bad
non-competitive reaction is exactly the profile probability `P(a,b)`. -/
lemma lvLabeledKernel_dominationBadSet
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s : PopState) (old : LVReaction)
    (hminpos : 0 < Nat.min s.1 s.2) :
    lvLabeledKernel v params (s, old) (dominationBadSet s) =
      ENNReal.ofReal ((lvEventProfile v params).badNonCompetitive s) := by
  rcases s with ⟨a, b⟩
  have hmin : Nat.min a b ≠ 0 := Nat.ne_of_gt hminpos
  have ha : a ≠ 0 := by
    intro ha
    apply hmin
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hmin
    simp [hb]
  have hφ :
      lvTotalPropensity params (a, b) =
        (params.alpha0 + params.alpha1) * a * b +
          (params.beta + params.delta) * (a + b) := by
    simp [lvTotalPropensity, hGamma0, hGamma1]
    ring
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hset :
        dominationBadSet (a, b) =
          {z | z.2 = .death1} ∪ {z | z.2 = .birth0} := by
      ext z
      simp [dominationBadSet, isBadNoncompetitiveReaction, hab,
        Nat.not_lt_of_ge hab.le]
    rw [hset, measure_union]
    · rw [lvLabeledKernel_reaction_probability,
        lvLabeledKernel_reaction_probability]
      by_cases hφ0 : lvTotalPropensity params (a, b) = 0
      · have hden0 :
            (params.alpha0 + params.alpha1) * (a : ℝ) * b +
                (params.beta + params.delta) * ((a : ℝ) + b) = 0 := by
          simpa [hφ] using hφ0
        simp [lvEventProfile, hmin, hab, hφ0, hden0]
      · simp only [hφ0, ↓reduceDIte, if_false, lvReactionWeight]
        rw [← mul_add]
        rw [← ENNReal.ofReal_add
          (mul_nonneg params.delta_nonneg (Nat.cast_nonneg _))
          (mul_nonneg params.beta_nonneg (Nat.cast_nonneg _))]
        rw [← ENNReal.ofReal_mul
          (one_div_nonneg.mpr (lvTotalPropensity_nonneg params (a, b)))]
        simp only [lvEventProfile, hmin, ↓reduceIte,
          Nat.min_eq_zero_iff, ha, hb, or_self, hab,
          Nat.not_lt_of_ge hab.le]
        apply congrArg ENNReal.ofReal
        rw [hφ]
        ring
    · exact Set.disjoint_left.2 (by simp)
    · exact (Set.to_countable _).measurableSet
  · simp [dominationBadSet, lvEventProfile,
      isBadNoncompetitiveReaction, hmin]
  · have hset :
        dominationBadSet (a, b) =
          {z | z.2 = .death0} ∪ {z | z.2 = .birth1} := by
      ext z
      simp [dominationBadSet, isBadNoncompetitiveReaction, hba]
    rw [hset, measure_union]
    · rw [lvLabeledKernel_reaction_probability,
        lvLabeledKernel_reaction_probability]
      by_cases hφ0 : lvTotalPropensity params (a, b) = 0
      · have hden0 :
            (params.alpha0 + params.alpha1) * (a : ℝ) * b +
                (params.beta + params.delta) * ((a : ℝ) + b) = 0 := by
          simpa [hφ] using hφ0
        simp [lvEventProfile, hmin, hba, hφ0, hden0]
      · simp only [hφ0, ↓reduceDIte, if_false, lvReactionWeight]
        rw [← mul_add]
        rw [← ENNReal.ofReal_add
          (mul_nonneg params.delta_nonneg (Nat.cast_nonneg _))
          (mul_nonneg params.beta_nonneg (Nat.cast_nonneg _))]
        rw [← ENNReal.ofReal_mul
          (one_div_nonneg.mpr (lvTotalPropensity_nonneg params (a, b)))]
        simp only [lvEventProfile, hmin, ↓reduceIte,
          Nat.min_eq_zero_iff, ha, hb, or_self, hba]
        apply congrArg ENNReal.ofReal
        rw [hφ]
        ring
    · exact Set.disjoint_left.2 (by simp)
    · exact (Set.to_countable _).measurableSet

/-- On an interior state with `γ = 0`, the probability of the selected good
competitive reactions is at least the profile lower bound `Q(a,b)`. -/
lemma lvLabeledKernel_dominationGoodSet
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s : PopState) (old : LVReaction)
    (hminpos : 0 < Nat.min s.1 s.2) :
    ENNReal.ofReal ((lvEventProfile v params).goodEvent s) ≤
      lvLabeledKernel v params (s, old) (dominationGoodSet v s) := by
  rcases s with ⟨a, b⟩
  have hmin : Nat.min a b ≠ 0 := Nat.ne_of_gt hminpos
  have ha : a ≠ 0 := by
    intro ha
    apply hmin
    simp [ha]
  have hb : b ≠ 0 := by
    intro hb
    apply hmin
    simp [hb]
  have hφ :
      lvTotalPropensity params (a, b) =
        (params.alpha0 + params.alpha1) * a * b +
          (params.beta + params.delta) * (a + b) := by
    simp [lvTotalPropensity, hGamma0, hGamma1]
    ring
  by_cases hφ0 : lvTotalPropensity params (a, b) = 0
  · have hden0 :
        (params.alpha0 + params.alpha1) * (a : ℝ) * b +
            (params.beta + params.delta) * ((a : ℝ) + b) = 0 := by
      simpa [hφ] using hφ0
    simp [lvEventProfile, hmin, hden0]
  · cases v with
    | selfDestructive =>
        have hset :
            dominationGoodSet .selfDestructive (a, b) =
              {z | z.2 = .inter0} ∪ {z | z.2 = .inter1} := by
          ext z
          simp [dominationGoodSet]
        rw [hset, measure_union]
        · rw [lvLabeledKernel_reaction_probability,
            lvLabeledKernel_reaction_probability]
          simp only [hφ0, ↓reduceDIte, if_false, lvReactionWeight]
          rw [← mul_add]
          rw [← ENNReal.ofReal_add
            (mul_nonneg
              (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
              (Nat.cast_nonneg _))
            (mul_nonneg
              (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
              (Nat.cast_nonneg _))]
          rw [← ENNReal.ofReal_mul
            (one_div_nonneg.mpr
              (lvTotalPropensity_nonneg params (a, b)))]
          simp only [lvEventProfile, hmin, ↓reduceIte, effectiveGoodRate]
          apply ENNReal.ofReal_le_ofReal
          rw [hφ]
          try ring_nf
          linarith
        · exact Set.disjoint_left.2 (by simp)
        · exact (Set.to_countable _).measurableSet
    | nonSelfDestructive =>
        rcases lt_trichotomy a b with hab | rfl | hba
        · have hset :
              dominationGoodSet .nonSelfDestructive (a, b) =
                {z | z.2 = .inter1} := by
            ext z
            simp [dominationGoodSet, hab, Nat.not_lt_of_ge hab.le]
          rw [hset, lvLabeledKernel_reaction_probability]
          simp only [hφ0, ↓reduceDIte, if_false, lvReactionWeight]
          rw [← ENNReal.ofReal_mul
            (one_div_nonneg.mpr
              (lvTotalPropensity_nonneg params (a, b)))]
          simp only [lvEventProfile, hmin, ↓reduceIte, effectiveGoodRate]
          apply ENNReal.ofReal_le_ofReal
          rw [hφ]
          have hrate := min_le_right params.alpha0 params.alpha1
          have habnn : 0 ≤ (a : ℝ) * b := by positivity
          have hdennn :
              0 ≤ (params.alpha0 + params.alpha1) * (a : ℝ) * b +
                (params.beta + params.delta) * ((a : ℝ) + b) := by
            rw [← hφ]
            exact lvTotalPropensity_nonneg params (a, b)
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hrate habnn) hdennn)
        · have hset :
              dominationGoodSet .nonSelfDestructive (a, a) =
                {z | z.2 = .inter0} ∪ {z | z.2 = .inter1} := by
            ext z
            simp [dominationGoodSet]
          rw [hset, measure_union]
          · rw [lvLabeledKernel_reaction_probability,
              lvLabeledKernel_reaction_probability]
            simp only [hφ0, ↓reduceDIte, if_false, lvReactionWeight]
            rw [← mul_add]
            rw [← ENNReal.ofReal_add
              (mul_nonneg
                (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
                (Nat.cast_nonneg _))
              (mul_nonneg
                (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
                (Nat.cast_nonneg _))]
            rw [← ENNReal.ofReal_mul
              (one_div_nonneg.mpr
                (lvTotalPropensity_nonneg params (a, a)))]
            simp only [lvEventProfile, hmin, ↓reduceIte,
              effectiveGoodRate]
            apply ENNReal.ofReal_le_ofReal
            rw [hφ]
            have hrate :
                min params.alpha0 params.alpha1 ≤
                  params.alpha0 + params.alpha1 := by
              nlinarith [min_le_left params.alpha0 params.alpha1,
                params.alpha1_nonneg]
            have hann : 0 ≤ (a : ℝ) * a := by positivity
            have hdennn :
                0 ≤ (params.alpha0 + params.alpha1) * (a : ℝ) * a +
                  (params.beta + params.delta) * ((a : ℝ) + a) := by
              rw [← hφ]
              exact lvTotalPropensity_nonneg params (a, a)
            have hnum :
                params.alpha0 * (a : ℝ) * a +
                    params.alpha1 * (a : ℝ) * a =
                  (params.alpha0 + params.alpha1) * ((a : ℝ) * a) := by
              ring
            rw [hnum]
            simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hrate hann) hdennn)
          · exact Set.disjoint_left.2 (by simp)
          · exact (Set.to_countable _).measurableSet
        · have hset :
              dominationGoodSet .nonSelfDestructive (a, b) =
                {z | z.2 = .inter0} := by
            ext z
            simp [dominationGoodSet, hba]
          rw [hset, lvLabeledKernel_reaction_probability]
          simp only [hφ0, ↓reduceDIte, if_false, lvReactionWeight]
          rw [← ENNReal.ofReal_mul
            (one_div_nonneg.mpr
              (lvTotalPropensity_nonneg params (a, b)))]
          simp only [lvEventProfile, hmin, ↓reduceIte, effectiveGoodRate]
          apply ENNReal.ofReal_le_ofReal
          rw [hφ]
          have hrate := min_le_left params.alpha0 params.alpha1
          have habnn : 0 ≤ (a : ℝ) * b := by positivity
          have hdennn :
              0 ≤ (params.alpha0 + params.alpha1) * (a : ℝ) * b +
                (params.beta + params.delta) * ((a : ℝ) + b) := by
            rw [← hφ]
            exact lvTotalPropensity_nonneg params (a, b)
          simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hrate habnn) hdennn)

/-- Paper `lem:coupling:dominates`, pathwise form.  These hypotheses are the
three interval rules of the pseudo-coupling, including its asynchronous freeze
when the minority count is strictly below the birth-death state. -/
theorem lem_coupling_dominates
    (M N J B : ℕ → ℕ)
    (P Q p q ξ : ℕ → ℝ)
    (hM0 : M 0 = N 0)
    (hJ0 : J 0 = B 0)
    (hD1 : ∀ t, P t ≤ p t)
    (hD2 : ∀ t, q t ≤ Q t)
    (hFreeze : ∀ t, M t < N t →
      M (t + 1) = M t ∧ J (t + 1) = J t)
    (hN : ∀ t,
      N (t + 1) =
        if ξ t < p t then N t + 1
        else if 1 - q t ≤ ξ t then N t - 1
        else N t)
    (hMbad : ∀ t, M t = N t → ξ t < P t →
      M (t + 1) ≤ M t + 1)
    (hMgood : ∀ t, M t = N t → 1 - Q t ≤ ξ t →
      M (t + 1) = M t - 1)
    (hMmiddle : ∀ t, M t = N t → P t ≤ ξ t →
      ξ t < 1 - Q t → M (t + 1) ≤ M t)
    (hJ : ∀ t, M t = N t →
      J (t + 1) = if ξ t < P t then J t + 1 else J t)
    (hB : ∀ t,
      B (t + 1) = if ξ t < p t then B t + 1 else B t) :
    ∀ t, M t ≤ N t ∧ J t ≤ B t := by
  intro t
  induction t with
  | zero =>
      exact ⟨hM0.le, hJ0.le⟩
  | succ t ih =>
      by_cases hEq : M t = N t
      · have hMnext : M (t + 1) ≤ N (t + 1) := by
          rw [hN t]
          split_ifs with hBirth hDeath
          · by_cases hBad : ξ t < P t
            · simpa [hEq] using hMbad t hEq hBad
            · by_cases hGood : 1 - Q t ≤ ξ t
              · rw [hMgood t hEq hGood]
                omega
              · have hMid := hMmiddle t hEq
                  (le_of_not_gt hBad) (lt_of_not_ge hGood)
                omega
          · have hGood : 1 - Q t ≤ ξ t := by
              have := hD2 t
              linarith
            rw [hMgood t hEq hGood, hEq]
          · by_cases hGood : 1 - Q t ≤ ξ t
            · rw [hMgood t hEq hGood, hEq]
              omega
            · have hNotBirth : p t ≤ ξ t := le_of_not_gt hBirth
              have hMid := hMmiddle t hEq
                ((hD1 t).trans hNotBirth) (lt_of_not_ge hGood)
              simpa [hEq] using hMid
        have hJnext : J (t + 1) ≤ B (t + 1) := by
          rw [hJ t hEq, hB t]
          split_ifs with hBad hBirth
          · omega
          · have := hD1 t
            linarith
          · omega
          · exact ih.2
        exact ⟨hMnext, hJnext⟩
      · have hLt : M t < N t := lt_of_le_of_ne ih.1 hEq
        obtain ⟨hMf, hJf⟩ := hFreeze t hLt
        have hMnext : M (t + 1) ≤ N (t + 1) := by
          rw [hMf, hN t]
          split_ifs <;> omega
        have hJnext : J (t + 1) ≤ B (t + 1) := by
          rw [hJf, hB t]
          split_ifs <;> omega
        exact ⟨hMnext, hJnext⟩

/-- A delayed-threshold tail consequence of a stochastic domination relation. -/
theorem lemma_delayed_coupling_tail_transfer
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → Nat) (τ : Nat → Nat)
    (_hτ : Monotone τ)
    (hτle : ∀ t : Nat, τ t ≤ t)
    (hBase : StochDominates μ X Y) :
    ∀ t : Nat, μ {ω | t ≤ X ω} ≤ μ {ω | τ t ≤ Y ω} := by
  intro t
  exact (hBase t).trans (measure_mono fun ω hω => (hτle t).trans hω)

/-- Construction of a nice dominating chain for LV systems with `γ = 0`.
    Paper: Section 4.2, Lemma at line 603. -/
theorem lemma_domination
    (v : LVVariant)
    (params : LVParams)
    (hAlpha : 0 < effectiveGoodRate v params)
    (_hGamma0 : params.gamma0 = 0)
    (_hGamma1 : params.gamma1 = 0) :
    ∃ N : NiceChain, IsDominatingChain N.toBirthDeathChain (lvEventProfile v params) := by
  set α := params.alpha0 + params.alpha1
  set αgood := effectiveGoodRate v params
  set θ := params.beta + params.delta
  have hα_pos : 0 < α := by
    cases v with
    | selfDestructive =>
        simpa [effectiveGoodRate, αgood, α] using hAlpha
    | nonSelfDestructive =>
        have h0 : 0 < params.alpha0 := lt_of_lt_of_le hAlpha (min_le_left _ _)
        have h1 : 0 < params.alpha1 := lt_of_lt_of_le hAlpha (min_le_right _ _)
        dsimp [α]
        linarith
  have hαgood_pos : 0 < αgood := hAlpha
  have hαgood_le_α : αgood ≤ α := by
    cases v with
    | selfDestructive => simp [αgood, α, effectiveGoodRate]
    | nonSelfDestructive =>
        dsimp [αgood, α, effectiveGoodRate]
        nlinarith [min_le_left params.alpha0 params.alpha1,
          min_le_right params.alpha0 params.alpha1]
  have hθ_nn : 0 ≤ θ := by
    dsimp [θ]
    linarith [params.beta_nonneg, params.delta_nonneg]
  let p : Nat → Real := fun n => if n = 0 then 0 else θ / (α * (n : Real) + θ)
  let q : Nat → Real := fun n => if n = 0 then 0 else αgood / (α + 2 * θ)
  have hp_nonneg : ∀ n, 0 ≤ p n := by
    intro n
    by_cases hn : n = 0
    · simp only [p]; subst hn; norm_num
    · simp only [p, if_neg hn]; positivity
  have hq_nonneg : ∀ n, 0 ≤ q n := by
    intro n
    by_cases hn : n = 0
    · simp only [q]; subst hn; norm_num
    · simp only [q, if_neg hn]; positivity
  have hpq_le_one : ∀ n, p n + q n ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp only [p, q]; subst hn; norm_num
    · have hcore := pq_cross_mul hα_pos hαgood_le_α hθ_nn
        (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)) hαgood_pos.le
      have hden1 : 0 < α * (n : Real) + θ := by positivity
      have hden2 : 0 < α + 2 * θ := by positivity
      have hdenmul : 0 < (α * (n : Real) + θ) * (α + 2 * θ) := by positivity
      have hsum :
          θ / (α * (n : Real) + θ) + αgood / (α + 2 * θ) ≤ 1 := by
        have hsum' :
            θ / (α * (n : Real) + θ) + αgood / (α + 2 * θ) =
              (θ * (α + 2 * θ) + αgood * (α * (n : Real) + θ)) /
                ((α * (n : Real) + θ) * (α + 2 * θ)) := by
          field_simp [hden1.ne', hden2.ne']
        rw [hsum']
        have : (θ * (α + 2 * θ) + αgood * (α * (n : Real) + θ)) /
            ((α * (n : Real) + θ) * (α + 2 * θ)) ≤
            ((α * (n : Real) + θ) * (α + 2 * θ)) /
              ((α * (n : Real) + θ) * (α + 2 * θ)) := by
          exact div_le_div_of_nonneg_right hcore (le_of_lt hdenmul)
        simpa [hdenmul.ne'] using this
      simpa [p, q, hn] using hsum
  let bd : BirthDeathChain :=
    { p := p
      q := q
      p_nonneg := hp_nonneg
      q_nonneg := hq_nonneg
      pq_le_one := hpq_le_one
      absorb_zero := by simp [p, q] }
  let C : Real := θ / α + 1
  let D : Real := αgood / (α + 2 * θ)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hp_le : ∀ n, 0 < n → bd.p n ≤ C / (n : Real) := by
    intro n hn
    have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
    have hnR_pos : 0 < (n : Real) := by exact_mod_cast hn
    have hden : 0 < α * (n : Real) + θ := by positivity
    simp only [bd, p, if_neg hn_ne]
    have hstep : θ / (α * (n : Real) + θ) ≤ θ / (α * (n : Real)) := by
      apply div_le_div_of_nonneg_left hθ_nn
      · positivity
      · nlinarith [hθ_nn]
    have hcalc : θ / (α * (n : Real)) = (θ / α) / (n : Real) := by
      field_simp [hα_pos.ne', hnR_pos.ne']
    calc
      θ / (α * (n : Real) + θ) ≤ θ / (α * (n : Real)) := hstep
      _ = (θ / α) / (n : Real) := hcalc
      _ ≤ ((θ / α) + 1) / (n : Real) := by
        have : (θ / α) ≤ (θ / α) + 1 := by linarith
        exact div_le_div_of_nonneg_right this (by positivity)
      _ = C / (n : Real) := by rfl
  have hq_ge : ∀ n, 0 < n → D ≤ bd.q n := by
    intro n hn
    have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
    simp [bd, q, D, hn_ne]
  let nc : NiceChain :=
    { toBirthDeathChain := bd
      C := C
      D := D
      C_pos := hC_pos
      D_pos := hD_pos
      p_le := hp_le
      q_ge := hq_ge }
  refine ⟨nc, ?_⟩
  constructor
  · intro a b
    by_cases hmin0 : Nat.min a b = 0
    · have hab0 : a = 0 ∨ b = 0 := (nat_min_eq_zero).1 hmin0
      simp only [lvEventProfile, Nat.min_eq_zero_iff, hab0, ↓reduceIte, hmin0, le_refl, p, nc, bd]
    · have hminpos : 0 < Nat.min a b := Nat.pos_of_ne_zero hmin0
      have hab_pos := nat_min_pos hminpos
      rcases hab_pos with ⟨ha1, hb1⟩
      have hdenL : 0 < α * (a : Real) * (b : Real) + θ * ((a : Real) + (b : Real)) := by
        positivity
      rcases lt_trichotomy a b with hab | rfl | hba
      · have hmin : Nat.min a b = a := Nat.min_eq_left hab.le
        have hnba : ¬b < a := Nat.not_lt_of_ge hab.le
        have ha_ne : a ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha1)
        have hb_ne : b ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb1)
        have hdenR : 0 < α * (a : Real) + θ := by positivity
        rw [hmin]
        simp only [lvEventProfile, Nat.min_eq_zero_iff, ha_ne, hb_ne, or_self,
          ↓reduceIte, hab, hnba, p, nc, bd]
        apply (div_le_div_iff₀ hdenL hdenR).2
        simpa [θ, mul_comm, mul_left_comm, mul_assoc, add_comm] using
          (d1_cross_mul (a := (b : Real)) (b := (a : Real))
            (by dsimp [θ]) params.beta_nonneg params.delta_nonneg
            hα_pos.le (by positivity) (by positivity) (by exact_mod_cast hab.le))
      · have ha_ne : a ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha1)
        simp only [Nat.min_self, lvEventProfile, Nat.min_eq_zero_iff,
          ha_ne, or_self, ↓reduceIte, lt_self_iff_false, p, nc, bd]
        positivity
      · have hmin : Nat.min a b = b := Nat.min_eq_right hba.le
        have ha_ne : a ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one ha1)
        have hb_ne : b ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hb1)
        have hdenR : 0 < α * (b : Real) + θ := by positivity
        rw [hmin]
        simp only [lvEventProfile, Nat.min_eq_zero_iff, ha_ne, hb_ne, or_self,
          ↓reduceIte, hba, p, nc, bd]
        exact (div_le_div_iff₀ hdenL hdenR).2
          (d1_cross_mul (a := (a : Real)) (b := (b : Real))
            (by dsimp [θ]) params.beta_nonneg params.delta_nonneg hα_pos.le
            (by positivity) (by positivity) (by exact_mod_cast hba.le))
  · intro a b
    by_cases hmin0 : Nat.min a b = 0
    · have hab0 : a = 0 ∨ b = 0 := (nat_min_eq_zero).1 hmin0
      simp only [hmin0, ↓reduceIte, lvEventProfile, Nat.min_eq_zero_iff, hab0, le_refl, q, nc, bd]
    · have hminpos : 0 < Nat.min a b := Nat.pos_of_ne_zero hmin0
      have hab_pos := nat_min_pos hminpos
      rcases hab_pos with ⟨ha1, hb1⟩
      have haR1 : (1 : Real) ≤ (a : Real) := Nat.one_le_cast.mpr ha1
      have hbR1 : (1 : Real) ≤ (b : Real) := Nat.one_le_cast.mpr hb1
      have hab0 : ¬ (a = 0 ∨ b = 0) := by
        intro h
        exact hmin0 ((nat_min_eq_zero).2 h)
      have hdenL : 0 < α + 2 * θ := by positivity
      have hdenR : 0 < α * (a : Real) * (b : Real) + θ * ((a : Real) + (b : Real)) := by
        positivity
      simp only [Nat.min_eq_zero_iff, hab0, ↓reduceIte, lvEventProfile, ge_iff_le, q, nc, bd]
      refine (div_le_div_iff₀ hdenL hdenR).2 ?_
      have haux : θ * ((a : Real) + (b : Real)) ≤ 2 * θ * (a : Real) * (b : Real) :=
        d2_ineq hθ_nn haR1 hbR1
      nlinarith [haux, hαgood_pos.le]

/-- Every nice chain becomes extinct almost surely from every finite start. -/
lemma niceChain_extinction_almost_sure
    (N : NiceChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N.toBirthDeathChain)]
    (n : Nat) :
    bdPathMeasure N.toBirthDeathChain n {ω | extinctionTime ω = ⊤} = 0 := by
  obtain ⟨nDrift, hDrift⟩ := nice_drift_neg N
  have hDrift' :
      ∀ m, nDrift ≤ m → 0 < m →
        N.toBirthDeathChain.p m - N.toBirthDeathChain.q m ≤ -(N.D / 2) := by
    intro m hm hmp
    have h := hDrift m hm hmp
    linarith
  exact bd_extinction_almost_sure N.toBirthDeathChain
    (N.D / 2) (half_pos N.D_pos) nDrift hDrift'
    N.D N.D_pos N.q_ge n

/-- Before consensus time, the path has not reached consensus. -/
private lemma before_consensus_not_reached
    (ω : Nat → PopState) (τ : Nat)
    (hτ : consensusTime ω = ↑τ) (t : Nat) (ht : t < τ) :
    ¬reachedConsensus (ω t) :=
  ((consensusTime_eq_coe_iff ω τ).mp hτ).2 t ht

/-- Before consensus time, both species have positive population. -/
private lemma before_consensus_min_pos
    (ω : Nat → PopState) (τ : Nat)
    (hτ : consensusTime ω = ↑τ) (t : Nat) (ht : t < τ) :
    0 < Nat.min (ω t).1 (ω t).2 := by
  have hne := before_consensus_not_reached ω τ hτ t ht
  simp only [reachedConsensus, not_or] at hne
  exact Nat.lt_min.mpr ⟨Nat.pos_of_ne_zero hne.1, Nat.pos_of_ne_zero hne.2⟩

/-- badGapCountUpTo decomposes at t+1 (bad gap case). -/
private lemma badGapCountUpTo_succ_bad (ω : Nat → PopState) (t : Nat)
    (h : isBadGapStep ω t) :
    badGapCountUpTo ω (t + 1) = badGapCountUpTo ω t + 1 := by
  classical
  change Finset.sum (Finset.range (t + 1)) (fun i => if isBadGapStep ω i then 1 else 0)
    = Finset.sum (Finset.range t) (fun i => if isBadGapStep ω i then 1 else 0) + 1
  rw [Finset.sum_range_succ, if_pos h]

/-- badGapCountUpTo decomposes at t+1 (not bad gap case). -/
private lemma badGapCountUpTo_succ_notbad (ω : Nat → PopState) (t : Nat)
    (h : ¬isBadGapStep ω t) :
    badGapCountUpTo ω (t + 1) = badGapCountUpTo ω t := by
  classical
  change Finset.sum (Finset.range (t + 1)) (fun i => if isBadGapStep ω i then 1 else 0)
    = Finset.sum (Finset.range t) (fun i => if isBadGapStep ω i then 1 else 0)
  rw [Finset.sum_range_succ, if_neg h, add_zero]

/-- Gap invariant: on gap-bounded paths, gap(t) + badGapCountUpTo(t) ≥ gap(0)
    for all t ≤ consensus time. This is the core combinatorial fact used in the
    gap argument for majority consensus. -/
private lemma gap_invariant_le_consensus
    (a b : Nat) (ω : Nat → PopState)
    (_hω0 : ω 0 = (a, b))
    (hGapBound : ∀ t : Nat, Nat.min (ω t).1 (ω t).2 > 0 →
      gap (ω (t + 1)) = gap (ω t) - 1 ∨ gap (ω (t + 1)) = gap (ω t) ∨
      gap (ω (t + 1)) = gap (ω t) + 1)
    (τ : Nat) (hτ : consensusTime ω = ↑τ) :
    ∀ t : Nat, t ≤ τ →
      (gap (ω 0) : Int) ≤ gap (ω t) + ↑(badGapCountUpTo ω t) := by
  classical
  intro t ht
  induction t with
  | zero => simp [badGapCountUpTo]
  | succ t ih =>
    have ht_lt : t < τ := Nat.lt_of_succ_le ht
    have hmin := before_consensus_min_pos ω τ hτ t ht_lt
    have ih_prev := ih (le_of_lt ht_lt)
    have hchange := hGapBound t hmin
    rcases hchange with h | h | h
    · -- gap decreases by 1: bad gap step
      have hBad : isBadGapStep ω t := ⟨hmin, h⟩
      rw [badGapCountUpTo_succ_bad ω t hBad]; push_cast; linarith
    · -- gap stays same: not a bad gap step
      have hNotBad : ¬ isBadGapStep ω t := by
        intro ⟨_, hgap⟩; linarith [h, hgap]
      rw [badGapCountUpTo_succ_notbad ω t hNotBad]; linarith
    · -- gap increases by 1: not a bad gap step
      have hNotBad : ¬ isBadGapStep ω t := by
        intro ⟨_, hgap⟩; linarith [h, hgap]
      rw [badGapCountUpTo_succ_notbad ω t hNotBad]; linarith

/-- Gap argument: on gap-bounded paths starting at (a,b) with a > b > 0,
    if consensus is reached and badGapCount < a - b, then the majority wins. -/
private lemma gap_majority_argument
    (a b : Nat) (ω : Nat → PopState) (hab : b < a)
    (hω0 : ω 0 = (a, b))
    (hGapBound : ∀ t : Nat, Nat.min (ω t).1 (ω t).2 > 0 →
      gap (ω (t + 1)) = gap (ω t) - 1 ∨ gap (ω (t + 1)) = gap (ω t) ∨
      gap (ω (t + 1)) = gap (ω t) + 1)
    (τ : Nat) (hτ : consensusTime ω = ↑τ)
    (hBadGap : badGapCountBeforeConsensus ω < a - b) :
    majorityConsensusEvent (a, b) ω := by
  -- Step 1: gap(τ) > 0 from invariant
  have hInv := gap_invariant_le_consensus a b ω hω0 hGapBound τ hτ τ le_rfl
  have hgap0 : gap (ω 0) = (a : Int) - (b : Int) := by simp [gap, hω0]
  rw [hgap0] at hInv
  have hBadCount : badGapCountBeforeConsensus ω = badGapCountUpTo ω τ := by
    simp [badGapCountBeforeConsensus, hτ]
  have hgap_pos : 0 < gap (ω τ) := by
    have : (badGapCountUpTo ω τ : Int) < (a : Int) - (b : Int) := by
      rw [← hBadCount]; omega
    linarith
  -- Step 2: at consensus, one species is 0
  have hCons := reachedConsensus_at_consensusTime' ω τ hτ
  -- Step 3: gap > 0 means species 0 wins
  simp only [reachedConsensus] at hCons
  rcases hCons with h1eq0 | h2eq0
  · -- (ω τ).1 = 0: gap = -(ω τ).2 ≤ 0, contradicting gap > 0
    exfalso
    simp only [gap] at hgap_pos
    omega
  · -- (ω τ).2 = 0: species 0 wins
    have h1pos : 0 < (ω τ).1 := by simp [gap] at hgap_pos; omega
    have hMaj : species0Majority (a, b) := by simp [species0Majority]; omega
    simp only [majorityConsensusEvent, hτ]
    left
    exact ⟨hMaj, h1pos, h2eq0⟩

/-- With γ=0, the LV kernel gap change is bounded by ±1 at each step
    when both species are positive. The kernel assigns measure 0 to
    states where the gap differs from the initial gap by more than 1.
    This is a kernel support property needed for the gap argument. -/
private lemma lvKernel_gap_support (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    (lvKernel v params) (a, b)
      {s : PopState | gap s ≠ gap (a, b) - 1 ∧
        gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 := by
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    simp [Measure.dirac_apply, gap]
  · -- The kernel is a weighted sum of Dirac measures. With γ=0, only transitions
    -- to (a±1,b), (a,b±1), and (a-1,b-1) [SD] have nonzero weight.
    -- All have gap change in {-1, 0, +1}.
    have ha_ne : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
    have hb_ne : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
    -- Each target state's gap is within 1 of gap(a,b)
    have hgap_birth0 : gap (a + 1, b) = gap (a, b) + 1 := by simp [gap]; omega
    have hgap_birth1 : gap (a, b + 1) = gap (a, b) - 1 := by simp [gap]; omega
    have hgap_death0 : gap (a - 1, b) = gap (a, b) - 1 := by simp [gap]; omega
    have hgap_death1 : gap (a, b - 1) = gap (a, b) + 1 := by simp [gap]; omega
    have hgap_inter_sd : gap (a - 1, b - 1) = gap (a, b) := by simp [gap]; omega
    -- Each target is NOT in the complement set
    have h_not_mem : ∀ s : PopState,
        (gap s = gap (a, b) - 1 ∨ gap s = gap (a, b) ∨ gap s = gap (a, b) + 1) →
        s ∉ {s : PopState | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧
          gap s ≠ gap (a, b) + 1} :=
      fun s h => by simp [Set.mem_setOf_eq]; tauto
    -- Now case split on variant and show each Dirac gives 0 to complement
    cases v with
    | nonSelfDestructive =>
      rw [lvKernel_nsd_apply params a b hφ]
      simp only [Measure.smul_apply, Measure.add_apply]
      -- Each Dirac measure applied to the complement is 0
      have h1 : Measure.dirac (a + 1, b)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inr (Or.inr hgap_birth0))]
      have h2 : Measure.dirac (a, b + 1)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inl hgap_birth1)]
      have h3 : Measure.dirac (a - 1, b)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inl hgap_death0)]
      have h4 : Measure.dirac (a, b - 1)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inr (Or.inr hgap_death1))]
      simp [h1, h2, h3, h4, hGamma0, hGamma1]
    | selfDestructive =>
      rw [lvKernel_sd_apply params a b hφ]
      simp only [Measure.smul_apply, Measure.add_apply]
      have h1 : Measure.dirac (a + 1, b)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inr (Or.inr hgap_birth0))]
      have h2 : Measure.dirac (a, b + 1)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inl hgap_birth1)]
      have h3 : Measure.dirac (a - 1, b)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inl hgap_death0)]
      have h4 : Measure.dirac (a, b - 1)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inr (Or.inr hgap_death1))]
      have h5 : Measure.dirac (a - 1, b - 1)
          {s | gap s ≠ gap (a, b) - 1 ∧ gap s ≠ gap (a, b) ∧ gap s ≠ gap (a, b) + 1} = 0 :=
        by rw [Measure.dirac_apply]; simp [h_not_mem _ (Or.inr (Or.inl hgap_inter_sd))]
      simp [h1, h2, h3, h4, h5, hGamma0, hGamma1]

/-- The gap-bounded hypothesis holds for every state (a,b) with both positive.
    Reformulated: the kernel maps any state to the set of gap-bounded successors
    with probability 1, i.e., the complement has measure 0. -/
private lemma lvKernel_gap_bounded_step (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    (s : PopState) :
    (lvKernel v params) s
      {s' : PopState | Nat.min s.1 s.2 > 0 →
        gap s' = gap s - 1 ∨ gap s' = gap s ∨ gap s' = gap s + 1}ᶜ = 0 := by
  by_cases hmin : Nat.min s.1 s.2 > 0
  · -- Both species positive: use lvKernel_gap_support
    have ha : 0 < s.1 := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hmin) (Nat.min_le_left _ _)
    have hb : 0 < s.2 := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hmin) (Nat.min_le_right _ _)
    have h := lvKernel_gap_support v params hGamma0 hGamma1 s.1 s.2 ha hb
    apply le_antisymm _ zero_le
    have heta : s = (s.1, s.2) := (Prod.mk.eta).symm
    calc (lvKernel v params) s {s' | ¬(Nat.min s.1 s.2 > 0 →
            gap s' = gap s - 1 ∨ gap s' = gap s ∨ gap s' = gap s + 1)}
        ≤ (lvKernel v params) (s.1, s.2) {s' | gap s' ≠ gap (s.1, s.2) - 1 ∧
            gap s' ≠ gap (s.1, s.2) ∧ gap s' ≠ gap (s.1, s.2) + 1} := by
          rw [heta]; apply measure_mono; intro s' hs'
          simp only [Set.mem_setOf_eq] at hs' ⊢
          push_neg at hs'
          exact hs'.2
      _ = 0 := h
  · -- One species zero: the hypothesis is vacuously true
    push_neg at hmin
    apply le_antisymm _ zero_le
    calc (lvKernel v params) s {s' | ¬(Nat.min s.1 s.2 > 0 →
            gap s' = gap s - 1 ∨ gap s' = gap s ∨ gap s' = gap s + 1)}
        ≤ (lvKernel v params) s ∅ := by
          apply measure_mono; intro s' hs'
          simp only [Set.mem_setOf_eq] at hs'
          push_neg at hs'
          exact absurd hs'.1 (by omega)
      _ = 0 := measure_empty

/-- Path-level gap-bounded property: at each step t, the event that the gap changes by
    more than ±1 while both species are positive has probability 0 under the LV path
    measure with γ=0.  Uses the joint lintegral formula to lift `lvKernel_gap_support`
    from a kernel property to a path property. -/
private lemma lvPathMeasure_gap_bounded_step_ae (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    (s0 : PopState)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] (t : ℕ) :
    lvPathMeasure v params s0
      {ω | Nat.min (ω t).1 (ω t).2 > 0 ∧
        gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
        gap (ω (t + 1)) ≠ gap (ω t) ∧
        gap (ω (t + 1)) ≠ gap (ω t) + 1} = 0 := by
  set μ := lvPathMeasure v params s0
  set K := lvKernel v params
  -- Define the "bad" set for each state s
  set Bad := fun (s : PopState) =>
    {s' : PopState | gap s' ≠ gap s - 1 ∧ gap s' ≠ gap s ∧ gap s' ≠ gap s + 1}
  -- Decompose the bad event by the state at time t
  have h_subset : {ω : ℕ → PopState | Nat.min (ω t).1 (ω t).2 > 0 ∧
      gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
      gap (ω (t + 1)) ≠ gap (ω t) ∧
      gap (ω (t + 1)) ≠ gap (ω t) + 1} ⊆
      ⋃ s : PopState, {ω | ω t = s} ∩
        {ω | Nat.min s.1 s.2 > 0 ∧ ω (t + 1) ∈ Bad s} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨ω t, rfl, hω⟩
  -- Each component has measure 0
  have h_zero : ∀ s : PopState,
      μ ({ω | ω t = s} ∩ {ω | Nat.min s.1 s.2 > 0 ∧ ω (t + 1) ∈ Bad s}) = 0 := by
    intro s
    by_cases hmin : Nat.min s.1 s.2 > 0
    · -- Both species positive: use joint lintegral + gap kernel support
      have ha : 0 < s.1 := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hmin) (Nat.min_le_left _ _)
      have hb : 0 < s.2 := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hmin) (Nat.min_le_right _ _)
      have hK_zero : K s (Bad s) = 0 := by
        have heta : s = (s.1, s.2) := (Prod.mk.eta).symm
        rw [heta]
        exact lvKernel_gap_support v params hGamma0 hGamma1 s.1 s.2 ha hb
      -- Define indicator functions for the joint lintegral
      let g₀ : PopState → ℝ≥0∞ := fun x => if x = s then 1 else 0
      let φ₀ : PopState → ℝ≥0∞ := fun y => if y ∈ Bad s then 1 else 0
      -- The joint lintegral ∫ g₀(ω t) · φ₀(ω(t+1)) dμ = 0
      suffices hjoint : ∫⁻ ω, g₀ (ω t) * φ₀ (ω (t + 1)) ∂μ = 0 by
        -- The set measure ≤ the joint lintegral
        apply le_antisymm _ zero_le
        calc μ ({ω | ω t = s} ∩ {ω | Nat.min s.1 s.2 > 0 ∧ ω (t + 1) ∈ Bad s})
            ≤ ∫⁻ ω, g₀ (ω t) * φ₀ (ω (t + 1)) ∂μ := by
              apply le_trans (measure_mono (Set.inter_subset_inter_right _
                (fun ω hω => hω.2)))
              -- μ({ω t = s} ∩ {ω(t+1) ∈ Bad s}) ≤ ∫ g₀·φ₀
              have hAB_meas : MeasurableSet ({ω : ℕ → PopState | ω t = s} ∩
                  {ω | ω (t + 1) ∈ Bad s}) := by
                apply MeasurableSet.inter
                · change MeasurableSet ((fun (ω : ℕ → PopState) => ω t) ⁻¹' {s})
                  exact (measurable_pi_apply t) (measurableSet_singleton s)
                · change MeasurableSet ((fun (ω : ℕ → PopState) => ω (t + 1)) ⁻¹' (Bad s))
                  exact (measurable_pi_apply (t + 1)) ((Set.to_countable _).measurableSet)
              calc μ ({ω | ω t = s} ∩ {ω | ω (t + 1) ∈ Bad s})
                  = ∫⁻ ω, ({ω : ℕ → PopState | ω t = s} ∩
                      {ω | ω (t + 1) ∈ Bad s}).indicator (fun _ => 1) ω ∂μ := by
                    rw [lintegral_indicator_const hAB_meas]; simp
                _ ≤ ∫⁻ ω, g₀ (ω t) * φ₀ (ω (t + 1)) ∂μ := by
                    apply lintegral_mono; intro ω
                    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq]
                    split_ifs with h
                    · obtain ⟨h1, h2⟩ := h; simp [g₀, φ₀, h1, h2]
                    · exact zero_le
          _ = 0 := hjoint
      -- Prove the joint lintegral = 0 via the joint formula + kernel bound
      change ∫⁻ ω, g₀ (ω t) * φ₀ (ω (t + 1))
        ∂(homogeneousPathMeasure (Measure.dirac s0) K) = 0
      rw [homogeneousPathMeasure_joint_lintegral K s0 t g₀ φ₀
        (measurable_of_countable _) (measurable_of_countable _)]
      -- ∫ g₀(x) · (∫ φ₀(y) dK(x)) dK^t(s₀) = 0
      -- Integrand is 0 for all x: either g₀(x)=0 (x≠s) or ∫φ₀ dK(s)=0 (x=s)
      simp only [show ∀ x, g₀ x * ∫⁻ y, φ₀ y ∂K x = 0 from fun x => by
        by_cases hx : x = s
        · rw [hx]; simp only [g₀, ↓reduceIte, one_mul]
          apply le_antisymm _ zero_le
          calc ∫⁻ y, φ₀ y ∂K s ≤ ∫⁻ y, (Bad s).indicator (fun _ => 1) y ∂K s := by
                apply lintegral_mono; intro y; simp only [φ₀, Set.indicator_apply]
                split_ifs <;> simp
            _ = K s (Bad s) := by
                rw [lintegral_indicator_const ((Set.to_countable _).measurableSet)]; simp
            _ = 0 := hK_zero
        · simp [g₀, hx], lintegral_zero]
    · -- min = 0: the condition min > 0 makes the set empty
      push_neg at hmin
      apply le_antisymm _ zero_le
      calc μ ({ω | ω t = s} ∩ {ω | Nat.min s.1 s.2 > 0 ∧ ω (t + 1) ∈ Bad s})
          ≤ μ ∅ := measure_mono (fun ω hω => absurd hω.2.1 (by omega))
        _ = 0 := measure_empty
  -- Countable union of null sets
  apply le_antisymm _ zero_le
  calc μ {ω | Nat.min (ω t).1 (ω t).2 > 0 ∧
        gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
        gap (ω (t + 1)) ≠ gap (ω t) ∧
        gap (ω (t + 1)) ≠ gap (ω t) + 1}
      ≤ μ (⋃ s : PopState, {ω | ω t = s} ∩
          {ω | Nat.min s.1 s.2 > 0 ∧ ω (t + 1) ∈ Bad s}) := measure_mono h_subset
    _ ≤ ∑' s, μ ({ω | ω t = s} ∩
          {ω | Nat.min s.1 s.2 > 0 ∧ ω (t + 1) ∈ Bad s}) := measure_iUnion_le _
    _ = 0 := ENNReal.tsum_eq_zero.mpr h_zero

/-- A model-independent finite reduction used by both upper-bound arguments:
apart from paths that never reach consensus, losing an initial strict majority
requires at least as many gap-decreasing steps as the initial gap. -/
theorem majorityConsensusProb_ge_one_sub_badGapTail
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (a b : Nat) (hab : b < a)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)]
    (hConsensus :
      lvPathMeasure v params (a, b)
        {ω | consensusTime ω = ⊤} = 0) :
    1 - badGapTail v params (a, b) (a - b) ≤
      majorityConsensusProb v params (a, b) := by
  let μ := lvPathMeasure v params (a, b)
  let MC : Set (ℕ → PopState) :=
    {ω | majorityConsensusEvent (a, b) ω}
  let EB : Set (ℕ → PopState) :=
    {ω | a - b ≤ badGapCountBeforeConsensus ω}
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold lvPathMeasure homogeneousPathMeasure
    infer_instance
  have hGapAE :
      ∀ᵐ ω ∂μ, ∀ t : ℕ, Nat.min (ω t).1 (ω t).2 > 0 →
        gap (ω (t + 1)) = gap (ω t) - 1 ∨
          gap (ω (t + 1)) = gap (ω t) ∨
          gap (ω (t + 1)) = gap (ω t) + 1 := by
    rw [ae_all_iff]
    intro t
    have hzero :=
      lvPathMeasure_gap_bounded_step_ae v params
        hGamma0 hGamma1 (a, b) t
    have hae :
        ∀ᵐ ω ∂μ, ¬(Nat.min (ω t).1 (ω t).2 > 0 ∧
          gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
          gap (ω (t + 1)) ≠ gap (ω t) ∧
          gap (ω (t + 1)) ≠ gap (ω t) + 1) := by
      rw [ae_iff]
      simpa only [μ, not_not] using hzero
    filter_upwards [hae] with ω hω hmin
    tauto
  have hInitialAE : ∀ᵐ ω ∂μ, ω 0 = (a, b) := by
    rw [ae_iff]
    have hmarg :
        μ.map (fun ω : ℕ → PopState => ω 0) =
          Measure.dirac (a, b) := by
      dsimp [μ]
      simp only [lvPathMeasure]
      exact homogeneousPathMeasure_marginal_zero
        (lvKernel v params) (Measure.dirac (a, b))
    calc
      μ {ω | ω 0 ≠ (a, b)} =
          μ ((fun ω : ℕ → PopState => ω 0) ⁻¹'
            {s | s ≠ (a, b)}) := rfl
      _ = μ.map (fun ω : ℕ → PopState => ω 0)
            {s | s ≠ (a, b)} := by
              symm
              exact Measure.map_apply (measurable_pi_apply 0)
                (DiscreteMeasurableSpace.forall_measurableSet _)
      _ = Measure.dirac (a, b) {s | s ≠ (a, b)} := by rw [hmarg]
      _ = 0 := by simp
  have hFiniteAE : ∀ᵐ ω ∂μ, consensusTime ω ≠ ⊤ := by
    rw [ae_iff]
    change μ {ω | ¬consensusTime ω ≠ ⊤} = 0
    rw [show {ω | ¬consensusTime ω ≠ ⊤} =
        {ω | consensusTime ω = ⊤} by
      ext ω
      simp]
    simpa only [μ] using hConsensus
  have hFailureAE : ∀ᵐ ω ∂μ, ω ∈ MCᶜ → ω ∈ EB := by
    filter_upwards [hGapAE, hInitialAE, hFiniteAE] with
      ω hGap hInitial hFinite
    intro hnotMC
    obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp hFinite
    by_contra hnotBad
    apply hnotMC
    exact gap_majority_argument a b ω hab hInitial hGap τ hτ.symm
      (Nat.lt_of_not_ge hnotBad)
  have hFail : μ MCᶜ ≤ μ EB :=
    measure_mono_ae hFailureAE
  have hMCmeas : MeasurableSet MC := by
    simpa only [MC] using
      measurableSet_majorityConsensusEvent (a, b)
  have hMCcomp : μ MC = 1 - μ MCᶜ := by
    have h := measure_compl hMCmeas.compl (measure_ne_top μ MCᶜ)
    simpa only [compl_compl, measure_univ] using h
  change 1 - μ EB ≤ μ MC
  rw [hMCcomp]
  exact tsub_le_tsub_left hFail 1

lemma one_lt_logScale_chain (n : ℕ) (hn : 2 ≤ n) :
    1 < logScale n := by
  unfold logScale
  have hthree : (3 : ℝ) ≤ n + 1 := by
    exact_mod_cast (show 3 ≤ n + 1 by omega)
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2
      Real.exp_one_lt_three
  exact hlog3.trans_le
    (Real.log_le_log (by norm_num) hthree)

lemma logSqScaleNat_cast_le_add_one_chain (n : ℕ) :
    (logSqScaleNat n : ℝ) ≤ logSqScale n + 1 := by
  unfold logSqScaleNat
  have hnonneg : 0 ≤ Int.ceil (logSqScale n) :=
    Int.ceil_nonneg (sq_nonneg _)
  rw [show (Int.toNat (Int.ceil (logSqScale n)) : ℝ) =
      (Int.ceil (logSqScale n) : ℝ) by
    exact_mod_cast Int.toNat_of_nonneg hnonneg]
  exact (Int.ceil_lt_add_one (logSqScale n)).le

lemma twice_poly_inv_succ_le_chain
    (n k : ℕ) (hn : 1 ≤ n) :
    ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ ≤
      ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
  let x : ℝ≥0∞ := n + 1
  have hx0 : x ≠ 0 := by simp [x]
  have hxtop : x ≠ ⊤ := by simp [x]
  have htwo : (2 : ℝ≥0∞) ≤ x := by
    dsimp [x]
    exact_mod_cast (show 2 ≤ n + 1 by omega)
  have hxeq : x = (↑(n + 1) : ℝ≥0∞) := by simp [x]
  rw [← hxeq]
  calc
    (x ^ (k + 1))⁻¹ + (x ^ (k + 1))⁻¹ =
        2 * (x ^ (k + 1))⁻¹ := by ring
    _ ≤ x * (x ^ (k + 1))⁻¹ := mul_le_mul_right' htwo _
    _ = x * x⁻¹ ^ (k + 1) := by rw [ENNReal.inv_pow]
    _ = x * (x⁻¹ ^ k * x⁻¹) := by rw [pow_succ]
    _ = x⁻¹ ^ k * (x * x⁻¹) := by ac_rfl
    _ = x⁻¹ ^ k := by rw [ENNReal.mul_inv_cancel hx0 hxtop, mul_one]
    _ = (x ^ k)⁻¹ := by rw [ENNReal.inv_pow]

lemma ennreal_poly_inv_eq_ofReal_chain (n k : ℕ) :
    ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ =
      ENNReal.ofReal (1 / (((n : ℝ) + 1) ^ k)) := by
  calc
    ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ =
        (ENNReal.ofReal ((n + 1 : ℕ) : ℝ) ^ k)⁻¹ := by
          rw [ENNReal.ofReal_natCast]
    _ = (ENNReal.ofReal ((((n + 1 : ℕ) : ℝ) ^ k)))⁻¹ := by
          rw [ENNReal.ofReal_pow (by positivity)]
    _ = ENNReal.ofReal (((((n + 1 : ℕ) : ℝ) ^ k))⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (pow_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ)) k)).symm
    _ = ENNReal.ofReal (1 / (((n : ℝ) + 1) ^ k)) := by
          norm_num [one_div]

end LVConsensus
