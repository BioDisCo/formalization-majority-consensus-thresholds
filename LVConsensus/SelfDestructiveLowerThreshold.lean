import LVConsensus.SelfDestructiveLower
import LVConsensus.LogIndividualEvents
import LVConsensus.NsdGapProof
import LVConsensus.KernelPathMap

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal BigOperators

namespace LVConsensus

/-!
# The corrected self-destructive lower threshold

The reaction history below records the first `K` demographic signs without
conditioning on the event that all `K` signs occur before consensus.  A
superharmonic completion probability then compares every surviving history
with an ordinary fair Rademacher walk.
-/

def sdClosingBit : LVReaction → Bool
  | .birth1 | .death0 => true
  | _ => false

private lemma not_individual_of_competitive
    (r : LVReaction) (hcomp : isCompetitiveReaction r) :
    ¬isIndividualReaction r := by
  cases r <;>
    simp_all [isIndividualReaction, isCompetitiveReaction]

def sdBitLevelEvent (d : ℝ) (K : ℕ) : Set (Fin K → Bool) :=
  {u | ∃ k ∈ Finset.range (K + 1),
    d ≤ ∑ i ∈ Finset.range k, finiteBitStep K u i}

lemma measurableSet_sdBitLevelEvent (d : ℝ) (K : ℕ) :
    MeasurableSet (sdBitLevelEvent d K) :=
  DiscreteMeasurableSpace.forall_measurableSet _

def sdPrefixSet (K j : ℕ) (u : Fin K → Bool)
    (E : Set (Fin K → Bool)) : Set (Fin K → Bool) :=
  {w | (∀ i : Fin K, i.val < j → w i = u i) ∧ w ∈ E}

lemma measurableSet_sdPrefixSet
    (K j : ℕ) (u : Fin K → Bool) (E : Set (Fin K → Bool)) :
    MeasurableSet (sdPrefixSet K j u E) :=
  DiscreteMeasurableSpace.forall_measurableSet _

noncomputable def sdCompletionPotential
    (K : ℕ) (E : Set (Fin K → Bool))
    (active : Bool) (j : ℕ) (u : Fin K → Bool) : ℝ≥0∞ :=
  if active ∧ j ≤ K then
    (2 : ℝ≥0∞) ^ j * uniformBits K (sdPrefixSet K j u E)
  else 0

private def setBit
    {K : ℕ} (u : Fin K → Bool) (j : Fin K) (b : Bool) :
    Fin K → Bool :=
  Function.update u j b

private lemma sdPrefixSet_succ_union
    (K j : ℕ) (hj : j < K) (u : Fin K → Bool)
    (E : Set (Fin K → Bool)) :
    sdPrefixSet K j u E =
      sdPrefixSet K (j + 1) (setBit u ⟨j, hj⟩ false) E ∪
        sdPrefixSet K (j + 1) (setBit u ⟨j, hj⟩ true) E := by
  classical
  ext w
  simp only [sdPrefixSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    by_cases hb : w ⟨j, hj⟩ = false
    · left
      refine ⟨?_, h.2⟩
      intro i hi
      by_cases hij : i.val = j
      · subst hij
        simp [setBit, hb]
      · have hil : i.val < j := by omega
        rw [h.1 i hil]
        have hine : i ≠ ⟨j, hj⟩ := by
          intro heq
          exact hij (congrArg Fin.val heq)
        simp [setBit, hine]
    · right
      have hb' : w ⟨j, hj⟩ = true := by
        cases hval : w ⟨j, hj⟩ <;> simp_all
      refine ⟨?_, h.2⟩
      intro i hi
      by_cases hij : i.val = j
      · subst hij
        simp [setBit, hb']
      · have hil : i.val < j := by omega
        rw [h.1 i hil]
        have hine : i ≠ ⟨j, hj⟩ := by
          intro heq
          exact hij (congrArg Fin.val heq)
        simp [setBit, hine]
  · rintro (h | h)
    · refine ⟨?_, h.2⟩
      intro i hi
      have := h.1 i (by omega)
      have hine : i ≠ ⟨j, hj⟩ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      simpa [setBit, hine] using this
    · refine ⟨?_, h.2⟩
      intro i hi
      have := h.1 i (by omega)
      have hine : i ≠ ⟨j, hj⟩ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      simpa [setBit, hine] using this

private lemma sdPrefixSet_succ_disjoint
    (K j : ℕ) (hj : j < K) (u : Fin K → Bool)
    (E : Set (Fin K → Bool)) :
    Disjoint
      (sdPrefixSet K (j + 1) (setBit u ⟨j, hj⟩ false) E)
      (sdPrefixSet K (j + 1) (setBit u ⟨j, hj⟩ true) E) := by
  classical
  rw [Set.disjoint_left]
  intro w h0 h1
  have h0j := h0.1 ⟨j, hj⟩ (by simp)
  have h1j := h1.1 ⟨j, hj⟩ (by simp)
  simp [setBit] at h0j h1j
  simp_all

lemma sdCompletionPotential_children
    (K j : ℕ) (hj : j < K) (u : Fin K → Bool)
    (E : Set (Fin K → Bool)) :
    sdCompletionPotential K E true (j + 1)
          (setBit u ⟨j, hj⟩ false) +
        sdCompletionPotential K E true (j + 1)
          (setBit u ⟨j, hj⟩ true) =
      2 * sdCompletionPotential K E true j u := by
  have hjle : j ≤ K := hj.le
  have hjsle : j + 1 ≤ K := by omega
  simp only [sdCompletionPotential, Bool.true_eq, true_and,
    hjle, hjsle, ↓reduceIte]
  rw [pow_succ]
  have hmeas0 :=
    measurableSet_sdPrefixSet K (j + 1)
      (setBit u ⟨j, hj⟩ false) E
  have hmeas1 :=
    measurableSet_sdPrefixSet K (j + 1)
      (setBit u ⟨j, hj⟩ true) E
  have hadd :=
    measure_union
      (sdPrefixSet_succ_disjoint K j hj u E) hmeas1
      (μ := uniformBits K)
  rw [← sdPrefixSet_succ_union K j hj u E] at hadd
  rw [hadd]
  ring

lemma sdCompletionPotential_at_full
    (K : ℕ) (u : Fin K → Bool) (E : Set (Fin K → Bool))
    (hu : u ∈ E) :
    sdCompletionPotential K E true K u = 1 := by
  classical
  have hprefix :
      sdPrefixSet K K u E = {u} := by
    ext w
    simp only [sdPrefixSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      apply funext
      intro i
      exact h.1 i i.isLt
    · intro h
      subst w
      exact ⟨fun _ _ => rfl, hu⟩
  simp only [sdCompletionPotential, Bool.true_eq, true_and, le_refl,
    ↓reduceIte, hprefix]
  rw [uniformBits_singleton]
  calc
    (2 : ℝ≥0∞) ^ K * (2⁻¹) ^ K =
        (2 * 2⁻¹) ^ K := by rw [← mul_pow]
    _ = 1 ^ K := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ = 1 := one_pow K

structure SdHistoryState (K : ℕ) where
  labeled : LabeledPopState
  history : Fin K → Bool
  count : ℕ
  active : Bool
  deriving DecidableEq, Repr, Countable

instance (K : ℕ) : MeasurableSpace (SdHistoryState K) := ⊤
instance (K : ℕ) : MeasurableSingletonClass (SdHistoryState K) := by
  infer_instance
instance (K : ℕ) : Nonempty (SdHistoryState K) :=
  ⟨⟨((0, 0), .idle), fun _ => false, 0, false⟩⟩

noncomputable def sdHistoryNext (K : ℕ) (x : SdHistoryState K)
    (z' : LabeledPopState) : SdHistoryState K := by
  classical
  exact
    if hdone : !x.active ∨ K ≤ x.count then
      { labeled := z', history := x.history,
        count := x.count, active := false }
    else if reachedConsensus x.labeled.1 then
      { labeled := z', history := x.history,
        count := x.count, active := false }

    else if hind : isIndividualReaction z'.2 then
      let j : Fin K := ⟨x.count, by omega⟩
      let u' := setBit x.history j (sdClosingBit z'.2)
      let c' := x.count + 1
      { labeled := z', history := u', count := c',
        active := decide (c' = K ∨ ¬reachedConsensus z'.1) }
    else if isCompetitiveReaction z'.2 then
      { labeled := z', history := x.history, count := x.count,
        active := decide (¬reachedConsensus z'.1) }
    else
      { labeled := z', history := x.history,
        count := x.count, active := false }

lemma sdHistoryNext_labeled
    (K : ℕ) (x : SdHistoryState K) (z' : LabeledPopState) :
    (sdHistoryNext K x z').labeled = z' := by
  classical
  unfold sdHistoryNext
  split_ifs <;> rfl

noncomputable def sdHistoryKernel
    (K : ℕ) (params : LVParams) :
    Kernel (SdHistoryState K) (SdHistoryState K) :=
  Kernel.ofFunOfCountable fun x =>
    (lvLabeledKernel .selfDestructive params x.labeled).map
      (sdHistoryNext K x)

instance sdHistoryKernel_isMarkovKernel
    (K : ℕ) (params : LVParams) :
    IsMarkovKernel (sdHistoryKernel K params) where
  isProbabilityMeasure x := by
    unfold sdHistoryKernel
    simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
    refine ⟨?_⟩
    rw [Measure.map_apply
      (measurable_of_countable (sdHistoryNext K x))
      MeasurableSet.univ]
    simp

noncomputable def sdHistoryPathMeasure
    (K : ℕ) (params : LVParams) (s0 : PopState) :
    Measure (ℕ → SdHistoryState K) :=
  homogeneousPathMeasure
    (Measure.dirac
      (⟨(s0, .idle), fun _ => false, 0, true⟩ :
        SdHistoryState K))
    (sdHistoryKernel K params)

lemma sdHistoryKernel_map_labeled
    (K : ℕ) (params : LVParams) (x : SdHistoryState K) :
    (sdHistoryKernel K params x).map SdHistoryState.labeled =
      lvLabeledKernel .selfDestructive params x.labeled := by
  unfold sdHistoryKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [Measure.map_map
    (measurable_of_countable SdHistoryState.labeled)
    (measurable_of_countable (sdHistoryNext K x))]
  have hcomp :
      SdHistoryState.labeled ∘ sdHistoryNext K x =
        (fun z : LabeledPopState => z) := by
    funext z
    exact sdHistoryNext_labeled K x z
  rw [hcomp]
  exact
    (Measure.map_id' :
      (lvLabeledKernel .selfDestructive params x.labeled).map
        (fun z => z) =
      lvLabeledKernel .selfDestructive params x.labeled)

theorem sdHistoryPathMeasure_map_labeled
    (K : ℕ) (params : LVParams) (s0 : PopState) :
    (sdHistoryPathMeasure K params s0).map
        (pathMap SdHistoryState.labeled) =
      lvLabeledPathMeasure .selfDestructive params s0 := by
  letI : Nonempty LabeledPopState := ⟨((0, 0), .idle)⟩
  unfold sdHistoryPathMeasure lvLabeledPathMeasure
  simpa using
    homogeneousPathMeasure_map_pathMap
      (sdHistoryKernel K params)
      (lvLabeledKernel .selfDestructive params)
      SdHistoryState.labeled
      (measurable_of_countable SdHistoryState.labeled)
      (sdHistoryKernel_map_labeled K params)
      (⟨(s0, .idle), fun _ => false, 0, true⟩ :
        SdHistoryState K)

def sdHistorySignedSum
    (K : ℕ) (x : SdHistoryState K) : ℝ :=
  ∑ i ∈ Finset.range x.count,
    finiteBitStep K x.history i

def sdHistoryGapConsistent
    (K : ℕ) (s0 : PopState) (x : SdHistoryState K) : Prop :=
  x.active = true →
    x.count ≤ K ∧
      (gap x.labeled.1 : ℝ) =
        (gap s0 : ℝ) - sdHistorySignedSum K x

lemma sdHistoryGapConsistent_initial
    (K : ℕ) (s0 : PopState) :
    sdHistoryGapConsistent K s0
      (⟨(s0, .idle), fun _ => false, 0, true⟩ :
        SdHistoryState K) := by
  intro _
  simp [sdHistorySignedSum]

private lemma sdHistorySignedSum_setBit_succ
    (K : ℕ) (x : SdHistoryState K) (hcount : x.count < K)
    (b : Bool) :
    sdHistorySignedSum K
        { labeled := x.labeled,
          history := setBit x.history ⟨x.count, hcount⟩ b,
          count := x.count + 1, active := true } =
      sdHistorySignedSum K x + (if b then 1 else -1) := by
  classical
  unfold sdHistorySignedSum
  rw [Finset.sum_range_succ]
  have hprefix :
      ∑ i ∈ Finset.range x.count,
          finiteBitStep K
            (setBit x.history ⟨x.count, hcount⟩ b) i =
        ∑ i ∈ Finset.range x.count,
          finiteBitStep K x.history i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hine : i ≠ x.count := by
      have hil := Finset.mem_range.mp hi
      omega
    have hfin :
        (⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hcount.le⟩ :
          Fin K) ≠ ⟨x.count, hcount⟩ := by
      intro heq
      exact hine (congrArg Fin.val heq)
    simp [finiteBitStep, Finset.mem_range.mp hi, hcount,
      setBit, hfin]
  rw [hprefix]
  simp [finiteBitStep, hcount, setBit]

private lemma sdReactionTarget_gap_individual
    (s : PopState) (r : LVReaction)
    (hopen : ¬reachedConsensus s)
    (hind : isIndividualReaction r) :
    (gap (lvReactionTarget .selfDestructive s r) : ℝ) =
      (gap s : ℝ) - (if sdClosingBit r then 1 else -1) := by
  rcases s with ⟨a, b⟩
  have ha : 0 < a := by
    simp only [reachedConsensus, not_or] at hopen
    exact Nat.pos_of_ne_zero hopen.1
  have hb : 0 < b := by
    simp only [reachedConsensus, not_or] at hopen
    exact Nat.pos_of_ne_zero hopen.2
  have hint :
      gap (lvReactionTarget .selfDestructive (a, b) r) =
        gap (a, b) - (if sdClosingBit r then 1 else -1) := by
    cases r <;>
      simp_all [isIndividualReaction, lvReactionTarget, sdClosingBit, gap] <;>
      omega
  exact_mod_cast hint

private lemma sdReactionTarget_gap_competitive
    (s : PopState) (r : LVReaction)
    (hopen : ¬reachedConsensus s)
    (hcomp : isCompetitiveReaction r) :
    (gap (lvReactionTarget .selfDestructive s r) : ℝ) =
      (gap s : ℝ) := by
  rcases s with ⟨a, b⟩
  have ha : 0 < a := by
    simp only [reachedConsensus, not_or] at hopen
    exact Nat.pos_of_ne_zero hopen.1
  have hb : 0 < b := by
    simp only [reachedConsensus, not_or] at hopen
    exact Nat.pos_of_ne_zero hopen.2
  have hint :
      gap (lvReactionTarget .selfDestructive (a, b) r) =
        gap (a, b) := by
    cases r <;>
      simp_all [isCompetitiveReaction, lvReactionTarget, gap] <;>
      omega
  exact_mod_cast hint

lemma sdHistoryNext_gap_consistent
    (K : ℕ) (s0 : PopState) (x : SdHistoryState K)
    (z' : LabeledPopState)
    (htarget :
      z'.1 =
        lvReactionTarget .selfDestructive x.labeled.1 z'.2)
    (hx : sdHistoryGapConsistent K s0 x) :
    sdHistoryGapConsistent K s0 (sdHistoryNext K x z') := by
  classical
  intro hnextActive
  have hdone : ¬(!x.active ∨ K ≤ x.count) := by
    intro h
    unfold sdHistoryNext at hnextActive
    rw [dif_pos h] at hnextActive
    simp at hnextActive
  have hopen : ¬reachedConsensus x.labeled.1 := by
    intro h
    unfold sdHistoryNext at hnextActive
    rw [dif_neg hdone, if_pos h] at hnextActive
    simp at hnextActive
  have hxActive : x.active = true := by
    cases h : x.active <;> simp_all
  have hcount : x.count < K := by
    simp only [hxActive, Bool.not_true, Bool.false_eq_true,
      false_or] at hdone
    omega
  have hxinv := hx hxActive
  by_cases hind : isIndividualReaction z'.2
  · have hnext :
        sdHistoryNext K x z' =
          { labeled := z',
            history :=
              setBit x.history ⟨x.count, hcount⟩
                (sdClosingBit z'.2),
            count := x.count + 1,
            active := decide
              (x.count + 1 = K ∨ ¬reachedConsensus z'.1) } := by
      unfold sdHistoryNext
      rw [dif_neg hdone, if_neg hopen, dif_pos hind]
    rw [hnext] at hnextActive ⊢
    refine ⟨?_, ?_⟩
    · change x.count + 1 ≤ K
      omega
    have hgap :=
      sdReactionTarget_gap_individual
        x.labeled.1 z'.2 hopen hind
    have hsum :=
      sdHistorySignedSum_setBit_succ K x hcount
        (sdClosingBit z'.2)
    have hsum' :
        sdHistorySignedSum K
            { labeled := z',
              history :=
                setBit x.history ⟨x.count, hcount⟩
                  (sdClosingBit z'.2),
              count := x.count + 1,
              active := decide
                (x.count + 1 = K ∨
                  ¬reachedConsensus z'.1) } =
          sdHistorySignedSum K x +
            (if sdClosingBit z'.2 then 1 else -1) := by
      change
        sdHistorySignedSum K
            { labeled := x.labeled,
              history :=
                setBit x.history ⟨x.count, hcount⟩
                  (sdClosingBit z'.2),
              count := x.count + 1,
              active := true } =
          sdHistorySignedSum K x +
            (if sdClosingBit z'.2 then 1 else -1)
      exact hsum
    change
      (gap z'.1 : ℝ) =
        (gap s0 : ℝ) -
          sdHistorySignedSum K
            { labeled := z',
              history :=
                setBit x.history ⟨x.count, hcount⟩
                  (sdClosingBit z'.2),
              count := x.count + 1,
              active := decide
                (x.count + 1 = K ∨
                  ¬reachedConsensus z'.1) }
    calc
      (gap z'.1 : ℝ) =
          (gap x.labeled.1 : ℝ) -
            (if sdClosingBit z'.2 then 1 else -1) := by
        rw [htarget]
        exact hgap
      _ =
          (gap s0 : ℝ) - sdHistorySignedSum K x -
            (if sdClosingBit z'.2 then 1 else -1) := by
        rw [hxinv.2]
      _ =
          (gap s0 : ℝ) -
            sdHistorySignedSum K
              { labeled := z',
                history :=
                  setBit x.history ⟨x.count, hcount⟩
                    (sdClosingBit z'.2),
                count := x.count + 1,
                active := decide
                  (x.count + 1 = K ∨
                    ¬reachedConsensus z'.1) } := by
        rw [hsum']
        ring
  · by_cases hcomp : isCompetitiveReaction z'.2
    · have hnext :
          sdHistoryNext K x z' =
            { labeled := z', history := x.history,
              count := x.count,
              active := decide (¬reachedConsensus z'.1) } := by
        unfold sdHistoryNext
        rw [dif_neg hdone, if_neg hopen, dif_neg hind, if_pos hcomp]
      rw [hnext] at hnextActive ⊢
      refine ⟨hxinv.1, ?_⟩
      have hgap :=
        sdReactionTarget_gap_competitive
          x.labeled.1 z'.2 hopen hcomp
      rw [htarget, hgap, hxinv.2]
      rfl
    · unfold sdHistoryNext at hnextActive
      rw [dif_neg hdone, if_neg hopen, dif_neg hind,
        if_neg hcomp] at hnextActive
      simp at hnextActive

lemma sdHistoryKernel_ae_next
    (K : ℕ) (params : LVParams) (x : SdHistoryState K) :
    ∀ᵐ y ∂sdHistoryKernel K params x,
      y = sdHistoryNext K x y.labeled := by
  unfold sdHistoryKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [ae_map_iff
    (μ := lvLabeledKernel .selfDestructive params x.labeled)
    (measurable_of_countable (sdHistoryNext K x)).aemeasurable
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact Filter.Eventually.of_forall fun z' => by
    rw [sdHistoryNext_labeled]

lemma sdHistoryKernel_ae_reactionTarget
    (K : ℕ) (params : LVParams) (x : SdHistoryState K) :
    ∀ᵐ y ∂sdHistoryKernel K params x,
      y.labeled.1 =
        lvReactionTarget .selfDestructive
          x.labeled.1 y.labeled.2 := by
  unfold sdHistoryKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [ae_map_iff
    (μ := lvLabeledKernel .selfDestructive params x.labeled)
    (measurable_of_countable (sdHistoryNext K x)).aemeasurable
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  filter_upwards [
    lvLabeledKernel_ae_reactionTarget
      .selfDestructive params x.labeled] with z' hz'
  simpa only [sdHistoryNext_labeled] using hz'

lemma sdHistoryKernel_ae_relevant_before_consensus
    (K : ℕ) (params : LVParams)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (x : SdHistoryState K)
    (hopen : ¬reachedConsensus x.labeled.1) :
    ∀ᵐ y ∂sdHistoryKernel K params x,
      isIndividualReaction y.labeled.2 ∨
        isCompetitiveReaction y.labeled.2 := by
  have hφpos :
      0 < lvTotalPropensity params x.labeled.1 := by
    rcases hs : x.labeled.1 with ⟨a, b⟩
    have ha : 0 < a := by
      simp only [hs, reachedConsensus, not_or] at hopen
      exact Nat.pos_of_ne_zero hopen.1
    have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
    unfold lvTotalPropensity
    have hbirth : 0 < params.beta * (a : ℝ) := mul_pos hBetaPos haR
    have hnonneg1 : 0 ≤ params.beta * (b : ℝ) :=
      mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have hnonneg2 : 0 ≤ params.delta * (a : ℝ) :=
      mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have hnonneg3 : 0 ≤ params.delta * (b : ℝ) :=
      mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have hnonneg4 : 0 ≤ params.alpha0 * (a : ℝ) * b :=
      mul_nonneg
        (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    have hnonneg5 : 0 ≤ params.alpha1 * (a : ℝ) * b :=
      mul_nonneg
        (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    rw [hGamma0, hGamma1]
    simp only [zero_mul, add_zero]
    nlinarith
  have hφ : lvTotalPropensity params x.labeled.1 ≠ 0 :=
    ne_of_gt hφpos
  have hidle :
      ∀ᵐ z' ∂lvLabeledKernel .selfDestructive params x.labeled,
        z'.2 ≠ .idle := by
    rw [ae_iff]
    calc
      lvLabeledKernel .selfDestructive params x.labeled
          {z' | ¬z'.2 ≠ .idle} =
          lvLabeledKernel .selfDestructive params x.labeled
            {z' | z'.2 = .idle} := by
              congr 1
              ext z'
              simp
      _ = 0 := by
        rw [lvLabeledKernel_reaction_probability]
        simp [hφ, lvReactionWeight]
  unfold sdHistoryKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [ae_map_iff
    (μ := lvLabeledKernel .selfDestructive params x.labeled)
    (measurable_of_countable (sdHistoryNext K x)).aemeasurable
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  filter_upwards [
    hidle,
    lvLabeledKernel_ae_no_intra
      params hGamma0 hGamma1 x.labeled] with z' hidle' hno
  have hrelevant :
      isIndividualReaction z'.2 ∨
        isCompetitiveReaction z'.2 := by
    cases h : z'.2 <;>
      simp_all [isIndividualReaction, isCompetitiveReaction]
  simpa only [sdHistoryNext_labeled] using hrelevant

theorem sdHistoryPathMeasure_gap_consistent_ae
    (K : ℕ) (params : LVParams) (s0 : PopState) :
    ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
      ∀ t : ℕ, sdHistoryGapConsistent K s0 (ω t) := by
  let x0 : SdHistoryState K :=
    ⟨(s0, .idle), fun _ => false, 0, true⟩
  have htrans :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ∀ t : ℕ,
          ω (t + 1) =
            sdHistoryNext K (ω t) (ω (t + 1)).labeled := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y => y = sdHistoryNext K x y.labeled)
        (sdHistoryKernel_ae_next K params)
  have htarget :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ∀ t : ℕ,
          (ω (t + 1)).labeled.1 =
            lvReactionTarget .selfDestructive
              (ω t).labeled.1 (ω (t + 1)).labeled.2 := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y =>
          y.labeled.1 =
            lvReactionTarget .selfDestructive
              x.labeled.1 y.labeled.2)
        (sdHistoryKernel_ae_reactionTarget K params)
  have hinitial :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ω 0 = x0 := by
    rw [ae_iff]
    simpa only [sdHistoryPathMeasure, x0] using
      homogeneousPathMeasure_initial_ne_null
        (sdHistoryKernel K params) x0
  filter_upwards [htrans, htarget, hinitial] with ω hstep hvalid h0
  intro t
  induction t with
  | zero =>
      rw [h0]
      exact sdHistoryGapConsistent_initial K s0
  | succ t ih =>
      rw [hstep t]
      exact sdHistoryNext_gap_consistent
        K s0 (ω t) (ω (t + 1)).labeled
          (hvalid t) ih

private lemma labeledIndividualCountUpTo_succ
    (ζ : ℕ → LabeledPopState) (t : ℕ) :
    labeledIndividualCountUpTo ζ (t + 1) =
      labeledIndividualCountUpTo ζ t +
        if isIndividualReaction (ζ (t + 1)).2 then 1 else 0 := by
  classical
  unfold labeledIndividualCountUpTo
  rw [Finset.sum_range_succ]

private lemma measurable_labeledIndividualCountUpTo
    (t : ℕ) :
    Measurable
      (fun ζ : ℕ → LabeledPopState =>
        labeledIndividualCountUpTo ζ t) := by
  classical
  unfold labeledIndividualCountUpTo
  apply Finset.measurable_sum
  intro i _hi
  apply Measurable.ite
  · change MeasurableSet
      ((fun ζ : ℕ → LabeledPopState => (ζ (i + 1)).2) ⁻¹'
        {r | isIndividualReaction r})
    exact
      (measurable_snd.comp (measurable_pi_apply (i + 1)))
        (DiscreteMeasurableSpace.forall_measurableSet _)
  · exact measurable_const
  · exact measurable_const

private lemma measurableSet_labeledIndividualCountBefore_lt
    (K : ℕ) (hK : 0 < K) :
    MeasurableSet
      {ζ : ℕ → LabeledPopState |
        labeledIndividualCountBeforeConsensus ζ < K} := by
  let TopE : Set (ℕ → LabeledPopState) :=
    {ζ |
      consensusTime (forgetLVLabels ζ) = ⊤}
  let FinE : ℕ → Set (ℕ → LabeledPopState) := fun t =>
    {ζ |
      consensusTime (forgetLVLabels ζ) = (t : WithTop ℕ)} ∩
      {ζ | labeledIndividualCountUpTo ζ t < K}
  have hTop : MeasurableSet TopE := by
    have hEq :
        TopE =
          (⋃ t : ℕ,
            {ζ : ℕ → LabeledPopState |
              consensusTime (forgetLVLabels ζ) =
                (t : WithTop ℕ)})ᶜ := by
      ext ζ
      cases htime : consensusTime (forgetLVLabels ζ) with
      | top => simp [TopE, htime]
      | coe t => simp [TopE, htime]
    rw [hEq]
    apply MeasurableSet.compl
    apply MeasurableSet.iUnion
    intro t
    exact
      (measurableSet_consensusTime_eq_coe t).preimage
        measurable_forgetLVLabels
  have hFin : ∀ t, MeasurableSet (FinE t) := by
    intro t
    apply MeasurableSet.inter
    · exact
        (measurableSet_consensusTime_eq_coe t).preimage
          measurable_forgetLVLabels
    · exact
        (measurable_labeledIndividualCountUpTo t)
          (DiscreteMeasurableSpace.forall_measurableSet
            {n : ℕ | n < K})
  have hEq :
      {ζ : ℕ → LabeledPopState |
          labeledIndividualCountBeforeConsensus ζ < K} =
        TopE ∪ ⋃ t : ℕ, FinE t := by
    ext ζ
    cases htime : consensusTime (forgetLVLabels ζ) with
    | top =>
        simp [labeledIndividualCountBeforeConsensus,
          TopE, FinE, htime, hK]
    | coe t =>
        simp [labeledIndividualCountBeforeConsensus,
          TopE, FinE, htime]
  rw [hEq]
  exact hTop.union (MeasurableSet.iUnion hFin)

theorem sdHistoryPathMeasure_records_individuals_ae
    (K : ℕ) (params : LVParams)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) :
    ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
      ∀ t : ℕ,
        (∀ u : ℕ, u ≤ t →
          ¬reachedConsensus (ω u).labeled.1) →
        labeledIndividualCountUpTo
            (pathMap SdHistoryState.labeled ω) t < K →
          (ω t).active = true ∧
            (ω t).count =
              labeledIndividualCountUpTo
                (pathMap SdHistoryState.labeled ω) t := by
  let x0 : SdHistoryState K :=
    ⟨(s0, .idle), fun _ => false, 0, true⟩
  have htrans :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ∀ t : ℕ,
          ω (t + 1) =
            sdHistoryNext K (ω t) (ω (t + 1)).labeled := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y => y = sdHistoryNext K x y.labeled)
        (sdHistoryKernel_ae_next K params)
  have hrelevant :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ∀ t : ℕ,
          ¬reachedConsensus (ω t).labeled.1 →
            isIndividualReaction (ω (t + 1)).labeled.2 ∨
              isCompetitiveReaction (ω (t + 1)).labeled.2 := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y =>
          ¬reachedConsensus x.labeled.1 →
            isIndividualReaction y.labeled.2 ∨
              isCompetitiveReaction y.labeled.2)
        (fun x => by
          by_cases hopen : reachedConsensus x.labeled.1
          · exact Filter.Eventually.of_forall fun _ h => (h hopen).elim
          · filter_upwards [
              sdHistoryKernel_ae_relevant_before_consensus
                K params hBetaPos hGamma0 hGamma1 x hopen] with y hy
            exact fun _ => hy)
  have hinitial :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ω 0 = x0 := by
    rw [ae_iff]
    simpa only [sdHistoryPathMeasure, x0] using
      homogeneousPathMeasure_initial_ne_null
        (sdHistoryKernel K params) x0
  filter_upwards [htrans, hrelevant, hinitial] with ω hstep hrel h0
  intro t
  induction t with
  | zero =>
      intro _ hlt
      rw [h0]
      simp only [x0]
      simp [labeledIndividualCountUpTo]
  | succ t ih =>
      intro hno hlt
      have hnoPrev : ∀ u : ℕ, u ≤ t →
          ¬reachedConsensus (ω u).labeled.1 :=
        fun u hu => hno u (by omega)
      have hopen := hno t (Nat.le_succ t)
      have hrelStep := hrel t hopen
      have hcountSucc :=
        labeledIndividualCountUpTo_succ
          (pathMap SdHistoryState.labeled ω) t
      rcases hrelStep with hind | hcomp
      · have hprevLt :
          labeledIndividualCountUpTo
              (pathMap SdHistoryState.labeled ω) t < K := by
          rw [hcountSucc] at hlt
          simp only [pathMap, hind, ↓reduceIte] at hlt
          omega
        have hprev := ih hnoPrev hprevLt
        rw [hstep t]
        unfold sdHistoryNext
        have hdone :
            ¬(!(ω t).active ∨ K ≤ (ω t).count) := by
          simp only [hprev.1, Bool.not_true, Bool.false_eq_true,
            false_or, hprev.2]
          omega
        rw [dif_neg hdone, if_neg hopen, dif_pos hind]
        have hnextOpen := hno (t + 1) le_rfl
        simp only [hprev.2, pathMap, hnextOpen, not_false_eq_true,
          or_true, decide_true, hcountSucc, hind, ↓reduceIte]
        exact ⟨True.intro, True.intro⟩
      · have hprevLt :
          labeledIndividualCountUpTo
              (pathMap SdHistoryState.labeled ω) t < K := by
          rw [hcountSucc] at hlt
          have hnotind : ¬isIndividualReaction
              ((pathMap SdHistoryState.labeled ω) (t + 1)).2 := by
            simpa only [pathMap] using
              not_individual_of_competitive
                (ω (t + 1)).labeled.2 hcomp
          simp only [hnotind, ↓reduceIte, add_zero] at hlt
          exact hlt
        have hprev := ih hnoPrev hprevLt
        have hnotind :
            ¬isIndividualReaction (ω (t + 1)).labeled.2 := by
          exact not_individual_of_competitive
            (ω (t + 1)).labeled.2 hcomp
        rw [hstep t]
        unfold sdHistoryNext
        have hdone :
            ¬(!(ω t).active ∨ K ≤ (ω t).count) := by
          simp only [hprev.1, Bool.not_true, Bool.false_eq_true,
            false_or, hprev.2]
          omega
        rw [dif_neg hdone, if_neg hopen, dif_neg hnotind,
          if_pos hcomp]
        have hnextOpen := hno (t + 1) le_rfl
        simp only [hprev.2, pathMap, hnextOpen, not_false_eq_true,
          decide_true, hcountSucc, hnotind, ↓reduceIte, add_zero]
        exact ⟨True.intro, True.intro⟩

theorem sdHistory_individual_count_ge_implies_completed_ae
    (K : ℕ) (hK : 0 < K) (params : LVParams)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) :
    ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
      K ≤ labeledIndividualCountBeforeConsensus
          (pathMap SdHistoryState.labeled ω) →
        ∃ t : ℕ,
          (ω t).active = true ∧ (ω t).count = K := by
  let x0 : SdHistoryState K :=
    ⟨(s0, .idle), fun _ => false, 0, true⟩
  have htrans :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ∀ t : ℕ,
          ω (t + 1) =
            sdHistoryNext K (ω t) (ω (t + 1)).labeled := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y => y = sdHistoryNext K x y.labeled)
        (sdHistoryKernel_ae_next K params)
  filter_upwards [
    htrans,
    sdHistoryPathMeasure_records_individuals_ae
      K params hBetaPos hGamma0 hGamma1 s0] with ω hstep hrecords
  intro hcount
  cases hT :
      consensusTime
        (forgetLVLabels
          (pathMap SdHistoryState.labeled ω)) with
  | top =>
      simp only [labeledIndividualCountBeforeConsensus, hT] at hcount
      omega
  | coe T =>
      have hcountT :
          K ≤
            labeledIndividualCountUpTo
              (pathMap SdHistoryState.labeled ω) T := by
        unfold labeledIndividualCountBeforeConsensus at hcount
        rw [hT] at hcount
        exact hcount
      let P : ℕ → Prop := fun q =>
        K ≤ labeledIndividualCountUpTo
          (pathMap SdHistoryState.labeled ω) q
      have hex : ∃ q, P q := ⟨T, hcountT⟩
      let q := Nat.find hex
      have hq : P q := Nat.find_spec hex
      have hqle : q ≤ T := Nat.find_min' hex hcountT
      have hqpos : 0 < q := by
        by_contra h
        have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
        have hcount0 :
            labeledIndividualCountUpTo
                (pathMap SdHistoryState.labeled ω) q = 0 := by
          rw [hq0]
          simp [labeledIndividualCountUpTo]
        change K ≤
          labeledIndividualCountUpTo
            (pathMap SdHistoryState.labeled ω) q at hq
        rw [hcount0] at hq
        omega
      obtain ⟨p, hqeq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hqpos)
      have hqeq' : q = p + 1 := by omega
      have hq' : P (p + 1) := by
        rw [← hqeq']
        exact hq
      have hqle' : p + 1 ≤ T := by
        rw [← hqeq']
        exact hqle
      have hpq : p < p + 1 := Nat.lt_succ_self p
      have hpfind : p < Nat.find hex := by
        change p < q
        omega
      have hpnot : ¬P p := Nat.find_min hex hpfind
      have hpcount :
          labeledIndividualCountUpTo
              (pathMap SdHistoryState.labeled ω) p < K := by
        simpa only [P, not_le] using hpnot
      have hsucc :=
        labeledIndividualCountUpTo_succ
          (pathMap SdHistoryState.labeled ω) p
      have hind :
          isIndividualReaction
            ((pathMap SdHistoryState.labeled ω) (p + 1)).2 := by
        by_contra hnot
        simp only [hnot, ↓reduceIte, add_zero] at hsucc
        change K ≤
          labeledIndividualCountUpTo
            (pathMap SdHistoryState.labeled ω) (p + 1) at hq'
        rw [hsucc] at hq'
        omega
      have hpcountEq :
          labeledIndividualCountUpTo
              (pathMap SdHistoryState.labeled ω) p + 1 = K := by
        change K ≤
          labeledIndividualCountUpTo
            (pathMap SdHistoryState.labeled ω) (p + 1) at hq'
        rw [hsucc] at hq'
        simp only [hind, ↓reduceIte] at hq'
        omega
      have hfirst :=
        (consensusTime_eq_coe_iff
          (forgetLVLabels
            (pathMap SdHistoryState.labeled ω)) T).mp hT
      have hpT : p < T := by omega
      have hno : ∀ u : ℕ, u ≤ p →
          ¬reachedConsensus (ω u).labeled.1 := by
        intro u hu
        have :=
          hfirst.2 u (lt_of_le_of_lt hu hpT)
        simpa only [forgetLVLabels, pathMap] using this
      have hprev := hrecords p hno hpcount
      refine ⟨p + 1, ?_⟩
      rw [hstep p]
      unfold sdHistoryNext
      have hdone :
          ¬(!(ω p).active ∨ K ≤ (ω p).count) := by
        simp only [hprev.1, Bool.not_true, Bool.false_eq_true,
          false_or, hprev.2]
        omega
      have hopen : ¬reachedConsensus (ω p).labeled.1 :=
        hno p le_rfl
      have hind' :
          isIndividualReaction (ω (p + 1)).labeled.2 := by
        simpa only [pathMap] using hind
      have hnewcount : (ω p).count + 1 = K := by
        rw [hprev.2]
        exact hpcountEq
      rw [dif_neg hdone, if_neg hopen, dif_pos hind']
      simp only [hnewcount, true_or, decide_true]
      exact ⟨True.intro, True.intro⟩

def sdHistoryPrefixSum
    (K : ℕ) (u : Fin K → Bool) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, finiteBitStep K u i

def sdHistoryPrefixSafe
    (K : ℕ) (s0 : PopState) (x : SdHistoryState K) : Prop :=
  x.active = true →
    ∀ k : ℕ, k ≤ x.count →
      sdHistoryPrefixSum K x.history k < (gap s0 : ℝ)

private lemma sdHistoryPrefixSum_setBit_of_le
    (K : ℕ) (u : Fin K → Bool)
    (j k : ℕ) (hj : j < K) (hk : k ≤ j)
    (b : Bool) :
    sdHistoryPrefixSum K (setBit u ⟨j, hj⟩ b) k =
      sdHistoryPrefixSum K u k := by
  classical
  unfold sdHistoryPrefixSum
  apply Finset.sum_congr rfl
  intro i hi
  have hil : i < k := Finset.mem_range.mp hi
  have hij : i ≠ j := by omega
  have hfin :
      (⟨i, lt_of_lt_of_le hil (hk.trans hj.le)⟩ : Fin K) ≠
        ⟨j, hj⟩ := by
    intro heq
    exact hij (congrArg Fin.val heq)
  simp [finiteBitStep, lt_of_lt_of_le hil (hk.trans hj.le),
    setBit, hfin]

private lemma sdReactionTarget_gap_pos_of_individual
    (s : PopState) (r : LVReaction)
    (hopen : ¬reachedConsensus s)
    (hgap : 0 < gap s)
    (hind : isIndividualReaction r)
    (hnotdiag :
      ¬((lvReactionTarget .selfDestructive s r).1 =
          (lvReactionTarget .selfDestructive s r).2 ∧
        0 < (lvReactionTarget .selfDestructive s r).1)) :
    0 < gap (lvReactionTarget .selfDestructive s r) := by
  rcases s with ⟨a, b⟩
  have ha : 0 < a := by
    simp only [reachedConsensus, not_or] at hopen
    exact Nat.pos_of_ne_zero hopen.1
  have hb : 0 < b := by
    simp only [reachedConsensus, not_or] at hopen
    exact Nat.pos_of_ne_zero hopen.2
  cases r <;>
    simp_all [isIndividualReaction, lvReactionTarget, gap] <;>
    omega

lemma sdHistoryNext_prefix_safe
    (K : ℕ) (s0 : PopState) (x : SdHistoryState K)
    (z' : LabeledPopState)
    (htarget :
      z'.1 =
        lvReactionTarget .selfDestructive x.labeled.1 z'.2)
    (hxGap : sdHistoryGapConsistent K s0 x)
    (hxSafe : sdHistoryPrefixSafe K s0 x)
    (hnextNotDiag :
      ¬(z'.1.1 = z'.1.2 ∧ 0 < z'.1.1)) :
    sdHistoryPrefixSafe K s0 (sdHistoryNext K x z') := by
  classical
  intro hnextActive
  have hdone : ¬(!x.active ∨ K ≤ x.count) := by
    intro h
    unfold sdHistoryNext at hnextActive
    rw [dif_pos h] at hnextActive
    simp at hnextActive
  have hopen : ¬reachedConsensus x.labeled.1 := by
    intro h
    unfold sdHistoryNext at hnextActive
    rw [dif_neg hdone, if_pos h] at hnextActive
    simp at hnextActive
  have hxActive : x.active = true := by
    cases h : x.active <;> simp_all
  have hcount : x.count < K := by
    simp only [hxActive, Bool.not_true, Bool.false_eq_true,
      false_or] at hdone
    omega
  have hxSafe' := hxSafe hxActive
  by_cases hind : isIndividualReaction z'.2
  · have hnext :
        sdHistoryNext K x z' =
          { labeled := z',
            history :=
              setBit x.history ⟨x.count, hcount⟩
                (sdClosingBit z'.2),
            count := x.count + 1,
            active := decide
              (x.count + 1 = K ∨ ¬reachedConsensus z'.1) } := by
      unfold sdHistoryNext
      rw [dif_neg hdone, if_neg hopen, dif_pos hind]
    rw [hnext] at hnextActive ⊢
    intro k hk
    change k ≤ x.count + 1 at hk
    by_cases hkold : k ≤ x.count
    · rw [sdHistoryPrefixSum_setBit_of_le
        K x.history x.count k hcount hkold]
      exact hxSafe' k hkold
    · have hknew : k = x.count + 1 := by omega
      subst k
      have hcurGap : 0 < gap x.labeled.1 := by
        have hcur := hxGap hxActive
        have hprefix := hxSafe' x.count le_rfl
        change
          sdHistorySignedSum K x < (gap s0 : ℝ) at hprefix
        have hgapReal : (0 : ℝ) < gap x.labeled.1 := by
          rw [hcur.2]
          linarith
        exact_mod_cast hgapReal
      have hnextGap :
          0 <
            gap
              (lvReactionTarget .selfDestructive
                x.labeled.1 z'.2) :=
        sdReactionTarget_gap_pos_of_individual
          x.labeled.1 z'.2 hopen hcurGap hind
            (by simpa only [← htarget] using hnextNotDiag)
      have hnextGapReal :
          (0 : ℝ) < gap z'.1 := by
        rw [htarget]
        exact_mod_cast hnextGap
      have hnextActive' :
          (sdHistoryNext K x z').active = true := by
        rw [hnext]
        exact hnextActive
      have hnextCons :=
        sdHistoryNext_gap_consistent
          K s0 x z' htarget hxGap hnextActive'
      rw [hnext] at hnextCons
      change
        sdHistorySignedSum K
            { labeled := z',
              history :=
                setBit x.history ⟨x.count, hcount⟩
                  (sdClosingBit z'.2),
              count := x.count + 1,
              active := decide
                (x.count + 1 = K ∨
                  ¬reachedConsensus z'.1) } <
          (gap s0 : ℝ)
      linarith [hnextCons.2]
  · by_cases hcomp : isCompetitiveReaction z'.2
    · have hnext :
          sdHistoryNext K x z' =
            { labeled := z', history := x.history,
              count := x.count,
              active := decide (¬reachedConsensus z'.1) } := by
        unfold sdHistoryNext
        rw [dif_neg hdone, if_neg hopen, dif_neg hind, if_pos hcomp]
      rw [hnext] at hnextActive ⊢
      intro k hk
      exact hxSafe' k hk
    · unfold sdHistoryNext at hnextActive
      rw [dif_neg hdone, if_neg hopen, dif_neg hind,
        if_neg hcomp] at hnextActive
      simp at hnextActive

theorem sdHistoryPathMeasure_prefix_safe_until_diagonal_ae
    (K : ℕ) (params : LVParams) (a b : ℕ)
    (hb : 0 < b) (hab : b ≤ a) :
    ∀ᵐ ω ∂sdHistoryPathMeasure K params (a, b),
      ∀ t : ℕ,
        (∀ u : ℕ, u ≤ t →
          ¬((ω u).labeled.1.1 = (ω u).labeled.1.2 ∧
            0 < (ω u).labeled.1.1)) →
          sdHistoryPrefixSafe K (a, b) (ω t) := by
  let x0 : SdHistoryState K :=
    ⟨((a, b), .idle), fun _ => false, 0, true⟩
  have htrans :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params (a, b),
        ∀ t : ℕ,
          ω (t + 1) =
            sdHistoryNext K (ω t) (ω (t + 1)).labeled := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y => y = sdHistoryNext K x y.labeled)
        (sdHistoryKernel_ae_next K params)
  have htarget :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params (a, b),
        ∀ t : ℕ,
          (ω (t + 1)).labeled.1 =
            lvReactionTarget .selfDestructive
              (ω t).labeled.1 (ω (t + 1)).labeled.2 := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y =>
          y.labeled.1 =
            lvReactionTarget .selfDestructive
              x.labeled.1 y.labeled.2)
        (sdHistoryKernel_ae_reactionTarget K params)
  have hinitial :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params (a, b),
        ω 0 = x0 := by
    rw [ae_iff]
    simpa only [sdHistoryPathMeasure, x0] using
      homogeneousPathMeasure_initial_ne_null
        (sdHistoryKernel K params) x0
  filter_upwards [
    htrans, htarget, hinitial,
    sdHistoryPathMeasure_gap_consistent_ae
      K params (a, b)] with ω hstep hvalid h0 hgap
  intro t
  induction t with
  | zero =>
      intro hno
      rw [h0]
      intro _
      intro k hk
      have hk0 : k = 0 := by simp only [x0] at hk; omega
      subst k
      simp only [sdHistoryPrefixSum, Finset.range_zero,
        Finset.sum_empty]
      have hgapPos : 0 < gap (a, b) := by
        have hnotdiag := hno 0 le_rfl
        simp only [h0, x0] at hnotdiag
        simp only [gap]
        omega
      exact_mod_cast hgapPos
  | succ t ih =>
      intro hno
      rw [hstep t]
      apply sdHistoryNext_prefix_safe
        K (a, b) (ω t) (ω (t + 1)).labeled
          (hvalid t) (hgap t)
      · apply ih
        intro u hu
        exact hno u (by omega)
      · exact hno (t + 1) le_rfl

theorem sdHistory_completed_level_implies_diagonal_ae
    (K : ℕ) (params : LVParams) (a b : ℕ)
    (hb : 0 < b) (hab : b ≤ a) :
    ∀ᵐ ω ∂sdHistoryPathMeasure K params (a, b),
      (∃ t : ℕ,
          (ω t).active = true ∧
            (ω t).count = K ∧
              (ω t).history ∈
                sdBitLevelEvent ((a : ℝ) - b) K) →
        ∃ u : ℕ,
          (ω u).labeled.1.1 = (ω u).labeled.1.2 ∧
            0 < (ω u).labeled.1.1 := by
  filter_upwards [
    sdHistoryPathMeasure_prefix_safe_until_diagonal_ae
      K params a b hb hab] with ω hsafe
  rintro ⟨t, ht⟩
  by_contra hnot
  push_neg at hnot
  have hprefixSafe :=
    hsafe t (fun u _hu hdiag =>
      (not_lt_of_ge (hnot u hdiag.1)) hdiag.2)
  rcases ht with ⟨hactive, hcount, hlevel⟩
  have hsafeAt := hprefixSafe hactive
  rcases hlevel with ⟨k, hk, hcross⟩
  have hkK : k ≤ K := by
    have := Finset.mem_range.mp hk
    omega
  have hbelow := hsafeAt k (by simpa only [hcount] using hkK)
  change
    sdHistoryPrefixSum K (ω t).history k < (gap (a, b) : ℝ)
      at hbelow
  change
    (a : ℝ) - b ≤
      sdHistoryPrefixSum K (ω t).history k at hcross
  have hgapCast : (gap (a, b) : ℝ) = (a : ℝ) - b := by
    simp only [gap]
    push_cast
    ring
  rw [hgapCast] at hbelow
  linarith

private lemma sdCompletionPotential_active_le_true
    (K : ℕ) (E : Set (Fin K → Bool)) (active : Bool)
    (j : ℕ) (u : Fin K → Bool) :
    sdCompletionPotential K E active j u ≤
      sdCompletionPotential K E true j u := by
  cases active <;> simp [sdCompletionPotential]

private lemma sdCompletionPotential_next_individual_le
    (K : ℕ) (E : Set (Fin K → Bool))
    (x : SdHistoryState K) (z' : LabeledPopState)
    (hactive : x.active = true) (hcount : x.count < K)
    (hopen : ¬reachedConsensus x.labeled.1)
    (hind : isIndividualReaction z'.2) :
    sdCompletionPotential K E
        (sdHistoryNext K x z').active
        (sdHistoryNext K x z').count
        (sdHistoryNext K x z').history ≤
      sdCompletionPotential K E true (x.count + 1)
        (setBit x.history ⟨x.count, hcount⟩
          (sdClosingBit z'.2)) := by
  classical
  unfold sdHistoryNext
  simp only [hactive, Bool.not_true, Bool.false_eq_true, false_or,
    not_le.mpr hcount, hopen, hind, ↓reduceDIte]
  exact sdCompletionPotential_active_le_true K E _ _ _

private lemma sdCompletionPotential_next_competitive_le
    (K : ℕ) (E : Set (Fin K → Bool))
    (x : SdHistoryState K) (z' : LabeledPopState)
    (hactive : x.active = true) (hcount : x.count < K)
    (hopen : ¬reachedConsensus x.labeled.1)
    (hnotind : ¬isIndividualReaction z'.2)
    (hcomp : isCompetitiveReaction z'.2) :
    sdCompletionPotential K E
        (sdHistoryNext K x z').active
        (sdHistoryNext K x z').count
        (sdHistoryNext K x z').history ≤
      sdCompletionPotential K E true x.count x.history := by
  classical
  unfold sdHistoryNext
  simp only [hactive, Bool.not_true, Bool.false_eq_true, false_or,
    not_le.mpr hcount, hopen, hnotind, hcomp, ↓reduceDIte]
  exact sdCompletionPotential_active_le_true K E _ _ _

/-- Before `K` demographic reactions have been recorded, the fair-sign
completion probability is superharmonic.  If consensus occurs first, the
potential loses mass; this is the formal counterpart of completing the
unused signs by fresh independent fair signs. -/
lemma sdHistoryKernel_completion_superharmonic
    (K : ℕ) (E : Set (Fin K → Bool))
    (params : LVParams)
    (hBetaDelta : params.beta = params.delta)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (x : SdHistoryState K) :
    ∫⁻ y,
        sdCompletionPotential K E y.active y.count y.history
          ∂sdHistoryKernel K params x ≤
      sdCompletionPotential K E x.active x.count x.history := by
  classical
  let V : SdHistoryState K → ℝ≥0∞ :=
    fun y => sdCompletionPotential K E y.active y.count y.history
  have hV : Measurable V := measurable_of_countable V
  unfold sdHistoryKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [lintegral_map hV (measurable_of_countable (sdHistoryNext K x))]
  by_cases hdone : !x.active ∨ K ≤ x.count
  · have hnext :
        ∀ z' : LabeledPopState,
          V (sdHistoryNext K x z') = 0 := by
      intro z'
      unfold V sdHistoryNext
      rw [dif_pos hdone]
      simp [sdCompletionPotential]
    simp_rw [hnext]
    simp
  by_cases hopen : reachedConsensus x.labeled.1
  · have hnext :
        ∀ z' : LabeledPopState,
          V (sdHistoryNext K x z') = 0 := by
      intro z'
      unfold V sdHistoryNext
      rw [dif_neg hdone, if_pos hopen]
      simp [sdCompletionPotential]
    simp_rw [hnext]
    simp
  have hactive : x.active = true := by
    cases h : x.active <;> simp_all
  have hcount : x.count < K := by
    simp only [hactive, Bool.not_true, Bool.false_eq_true, false_or] at hdone
    omega
  rcases hlabel : x.labeled with ⟨⟨a, b⟩, old⟩
  have hopen' : ¬reachedConsensus (a, b) := by
    simpa only [hlabel] using hopen
  have ha : 0 < a := by
    simp only [reachedConsensus, not_or] at hopen'
    exact Nat.pos_of_ne_zero hopen'.1
  have hb : 0 < b := by
    simp only [reachedConsensus, not_or] at hopen'
    exact Nat.pos_of_ne_zero hopen'.2
  have hφpos : 0 < lvTotalPropensity params (a, b) := by
    have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
    have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    unfold lvTotalPropensity
    rw [hBetaDelta, hGamma0, hGamma1]
    nlinarith [params.delta_nonneg, params.alpha0_nonneg,
      params.alpha1_nonneg,
      mul_nonneg params.alpha0_nonneg haR.le,
      mul_nonneg (mul_nonneg params.alpha0_nonneg haR.le) hbR.le,
      mul_nonneg params.alpha1_nonneg haR.le,
      mul_nonneg (mul_nonneg params.alpha1_nonneg haR.le) hbR.le]
  have hφ : lvTotalPropensity params (a, b) ≠ 0 := ne_of_gt hφpos
  let Vcur := sdCompletionPotential K E true x.count x.history
  let Vfalse := sdCompletionPotential K E true (x.count + 1)
    (setBit x.history ⟨x.count, hcount⟩ false)
  let Vtrue := sdCompletionPotential K E true (x.count + 1)
    (setBit x.history ⟨x.count, hcount⟩ true)
  have hchildren : Vfalse + Vtrue = 2 * Vcur := by
    exact sdCompletionPotential_children
      K x.count hcount x.history E
  have hb0 :
      V (sdHistoryNext K x
        (lvReactionTarget .selfDestructive (a, b) .birth0, .birth0)) ≤
        Vfalse := by
    simpa [V, Vfalse, sdClosingBit] using
      sdCompletionPotential_next_individual_le K E x
        (lvReactionTarget .selfDestructive (a, b) .birth0, .birth0)
        hactive hcount hopen (by simp [isIndividualReaction])
  have hb1 :
      V (sdHistoryNext K x
        (lvReactionTarget .selfDestructive (a, b) .birth1, .birth1)) ≤
        Vtrue := by
    simpa [V, Vtrue, sdClosingBit] using
      sdCompletionPotential_next_individual_le K E x
        (lvReactionTarget .selfDestructive (a, b) .birth1, .birth1)
        hactive hcount hopen (by simp [isIndividualReaction])
  have hd0 :
      V (sdHistoryNext K x
        (lvReactionTarget .selfDestructive (a, b) .death0, .death0)) ≤
        Vtrue := by
    simpa [V, Vtrue, sdClosingBit] using
      sdCompletionPotential_next_individual_le K E x
        (lvReactionTarget .selfDestructive (a, b) .death0, .death0)
        hactive hcount hopen (by simp [isIndividualReaction])
  have hd1 :
      V (sdHistoryNext K x
        (lvReactionTarget .selfDestructive (a, b) .death1, .death1)) ≤
        Vfalse := by
    simpa [V, Vfalse, sdClosingBit] using
      sdCompletionPotential_next_individual_le K E x
        (lvReactionTarget .selfDestructive (a, b) .death1, .death1)
        hactive hcount hopen (by simp [isIndividualReaction])
  have hi0 :
      V (sdHistoryNext K x
        (lvReactionTarget .selfDestructive (a, b) .inter0, .inter0)) ≤
        Vcur := by
    simpa [V, Vcur] using
      sdCompletionPotential_next_competitive_le K E x
        (lvReactionTarget .selfDestructive (a, b) .inter0, .inter0)
        hactive hcount hopen (by simp [isIndividualReaction])
        (by simp [isCompetitiveReaction])
  have hi1 :
      V (sdHistoryNext K x
        (lvReactionTarget .selfDestructive (a, b) .inter1, .inter1)) ≤
        Vcur := by
    simpa [V, Vcur] using
      sdCompletionPotential_next_competitive_le K E x
        (lvReactionTarget .selfDestructive (a, b) .inter1, .inter1)
        hactive hcount hopen (by simp [isIndividualReaction])
        (by simp [isCompetitiveReaction])
  simp only [lvLabeledKernel, Kernel.ofFunOfCountable, Kernel.coe_mk,
    hφ, ↓reduceDIte, lvReactionWeight,
    lintegral_smul_measure, lintegral_add_measure, lintegral_dirac,
    smul_eq_mul]
  simp only [mul_add, ← mul_assoc]
  calc
    ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.beta * a) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .birth0,
                .birth0)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.beta * b) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .birth1,
                .birth1)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.delta * a) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .death0,
                .death0)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.delta * b) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .death1,
                .death1)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.alpha0 * a * b) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .inter0,
                .inter0)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.alpha1 * a * b) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .inter1,
                .inter1)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal
            (params.gamma0 * (a * (a - 1) / 2)) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .intra0,
                .intra0)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal
            (params.gamma1 * (b * (b - 1) / 2)) *
            V (sdHistoryNext K x
              (lvReactionTarget .selfDestructive (a, b) .intra1,
                .intra1))
      ≤ ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          (ENNReal.ofReal (params.beta * a) * Vfalse +
            ENNReal.ofReal (params.beta * b) * Vtrue +
            ENNReal.ofReal (params.delta * a) * Vtrue +
            ENNReal.ofReal (params.delta * b) * Vfalse +
            ENNReal.ofReal (params.alpha0 * a * b) * Vcur +
            ENNReal.ofReal (params.alpha1 * a * b) * Vcur) := by
        rw [hGamma0, hGamma1]
        simp only [zero_mul, ENNReal.ofReal_zero, mul_zero, add_zero]
        rw [show
          ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
              (ENNReal.ofReal (params.beta * a) * Vfalse +
                ENNReal.ofReal (params.beta * b) * Vtrue +
                ENNReal.ofReal (params.delta * a) * Vtrue +
                ENNReal.ofReal (params.delta * b) * Vfalse +
                ENNReal.ofReal (params.alpha0 * a * b) * Vcur +
                ENNReal.ofReal (params.alpha1 * a * b) * Vcur) =
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.beta * a) * Vfalse +
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                  ENNReal.ofReal (params.beta * b) * Vtrue +
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                  ENNReal.ofReal (params.delta * a) * Vtrue +
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                  ENNReal.ofReal (params.delta * b) * Vfalse +
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                  ENNReal.ofReal (params.alpha0 * a * b) * Vcur +
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                  ENNReal.ofReal (params.alpha1 * a * b) * Vcur by
            ring]
        have ht0 :
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.beta * a) *
                  V (sdHistoryNext K x
                    (lvReactionTarget .selfDestructive (a, b) .birth0,
                      .birth0)) ≤
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.beta * a) * Vfalse :=
          mul_le_mul_left' hb0 _
        have ht1 :
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.beta * b) *
                  V (sdHistoryNext K x
                    (lvReactionTarget .selfDestructive (a, b) .birth1,
                      .birth1)) ≤
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.beta * b) * Vtrue :=
          mul_le_mul_left' hb1 _
        have ht2 :
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.delta * a) *
                  V (sdHistoryNext K x
                    (lvReactionTarget .selfDestructive (a, b) .death0,
                      .death0)) ≤
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.delta * a) * Vtrue :=
          mul_le_mul_left' hd0 _
        have ht3 :
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.delta * b) *
                  V (sdHistoryNext K x
                    (lvReactionTarget .selfDestructive (a, b) .death1,
                      .death1)) ≤
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.delta * b) * Vfalse :=
          mul_le_mul_left' hd1 _
        have ht4 :
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.alpha0 * a * b) *
                  V (sdHistoryNext K x
                    (lvReactionTarget .selfDestructive (a, b) .inter0,
                      .inter0)) ≤
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.alpha0 * a * b) * Vcur :=
          mul_le_mul_left' hi0 _
        have ht5 :
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.alpha1 * a * b) *
                  V (sdHistoryNext K x
                    (lvReactionTarget .selfDestructive (a, b) .inter1,
                      .inter1)) ≤
              ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
                ENNReal.ofReal (params.alpha1 * a * b) * Vcur :=
          mul_le_mul_left' hi1 _
        have hs01 := add_le_add ht0 ht1
        have hs012 := add_le_add hs01 ht2
        have hs0123 := add_le_add hs012 ht3
        have hs01234 := add_le_add hs0123 ht4
        simpa using add_le_add hs01234 ht5
    _ = Vcur := by
      rw [hBetaDelta]
      have hβa : 0 ≤ params.delta * (a : ℝ) :=
        mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
      have hβb : 0 ≤ params.delta * (b : ℝ) :=
        mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
      have hα0 : 0 ≤ params.alpha0 * (a : ℝ) * b :=
        mul_nonneg
          (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
      have hα1 : 0 ≤ params.alpha1 * (a : ℝ) * b :=
        mul_nonneg
          (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)
      have hinv : 0 ≤ 1 / lvTotalPropensity params (a, b) :=
        one_div_nonneg.mpr hφpos.le
      have htotal :
          2 * (params.delta * (a : ℝ)) +
              2 * (params.delta * (b : ℝ)) +
              (params.alpha0 * (a : ℝ) * b +
                params.alpha1 * (a : ℝ) * b) =
            lvTotalPropensity params (a, b) := by
        unfold lvTotalPropensity
        rw [hBetaDelta, hGamma0, hGamma1]
        ring
      have hweight :
          2 * ENNReal.ofReal
                (params.delta * (a : ℝ) + params.delta * b) +
              ENNReal.ofReal
                (params.alpha0 * (a : ℝ) * b +
                  params.alpha1 * (a : ℝ) * b) =
            ENNReal.ofReal (lvTotalPropensity params (a, b)) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_add
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
              (add_nonneg hβa hβb))
            (add_nonneg hα0 hα1)]
        congr 1
        nlinarith [htotal]
      calc
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
            (ENNReal.ofReal (params.delta * a) * Vfalse +
              ENNReal.ofReal (params.delta * b) * Vtrue +
              ENNReal.ofReal (params.delta * a) * Vtrue +
              ENNReal.ofReal (params.delta * b) * Vfalse +
              ENNReal.ofReal (params.alpha0 * a * b) * Vcur +
              ENNReal.ofReal (params.alpha1 * a * b) * Vcur) =
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
              ((ENNReal.ofReal (params.delta * a) +
                    ENNReal.ofReal (params.delta * b)) *
                  (Vfalse + Vtrue) +
                (ENNReal.ofReal (params.alpha0 * a * b) +
                    ENNReal.ofReal (params.alpha1 * a * b)) * Vcur) := by
                ring
        _ = ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
              ((ENNReal.ofReal (params.delta * a) +
                    ENNReal.ofReal (params.delta * b)) *
                  (2 * Vcur) +
                (ENNReal.ofReal (params.alpha0 * a * b) +
                    ENNReal.ofReal (params.alpha1 * a * b)) * Vcur) := by
                rw [hchildren]
        _ =
            ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
              ((2 * ENNReal.ofReal
                    (params.delta * (a : ℝ) + params.delta * b) +
                  ENNReal.ofReal
                    (params.alpha0 * (a : ℝ) * b +
                      params.alpha1 * (a : ℝ) * b)) * Vcur) := by
                rw [ENNReal.ofReal_add hβa hβb,
                  ENNReal.ofReal_add hα0 hα1]
                ring
        _ = ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
              ENNReal.ofReal (lvTotalPropensity params (a, b)) *
                Vcur := by rw [hweight]; ring
        _ = Vcur := by
          rw [← ENNReal.ofReal_mul hinv, one_div_mul_cancel hφ,
            ENNReal.ofReal_one, one_mul]
    _ = V x := by simp [V, Vcur, hactive]

/-- History states in which all `K` demographic signs have been recorded and
the resulting bit vector lies in `E`. -/
def sdCompletedStateSet
    (K : ℕ) (E : Set (Fin K → Bool)) : Set (SdHistoryState K) :=
  {x | x.active = true ∧ x.count = K ∧ x.history ∈ E}

lemma measurableSet_sdCompletedStateSet
    (K : ℕ) (E : Set (Fin K → Bool)) :
    MeasurableSet (sdCompletedStateSet K E) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- The sub-probability distribution of the first `K` demographic signs
before consensus is dominated by the uniform distribution on `K` fair bits.
The missing mass consists exactly of paths on which consensus occurs before
all `K` signs have been recorded. -/
theorem sdHistory_completed_event_le_uniform
    (K : ℕ) (E : Set (Fin K → Bool))
    (params : LVParams)
    (hBetaDelta : params.beta = params.delta)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) :
    sdHistoryPathMeasure K params s0
        {ω | ∃ t : ℕ, ω t ∈ sdCompletedStateSet K E} ≤
      uniformBits K E := by
  let H := sdHistoryKernel K params
  let x0 : SdHistoryState K :=
    ⟨(s0, .idle), fun _ => false, 0, true⟩
  let V : SdHistoryState K → ℝ≥0∞ :=
    fun x => sdCompletionPotential K E x.active x.count x.history
  let A := sdCompletedStateSet K E
  let P := sdHistoryPathMeasure K params s0
  have hA : ∀ x ∈ A, 1 ≤ V x := by
    intro x hx
    rcases hx with ⟨hactive, hcount, hhist⟩
    dsimp [A, V] at *
    rw [hactive, hcount]
    exact le_of_eq (sdCompletionPotential_at_full K x.history E hhist).symm
  have hSuper : ∀ x, ∫⁻ y, V y ∂H x ≤ V x := by
    intro x
    exact sdHistoryKernel_completion_superharmonic
      K E params hBetaDelta hBetaPos hGamma0 hGamma1 x
  have hMono : Monotone (pathHitsBy A) := by
    intro m n hmn ω hω
    rcases hω with ⟨t, htm, htA⟩
    exact ⟨t, htm.trans hmn, htA⟩
  have hEach : ∀ N, P (pathHitsBy A N) ≤ V x0 := by
    intro N
    exact homogeneousPathMeasure_hitBy_le H V A hA hSuper x0 N
  have hUnion :
      {ω : ℕ → SdHistoryState K | ∃ t : ℕ, ω t ∈ A} =
        ⋃ N : ℕ, pathHitsBy A N := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, pathHitsBy]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, t, le_rfl, ht⟩
    · rintro ⟨N, t, _htN, ht⟩
      exact ⟨t, ht⟩
  have hV0 : V x0 = uniformBits K E := by
    simp only [V, x0, sdCompletionPotential, Bool.true_eq,
      true_and, Nat.zero_le, ↓reduceIte, pow_zero, one_mul]
    congr 1
    ext u
    simp [sdPrefixSet]
  change P {ω | ∃ t : ℕ, ω t ∈ A} ≤ uniformBits K E
  rw [hUnion, hMono.measure_iUnion, ← hV0]
  exact iSup_le hEach

def sdCompletedPathEvent
    (K : ℕ) (E : Set (Fin K → Bool)) :
    Set (ℕ → SdHistoryState K) :=
  {ω | ∃ t : ℕ, ω t ∈ sdCompletedStateSet K E}

lemma measurableSet_sdCompletedPathEvent
    (K : ℕ) (E : Set (Fin K → Bool)) :
    MeasurableSet (sdCompletedPathEvent K E) := by
  rw [show
    sdCompletedPathEvent K E =
      ⋃ t : ℕ,
        (fun ω : ℕ → SdHistoryState K => ω t) ⁻¹'
          sdCompletedStateSet K E by
    ext ω
    simp [sdCompletedPathEvent]]
  exact MeasurableSet.iUnion fun t =>
    (measurable_pi_apply t)
      (measurableSet_sdCompletedStateSet K E)

private lemma sdCompletedPathEvent_union_compl
    (K : ℕ) (E : Set (Fin K → Bool)) :
    sdCompletedPathEvent K E ∪
        sdCompletedPathEvent K Eᶜ =
      sdCompletedPathEvent K Set.univ := by
  ext ω
  simp only [sdCompletedPathEvent, sdCompletedStateSet,
    Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.mem_univ, and_true]
  constructor
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact ⟨t, ht.1, ht.2.1⟩
    · exact ⟨t, ht.1, ht.2.1⟩
  · rintro ⟨t, hactive, hcount⟩
    by_cases hE : (ω t).history ∈ E
    · exact Or.inl ⟨t, hactive, hcount, hE⟩
    · exact Or.inr ⟨t, hactive, hcount, hE⟩

private lemma sdHistoryNext_inactive
    (K : ℕ) (x : SdHistoryState K) (z' : LabeledPopState)
    (hx : x.active = false) :
    (sdHistoryNext K x z').active = false := by
  unfold sdHistoryNext
  rw [dif_pos (Or.inl (by simp [hx]))]

private lemma sdHistoryNext_completed_inactive
    (K : ℕ) (x : SdHistoryState K) (z' : LabeledPopState)
    (hcount : x.count = K) :
    (sdHistoryNext K x z').active = false := by
  unfold sdHistoryNext
  rw [dif_pos (Or.inr (by omega))]

theorem sdHistory_completed_unique_ae
    (K : ℕ) (params : LVParams) (s0 : PopState) :
    ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
      ∀ t u : ℕ,
        (ω t).active = true → (ω t).count = K →
        (ω u).active = true → (ω u).count = K →
          t = u := by
  let x0 : SdHistoryState K :=
    ⟨(s0, .idle), fun _ => false, 0, true⟩
  have htrans :
      ∀ᵐ ω ∂sdHistoryPathMeasure K params s0,
        ∀ t : ℕ,
          ω (t + 1) =
            sdHistoryNext K (ω t) (ω (t + 1)).labeled := by
    simpa only [sdHistoryPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (sdHistoryKernel K params) x0
        (fun x y => y = sdHistoryNext K x y.labeled)
        (sdHistoryKernel_ae_next K params)
  filter_upwards [htrans] with ω hstep
  have hpersist :
      ∀ n m : ℕ, n ≤ m → (ω n).active = false →
        (ω m).active = false := by
    intro n m hnm hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    induction d with
    | zero => simpa using hn
    | succ d ih =>
        rw [Nat.add_succ, hstep (n + d)]
        exact sdHistoryNext_inactive
          K (ω (n + d)) (ω (n + d + 1)).labeled
            (ih (Nat.le_add_right n d))
  intro t u htactive htcount huactive hucount
  by_contra hne
  rcases lt_or_gt_of_ne hne with htu | hut
  · have hnext :
        (ω (t + 1)).active = false := by
      rw [hstep t]
      exact sdHistoryNext_completed_inactive
        K (ω t) (ω (t + 1)).labeled htcount
    have huFalse :=
      hpersist (t + 1) u (by omega) hnext
    rw [huactive] at huFalse
    contradiction
  · have hnext :
        (ω (u + 1)).active = false := by
      rw [hstep u]
      exact sdHistoryNext_completed_inactive
        K (ω u) (ω (u + 1)).labeled hucount
    have htFalse :=
      hpersist (u + 1) t (by omega) hnext
    rw [htactive] at htFalse
    contradiction

/-- The first `K` demographic signs have their fair-bit law up to the
lower-tail probability that fewer than `K` demographic reactions occur
before consensus. -/
theorem sdHistory_completed_probability_lower
    (K : ℕ) (hK : 0 < K)
    (E : Set (Fin K → Bool))
    (params : LVParams)
    (hBetaDelta : params.beta = params.delta)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) (r q : ℝ≥0∞)
    (hLow :
      lvLabeledPathMeasure .selfDestructive params s0
          {ζ | labeledIndividualCountBeforeConsensus ζ < K} ≤ r)
    (hFair : q ≤ uniformBits K E) :
    q - r ≤
      sdHistoryPathMeasure K params s0
        (sdCompletedPathEvent K E) := by
  let P := sdHistoryPathMeasure K params s0
  let A := sdCompletedPathEvent K E
  let B := sdCompletedPathEvent K Eᶜ
  let U := sdCompletedPathEvent K Set.univ
  let L : Set (ℕ → SdHistoryState K) :=
    {ω |
      labeledIndividualCountBeforeConsensus
        (pathMap SdHistoryState.labeled ω) < K}
  have hAmeas : MeasurableSet A :=
    measurableSet_sdCompletedPathEvent K E
  have hBmeas : MeasurableSet B :=
    measurableSet_sdCompletedPathEvent K Eᶜ
  have hUmeas : MeasurableSet U :=
    measurableSet_sdCompletedPathEvent K Set.univ
  have hLbase :
      MeasurableSet
        {ζ : ℕ → LabeledPopState |
          labeledIndividualCountBeforeConsensus ζ < K} :=
    measurableSet_labeledIndividualCountBefore_lt K hK
  have hLmeas : MeasurableSet L :=
    hLbase.preimage
      (measurable_pathMap SdHistoryState.labeled
        (measurable_of_countable SdHistoryState.labeled))
  have hNoCompLow : ∀ᵐ ω ∂P, ω ∈ Uᶜ → ω ∈ L := by
    filter_upwards [
      sdHistory_individual_count_ge_implies_completed_ae
        K hK params hBetaPos hGamma0 hGamma1 s0] with ω hcomplete
    intro hnotU
    by_contra hnotL
    have hge :
        K ≤ labeledIndividualCountBeforeConsensus
          (pathMap SdHistoryState.labeled ω) := by
      simpa only [L, Set.mem_setOf_eq, not_lt] using hnotL
    obtain ⟨t, hactive, hcount⟩ := hcomplete hge
    exact hnotU ⟨t, hactive, hcount, Set.mem_univ _⟩
  have hNoComp :
      P Uᶜ ≤ r := by
    calc
      P Uᶜ ≤ P L := measure_mono_ae hNoCompLow
      _ =
          lvLabeledPathMeasure .selfDestructive params s0
            {ζ | labeledIndividualCountBeforeConsensus ζ < K} := by
        rw [← sdHistoryPathMeasure_map_labeled K params s0]
        rw [Measure.map_apply
          (measurable_pathMap SdHistoryState.labeled
            (measurable_of_countable SdHistoryState.labeled))
          hLbase]
        rfl
      _ ≤ r := hLow
  have hB :
      P B ≤ uniformBits K Eᶜ := by
    exact sdHistory_completed_event_le_uniform
      K Eᶜ params hBetaDelta hBetaPos hGamma0 hGamma1 s0
  have hUnion : A ∪ B = U := by
    exact sdCompletedPathEvent_union_compl K E
  have hDisj : AEDisjoint P A B := by
    have hae : ∀ᵐ ω ∂P, ω ∉ A ∩ B := by
      filter_upwards [
        sdHistory_completed_unique_ae K params s0] with ω hunique
      intro hω
      rcases hω.1 with ⟨t, htactive, htcount, htE⟩
      rcases hω.2 with ⟨u, huactive, hucount, huE⟩
      have htu :=
        hunique t u htactive htcount huactive hucount
      subst u
      exact huE htE
    exact compl_mem_ae_iff.mp hae
  haveI : IsProbabilityMeasure P := by
    dsimp [P, sdHistoryPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hPartition :
      P A + P B + P Uᶜ = 1 := by
    rw [← measure_union₀ hBmeas.nullMeasurableSet hDisj, hUnion,
      measure_add_measure_compl hUmeas, measure_univ]
  have hUniformPartition :
      uniformBits K E + uniformBits K Eᶜ = 1 := by
    simpa only [measure_univ] using
      (measure_add_measure_compl
        (μ := uniformBits K)
        (DiscreteMeasurableSpace.forall_measurableSet E))
  have hsum :
      uniformBits K E + uniformBits K Eᶜ ≤
        (P A + r) + uniformBits K Eᶜ := by
    rw [hUniformPartition, ← hPartition]
    calc
      P A + P B + P Uᶜ ≤ P A + uniformBits K Eᶜ + r := by
        gcongr
      _ = (P A + r) + uniformBits K Eᶜ := by
        ring
  have hfinite : uniformBits K Eᶜ ≠ ⊤ :=
    measure_ne_top (uniformBits K) Eᶜ
  have hfairToA :
      uniformBits K E ≤ P A + r := by
    exact
      (ENNReal.add_le_add_iff_right hfinite).mp
        (by simpa only [add_assoc] using hsum)
  apply tsub_le_iff_right.mpr
  exact hFair.trans hfairToA

def sdHistoryPositiveDiagonalEvent
    (K : ℕ) : Set (ℕ → SdHistoryState K) :=
  {ω | ∃ t : ℕ,
    (ω t).labeled.1.1 = (ω t).labeled.1.2 ∧
      0 < (ω t).labeled.1.1}

lemma measurableSet_sdHistoryPositiveDiagonalEvent
    (K : ℕ) :
    MeasurableSet (sdHistoryPositiveDiagonalEvent K) := by
  rw [show
    sdHistoryPositiveDiagonalEvent K =
      ⋃ t : ℕ,
        (fun ω : ℕ → SdHistoryState K => ω t) ⁻¹'
          {x |
            x.labeled.1.1 = x.labeled.1.2 ∧
              0 < x.labeled.1.1} by
    ext ω
    simp [sdHistoryPositiveDiagonalEvent]]
  exact MeasurableSet.iUnion fun t =>
    (measurable_pi_apply t)
      (DiscreteMeasurableSpace.forall_measurableSet _)

def sdHistoryPopulationPath
    {K : ℕ} (ω : ℕ → SdHistoryState K) : ℕ → PopState :=
  fun t => (ω t).labeled.1

lemma measurable_sdHistoryPopulationPath
    (K : ℕ) :
    Measurable
      (sdHistoryPopulationPath :
        (ℕ → SdHistoryState K) → (ℕ → PopState)) :=
  measurable_pathMap
    (fun x : SdHistoryState K => x.labeled.1)
    (measurable_of_countable fun x : SdHistoryState K => x.labeled.1)

theorem sdHistoryPathMeasure_map_population
    (K : ℕ) (params : LVParams) (s0 : PopState) :
    (sdHistoryPathMeasure K params s0).map
        sdHistoryPopulationPath =
      lvPathMeasure .selfDestructive params s0 := by
  have hcomp :
      (sdHistoryPopulationPath :
          (ℕ → SdHistoryState K) → (ℕ → PopState)) =
        forgetLVLabels ∘ pathMap SdHistoryState.labeled := by
    funext ω
    rfl
  rw [hcomp, ← Measure.map_map
    measurable_forgetLVLabels
    (measurable_pathMap SdHistoryState.labeled
      (measurable_of_countable SdHistoryState.labeled)),
    sdHistoryPathMeasure_map_labeled,
    lvLabeledPathMeasure_map_forget]

private lemma measurableSet_positiveDiagonalEvent :
    MeasurableSet
      {ω : ℕ → PopState |
        ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
  rw [show
    {ω : ℕ → PopState |
        ∃ t : ℕ, (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} =
      ⋃ t : ℕ,
        (fun ω : ℕ → PopState => ω t) ⁻¹'
          {s : PopState | s.1 = s.2 ∧ 0 < s.1} by
    ext ω
    simp]
  exact MeasurableSet.iUnion fun t =>
    (measurable_pi_apply t)
      (DiscreteMeasurableSpace.forall_measurableSet _)

/-- Quantitative core of the corrected SD lower threshold.  The probability
of reaching the positive diagonal is at least the fair-walk crossing
probability minus the lower-tail probability for obtaining `K` demographic
reactions before consensus. -/
theorem sd_positive_diagonal_probability_lower
    (K : ℕ) (hK : 0 < K)
    (params : LVParams)
    (hBetaDelta : params.beta = params.delta)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (a b : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (r q : ℝ≥0∞)
    (hLow :
      lvLabeledPathMeasure .selfDestructive params (a, b)
          {ζ | labeledIndividualCountBeforeConsensus ζ < K} ≤ r)
    (hFair :
      q ≤ uniformBits K
        (sdBitLevelEvent ((a : ℝ) - b) K)) :
    q - r ≤
      lvPathMeasure .selfDestructive params (a, b)
        {ω | ∃ t : ℕ,
          (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
  let P := sdHistoryPathMeasure K params (a, b)
  let A :=
    sdCompletedPathEvent K
      (sdBitLevelEvent ((a : ℝ) - b) K)
  let D := sdHistoryPositiveDiagonalEvent K
  have hA :
      q - r ≤ P A := by
    exact sdHistory_completed_probability_lower
      K hK (sdBitLevelEvent ((a : ℝ) - b) K)
        params hBetaDelta hBetaPos hGamma0 hGamma1
        (a, b) r q hLow hFair
  have hAD : P A ≤ P D := by
    apply measure_mono_ae
    filter_upwards [
      sdHistory_completed_level_implies_diagonal_ae
        K params a b hb hab] with ω hω
    intro hAω
    exact hω hAω
  have hD :
      P D =
        lvPathMeasure .selfDestructive params (a, b)
          {ω | ∃ t : ℕ,
            (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
    rw [← sdHistoryPathMeasure_map_population
      K params (a, b)]
    rw [Measure.map_apply
      (measurable_sdHistoryPopulationPath K)
      measurableSet_positiveDiagonalEvent]
    rfl
  exact hA.trans (hAD.trans_eq hD)

/-- Corrected paper-level SD lower threshold.  Positive demographic rates
are essential: if `β = δ = 0`, the signed gap is constant and the theorem is
false. -/
theorem thm_self_destructive_lower_threshold
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hAlpha : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hBetaPos : 0 < params.beta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ φ : ℝ, 0 < φ ∧ ∃ n₀ : ℕ,
        ∀ a b : ℕ, n₀ ≤ a + b → 0 < b → b ≤ a →
          (a : ℝ) - b ≤
              φ * Real.sqrt (Real.log (a + b)) →
            majorityConsensusProb .selfDestructive
                params (a, b) ≤
              ENNReal.ofReal (1 / 2 + ε) := by
  intro ε hε
  let η : ℝ := min ε (1 / 2)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hTheta : 0 < params.beta + params.delta := by
    rw [← hBetaDelta]
    linarith
  have hGood :
      0 < effectiveGoodRate .selfDestructive params := by
    simpa only [effectiveGoodRate] using hAlpha
  obtain ⟨f, g, hf, hg, hLogTail⟩ :=
    lemma_log_individual_events_full
      .selfDestructive params hTheta hGood
        hGamma0 hGamma1
  have hclt0 : 0 < 1 - η / 2 := by linarith
  have hclt1 : 1 - η / 2 < 1 := by linarith
  obtain ⟨θ, hθ, K₀, hCLT⟩ :=
    uniformBits_bitMaxEvent_lower
      (1 - η / 2) hclt0 hclt1
  let C : ℝ :=
    max ((K₀ : ℝ) / f)
      (-Real.log (η / 2) / g)
  have hlogTend :
      Filter.Tendsto
        (fun n : ℕ => Real.log (n : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop
  obtain ⟨b₀, hb₀⟩ :
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
        C ≤ Real.log (b : ℝ) := by
    have hev := hlogTend.eventually_ge_atTop C
    rwa [Filter.eventually_atTop] at hev
  let φ : ℝ := min 1 (θ * Real.sqrt (f / 2))
  have hφ : 0 < φ := by
    apply lt_min (by norm_num)
    exact mul_pos hθ (Real.sqrt_pos.mpr (by positivity))
  refine ⟨φ, hφ, max 16 (4 * b₀), ?_⟩
  intro a b hn hb hab hgap
  have hn16 : 16 ≤ a + b := (le_max_left _ _).trans hn
  have hnb0 : 4 * b₀ ≤ a + b := (le_max_right _ _).trans hn
  have hnPos : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < a + b by omega)
  have hlogNonneg :
      0 ≤ Real.log ((a + b : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ a + b by omega))
  have hφle : φ ≤ 1 := min_le_left _ _
  have hlogLeN :
      Real.log ((a + b : ℕ) : ℝ) ≤ (a + b : ℕ) :=
    Real.log_le_self hnPos.le
  have hsqrtLogLe :
      Real.sqrt (Real.log ((a + b : ℕ) : ℝ)) ≤
        Real.sqrt ((a + b : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt hlogLeN
  have hsqrtNLeHalf :
      Real.sqrt ((a + b : ℕ) : ℝ) ≤
        ((a + b : ℕ) : ℝ) / 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hn4 : (4 : ℝ) ≤ (a + b : ℕ) := by
        exact_mod_cast (show 4 ≤ a + b by omega)
      nlinarith
  have hgapHalf :
      (a : ℝ) - b ≤ ((a + b : ℕ) : ℝ) / 2 := by
    calc
      (a : ℝ) - b ≤
          φ * Real.sqrt (Real.log (a + b)) := hgap
      _ ≤ Real.sqrt (Real.log ((a + b : ℕ) : ℝ)) := by
        have hsqrt0 :
            0 ≤ Real.sqrt (Real.log ((a + b : ℕ) : ℝ)) :=
          Real.sqrt_nonneg _
        simpa only [Nat.cast_add] using
          (mul_le_of_le_one_left hsqrt0 hφle)
      _ ≤ Real.sqrt ((a + b : ℕ) : ℝ) := hsqrtLogLe
      _ ≤ ((a + b : ℕ) : ℝ) / 2 := hsqrtNLeHalf
  have hnLe4bReal :
      ((a + b : ℕ) : ℝ) ≤ 4 * (b : ℝ) := by
    push_cast at hgapHalf ⊢
    nlinarith
  have hnLe4b : a + b ≤ 4 * b := by
    exact_mod_cast hnLe4bReal
  have hbLarge : b₀ ≤ b := by omega
  have hsqrtNLeQuarter :
      Real.sqrt ((a + b : ℕ) : ℝ) ≤
        ((a + b : ℕ) : ℝ) / 4 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hn16R : (16 : ℝ) ≤ (a + b : ℕ) := by
        exact_mod_cast hn16
      nlinarith
  have hquarterLeB :
      ((a + b : ℕ) : ℝ) / 4 ≤ (b : ℝ) := by
    linarith
  have hsqrtNLeB :
      Real.sqrt ((a + b : ℕ) : ℝ) ≤ (b : ℝ) :=
    hsqrtNLeQuarter.trans hquarterLeB
  have hsqrtNPos :
      0 < Real.sqrt ((a + b : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hnPos
  have hlogB :
      Real.log ((a + b : ℕ) : ℝ) / 2 ≤
        Real.log (b : ℝ) := by
    calc
      Real.log ((a + b : ℕ) : ℝ) / 2 =
          Real.log (Real.sqrt ((a + b : ℕ) : ℝ)) :=
        (Real.log_sqrt hnPos.le).symm
      _ ≤ Real.log (b : ℝ) :=
        Real.log_le_log hsqrtNPos hsqrtNLeB
  have hCLogB : C ≤ Real.log (b : ℝ) :=
    hb₀ b hbLarge
  let K : ℕ := Nat.ceil (f * Real.log b)
  have hK₀Real :
      (K₀ : ℝ) ≤ f * Real.log (b : ℝ) := by
    have hbase :
        (K₀ : ℝ) / f ≤ Real.log (b : ℝ) :=
      (le_max_left _ _).trans hCLogB
    have hf0 : 0 < f := hf
    calc
      (K₀ : ℝ) = f * ((K₀ : ℝ) / f) := by field_simp
      _ ≤ f * Real.log (b : ℝ) :=
        mul_le_mul_of_nonneg_left hbase hf.le
  have hK₀K : K₀ ≤ K := by
    have hceil :
        f * Real.log (b : ℝ) ≤
          (Nat.ceil (f * Real.log b) : ℝ) :=
      Nat.le_ceil _
    exact_mod_cast hK₀Real.trans hceil
  have hlogBPos : 0 < Real.log (b : ℝ) := by
    have hbOne : (1 : ℝ) < b := by
      have : 4 ≤ b := by omega
      exact_mod_cast (show 1 < b by omega)
    exact Real.log_pos hbOne
  have hK : 0 < K := by
    exact Nat.ceil_pos.mpr (mul_pos hf hlogBPos)
  have hLowBase :=
    hLogTail (a, b) b
      (by simp [Nat.min_eq_right hab]) hb
  have hLow :
      lvLabeledPathMeasure .selfDestructive params (a, b)
          {ζ | labeledIndividualCountBeforeConsensus ζ < K} ≤
        ENNReal.ofReal (η / 2) := by
    calc
      lvLabeledPathMeasure .selfDestructive params (a, b)
          {ζ | labeledIndividualCountBeforeConsensus ζ < K}
        ≤ ENNReal.ofReal
            (Real.exp (-(g * Real.log b))) := by
          simpa only [K] using hLowBase
      _ ≤ ENNReal.ofReal (η / 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.exp_log (by positivity : 0 < η / 2)]
        apply Real.exp_le_exp.mpr
        have hbase :
            -Real.log (η / 2) / g ≤
              Real.log (b : ℝ) :=
          (le_max_right _ _).trans hCLogB
        have hmul :=
          mul_le_mul_of_nonneg_left hbase hg.le
        have hcancel :
            g * (-Real.log (η / 2) / g) =
              -Real.log (η / 2) := by
          field_simp
        rw [hcancel] at hmul
        linarith
  have hKReal :
      f / 2 * Real.log ((a + b : ℕ) : ℝ) ≤ (K : ℝ) := by
    have hmul :
        f / 2 * Real.log ((a + b : ℕ) : ℝ) ≤
          f * Real.log (b : ℝ) := by
      calc
        f / 2 * Real.log ((a + b : ℕ) : ℝ) =
            f * (Real.log ((a + b : ℕ) : ℝ) / 2) := by ring
        _ ≤ f * Real.log (b : ℝ) :=
          mul_le_mul_of_nonneg_left hlogB hf.le
    have hceil :
        f * Real.log (b : ℝ) ≤
          (Nat.ceil (f * Real.log b) : ℝ) :=
      Nat.le_ceil _
    simpa only [K] using hmul.trans hceil
  have hgapK :
      (a : ℝ) - b ≤ θ * Real.sqrt K := by
    have hφProd :
        φ ≤ θ * Real.sqrt (f / 2) :=
      min_le_right _ _
    have hsqrtFactor :
        Real.sqrt (f / 2) *
            Real.sqrt (Real.log ((a + b : ℕ) : ℝ)) =
          Real.sqrt
            ((f / 2) *
              Real.log ((a + b : ℕ) : ℝ)) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ f / 2)]
    have hsqrtK :
        Real.sqrt
            ((f / 2) *
              Real.log ((a + b : ℕ) : ℝ)) ≤
          Real.sqrt (K : ℝ) :=
      Real.sqrt_le_sqrt hKReal
    calc
      (a : ℝ) - b ≤
          φ * Real.sqrt (Real.log (a + b)) := hgap
      _ ≤
          (θ * Real.sqrt (f / 2)) *
            Real.sqrt
              (Real.log ((a + b : ℕ) : ℝ)) := by
        have hsqrt0 :
            0 ≤ Real.sqrt
              (Real.log ((a + b : ℕ) : ℝ)) :=
          Real.sqrt_nonneg _
        simpa only [Nat.cast_add] using
          (mul_le_mul_of_nonneg_right hφProd hsqrt0)
      _ =
          θ * Real.sqrt
            ((f / 2) *
              Real.log ((a + b : ℕ) : ℝ)) := by
        rw [← hsqrtFactor]
        ring
      _ ≤ θ * Real.sqrt (K : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtK hθ.le
      _ = θ * Real.sqrt K := by rfl
  have hFair :
      ENNReal.ofReal (1 - η / 2) ≤
        uniformBits K
          (sdBitLevelEvent ((a : ℝ) - b) K) := by
    calc
      ENNReal.ofReal (1 - η / 2) ≤
          uniformBits K (bitMaxEvent θ K) :=
        hCLT K hK₀K
      _ ≤ uniformBits K
          (sdBitLevelEvent ((a : ℝ) - b) K) := by
        apply measure_mono
        intro u hu
        rcases hu with ⟨k, hk, hbound⟩
        exact ⟨k, hk, hgapK.trans hbound⟩
  have hDiagRaw :=
    sd_positive_diagonal_probability_lower
      K hK params hBetaDelta hBetaPos hGamma0 hGamma1
        a b hb hab
        (ENNReal.ofReal (η / 2))
        (ENNReal.ofReal (1 - η / 2))
        hLow hFair
  have hDiag :
      ENNReal.ofReal (1 - η) ≤
        lvPathMeasure .selfDestructive params (a, b)
          {ω | ∃ t : ℕ,
            (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} := by
    calc
      ENNReal.ofReal (1 - η) =
          ENNReal.ofReal (1 - η / 2 - η / 2) := by
            congr 1
            ring
      _ =
          ENNReal.ofReal (1 - η / 2) -
            ENNReal.ofReal (η / 2) :=
        ENNReal.ofReal_sub (1 - η / 2)
          (by positivity : 0 ≤ η / 2)
      _ ≤
          lvPathMeasure .selfDestructive params (a, b)
            {ω | ∃ t : ℕ,
              (ω t).1 = (ω t).2 ∧ 0 < (ω t).1} :=
        hDiagRaw
  let μ := lvPathMeasure .selfDestructive params (a, b)
  let D : Set (ℕ → PopState) :=
    {ω | ∃ t : ℕ,
      (ω t).1 = (ω t).2 ∧ 0 < (ω t).1}
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hDmeas : MeasurableSet D :=
    measurableSet_positiveDiagonalEvent
  have hDc :
      μ Dᶜ ≤ ENNReal.ofReal η := by
    have hEq : μ Dᶜ = 1 - μ D := by
      have := measure_compl hDmeas (measure_ne_top μ D)
      rwa [measure_univ] at this
    have hsum :
        ENNReal.ofReal (1 - η) + ENNReal.ofReal η = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) hη.le]
      simp
    calc
      μ Dᶜ = 1 - μ D := hEq
      _ ≤ 1 - ENNReal.ofReal (1 - η) :=
        tsub_le_tsub_left hDiag 1
      _ = ENNReal.ofReal η := by
        rw [← hsum, ENNReal.add_sub_cancel_left
          ENNReal.ofReal_ne_top]
  have hStructural :=
    thm_self_destructive_lower
      params hNeutral hGamma0 hGamma1 a b hb hab
  change
    majorityConsensusProb .selfDestructive params (a, b) ≤
      ENNReal.ofReal (1 / 2) +
        ENNReal.ofReal (1 / 2) * μ Dᶜ at hStructural
  calc
    majorityConsensusProb .selfDestructive params (a, b)
      ≤ ENNReal.ofReal (1 / 2) +
          ENNReal.ofReal (1 / 2) * μ Dᶜ :=
        hStructural
    _ ≤ ENNReal.ofReal (1 / 2) +
          ENNReal.ofReal (1 / 2) *
            ENNReal.ofReal η := by
      gcongr
    _ = ENNReal.ofReal (1 / 2 + η / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by positivity : 0 ≤ 1 / 2 * η)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1 / 2 + ε) := by
      apply ENNReal.ofReal_le_ofReal
      linarith

end LVConsensus
