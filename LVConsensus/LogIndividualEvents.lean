import LVConsensus.SelfDestructiveLower
import LVConsensus.NiceUpperDomination
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal BigOperators

namespace LVConsensus

/-!
# Logarithmically many individual reactions

This file formalizes the stopped-level argument in
`lemma:log-individual-events`.  Reaction-labelled paths are essential for the
non-self-destructive model: a competitive death and an individual death can
have the same unlabelled population-state transition.
-/

private def individualReactionSet : Set LabeledPopState :=
  {z | isIndividualReaction z.2}

private lemma measurableSet_individualReactionSet :
    MeasurableSet individualReactionSet :=
  (Set.to_countable individualReactionSet).measurableSet

/-- Exact probability of an individual reaction in an interior state when
intraspecific competition is absent. -/
lemma lvLabeledKernel_individual_probability
    (v : LVVariant) (params : LVParams) (z : LabeledPopState)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hz0 : 0 < z.1.1) (hz1 : 0 < z.1.2) :
    lvLabeledKernel v params z individualReactionSet =
      ENNReal.ofReal
        ((params.beta + params.delta) *
          ((z.1.1 : ℝ) + z.1.2) /
            lvTotalPropensity params z.1) := by
  rcases z with ⟨⟨a, b⟩, old⟩
  change
    lvLabeledKernel v params ((a, b), old) individualReactionSet =
      ENNReal.ofReal
        ((params.beta + params.delta) * ((a : ℝ) + b) /
          lvTotalPropensity params (a, b))
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · simp only [lvLabeledKernel, Kernel.ofFunOfCountable,
      Kernel.coe_mk, hφ, dif_pos, div_zero, ENNReal.ofReal_zero]
    simp [individualReactionSet, isIndividualReaction,
      Measure.dirac_apply]
  have hφpos : 0 < lvTotalPropensity params (a, b) :=
    lt_of_le_of_ne
      (lvTotalPropensity_nonneg params (a, b)) (Ne.symm hφ)
  have hset :
      individualReactionSet =
        {z | z.2 = .birth0} ∪ {z | z.2 = .birth1} ∪
          {z | z.2 = .death0} ∪ {z | z.2 = .death1} := by
    ext z'
    rcases z' with ⟨s', r⟩
    cases r <;> simp [individualReactionSet, isIndividualReaction]
  rw [hset]
  let A : Set LabeledPopState := {z | z.2 = .birth0}
  let B : Set LabeledPopState := {z | z.2 = .birth1}
  let C : Set LabeledPopState := {z | z.2 = .death0}
  let D : Set LabeledPopState := {z | z.2 = .death1}
  change lvLabeledKernel v params ((a, b), old)
      (((A ∪ B) ∪ C) ∪ D) = _
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    simp [A, B]
  have hABC : Disjoint (A ∪ B) C := by
    rw [Set.disjoint_left]
    simp [A, B, C]
  have hABCD : Disjoint ((A ∪ B) ∪ C) D := by
    rw [Set.disjoint_left]
    intro ⟨s, r⟩ hr hrD
    change ((r = .birth0 ∨ r = .birth1) ∨ r = .death0) at hr
    change r = .death1 at hrD
    rw [hrD] at hr
    simp at hr
  rw [measure_union hABCD (by measurability),
    measure_union hABC (by measurability),
    measure_union hAB (by measurability)]
  dsimp [A, B, C, D]
  simp_rw [lvLabeledKernel_reaction_probability]
  simp only [hφ, ↓reduceDIte, reduceCtorEq, if_false,
    lvReactionWeight]
  have hinv : (0 : ℝ) ≤ 1 / lvTotalPropensity params (a, b) :=
    one_div_nonneg.mpr hφpos.le
  have hβa : 0 ≤ params.beta * (a : ℝ) :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  have hβb : 0 ≤ params.beta * (b : ℝ) :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  have hδa : 0 ≤ params.delta * (a : ℝ) :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  have hδb : 0 ≤ params.delta * (b : ℝ) :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  let W : ℝ :=
    params.beta * (a : ℝ) + params.beta * (b : ℝ) +
      params.delta * (a : ℝ) + params.delta * (b : ℝ)
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  calc
    ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.beta * (a : ℝ)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.beta * (b : ℝ)) +
      ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.delta * (a : ℝ)) +
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal (params.delta * (b : ℝ)) =
        ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          (ENNReal.ofReal (params.beta * (a : ℝ)) +
            ENNReal.ofReal (params.beta * (b : ℝ)) +
            ENNReal.ofReal (params.delta * (a : ℝ)) +
            ENNReal.ofReal (params.delta * (b : ℝ))) := by ring
    _ = ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) *
          ENNReal.ofReal W := by
      dsimp [W]
      rw [← ENNReal.ofReal_add hβa hβb,
        ← ENNReal.ofReal_add (add_nonneg hβa hβb) hδa,
        ← ENNReal.ofReal_add
          (add_nonneg (add_nonneg hβa hβb) hδa) hδb]
    _ = ENNReal.ofReal
          ((1 / lvTotalPropensity params (a, b)) * W) :=
      (ENNReal.ofReal_mul hinv).symm
    _ = ENNReal.ofReal
          ((params.beta + params.delta) * ((a : ℝ) + b) /
            lvTotalPropensity params (a, b)) := by
      congr 1
      dsimp [W]
      field_simp [hφ]
      ring

/-- The paper's uniform one-step lower bound, now stated for actual reaction
labels and therefore valid for both LV variants. -/
lemma lvLabeledKernel_individual_probability_lb
    (v : LVVariant) (params : LVParams) (z : LabeledPopState)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (k : ℕ)
    (hk : Nat.min z.1.1 z.1.2 = k) (hk0 : 0 < k) :
    ENNReal.ofReal
        ((params.beta + params.delta) /
          ((params.alpha0 + params.alpha1) * k +
            2 * (params.beta + params.delta))) ≤
      lvLabeledKernel v params z individualReactionSet := by
  have hz0 : 0 < z.1.1 := lt_of_lt_of_le hk0 (hk ▸ Nat.min_le_left _ _)
  have hz1 : 0 < z.1.2 := lt_of_lt_of_le hk0 (hk ▸ Nat.min_le_right _ _)
  rw [lvLabeledKernel_individual_probability
    v params z hGamma0 hGamma1 hz0 hz1]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total z.1.1 z.1.2 with hab | hba
  · have hmin : Nat.min z.1.1 z.1.2 = z.1.1 :=
      Nat.min_eq_left hab
    rw [hmin] at hk
    subst k
    have hφ :
        lvTotalPropensity params z.1 =
          (params.beta + params.delta) *
              ((z.1.2 : ℝ) + z.1.1) +
            (params.alpha0 + params.alpha1) *
              (z.1.2 : ℝ) * z.1.1 := by
      simp only [lvTotalPropensity, hGamma0, hGamma1]
      push_cast
      ring
    rw [hφ]
    simpa only [add_comm] using
      noncompetitive_prob_lb_nat params z.1.2 z.1.1 hab hk0 hTheta
  · have hmin : Nat.min z.1.1 z.1.2 = z.1.2 :=
      Nat.min_eq_right hba
    rw [hmin] at hk
    subst k
    have hφ :
        lvTotalPropensity params z.1 =
          (params.beta + params.delta) *
              ((z.1.1 : ℝ) + z.1.2) +
            (params.alpha0 + params.alpha1) *
              (z.1.1 : ℝ) * z.1.2 := by
      simp only [lvTotalPropensity, hGamma0, hGamma1]
      push_cast
      ring
    rw [hφ]
    exact noncompetitive_prob_lb_nat
      params z.1.1 z.1.2 hba hk0 hTheta

/-! ## Indicators sampled at the first visit to each minority level -/

private def labeledMinCount (ζ : ℕ → LabeledPopState) (t : ℕ) : ℕ :=
  Nat.min (ζ t).1.1 (ζ t).1.2

private noncomputable instance individualReaction_decidable (r : LVReaction) :
    Decidable (isIndividualReaction r) := by
  exact Classical.propDecidable _

private lemma labeledMinCount_measurable (t : ℕ) :
    Measurable (fun ζ : ℕ → LabeledPopState =>
      labeledMinCount ζ t) :=
  (measurable_of_countable
    (fun z : LabeledPopState => Nat.min z.1.1 z.1.2)).comp
      (show Measurable
        (fun ζ : ℕ → LabeledPopState => ζ t) from
          measurable_pi_apply t)

/-- The labelled path visits level `k` for the first time at time `t`. -/
private def firstLevelAt (k t : ℕ) : Set (ℕ → LabeledPopState) :=
  {ζ | labeledMinCount ζ t = k ∧
    ∀ u < t, labeledMinCount ζ u ≠ k}

private lemma measurableSet_firstLevelAt (k t : ℕ) :
    MeasurableSet (firstLevelAt k t) := by
  have hnow :
      MeasurableSet {ζ : ℕ → LabeledPopState |
        labeledMinCount ζ t = k} := by
    exact (measurable_of_countable
      (fun z : LabeledPopState => Nat.min z.1.1 z.1.2)).comp
        (measurable_pi_apply t) (measurableSet_singleton k)
  have hpast :
      MeasurableSet {ζ : ℕ → LabeledPopState |
        ∀ u < t, labeledMinCount ζ u ≠ k} := by
    rw [show {ζ : ℕ → LabeledPopState |
        ∀ u < t, labeledMinCount ζ u ≠ k} =
      ⋂ u : Fin t, {ζ | labeledMinCount ζ u ≠ k} by
        ext ζ
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h u
          exact h u u.2
        · intro h u hu
          exact h ⟨u, hu⟩]
    exact MeasurableSet.iInter fun u =>
      (labeledMinCount_measurable u)
        (measurableSet_singleton k).compl
  exact hnow.inter hpast

private lemma firstLevelAt_cylinder (k t : ℕ) :
    isCylinderUpTo t (firstLevelAt k t) := by
  intro ζ η heq hζ
  constructor
  · simpa only [labeledMinCount, heq t le_rfl] using hζ.1
  · intro u hu
    simpa only [labeledMinCount, heq u (Nat.le_of_lt hu)] using
      hζ.2 u hu

/-- A first-level cell additionally records the labelled state at the
stopping time. -/
private def firstLevelBlock
    (k t : ℕ) (z : LabeledPopState) : Set (ℕ → LabeledPopState) :=
  firstLevelAt k t ∩ {ζ | ζ t = z}

private lemma measurableSet_firstLevelBlock
    (k t : ℕ) (z : LabeledPopState) :
    MeasurableSet (firstLevelBlock k t z) :=
  (measurableSet_firstLevelAt k t).inter (by
    exact (show Measurable
      (fun ζ : ℕ → LabeledPopState => ζ t) from
        measurable_pi_apply t) (measurableSet_singleton z))

private lemma firstLevelBlock_cylinder
    (k t : ℕ) (z : LabeledPopState) :
    isCylinderUpTo t (firstLevelBlock k t z) := by
  intro ζ η heq hζ
  refine ⟨firstLevelAt_cylinder k t ζ η heq hζ.1, ?_⟩
  change η t = z
  rw [← heq t le_rfl]
  exact hζ.2

private lemma firstLevelAt_unique
    (k t u : ℕ) (ζ : ℕ → LabeledPopState)
    (ht : ζ ∈ firstLevelAt k t)
    (hu : ζ ∈ firstLevelAt k u) :
    t = u := by
  rcases lt_trichotomy t u with htu | htu | htu
  · exact absurd ht.1 (hu.2 t htu)
  · exact htu
  · exact absurd hu.1 (ht.2 u htu)

private lemma firstLevelBlock_pairwise (k : ℕ) :
    Pairwise fun q q' : ℕ × LabeledPopState =>
      Disjoint
        (firstLevelBlock k q.1 q.2)
        (firstLevelBlock k q'.1 q'.2) := by
  intro ⟨t, z⟩ ⟨u, z'⟩ hne
  rw [Set.disjoint_left]
  intro ζ ht hu
  have htu := firstLevelAt_unique k t u ζ ht.1 hu.1
  subst u
  have hzz : z = z' := ht.2.symm.trans hu.2
  exact hne (Prod.ext rfl hzz)

/-- Whether the reaction immediately following the first visit to level `k`
is an individual reaction.  It is `false` if the level is never visited. -/
private noncomputable def levelIndividual
    (k : ℕ) (ζ : ℕ → LabeledPopState) : Bool :=
  by
    classical
    exact if ∃ t : ℕ, ζ ∈ firstLevelAt k t ∧
        isIndividualReaction (ζ (t + 1)).2
      then true
      else false

private lemma levelIndividual_measurable (k : ℕ) :
    Measurable (levelIndividual k) := by
  classical
  let E : Set (ℕ → LabeledPopState) :=
    ⋃ t : ℕ, firstLevelAt k t ∩
      {ζ | isIndividualReaction (ζ (t + 1)).2}
  have hE : MeasurableSet E := by
    apply MeasurableSet.iUnion
    intro t
    exact (measurableSet_firstLevelAt k t).inter
      ((Set.to_countable
        {z : LabeledPopState | isIndividualReaction z.2}).measurableSet.preimage
          (show Measurable
            (fun ζ : ℕ → LabeledPopState => ζ (t + 1)) from
              measurable_pi_apply (t + 1)))
  have heq : levelIndividual k =
      fun ζ => if ζ ∈ E then true else false := by
    funext ζ
    simp only [levelIndividual, E, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [heq]
  exact Measurable.ite hE measurable_const measurable_const

private lemma levelIndividual_of_firstLevelAt
    (k t : ℕ) (ζ : ℕ → LabeledPopState)
    (ht : ζ ∈ firstLevelAt k t) :
    levelIndividual k ζ =
      decide (isIndividualReaction (ζ (t + 1)).2) := by
  classical
  unfold levelIndividual
  by_cases h : isIndividualReaction (ζ (t + 1)).2
  · rw [if_pos ⟨t, ht, h⟩]
    simp [h]
  · rw [if_neg]
    · simp [h]
    · rintro ⟨u, hu, hi⟩
      have hut := firstLevelAt_unique k u t ζ hu ht
      subst u
      exact h hi

/-- The no-downward-jump condition through time `t`. -/
private def minStepValidUpTo
    (t : ℕ) (ζ : ℕ → LabeledPopState) : Prop :=
  ∀ u < t, labeledMinCount ζ u ≤ labeledMinCount ζ (u + 1) + 1

private lemma measurableSet_minStepValidUpTo (t : ℕ) :
    MeasurableSet {ζ : ℕ → LabeledPopState | minStepValidUpTo t ζ} := by
  rw [show {ζ : ℕ → LabeledPopState | minStepValidUpTo t ζ} =
      ⋂ u : Fin t,
        {ζ | labeledMinCount ζ u ≤ labeledMinCount ζ (u + 1) + 1} by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, minStepValidUpTo]
    constructor
    · intro h u
      exact h u u.2
    · intro h u hu
      exact h ⟨u, hu⟩]
  apply MeasurableSet.iInter
  intro u
  have hp : Measurable
      (fun ζ : ℕ → LabeledPopState =>
        (labeledMinCount ζ u, labeledMinCount ζ (u + 1))) :=
    (labeledMinCount_measurable u).prodMk
      (labeledMinCount_measurable (u + 1))
  exact hp ((Set.to_countable
    {q : ℕ × ℕ | q.1 ≤ q.2 + 1}).measurableSet)

private lemma minStepValidUpTo_cylinder (t : ℕ) :
    isCylinderUpTo t
      {ζ : ℕ → LabeledPopState | minStepValidUpTo t ζ} := by
  intro ζ η heq hζ u hu
  simpa only [labeledMinCount, heq u (Nat.le_of_lt hu),
    heq (u + 1) (by omega)] using hζ u hu

/-- On a valid prefix descending from level `m` to level `k`, every
intermediate level has already been visited. -/
private lemma exists_firstLevelAt_between
    (m k ℓ t : ℕ) (ζ : ℕ → LabeledPopState)
    (h0 : labeledMinCount ζ 0 = m)
    (ht : ζ ∈ firstLevelAt k t)
    (hvalid : minStepValidUpTo t ζ)
    (hkℓ : k < ℓ) (hℓm : ℓ ≤ m) :
    ∃ u < t, ζ ∈ firstLevelAt ℓ u := by
  let f := labeledMinCount ζ
  have h0f : f 0 = m := h0
  have htf : f t = k := ht.1
  let hex : ∃ u, f u ≤ ℓ := ⟨t, by
    rw [htf]
    omega⟩
  have hu_le : f (Nat.find hex) ≤ ℓ := Nat.find_spec hex
  have huℓ : f (Nat.find hex) = ℓ := by
    by_cases hu0 : Nat.find hex = 0
    · rw [hu0, h0f] at hu_le ⊢
      omega
    · obtain ⟨r, hr⟩ :=
        Nat.exists_eq_succ_of_ne_zero hu0
      rw [hr] at hu_le ⊢
      have hprev : ¬f r ≤ ℓ :=
        fun hle => Nat.find_min hex (hr ▸ Nat.lt_succ_self r) hle
      have hstep : f r ≤ f (r + 1) + 1 := by
        apply hvalid r
        have hut : Nat.find hex ≤ t :=
          Nat.find_min' hex (by rw [htf]; omega)
        omega
      have hu_le' : f (r + 1) ≤ ℓ := by
        simpa only [Nat.succ_eq_add_one] using hu_le
      change f (r + 1) = ℓ
      omega
  have hut : Nat.find hex ≤ t := Nat.find_min' hex (by
    rw [htf]
    omega)
  have hut' : Nat.find hex < t := by
    by_contra hnot
    have : Nat.find hex = t := by omega
    rw [this, htf] at huℓ
    omega
  refine ⟨Nat.find hex, hut', huℓ, ?_⟩
  intro q hqu hq
  change f q = ℓ at hq
  exact Nat.find_min hex hqu (by
    rw [hq])

private lemma levelIndividual_congr_before_current
    (m k ℓ t : ℕ) (ζ η : ℕ → LabeledPopState)
    (h0 : labeledMinCount ζ 0 = m)
    (ht : ζ ∈ firstLevelAt k t)
    (hvalid : minStepValidUpTo t ζ)
    (hkℓ : k < ℓ) (hℓm : ℓ ≤ m)
    (heq : ∀ u, u ≤ t → ζ u = η u) :
    levelIndividual ℓ ζ = levelIndividual ℓ η := by
  obtain ⟨u, hut, hu⟩ :=
    exists_firstLevelAt_between m k ℓ t ζ h0 ht hvalid hkℓ hℓm
  have huη : η ∈ firstLevelAt ℓ u := by
    apply firstLevelAt_cylinder ℓ u ζ η
    · intro q hq
      exact heq q (hq.trans (Nat.le_of_lt hut))
    · exact hu
  rw [levelIndividual_of_firstLevelAt ℓ u ζ hu,
    levelIndividual_of_firstLevelAt ℓ u η huη,
    heq (u + 1) (by omega)]

private def descendingLevel (m : ℕ) (i : Fin m) : ℕ :=
  m - i.val

private lemma descendingLevel_pos (m : ℕ) (i : Fin m) :
    0 < descendingLevel m i := by
  unfold descendingLevel
  omega

private lemma descendingLevel_le (m : ℕ) (i : Fin m) :
    descendingLevel m i ≤ m := by
  unfold descendingLevel
  omega

private lemma descendingLevel_lt_of_lt
    (m : ℕ) (i j : Fin m) (hji : j < i) :
    descendingLevel m i < descendingLevel m j := by
  unfold descendingLevel
  omega

private lemma bernoulliPastSpace_le_ambient
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → Bool) (hX : ∀ i, Measurable (X i))
    (i : Fin n) :
    bernoulliPastSpace X i ≤ ‹MeasurableSpace Ω› := by
  unfold bernoulliPastSpace
  apply iSup_le
  intro j
  apply iSup_le
  intro _hji
  exact (hX j).comap_le

/-- Membership in an event generated by the earlier Bernoulli variables only
depends on the values of those variables. -/
private lemma bernoulliPast_event_congr
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → Bool) (i : Fin n)
    (A : Set Ω) (hA : MeasurableSet[bernoulliPastSpace X i] A)
    (ω η : Ω)
    (heq : ∀ j : Fin n, j < i → X j ω = X j η)
    (hω : ω ∈ A) :
    η ∈ A := by
  let F : Ω → (Fin i.val → Bool) :=
    fun ξ j => X ⟨j.val, j.2.trans i.2⟩ ξ
  have hpast :
      bernoulliPastSpace X i ≤
        MeasurableSpace.comap F ⊤ := by
    unfold bernoulliPastSpace
    apply iSup_le
    intro j
    apply iSup_le
    intro hji
    have hji' : j.val < i.val := hji
    let G : (Fin i.val → Bool) → Bool :=
      fun p => p ⟨j.val, hji'⟩
    have hfactor : X j = G ∘ F := by
      funext ξ
      rfl
    change MeasurableSpace.comap (X j) ⊤ ≤
      MeasurableSpace.comap F ⊤
    rw [hfactor, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  obtain ⟨C, _hC, hAC⟩ :=
    MeasurableSpace.measurableSet_comap.mp (hpast A hA)
  rw [← hAC] at hω ⊢
  have hF : F ω = F η := by
    funext j
    exact heq ⟨j.val, j.2.trans i.2⟩ j.2
  simpa only [Set.mem_preimage, hF] using hω

private def stoppedLevelBlock
    (s0 : PopState) (m : ℕ) (i : Fin m)
    (A : Set (ℕ → LabeledPopState))
    (t : ℕ) (z : LabeledPopState) :
    Set (ℕ → LabeledPopState) :=
  A ∩ firstLevelBlock (descendingLevel m i) t z ∩
    {ζ | ζ 0 = (s0, .idle)} ∩
      {ζ | minStepValidUpTo t ζ}

private lemma measurableSet_stoppedLevelBlock
    (s0 : PopState) (m : ℕ) (i : Fin m)
    (A : Set (ℕ → LabeledPopState))
    (hA : MeasurableSet A)
    (t : ℕ) (z : LabeledPopState) :
    MeasurableSet (stoppedLevelBlock s0 m i A t z) := by
  exact ((hA.inter
    (measurableSet_firstLevelBlock
      (descendingLevel m i) t z)).inter
      (by measurability)).inter
        (measurableSet_minStepValidUpTo t)

private lemma stoppedLevelBlock_cylinder
    (s0 : PopState) (m : ℕ) (hm : Nat.min s0.1 s0.2 = m)
    (i : Fin m)
    (X : Fin m → (ℕ → LabeledPopState) → Bool)
    (hX : ∀ j, X j = levelIndividual (descendingLevel m j))
    (A : Set (ℕ → LabeledPopState))
    (hA : MeasurableSet[bernoulliPastSpace X i] A)
    (t : ℕ) (z : LabeledPopState) :
    isCylinderUpTo t (stoppedLevelBlock s0 m i A t z) := by
  intro ζ η hpref hζ
  rcases hζ with ⟨⟨⟨hζA, hζlevel⟩, hζ0⟩, hζvalid⟩
  have hηlevel :
      η ∈ firstLevelBlock (descendingLevel m i) t z :=
    firstLevelBlock_cylinder
      (descendingLevel m i) t z ζ η hpref hζlevel
  have hη0 : η 0 = (s0, .idle) := by
    rw [← hpref 0 (Nat.zero_le t)]
    exact hζ0
  have hηvalid : minStepValidUpTo t η :=
    minStepValidUpTo_cylinder t ζ η hpref hζvalid
  have hζmin0 : labeledMinCount ζ 0 = m := by
    change ζ 0 = (s0, .idle) at hζ0
    unfold labeledMinCount
    rw [hζ0]
    exact hm
  have hηA : η ∈ A := by
    apply bernoulliPast_event_congr X i A hA ζ η
    · intro j hji
      simpa only [hX j] using
        (levelIndividual_congr_before_current
          m (descendingLevel m i) (descendingLevel m j) t ζ η
          hζmin0 hζlevel.1 hζvalid
          (descendingLevel_lt_of_lt m i j hji)
          (descendingLevel_le m j) hpref)
    · exact hζA
  exact ⟨⟨⟨hηA, hηlevel⟩, hη0⟩, hηvalid⟩

private lemma stoppedLevelBlock_pairwise
    (s0 : PopState) (m : ℕ) (i : Fin m)
    (A : Set (ℕ → LabeledPopState)) :
    Pairwise fun q q' : ℕ × LabeledPopState =>
      Disjoint
        (stoppedLevelBlock s0 m i A q.1 q.2)
        (stoppedLevelBlock s0 m i A q'.1 q'.2) := by
  intro q q' hne
  exact (firstLevelBlock_pairwise
    (descendingLevel m i) hne).mono
      (by
        intro ζ hζ
        exact hζ.1.1.2)
      (by
        intro ζ hζ
        exact hζ.1.1.2)

private lemma min_step_of_coordinate_steps
    (a b a' b' : ℕ)
    (ha : a ≤ a' + 1) (hb : b ≤ b' + 1) :
    Nat.min a b ≤ Nat.min a' b' + 1 := by
  rcases le_total a' b' with hab | hba
  · simpa only [Nat.min_eq_left hab] using
      (Nat.min_le_left a b).trans ha
  · simpa only [Nat.min_eq_right hba] using
      (Nat.min_le_right a b).trans hb

private lemma reactionTarget_min_step
    (v : LVVariant) (s : PopState) (r : LVReaction)
    (hno0 : r ≠ .intra0) (hno1 : r ≠ .intra1) :
    Nat.min s.1 s.2 ≤
      Nat.min (lvReactionTarget v s r).1
        (lvReactionTarget v s r).2 + 1 := by
  cases v <;> cases r
  all_goals try { contradiction }
  all_goals
    apply min_step_of_coordinate_steps <;>
      simp only [lvReactionTarget] <;> omega

private lemma lvLabeledKernel_ae_no_intra_log
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (z : LabeledPopState) :
    ∀ᵐ z' ∂lvLabeledKernel v params z,
      z'.2 ≠ .intra0 ∧ z'.2 ≠ .intra1 := by
  have h0 :
      ∀ᵐ z' ∂lvLabeledKernel v params z,
        z'.2 ≠ .intra0 := by
    rw [ae_iff]
    calc
      lvLabeledKernel v params z
          {z' | ¬z'.2 ≠ LVReaction.intra0} =
          lvLabeledKernel v params z
            {z' | z'.2 = LVReaction.intra0} := by
              congr 1
              ext z'
              simp
      _ = 0 := by
        rw [lvLabeledKernel_reaction_probability]
        simp [lvReactionWeight, hGamma0]
  have h1 :
      ∀ᵐ z' ∂lvLabeledKernel v params z,
        z'.2 ≠ .intra1 := by
    rw [ae_iff]
    calc
      lvLabeledKernel v params z
          {z' | ¬z'.2 ≠ LVReaction.intra1} =
          lvLabeledKernel v params z
            {z' | z'.2 = LVReaction.intra1} := by
              congr 1
              ext z'
              simp
      _ = 0 := by
        rw [lvLabeledKernel_reaction_probability]
        simp [lvReactionWeight, hGamma1]
  filter_upwards [h0, h1] with z' hz0 hz1
  exact ⟨hz0, hz1⟩

private lemma lvLabeledPath_min_step_ae
    (v : LVVariant) (params : LVParams) (s0 : PopState)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
      ∀ t : ℕ,
        labeledMinCount ζ t ≤ labeledMinCount ζ (t + 1) + 1 := by
  letI : Nonempty LabeledPopState := ⟨(s0, .idle)⟩
  unfold lvLabeledPathMeasure
  let R : LabeledPopState → LabeledPopState → Prop :=
    fun z z' =>
      Nat.min z.1.1 z.1.2 ≤ Nat.min z'.1.1 z'.1.2 + 1
  have hstep :
      ∀ z, ∀ᵐ z' ∂lvLabeledKernel v params z,
        R z z' := by
    intro z
    filter_upwards [
      lvLabeledKernel_ae_reactionTarget v params z,
      lvLabeledKernel_ae_no_intra_log
        v params hGamma0 hGamma1 z] with z' hz' hno
    dsimp [R, labeledMinCount]
    rw [hz']
    exact reactionTarget_min_step v z.1 z'.2 hno.1 hno.2
  have hrel := homogeneousPathMeasure_transition_ae
    (lvLabeledKernel v params) (s0, .idle) R hstep
  filter_upwards [hrel] with ζ hζ
  intro t
  have ht := hζ t
  simpa only [R, labeledMinCount] using ht

private lemma lvLabeledPath_initial_ae
    (v : LVVariant) (params : LVParams) (s0 : PopState) :
    ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
      ζ 0 = (s0, .idle) := by
  letI : Nonempty LabeledPopState := ⟨(s0, .idle)⟩
  rw [ae_iff]
  exact homogeneousPathMeasure_initial_ne_null
    (lvLabeledKernel v params) (s0, .idle)

private lemma exists_stoppedLevelBlock_of_good
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (i : Fin m) (A : Set (ℕ → LabeledPopState))
    (ζ : ℕ → LabeledPopState)
    (hA : ζ ∈ A)
    (h0 : ζ 0 = (s0, .idle))
    (hstep : ∀ t : ℕ,
      labeledMinCount ζ t ≤ labeledMinCount ζ (t + 1) + 1)
    (hcons :
      consensusTime (forgetLVLabels ζ) < ⊤) :
    ∃ q : ℕ × LabeledPopState,
      ζ ∈ stoppedLevelBlock s0 m i A q.1 q.2 := by
  obtain ⟨T, hT⟩ :=
    WithTop.ne_top_iff_exists.mp
      (WithTop.lt_top_iff_ne_top.mp hcons)
  have hstart : labeledMinCount ζ 0 = m := by
    unfold labeledMinCount
    rw [h0]
    exact hm
  have hend : labeledMinCount ζ T = 0 := by
    have hreach :=
      reachedConsensus_at_consensusTime'
        (forgetLVLabels ζ) T hT.symm
    rcases hreach with hleft | hright
    · change (ζ T).1.1 = 0 at hleft
      unfold labeledMinCount
      exact Nat.min_eq_zero_iff.mpr (Or.inl hleft)
    · change (ζ T).1.2 = 0 at hright
      unfold labeledMinCount
      exact Nat.min_eq_zero_iff.mpr (Or.inr hright)
  obtain ⟨t, htT, htk⟩ :=
    discrete_descending_ivt
      (labeledMinCount ζ) T m hstart hend
      (fun t _ht => hstep t)
      (descendingLevel m i) (descendingLevel_le m i)
  let hex : ∃ u, labeledMinCount ζ u =
      descendingLevel m i := ⟨t, htk⟩
  let u := Nat.find hex
  have hu : labeledMinCount ζ u =
      descendingLevel m i := Nat.find_spec hex
  have hfirst : ζ ∈ firstLevelAt (descendingLevel m i) u := by
    refine ⟨hu, ?_⟩
    intro q hqu
    exact fun hq => Nat.find_min hex hqu hq
  refine ⟨(u, ζ u), ?_⟩
  exact ⟨⟨⟨hA, hfirst, rfl⟩, h0⟩,
    fun q hqu => hstep q⟩

private noncomputable def levelIndividualProbability
    (params : LVParams) (k : ℕ) : ℝ :=
  (params.beta + params.delta) /
    ((params.alpha0 + params.alpha1) * k +
      2 * (params.beta + params.delta))

private lemma levelIndividualProbability_pos
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (k : ℕ) :
    0 < levelIndividualProbability params k := by
  unfold levelIndividualProbability
  have hAlpha : 0 ≤ params.alpha0 + params.alpha1 := by
    linarith [params.alpha0_nonneg, params.alpha1_nonneg]
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden :
      0 < (params.alpha0 + params.alpha1) * (k : ℝ) +
        2 * (params.beta + params.delta) := by
    nlinarith [mul_nonneg hAlpha hk]
  exact div_pos hTheta hden

private lemma levelIndividualProbability_le_one
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (k : ℕ) :
    levelIndividualProbability params k ≤ 1 := by
  unfold levelIndividualProbability
  have hAlpha : 0 ≤ params.alpha0 + params.alpha1 := by
    linarith [params.alpha0_nonneg, params.alpha1_nonneg]
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden :
      0 < (params.alpha0 + params.alpha1) * (k : ℝ) +
        2 * (params.beta + params.delta) := by
    nlinarith [mul_nonneg hAlpha hk]
  apply (div_le_one hden).mpr
  nlinarith [mul_nonneg hAlpha hk]

private def nextIndividualEvent : Set (ℕ → LabeledPopState) :=
  {ζ | isIndividualReaction (ζ 1).2}

private lemma measurableSet_nextIndividualEvent :
    MeasurableSet nextIndividualEvent :=
  ((Set.to_countable individualReactionSet).measurableSet.preimage
    (show Measurable
      (fun ζ : ℕ → LabeledPopState => ζ 1) from
        measurable_pi_apply 1))

private def nextIndividualFailure : Set (ℕ → LabeledPopState) :=
  nextIndividualEventᶜ

private lemma measurableSet_nextIndividualFailure :
    MeasurableSet nextIndividualFailure :=
  measurableSet_nextIndividualEvent.compl

private lemma fresh_nextIndividualFailure_le
    (v : LVVariant) (params : LVParams) (z : LabeledPopState)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (k : ℕ) (hk : Nat.min z.1.1 z.1.2 = k)
    (hk0 : 0 < k) :
    homogeneousPathMeasure (Measure.dirac z)
        (lvLabeledKernel v params) nextIndividualFailure ≤
      1 - ENNReal.ofReal (levelIndividualProbability params k) := by
  letI : Nonempty LabeledPopState := ⟨z⟩
  let P := homogeneousPathMeasure (Measure.dirac z)
    (lvLabeledKernel v params)
  letI : IsProbabilityMeasure P := by
    dsimp [P, homogeneousPathMeasure]
    infer_instance
  have hnext :
      P nextIndividualEvent =
        lvLabeledKernel v params z individualReactionSet := by
    change P ((fun ζ : ℕ → LabeledPopState => ζ 1) ⁻¹'
      individualReactionSet) =
        lvLabeledKernel v params z individualReactionSet
    rw [← Measure.map_apply (measurable_pi_apply 1)
      measurableSet_individualReactionSet,
      homogeneousPathMeasure_dirac_marginal,
      kernelIter_one_generic]
  have hlower :
      ENNReal.ofReal (levelIndividualProbability params k) ≤
        lvLabeledKernel v params z individualReactionSet := by
    exact lvLabeledKernel_individual_probability_lb
      v params z hTheta hGamma0 hGamma1 k hk hk0
  calc
    P nextIndividualFailure =
        1 - P nextIndividualEvent := by
      rw [nextIndividualFailure,
        measure_compl measurableSet_nextIndividualEvent
          (measure_ne_top P nextIndividualEvent)]
      simp
    _ = 1 -
        lvLabeledKernel v params z individualReactionSet := by
      rw [hnext]
    _ ≤ 1 -
        ENNReal.ofReal (levelIndividualProbability params k) :=
      tsub_le_tsub_left hlower 1

private lemma stoppedLevel_failure_eq_shift
    (s0 : PopState) (m : ℕ) (i : Fin m)
    (A : Set (ℕ → LabeledPopState))
    (t : ℕ) (z : LabeledPopState) :
    stoppedLevelBlock s0 m i A t z ∩
        {ζ | levelIndividual (descendingLevel m i) ζ = false} =
      stoppedLevelBlock s0 m i A t z ∩
        (pathShift t) ⁻¹' nextIndividualFailure := by
  ext ζ
  constructor
  · rintro ⟨hB, hfalse⟩
    refine ⟨hB, ?_⟩
    change levelIndividual (descendingLevel m i) ζ = false at hfalse
    have hfirst :
        ζ ∈ firstLevelAt (descendingLevel m i) t :=
      hB.1.1.2.1
    rw [levelIndividual_of_firstLevelAt
      (descendingLevel m i) t ζ hfirst] at hfalse
    have hnind : ¬isIndividualReaction (ζ (t + 1)).2 := by
      exact (Bool.decide_false_iff
        (isIndividualReaction (ζ (t + 1)).2)).mp hfalse
    change (pathShift t ζ) ∈ nextIndividualFailure
    simpa only [nextIndividualFailure, Set.mem_compl_iff,
      nextIndividualEvent, Set.mem_setOf_eq, pathShift] using hnind
  · rintro ⟨hB, hfailure⟩
    refine ⟨hB, ?_⟩
    change levelIndividual (descendingLevel m i) ζ = false
    have hfirst :
        ζ ∈ firstLevelAt (descendingLevel m i) t :=
      hB.1.1.2.1
    rw [levelIndividual_of_firstLevelAt
      (descendingLevel m i) t ζ hfirst]
    apply (Bool.decide_false_iff
      (isIndividualReaction (ζ (t + 1)).2)).mpr
    simpa only [Set.mem_preimage, nextIndividualFailure,
      Set.mem_compl_iff, nextIndividualEvent, Set.mem_setOf_eq,
      pathShift] using hfailure

private lemma stoppedLevels_conditional_lower_bound
    (v : LVVariant) (params : LVParams)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hConsensus :
      ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
        consensusTime (forgetLVLabels ζ) < ⊤) :
    let μ := lvLabeledPathMeasure v params s0
    let X : Fin m → (ℕ → LabeledPopState) → Bool :=
      fun i => levelIndividual (descendingLevel m i)
    ∀ (i : Fin m) (A : Set (ℕ → LabeledPopState)),
      MeasurableSet[bernoulliPastSpace X i] A →
        μ.real A * levelIndividualProbability params
            (descendingLevel m i) ≤
          μ.real (A ∩ {ζ | X i ζ = true}) := by
  dsimp only
  let μ := lvLabeledPathMeasure v params s0
  let X : Fin m → (ℕ → LabeledPopState) → Bool :=
    fun i => levelIndividual (descendingLevel m i)
  letI : Nonempty LabeledPopState := ⟨(s0, .idle)⟩
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, lvLabeledPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hXmeas : ∀ j, Measurable (X j) :=
    fun j => levelIndividual_measurable (descendingLevel m j)
  intro i A hA
  have hAmeas : MeasurableSet A :=
    (bernoulliPastSpace_le_ambient X hXmeas i) A hA
  let p : ℝ := levelIndividualProbability params
    (descendingLevel m i)
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hp0 : 0 ≤ p :=
    (levelIndividualProbability_pos params hTheta
      (descendingLevel m i)).le
  have hp1 : p ≤ 1 :=
    levelIndividualProbability_le_one params hTheta
      (descendingLevel m i)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    simpa only [← ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal hp1
  let B : (ℕ × LabeledPopState) →
      Set (ℕ → LabeledPopState) :=
    fun r => stoppedLevelBlock s0 m i A r.1 r.2
  let U : Set (ℕ → LabeledPopState) :=
    ⋃ r : ℕ × LabeledPopState,
      B r ∩ (pathShift r.1) ⁻¹' nextIndividualFailure
  let V : Set (ℕ → LabeledPopState) :=
    ⋃ r : ℕ × LabeledPopState, B r
  let L : Set (ℕ → LabeledPopState) :=
    {ζ | X i ζ = true}
  let F : Set (ℕ → LabeledPopState) :=
    {ζ | X i ζ = false}
  have hBmeas : ∀ r, MeasurableSet (B r) := by
    intro r
    exact measurableSet_stoppedLevelBlock
      s0 m i A hAmeas r.1 r.2
  have hBpair :
      Pairwise fun r r' : ℕ × LabeledPopState =>
        Disjoint (B r) (B r') := by
    exact stoppedLevelBlock_pairwise s0 m i A
  have hpiece : ∀ r : ℕ × LabeledPopState,
      μ (B r ∩ (pathShift r.1) ⁻¹'
          nextIndividualFailure) ≤
        (1 - q) * μ (B r) := by
    intro r
    change homogeneousPathMeasure
        (Measure.dirac (s0, .idle))
        (lvLabeledKernel v params)
        (B r ∩ (pathShift r.1) ⁻¹'
          nextIndividualFailure) ≤
      (1 - q) *
        homogeneousPathMeasure
          (Measure.dirac (s0, .idle))
          (lvLabeledKernel v params) (B r)
    apply homogeneousPathMeasure_markov_bound
      (lvLabeledKernel v params) (s0, .idle) r.1 (1 - q)
      (B r) nextIndividualFailure
      (hBmeas r) measurableSet_nextIndividualFailure
    · exact stoppedLevelBlock_cylinder
        s0 m hm i X (fun _ => rfl) A hA r.1 r.2
    · intro ζ hζ
      have hk :
          Nat.min (ζ r.1).1.1 (ζ r.1).1.2 =
            descendingLevel m i := hζ.1.1.2.1.1
      simpa only [p, q] using
        fresh_nextIndividualFailure_le
          v params (ζ r.1) hTheta hGamma0 hGamma1
          (descendingLevel m i) hk (descendingLevel_pos m i)
  have hcover :
      μ (A ∩ F) ≤ μ U := by
    apply measure_mono_ae
    filter_upwards [
      lvLabeledPath_initial_ae v params s0,
      lvLabeledPath_min_step_ae
        v params s0 hGamma0 hGamma1,
      hConsensus] with ζ hζ0 hζstep hζcons
    intro hζ
    obtain ⟨r, hr⟩ :=
      exists_stoppedLevelBlock_of_good
        s0 m hm i A ζ hζ.1 hζ0 hζstep hζcons
    have hfail :
        ζ ∈ stoppedLevelBlock s0 m i A r.1 r.2 ∩
          {η | levelIndividual
            (descendingLevel m i) η = false} := by
      refine ⟨hr, ?_⟩
      exact hζ.2
    rw [stoppedLevel_failure_eq_shift
      s0 m i A r.1 r.2] at hfail
    exact Set.mem_iUnion.mpr ⟨r, hfail⟩
  have hfailENN :
      μ (A ∩ F) ≤ (1 - q) * μ A := by
    calc
      μ (A ∩ F) ≤ μ U := hcover
      _ ≤ ∑' r : ℕ × LabeledPopState,
          μ (B r ∩ (pathShift r.1) ⁻¹'
            nextIndividualFailure) :=
        measure_iUnion_le _
      _ ≤ ∑' r : ℕ × LabeledPopState,
          (1 - q) * μ (B r) :=
        ENNReal.tsum_le_tsum hpiece
      _ = (1 - q) *
          ∑' r : ℕ × LabeledPopState, μ (B r) := by
        rw [ENNReal.tsum_mul_left]
      _ = (1 - q) * μ V := by
        rw [show μ V =
            ∑' r : ℕ × LabeledPopState, μ (B r) by
          exact measure_iUnion hBpair hBmeas]
      _ ≤ (1 - q) * μ A := by
        apply mul_le_mul_left'
        apply measure_mono
        intro ζ hζ
        simp only [V, Set.mem_iUnion] at hζ
        obtain ⟨r, hr⟩ := hζ
        exact hr.1.1.1
  have hfailReal :
      μ.real (A ∩ F) ≤ (1 - p) * μ.real A := by
    have hreal := (ENNReal.toReal_le_toReal
      (measure_ne_top μ (A ∩ F))
      (ENNReal.mul_ne_top
        (ENNReal.sub_ne_top ENNReal.one_ne_top)
        (measure_ne_top μ A))).mpr hfailENN
    have hqreal : q.toReal = p := by
      dsimp [q]
      exact ENNReal.toReal_ofReal hp0
    simpa only [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top,
      ENNReal.toReal_one, hqreal] using hreal
  have hLmeas : MeasurableSet L :=
    hXmeas i (measurableSet_singleton true)
  have hFmeas : MeasurableSet F :=
    hXmeas i (measurableSet_singleton false)
  have hdisj : Disjoint (A ∩ L) (A ∩ F) := by
    rw [Set.disjoint_left]
    intro ζ hζL hζF
    simp only [Set.mem_inter_iff, L, F,
      Set.mem_setOf_eq] at hζL hζF
    simp [hζL.2] at hζF
  have hunion : (A ∩ L) ∪ (A ∩ F) = A := by
    ext ζ
    simp only [Set.mem_union, Set.mem_inter_iff,
      L, F, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hζ
      cases hXi : X i ζ with
      | false => exact Or.inr ⟨hζ, rfl⟩
      | true => exact Or.inl ⟨hζ, rfl⟩
  have hsplit :
      μ.real A = μ.real (A ∩ L) + μ.real (A ∩ F) := by
    calc
      μ.real A =
          μ.real ((A ∩ L) ∪ (A ∩ F)) := by rw [hunion]
      _ = μ.real (A ∩ L) + μ.real (A ∩ F) :=
        measureReal_union hdisj (hAmeas.inter hFmeas)
  change μ.real A * p ≤ μ.real (A ∩ L)
  nlinarith

/-! ## Independent comparison variables -/

private noncomputable def individualCoin (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true +
    ENNReal.ofReal (1 - p) • Measure.dirac false

private lemma individualCoin_isProbability
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (individualCoin p) := by
  refine ⟨?_⟩
  simp [individualCoin]
  rw [← ENNReal.ofReal_add hp0]
  norm_num
  linarith

private lemma individualCoin_true
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    individualCoin p {true} = ENNReal.ofReal p := by
  simp [individualCoin, Measure.smul_apply, hp0, hp1]

private noncomputable def levelCoins
    (params : LVParams) (m : ℕ) :
    Measure (Fin m → Bool) :=
  Measure.infinitePi fun i : Fin m =>
    individualCoin
      (levelIndividualProbability params (descendingLevel m i))

private lemma levelCoins_isProbability
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) :
    IsProbabilityMeasure (levelCoins params m) := by
  letI : ∀ i : Fin m,
      IsProbabilityMeasure
        (individualCoin
          (levelIndividualProbability params
            (descendingLevel m i))) := by
    intro i
    exact individualCoin_isProbability _
      (levelIndividualProbability_pos params hTheta _).le
      (levelIndividualProbability_le_one params hTheta _)
  unfold levelCoins
  infer_instance

private def levelCoinStep
    {m : ℕ} (i : Fin m) (ω : Fin m → Bool) : Bool :=
  ω i

private lemma levelCoinStep_measurable
    {m : ℕ} (i : Fin m) :
    Measurable (levelCoinStep i) :=
  measurable_pi_apply i

private lemma levelCoinStep_indep
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) :
    iIndepFun levelCoinStep (levelCoins params m) := by
  letI : ∀ i : Fin m,
      IsProbabilityMeasure
        (individualCoin
          (levelIndividualProbability params
            (descendingLevel m i))) := by
    intro i
    exact individualCoin_isProbability _
      (levelIndividualProbability_pos params hTheta _).le
      (levelIndividualProbability_le_one params hTheta _)
  change iIndepFun (fun i ω => id (ω i))
    (Measure.infinitePi fun i : Fin m =>
      individualCoin
        (levelIndividualProbability params
          (descendingLevel m i)))
  exact iIndepFun_infinitePi
    (P := fun i : Fin m =>
      individualCoin
        (levelIndividualProbability params
          (descendingLevel m i)))
    (X := fun _ : Fin m => id)
    (fun _ => measurable_id)

private lemma levelCoins_coin_true
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) (i : Fin m) :
    levelCoins params m
        {ω | levelCoinStep i ω = true} =
      ENNReal.ofReal
        (levelIndividualProbability params
          (descendingLevel m i)) := by
  letI : ∀ j : Fin m,
      IsProbabilityMeasure
        (individualCoin
          (levelIndividualProbability params
            (descendingLevel m j))) := by
    intro j
    exact individualCoin_isProbability _
      (levelIndividualProbability_pos params hTheta _).le
      (levelIndividualProbability_le_one params hTheta _)
  change levelCoins params m
    ((fun ω : Fin m → Bool => ω i) ⁻¹' {true}) =
      ENNReal.ofReal
        (levelIndividualProbability params
          (descendingLevel m i))
  rw [← Measure.map_apply (measurable_pi_apply i)
    (measurableSet_singleton true)]
  unfold levelCoins
  rw [Measure.infinitePi_map_eval]
  exact individualCoin_true _
    (levelIndividualProbability_pos params hTheta _).le
    (levelIndividualProbability_le_one params hTheta _)

private noncomputable def stoppedLevelCount
    (m : ℕ) (ζ : ℕ → LabeledPopState) : ℕ :=
  ∑ i : Fin m,
    if levelIndividual (descendingLevel m i) ζ then 1 else 0

private def levelCoinCount
    (m : ℕ) (ω : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, if levelCoinStep i ω then 1 else 0

private lemma stoppedLevelCount_measurable (m : ℕ) :
    Measurable (stoppedLevelCount m) := by
  unfold stoppedLevelCount
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_of_finite
    (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (levelIndividual_measurable (descendingLevel m i))

private lemma levelCoinCount_measurable (m : ℕ) :
    Measurable (levelCoinCount m) := by
  unfold levelCoinCount
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_of_finite
    (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (levelCoinStep_measurable i)

private lemma stoppedLevels_sum_domination
    (v : LVVariant) (params : LVParams)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hConsensus :
      ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
        consensusTime (forgetLVLabels ζ) < ⊤)
    (r : ℕ) :
    levelCoins params m
        {ω | r ≤ levelCoinCount m ω} ≤
      lvLabeledPathMeasure v params s0
        {ζ | r ≤ stoppedLevelCount m ζ} := by
  let μ := lvLabeledPathMeasure v params s0
  let ν := levelCoins params m
  let X : Fin m → (ℕ → LabeledPopState) → Bool :=
    fun i => levelIndividual (descendingLevel m i)
  let Y : Fin m → (Fin m → Bool) → Bool :=
    fun i => levelCoinStep i
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, lvLabeledPathMeasure, homogeneousPathMeasure]
    infer_instance
  letI : IsProbabilityMeasure ν :=
    levelCoins_isProbability params hTheta m
  have hdom :
      BernoulliConditionallyGECross μ ν X Y := by
    intro i A hA
    have hlower :=
      stoppedLevels_conditional_lower_bound
        v params s0 m hm hTheta hGamma0 hGamma1
        hConsensus i A hA
    have hcoin :
        ν.real {ω | Y i ω = true} =
          levelIndividualProbability params
            (descendingLevel m i) := by
      rw [measureReal_def]
      dsimp [ν, Y]
      rw [levelCoins_coin_true params hTheta m i]
      exact ENNReal.toReal_ofReal
        (levelIndividualProbability_pos
          params hTheta (descendingLevel m i)).le
    simpa only [hcoin] using hlower
  simpa only [μ, ν, X, Y, stoppedLevelCount,
    levelCoinCount] using
    bernoulli_sum_domination_lower_cross
      μ ν m X Y
      (fun i =>
        levelIndividual_measurable (descendingLevel m i))
      (fun i => levelCoinStep_measurable i)
      (levelCoinStep_indep params hTheta m)
      hdom r

private lemma stoppedLevels_lower_tail_le
    (v : LVVariant) (params : LVParams)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hConsensus :
      ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
        consensusTime (forgetLVLabels ζ) < ⊤)
    (r : ℕ) :
    lvLabeledPathMeasure v params s0
        {ζ | stoppedLevelCount m ζ < r} ≤
      levelCoins params m
        {ω | levelCoinCount m ω < r} := by
  let μ := lvLabeledPathMeasure v params s0
  let ν := levelCoins params m
  let A : Set (ℕ → LabeledPopState) :=
    {ζ | r ≤ stoppedLevelCount m ζ}
  let B : Set (Fin m → Bool) :=
    {ω | r ≤ levelCoinCount m ω}
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, lvLabeledPathMeasure, homogeneousPathMeasure]
    infer_instance
  letI : IsProbabilityMeasure ν :=
    levelCoins_isProbability params hTheta m
  have hAmeas : MeasurableSet A :=
    (stoppedLevelCount_measurable m) measurableSet_Ici
  have hBmeas : MeasurableSet B :=
    (levelCoinCount_measurable m) measurableSet_Ici
  have hdom : ν B ≤ μ A := by
    simpa only [μ, ν, A, B] using
      stoppedLevels_sum_domination
        v params s0 m hm hTheta hGamma0 hGamma1
        hConsensus r
  have hcompl : μ Aᶜ ≤ ν Bᶜ := by
    rw [measure_compl hAmeas (measure_ne_top μ A),
      measure_compl hBmeas (measure_ne_top ν B)]
    simpa only [measure_univ] using
      (tsub_le_tsub_left hdom 1)
  simpa only [μ, ν, A, B, Set.compl_setOf,
    not_le] using hcompl

private noncomputable def levelCoinMean
    (params : LVParams) (m : ℕ) : ℝ :=
  ∑ i : Fin m,
    levelIndividualProbability params (descendingLevel m i)

private def levelCoinCountReal
    (m : ℕ) (ω : Fin m → Bool) : ℝ :=
  ∑ i : Fin m, if levelCoinStep i ω then 1 else 0

private lemma levelCoinCountReal_rep
    (m : ℕ) (ω : Fin m → Bool) :
    levelCoinCountReal m ω =
      ∑ i : Fin m,
        if levelCoinStep i ω then (1 : ℝ) else 0 := rfl

private lemma levelCoin_indicator_integral
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) (i : Fin m) :
    ∫ ω, (if levelCoinStep i ω then (1 : ℝ) else 0)
        ∂levelCoins params m =
      levelIndividualProbability params
        (descendingLevel m i) := by
  let L : Set (Fin m → Bool) :=
    {ω | levelCoinStep i ω = true}
  have hL : MeasurableSet L :=
    (levelCoinStep_measurable i)
      (measurableSet_singleton true)
  have hfun :
      (fun ω : Fin m → Bool =>
          if levelCoinStep i ω then (1 : ℝ) else 0) =
        L.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : levelCoinStep i ω = true
    · simp [L, h]
    · have hf := Bool.eq_false_of_not_eq_true h
      simp [L, h, hf]
  rw [hfun]
  calc
    ∫ ω, L.indicator (fun _ => (1 : ℝ)) ω
        ∂levelCoins params m =
        (levelCoins params m).real L := by
          simpa only [smul_eq_mul, mul_one] using
            (integral_indicator_const
              (μ := levelCoins params m) (1 : ℝ) hL)
    _ = levelIndividualProbability params
          (descendingLevel m i) := by
      rw [measureReal_def,
        levelCoins_coin_true params hTheta m i]
      exact ENNReal.toReal_ofReal
        (levelIndividualProbability_pos params hTheta _).le

private lemma levelCoinCountReal_integral
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) :
    ∫ ω, levelCoinCountReal m ω
        ∂levelCoins params m =
      levelCoinMean params m := by
  letI : IsProbabilityMeasure (levelCoins params m) :=
    levelCoins_isProbability params hTheta m
  unfold levelCoinCountReal levelCoinMean
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun i _hi =>
      levelCoin_indicator_integral params hTheta m i
  · intro i _hi
    have hmeas :
        Measurable (fun ω : Fin m → Bool =>
          if levelCoinStep i ω then (1 : ℝ) else 0) :=
      (measurable_of_finite
        (fun b : Bool => if b then (1 : ℝ) else 0)).comp
          (levelCoinStep_measurable i)
    exact Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
      (ae_of_all _ (by
        intro ω
        cases levelCoinStep i ω <;> simp))

private lemma levelCoins_lower_tail
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) :
    levelCoins params m
        {ω | levelCoinCount m ω <
          Nat.ceil (levelCoinMean params m / 2)} ≤
      ENNReal.ofReal
        (Real.exp (-(levelCoinMean params m) / 8)) := by
  letI : IsProbabilityMeasure (levelCoins params m) :=
    levelCoins_isProbability params hTheta m
  have hchernoff :=
    lemma_chernoff_lower
      (levelCoins params m) m
      (fun i : Fin m => levelCoinStep i)
      (levelCoinCountReal m)
      (levelCoinCountReal_rep m)
      (fun i => levelCoinStep_measurable i)
      (levelCoinStep_indep params hTheta m)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [levelCoinCountReal_integral
    params hTheta m] at hchernoff
  calc
    levelCoins params m
        {ω | levelCoinCount m ω <
          Nat.ceil (levelCoinMean params m / 2)}
        ≤ levelCoins params m
          {ω | levelCoinCountReal m ω ≤
            (1 - (1 / 2 : ℝ)) *
              levelCoinMean params m} := by
        apply measure_mono
        intro ω hω
        have hlt :
            (levelCoinCount m ω : ℝ) <
              levelCoinMean params m / 2 :=
          Nat.lt_ceil.mp hω
        have heq :
            levelCoinCountReal m ω =
              (levelCoinCount m ω : ℝ) := by
          unfold levelCoinCountReal levelCoinCount
          push_cast
          rfl
        change levelCoinCountReal m ω ≤
          (1 - (1 / 2 : ℝ)) * levelCoinMean params m
        rw [heq]
        linarith
    _ ≤ ENNReal.ofReal
        (Real.exp
          (-(levelCoinMean params m) *
            (1 / 2 : ℝ) ^ (2 : ℕ) / 2)) :=
      hchernoff
    _ = ENNReal.ofReal
        (Real.exp (-(levelCoinMean params m) / 8)) := by
      apply congrArg ENNReal.ofReal
      apply congrArg Real.exp
      ring

private lemma stoppedLevels_chernoff_lower_tail
    (v : LVVariant) (params : LVParams)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hConsensus :
      ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
        consensusTime (forgetLVLabels ζ) < ⊤) :
    lvLabeledPathMeasure v params s0
        {ζ | stoppedLevelCount m ζ <
          Nat.ceil (levelCoinMean params m / 2)} ≤
      ENNReal.ofReal
        (Real.exp (-(levelCoinMean params m) / 8)) := by
  exact (stoppedLevels_lower_tail_le
    v params s0 m hm hTheta hGamma0 hGamma1 hConsensus
    (Nat.ceil (levelCoinMean params m / 2))).trans
      (levelCoins_lower_tail params hTheta m)

private noncomputable def successfulLevelTime
    (k : ℕ) (ζ : ℕ → LabeledPopState) : ℕ := by
  classical
  exact if h : ∃ t : ℕ, ζ ∈ firstLevelAt k t ∧
      isIndividualReaction (ζ (t + 1)).2
    then Nat.find h
    else 0

private lemma successfulLevelTime_spec
    (k : ℕ) (ζ : ℕ → LabeledPopState)
    (h : levelIndividual k ζ = true) :
    ζ ∈ firstLevelAt k (successfulLevelTime k ζ) ∧
      isIndividualReaction
        (ζ (successfulLevelTime k ζ + 1)).2 := by
  classical
  have hex : ∃ t : ℕ, ζ ∈ firstLevelAt k t ∧
      isIndividualReaction (ζ (t + 1)).2 := by
    unfold levelIndividual at h
    split at h
    · assumption
    · simp at h
  unfold successfulLevelTime
  rw [dif_pos hex]
  exact Nat.find_spec hex

private lemma exists_firstLevelAt_before_consensus
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (i : Fin m) (ζ : ℕ → LabeledPopState)
    (h0 : ζ 0 = (s0, .idle))
    (hstep : ∀ t : ℕ,
      labeledMinCount ζ t ≤ labeledMinCount ζ (t + 1) + 1)
    (T : ℕ)
    (hT : consensusTime (forgetLVLabels ζ) = (T : WithTop ℕ)) :
    ∃ t < T, ζ ∈ firstLevelAt (descendingLevel m i) t := by
  have hstart : labeledMinCount ζ 0 = m := by
    unfold labeledMinCount
    rw [h0]
    exact hm
  have hend : labeledMinCount ζ T = 0 := by
    have hreach :=
      reachedConsensus_at_consensusTime'
        (forgetLVLabels ζ) T hT
    rcases hreach with hleft | hright
    · change (ζ T).1.1 = 0 at hleft
      unfold labeledMinCount
      exact Nat.min_eq_zero_iff.mpr (Or.inl hleft)
    · change (ζ T).1.2 = 0 at hright
      unfold labeledMinCount
      exact Nat.min_eq_zero_iff.mpr (Or.inr hright)
  obtain ⟨t, htT, htk⟩ :=
    discrete_descending_ivt
      (labeledMinCount ζ) T m hstart hend
      (fun t _ht => hstep t)
      (descendingLevel m i) (descendingLevel_le m i)
  have htT' : t < T := by
    by_contra hnot
    have : t = T := by omega
    subst t
    rw [hend] at htk
    exact (Nat.ne_of_gt (descendingLevel_pos m i)) htk.symm
  let hex : ∃ u, labeledMinCount ζ u =
      descendingLevel m i := ⟨t, htk⟩
  let u := Nat.find hex
  have hu : labeledMinCount ζ u =
      descendingLevel m i := Nat.find_spec hex
  have hut : u ≤ t := Nat.find_min' hex htk
  refine ⟨u, hut.trans_lt htT', hu, ?_⟩
  intro q hqu
  exact fun hq => Nat.find_min hex hqu hq

private lemma stoppedLevelCount_le_labeledCount
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (ζ : ℕ → LabeledPopState)
    (h0 : ζ 0 = (s0, .idle))
    (hstep : ∀ t : ℕ,
      labeledMinCount ζ t ≤ labeledMinCount ζ (t + 1) + 1)
    (T : ℕ)
    (hT : consensusTime (forgetLVLabels ζ) = (T : WithTop ℕ)) :
    stoppedLevelCount m ζ ≤
      labeledIndividualCountBeforeConsensus ζ := by
  classical
  let S : Finset (Fin m) :=
    Finset.univ.filter fun i =>
      levelIndividual (descendingLevel m i) ζ = true
  let R : Finset ℕ :=
    (Finset.range T).filter fun t =>
      isIndividualReaction (ζ (t + 1)).2
  let f : Fin m → ℕ :=
    fun i => successfulLevelTime (descendingLevel m i) ζ
  have hmap : Set.MapsTo f S R := by
    intro i hi
    change i ∈ S at hi
    have hi' :
        levelIndividual (descendingLevel m i) ζ = true := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ,
        true_and] using hi
    have hspec :=
      successfulLevelTime_spec
        (descendingLevel m i) ζ hi'
    obtain ⟨u, huT, hfirst⟩ :=
      exists_firstLevelAt_before_consensus
        s0 m hm i ζ h0 hstep T hT
    have heq :
        f i = u := by
      exact firstLevelAt_unique
        (descendingLevel m i) (f i) u ζ hspec.1 hfirst
    change f i ∈ R
    simp only [R, Finset.mem_filter, Finset.mem_range]
    constructor
    · rw [heq]
      exact huT
    · exact hspec.2
  have hinj : (S : Set (Fin m)).InjOn f := by
    intro i hi j hj hij
    change i ∈ S at hi
    change j ∈ S at hj
    have hi' :
        levelIndividual (descendingLevel m i) ζ = true := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ,
        true_and] using hi
    have hj' :
        levelIndividual (descendingLevel m j) ζ = true := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ,
        true_and] using hj
    have hispec :=
      successfulLevelTime_spec
        (descendingLevel m i) ζ hi'
    have hjspec :=
      successfulLevelTime_spec
        (descendingLevel m j) ζ hj'
    have hlevels :
        descendingLevel m i = descendingLevel m j := by
      calc
        descendingLevel m i =
            labeledMinCount ζ (f i) := hispec.1.1.symm
        _ = labeledMinCount ζ (f j) := by rw [hij]
        _ = descendingLevel m j := hjspec.1.1
    apply Fin.ext
    unfold descendingLevel at hlevels
    omega
  have hcard : S.card ≤ R.card :=
    Finset.card_le_card_of_injOn f hmap hinj
  have hS :
      stoppedLevelCount m ζ = S.card := by
    simp [stoppedLevelCount, S]
  have hR :
      R.card = labeledIndividualCountUpTo ζ T := by
    symm
    simp [R, labeledIndividualCountUpTo]
  rw [hS]
  unfold labeledIndividualCountBeforeConsensus
  rw [hT]
  change S.card ≤ labeledIndividualCountUpTo ζ T
  rw [← hR]
  exact hcard

/-- Finite-`m` stopped-level conclusion: before consensus, the number of
individual reactions has the same Chernoff lower tail as the independent
level comparison variables. -/
theorem labeledIndividualCount_chernoff
    (v : LVVariant) (params : LVParams)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hConsensus :
      ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
        consensusTime (forgetLVLabels ζ) < ⊤) :
    lvLabeledPathMeasure v params s0
        {ζ | labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil (levelCoinMean params m / 2)} ≤
      ENNReal.ofReal
        (Real.exp (-(levelCoinMean params m) / 8)) := by
  have hcount :
      lvLabeledPathMeasure v params s0
          {ζ | labeledIndividualCountBeforeConsensus ζ <
            Nat.ceil (levelCoinMean params m / 2)} ≤
        lvLabeledPathMeasure v params s0
          {ζ | stoppedLevelCount m ζ <
            Nat.ceil (levelCoinMean params m / 2)} := by
    apply measure_mono_ae
    filter_upwards [
      lvLabeledPath_initial_ae v params s0,
      lvLabeledPath_min_step_ae
        v params s0 hGamma0 hGamma1,
      hConsensus] with ζ hζ0 hζstep hζcons
    intro hζ
    obtain ⟨T, hT⟩ :=
      WithTop.ne_top_iff_exists.mp
        (WithTop.lt_top_iff_ne_top.mp hζcons)
    have hle :=
      stoppedLevelCount_le_labeledCount
        s0 m hm ζ hζ0 hζstep T hT.symm
    exact hle.trans_lt hζ
  exact hcount.trans
    (stoppedLevels_chernoff_lower_tail
      v params s0 m hm hTheta hGamma0 hGamma1 hConsensus)

private noncomputable def logIndividualConstant
    (params : LVParams) : ℝ :=
  (params.beta + params.delta) /
    ((params.alpha0 + params.alpha1) +
      2 * (params.beta + params.delta))

private lemma logIndividualConstant_pos
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta) :
    0 < logIndividualConstant params := by
  unfold logIndividualConstant
  have hAlpha : 0 ≤ params.alpha0 + params.alpha1 := by
    linarith [params.alpha0_nonneg, params.alpha1_nonneg]
  have hden :
      0 < (params.alpha0 + params.alpha1) +
        2 * (params.beta + params.delta) := by
    linarith
  exact div_pos hTheta hden

private lemma reciprocal_level_le_probability
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (k : ℕ) (hk : 0 < k) :
    logIndividualConstant params / k ≤
      levelIndividualProbability params k := by
  let θ := params.beta + params.delta
  let α := params.alpha0 + params.alpha1
  have hα : 0 ≤ α := by
    dsimp [α]
    linarith [params.alpha0_nonneg, params.alpha1_nonneg]
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hθ : 0 < θ := hTheta
  have hbase : 0 < α + 2 * θ := by
    dsimp [θ]
    linarith
  have hden : 0 < α * (k : ℝ) + 2 * θ := by
    nlinarith [mul_nonneg hα hkR.le]
  unfold logIndividualConstant levelIndividualProbability
  change θ / (α + 2 * θ) / (k : ℝ) ≤
    θ / (α * (k : ℝ) + 2 * θ)
  rw [div_le_div_iff₀ hkR hden, div_mul_eq_mul_div,
    div_le_iff₀ hbase]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  ring_nf
  nlinarith [sq_pos_of_pos hθ]

private lemma levelCoinMean_harmonic_lower
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) :
    logIndividualConstant params * (harmonic m : ℝ) ≤
      levelCoinMean params m := by
  let c := logIndividualConstant params
  have hterm : ∀ i : Fin m,
      c / (descendingLevel m i : ℝ) ≤
        levelIndividualProbability params
          (descendingLevel m i) := by
    intro i
    exact reciprocal_level_le_probability
      params hTheta (descendingLevel m i)
        (descendingLevel_pos m i)
  have hsum :
      (∑ i : Fin m, c / (descendingLevel m i : ℝ)) =
        c * (harmonic m : ℝ) := by
    change (∑ i : Fin m,
      c / ((m - i.val : ℕ) : ℝ)) =
        c * (harmonic m : ℝ)
    have hfin :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ =>
          c / ((m - i : ℕ) : ℝ)) m
    rw [hfin]
    change (∑ i ∈ Finset.range m,
      c / ((m - i : ℕ) : ℝ)) =
        c * (harmonic m : ℝ)
    have hreflect :
        (∑ i ∈ Finset.range m,
            c / ((m - i : ℕ) : ℝ)) =
          ∑ k ∈ Finset.range m,
            c / (((k : ℝ) + 1)) := by
      rw [← Finset.sum_range_reflect
        (fun k => c / ((k : ℝ) + 1)) m]
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      congr 1
      norm_cast
      omega
    rw [hreflect, harmonic_cast_eq_sum_real,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  rw [← hsum]
  unfold levelCoinMean
  exact Finset.sum_le_sum fun i _hi => hterm i

private lemma levelCoinMean_log_lower
    (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (m : ℕ) :
    logIndividualConstant params * Real.log (m + 1) ≤
      levelCoinMean params m := by
  have hc :
      0 ≤ logIndividualConstant params :=
    (logIndividualConstant_pos params hTheta).le
  have hlog :
      Real.log ((m : ℝ) + 1) ≤ (harmonic m : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (log_add_one_le_harmonic m)
  exact (mul_le_mul_of_nonneg_left
    hlog hc).trans
      (levelCoinMean_harmonic_lower params hTheta m)

/-- Logarithmic lower tail in the form stated in the paper.  The constants
are explicit: `f = c/2` and `g = c/8`, where
`c = (β+δ)/(α₀+α₁+2(β+δ))`. -/
theorem labeledIndividualCount_log_lower_tail
    (v : LVVariant) (params : LVParams)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hTheta : 0 < params.beta + params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (hConsensus :
      ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
        consensusTime (forgetLVLabels ζ) < ⊤) :
    lvLabeledPathMeasure v params s0
        {ζ | labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil
            (logIndividualConstant params *
              Real.log (m + 1) / 2)} ≤
      ENNReal.ofReal
        (Real.exp
          (-(logIndividualConstant params *
            Real.log (m + 1)) / 8)) := by
  have hmean :=
    levelCoinMean_log_lower params hTheta m
  calc
    lvLabeledPathMeasure v params s0
        {ζ | labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil
            (logIndividualConstant params *
              Real.log (m + 1) / 2)}
      ≤ lvLabeledPathMeasure v params s0
          {ζ | labeledIndividualCountBeforeConsensus ζ <
            Nat.ceil (levelCoinMean params m / 2)} := by
        apply measure_mono
        intro ζ hζ
        exact hζ.trans_le (Nat.ceil_mono (by linarith))
    _ ≤ ENNReal.ofReal
        (Real.exp (-(levelCoinMean params m) / 8)) :=
      labeledIndividualCount_chernoff
        v params s0 m hm hTheta hGamma0 hGamma1 hConsensus
    _ ≤ ENNReal.ofReal
        (Real.exp
          (-(logIndividualConstant params *
            Real.log (m + 1)) / 8)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith

private lemma measurableSet_consensusTime_top :
    MeasurableSet
      {ω : ℕ → PopState | consensusTime ω = ⊤} := by
  rw [show {ω : ℕ → PopState | consensusTime ω = ⊤} =
      (⋃ t : ℕ,
        {ω | consensusTime ω = (t : WithTop ℕ)})ᶜ by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
      Set.mem_iUnion, not_exists]
    constructor
    · intro htop t
      intro heq
      exact WithTop.coe_ne_top (heq.symm.trans htop)
    · intro h
      cases hct : consensusTime ω with
      | top => rfl
      | coe t => exact (h t hct).elim]
  exact (MeasurableSet.iUnion fun t =>
    measurableSet_consensusTime_eq_coe t).compl

private lemma labeled_consensus_ae_of_expected_ne_top
    (v : LVVariant) (params : LVParams) (s0 : PopState)
    (hfinite : expectedConsensusTimeTail v params s0 ≠ ⊤) :
    ∀ᵐ ζ ∂lvLabeledPathMeasure v params s0,
      consensusTime (forgetLVLabels ζ) < ⊤ := by
  let μ := lvPathMeasure v params s0
  have hlim :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top
      (by simpa only [expectedConsensusTimeTail] using hfinite)
  have htop_le :
      μ {ω | consensusTime ω = ⊤} ≤ 0 := by
    apply ge_of_tendsto' hlim
    intro t
    change lvPathMeasure v params s0
        {ω | consensusTime ω = ⊤} ≤
      consensusTail v params s0 (t + 1)
    apply measure_mono
    intro ω hω
    change (t + 1 : WithTop ℕ) ≤ consensusTime ω
    rw [hω]
    exact le_top
  have htop :
      μ {ω | consensusTime ω = ⊤} = 0 :=
    bot_unique htop_le
  rw [ae_iff]
  rw [show {ζ | ¬consensusTime (forgetLVLabels ζ) < ⊤} =
      {ζ | consensusTime (forgetLVLabels ζ) = ⊤} by
    ext ζ
    simp]
  calc
    lvLabeledPathMeasure v params s0
        {ζ | consensusTime (forgetLVLabels ζ) = ⊤} =
      (lvLabeledPathMeasure v params s0).map
        forgetLVLabels
        {ω | consensusTime ω = ⊤} := by
          symm
          exact Measure.map_apply
            measurable_forgetLVLabels
            measurableSet_consensusTime_top
    _ = μ {ω | consensusTime ω = ⊤} := by
      rw [lvLabeledPathMeasure_map_forget]
    _ = 0 := htop

/-- Unconditional logarithmic lower tail.  The positivity of
`effectiveGoodRate` is used only to construct the nice dominating chain and
deduce almost-sure consensus; no certificate or path-law assumption appears
in the statement. -/
theorem labeledIndividualCount_log_lower_tail_unconditional
    (v : LVVariant) (params : LVParams)
    (hTheta : 0 < params.beta + params.delta)
    (hGood : 0 < effectiveGoodRate v params)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) (m : ℕ)
    (hm : Nat.min s0.1 s0.2 = m)
    (hm0 : 0 < m) :
    lvLabeledPathMeasure v params s0
        {ζ | labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil
            (logIndividualConstant params *
              Real.log (m + 1) / 2)} ≤
      ENNReal.ofReal
        (Real.exp
          (-(logIndividualConstant params *
            Real.log (m + 1)) / 8)) := by
  obtain ⟨N, hDom⟩ :=
    lemma_domination v params hGood hGamma0 hGamma1
  obtain ⟨⟨C, hC, hExpected⟩, _hWhp,
      _hBadMean, _hBadWhp⟩ :=
    thm_nice_upper_domination
      v params hGamma0 hGamma1 N hDom
  have htotal : 0 < s0.1 + s0.2 := by
    have hmle : m ≤ s0.1 :=
      hm ▸ Nat.min_le_left s0.1 s0.2
    omega
  have hbound :=
    hExpected s0 htotal
  have hfinite :
      expectedConsensusTimeTail v params s0 ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  exact labeledIndividualCount_log_lower_tail
    v params s0 m hm hTheta hGamma0 hGamma1
      (labeled_consensus_ae_of_expected_ne_top
        v params s0 hfinite)

/-- Paper-facing logarithmic individual-events lemma for neutral systems.
The displayed probability is the lower-tail form of
`I(S) ≥ f log m` with probability at least `1 - m⁻ᵍ`. -/
theorem lemma_log_individual_events_full
    (v : LVVariant) (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hTheta : 0 < params.beta + params.delta)
    (hAlpha : 0 < params.alpha0 + params.alpha1)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∃ f g : ℝ, 0 < f ∧ 0 < g ∧
      ∀ (s0 : PopState) (m : ℕ),
        Nat.min s0.1 s0.2 = m → 0 < m →
          lvLabeledPathMeasure v params s0
              {ζ | labeledIndividualCountBeforeConsensus ζ <
                Nat.ceil (f * Real.log m)} ≤
            ENNReal.ofReal
              (Real.exp (-(g * Real.log m))) := by
  have hGood : 0 < effectiveGoodRate v params := by
    cases v with
    | selfDestructive =>
        simpa only [effectiveGoodRate] using hAlpha
    | nonSelfDestructive =>
        have ha0 : 0 < params.alpha0 := by
          rw [hNeutral] at hAlpha
          linarith
        have ha1 : 0 < params.alpha1 := by
          rw [← hNeutral]
          exact ha0
        simpa only [effectiveGoodRate] using lt_min ha0 ha1
  let c := logIndividualConstant params
  have hc : 0 < c :=
    logIndividualConstant_pos params hTheta
  refine ⟨c / 2, c / 8, by positivity, by positivity, ?_⟩
  intro s0 m hm hm0
  have hbase :=
    labeledIndividualCount_log_lower_tail_unconditional
      v params hTheta hGood hGamma0 hGamma1 s0 m hm hm0
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast hm0
  have hlog :
      Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log hmR (by linarith)
  have hthreshold :
      c / 2 * Real.log (m : ℝ) ≤
        c * Real.log ((m : ℝ) + 1) / 2 := by
    calc
      c / 2 * Real.log (m : ℝ) ≤
          c / 2 * Real.log ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = c * Real.log ((m : ℝ) + 1) / 2 := by ring
  calc
    lvLabeledPathMeasure v params s0
        {ζ | labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil (c / 2 * Real.log m)}
      ≤ lvLabeledPathMeasure v params s0
          {ζ | labeledIndividualCountBeforeConsensus ζ <
            Nat.ceil
              (logIndividualConstant params *
                Real.log (m + 1) / 2)} := by
        apply measure_mono
        intro ζ hζ
        change labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil (c / 2 * Real.log m) at hζ
        change labeledIndividualCountBeforeConsensus ζ <
          Nat.ceil
            (logIndividualConstant params *
              Real.log (m + 1) / 2)
        apply hζ.trans_le
        apply Nat.ceil_mono
        simpa only [c, Nat.cast_add, Nat.cast_one] using hthreshold
    _ ≤ ENNReal.ofReal
        (Real.exp
          (-(logIndividualConstant params *
            Real.log (m + 1)) / 8)) :=
      hbase
    _ ≤ ENNReal.ofReal
        (Real.exp (-(c / 8 * Real.log m))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hmul :
          c * Real.log (m : ℝ) ≤
            c * Real.log ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlog hc.le
      simpa only [c, Nat.cast_add, Nat.cast_one] using
        (show
          -(c * Real.log ((m : ℝ) + 1)) / 8 ≤
            -(c / 8 * Real.log (m : ℝ)) by
          linarith)

end LVConsensus
