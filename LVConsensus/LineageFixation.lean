import LVConsensus.LineageAggregation

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal

namespace LVConsensus

lemma measurable_permuteLineageCounts
    {n : Nat} (π : Equiv.Perm (Lineage n)) :
    Measurable (permuteLineageCounts π : LinState n → LinState n) :=
  measurable_of_countable _

lemma measurable_lineageAggregate
    (a : Nat) {n : Nat} :
    Measurable (lineageAggregate a : LinState n → PopState) :=
  measurable_of_countable _

/-- A path event is equivariant under every permutation of the initial
lineage labels.  This is the path-space version of
`lineageKernel_equivariant`. -/
theorem lineagePathMeasure_permute
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) :
    (lineagePathMeasure params n).map
        (pathMap (permuteLineageCounts π)) =
      lineagePathMeasure params n := by
  unfold lineagePathMeasure
  rw [← initialLineages_permute π]
  exact homogeneousPathMeasure_map_pathMap
    (lineageKernel params n)
    (lineageKernel params n)
    (permuteLineageCounts π)
    (measurable_permuteLineageCounts π)
    (fun L => (lineageKernel_equivariant params π L).symm)
    (initialLineages n)

/-- At a lineage state, `i` is the only initial lineage with living
descendants. -/
def soleLineage {n : Nat} (i : Lineage n) (L : LinState n) : Prop :=
  0 < L i ∧ ∀ j, j ≠ i → L j = 0

/-- The event that `i` is the first lineage to occur as the sole living
initial lineage.  The explicit first-occurrence condition makes these events
disjoint on all paths, including paths outside the support of the Markov
chain. -/
def lineageWinnerEvent {n : Nat} (i : Lineage n)
    (ω : Nat → LinState n) : Prop :=
  ∃ t, soleLineage i (ω t) ∧
    ∀ u < t, ∀ j, ¬soleLineage j (ω u)

lemma soleLineage_unique
    {n : Nat} {i j : Lineage n} {L : LinState n}
    (hi : soleLineage i L) (hj : soleLineage j L) :
    i = j := by
  by_contra hij
  have hz := hi.2 j (Ne.symm hij)
  exact (Nat.ne_of_gt hj.1) hz

lemma lineageWinnerEvent_disjoint
    {n : Nat} {i j : Lineage n} (hij : i ≠ j) :
    Disjoint
      {ω : Nat → LinState n | lineageWinnerEvent i ω}
      {ω : Nat → LinState n | lineageWinnerEvent j ω} := by
  rw [Set.disjoint_left]
  intro ω hi hj
  rcases hi with ⟨ti, hit, hbeforei⟩
  rcases hj with ⟨tj, hjt, hbeforej⟩
  rcases lt_trichotomy ti tj with hlt | heq | hgt
  · exact hbeforej ti hlt i hit
  · exact hij (soleLineage_unique hit (heq ▸ hjt))
  · exact hbeforei tj hgt j hjt

lemma measurableSet_lineageWinnerEvent
    {n : Nat} (i : Lineage n) :
    MeasurableSet
      {ω : Nat → LinState n | lineageWinnerEvent i ω} := by
  classical
  have hsole : ∀ (j : Lineage n) (t : Nat),
      MeasurableSet {ω : Nat → LinState n | soleLineage j (ω t)} := by
    intro j t
    have hs : MeasurableSet {L : LinState n | soleLineage j L} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    exact hs.preimage (measurable_pi_apply t)
  have hset :
      {ω : Nat → LinState n | lineageWinnerEvent i ω} =
        ⋃ t : Nat,
          {ω | soleLineage i (ω t)} ∩
            ⋂ u ∈ Finset.range t,
              ⋂ j : Lineage n, {ω | soleLineage j (ω u)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
    constructor
    · rintro ⟨t, hit, hbefore⟩
      exact ⟨t, hit, fun u hu j => hbefore u hu j⟩
    · rintro ⟨t, hit, hbefore⟩
      exact ⟨t, hit, fun u hu j => hbefore u hu j⟩
  rw [hset]
  exact MeasurableSet.iUnion fun t =>
    (hsole i t).inter
      (MeasurableSet.biInter (Finset.range t).countable_toSet fun u _ =>
        MeasurableSet.iInter fun j => (hsole j u).compl)

lemma soleLineage_permute_iff
    {n : Nat} (π : Equiv.Perm (Lineage n))
    (i : Lineage n) (L : LinState n) :
    soleLineage i (permuteLineageCounts π L) ↔
      soleLineage (π i) L := by
  constructor
  · rintro ⟨hi, hzero⟩
    refine ⟨hi, ?_⟩
    intro j hji
    have hpre : π.symm j ≠ i := by
      intro h
      apply hji
      simpa using congrArg π h
    simpa [permuteLineageCounts] using hzero (π.symm j) hpre
  · rintro ⟨hi, hzero⟩
    refine ⟨hi, ?_⟩
    intro j hji
    exact hzero (π j) (fun h => hji (π.injective h))

lemma lineageWinnerEvent_permute_iff
    {n : Nat} (π : Equiv.Perm (Lineage n))
    (i : Lineage n) (ω : Nat → LinState n) :
    lineageWinnerEvent i
        (pathMap (permuteLineageCounts π) ω) ↔
      lineageWinnerEvent (π i) ω := by
  simp only [lineageWinnerEvent, pathMap, soleLineage_permute_iff]
  constructor
  · rintro ⟨t, hit, hbefore⟩
    refine ⟨t, hit, ?_⟩
    intro u hu j hj
    exact hbefore u hu (π.symm j) (by simpa using hj)
  · rintro ⟨t, hit, hbefore⟩
    refine ⟨t, hit, ?_⟩
    intro u hu j hj
    exact hbefore u hu (π j) hj

lemma lineageWinnerEvent_measure_invariant
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (i : Lineage n) :
    lineagePathMeasure params n
        {ω | lineageWinnerEvent i ω} =
      lineagePathMeasure params n
        {ω | lineageWinnerEvent (π i) ω} := by
  let P := lineagePathMeasure params n
  have hpath := lineagePathMeasure_permute params π
  have hmeas := measurableSet_lineageWinnerEvent i
  have hpre :
      (pathMap (permuteLineageCounts π)) ⁻¹'
          {ω | lineageWinnerEvent i ω} =
        {ω | lineageWinnerEvent (π i) ω} := by
    ext ω
    exact lineageWinnerEvent_permute_iff π i ω
  calc
    P {ω | lineageWinnerEvent i ω}
        = P.map (pathMap (permuteLineageCounts π))
            {ω | lineageWinnerEvent i ω} := by rw [hpath]
    _ = P ((pathMap (permuteLineageCounts π)) ⁻¹'
          {ω | lineageWinnerEvent i ω}) := by
        rw [Measure.map_apply
          (measurable_pathMap _ (measurable_permuteLineageCounts π)) hmeas]
    _ = P {ω | lineageWinnerEvent (π i) ω} := by rw [hpre]

lemma measurableSet_consensusReachedEvent_lineage :
    MeasurableSet {ω : Nat → PopState | consensusReachedEvent ω} := by
  have hset :
      {ω : Nat → PopState | consensusReachedEvent ω} =
        ⋃ t : Nat, {ω : Nat → PopState | consensusTime ω = ↑t} := by
    ext ω
    constructor
    · intro hω
      change consensusTime ω < ⊤ at hω
      have hne : consensusTime ω ≠ ⊤ :=
        WithTop.lt_top_iff_ne_top.mp hω
      rcases WithTop.ne_top_iff_exists.mp hne with ⟨t, ht⟩
      exact Set.mem_iUnion.mpr ⟨t, ht.symm⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨t, ht⟩
      change consensusTime ω < ⊤
      rw [ht]
      exact WithTop.coe_lt_top t
  rw [hset]
  exact MeasurableSet.iUnion fun t =>
    measurableSet_consensusTime_eq_coe t

/-- Every nontrivial prefix partition of the initial lineages reaches
consensus almost surely.  This uses only the almost-sure-consensus part of the
Lotka--Volterra analysis, not its majority-probability formula. -/
lemma lineage_prefix_consensus_almost_sure
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    lineagePathMeasure params (a + b)
        {ω | consensusReachedEvent
          (pathMap (lineageAggregate a) ω)} = 1 := by
  let P := lineagePathMeasure params (a + b)
  let f : (Nat → LinState (a + b)) → (Nat → PopState) :=
    pathMap (lineageAggregate a)
  let C : Set (Nat → PopState) := {ω | consensusReachedEvent ω}
  have hf : Measurable f :=
    measurable_pathMap _ (measurable_lineageAggregate a)
  have hC : MeasurableSet C :=
    measurableSet_consensusReachedEvent_lineage
  have hbridge :=
    lineagePathMeasure_map_aggregate
      params hNeutral hEq0 hEq1 a b
  have hpush := congrArg (fun μ : Measure (Nat → PopState) => μ C) hbridge
  rw [Measure.map_apply hf hC] at hpush
  have hGamma0 : 0 < params.gamma0 := by
    rw [hEq0]
    positivity
  have hGamma1 : 0 < params.gamma1 := by
    rw [hEq1, ← hNeutral]
    positivity
  have hAlphaSum : 0 < params.alpha0 + params.alpha1 := by
    rw [← hNeutral]
    linarith
  have hcons :=
    nsd_consensus_almost_sure_general params
      hGamma0 hGamma1 hAlphaSum a b ha hb
      hAlpha hNeutral hEq0 hEq1
  calc
    P {ω | consensusReachedEvent
        (pathMap (lineageAggregate a) ω)}
        = P (f ⁻¹' C) := rfl
    _ = lvPathMeasure .nonSelfDestructive params (a, b) C := hpush
    _ = 1 := hcons

lemma lineage_prefix_no_revival_species0
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b t : Nat) :
    lineagePathMeasure params (a + b)
        {ω |
          (lineageAggregate a (ω t)).1 = 0 ∧
          (lineageAggregate a (ω (t + 1))).1 ≠ 0} = 0 := by
  let P := lineagePathMeasure params (a + b)
  let f : (Nat → LinState (a + b)) → (Nat → PopState) :=
    pathMap (lineageAggregate a)
  let A : Set (Nat → PopState) :=
    {ω | (ω t).1 = 0 ∧ (ω (t + 1)).1 ≠ 0}
  have hf : Measurable f :=
    measurable_pathMap _ (measurable_lineageAggregate a)
  have hA : MeasurableSet A := by
    exact ((measurable_pi_apply t).fst
      (measurableSet_singleton 0)).inter
      ((measurable_pi_apply (t + 1)).fst
        (measurableSet_singleton 0).compl)
  have hbridge :=
    lineagePathMeasure_map_aggregate
      params hNeutral hEq0 hEq1 a b
  have hpush := congrArg (fun μ : Measure (Nat → PopState) => μ A) hbridge
  rw [Measure.map_apply hf hA] at hpush
  calc
    P {ω |
        (lineageAggregate a (ω t)).1 = 0 ∧
        (lineageAggregate a (ω (t + 1))).1 ≠ 0}
        = P (f ⁻¹' A) := rfl
    _ = lvPathMeasure .nonSelfDestructive params (a, b) A := hpush
    _ = 0 := nsd_path_no_revival_species0 params (a, b) t

lemma lineage_prefix_no_revival_species1
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b t : Nat) :
    lineagePathMeasure params (a + b)
        {ω |
          (lineageAggregate a (ω t)).2 = 0 ∧
          (lineageAggregate a (ω (t + 1))).2 ≠ 0} = 0 := by
  let P := lineagePathMeasure params (a + b)
  let f : (Nat → LinState (a + b)) → (Nat → PopState) :=
    pathMap (lineageAggregate a)
  let A : Set (Nat → PopState) :=
    {ω | (ω t).2 = 0 ∧ (ω (t + 1)).2 ≠ 0}
  have hf : Measurable f :=
    measurable_pathMap _ (measurable_lineageAggregate a)
  have hA : MeasurableSet A := by
    exact ((measurable_pi_apply t).snd
      (measurableSet_singleton 0)).inter
      ((measurable_pi_apply (t + 1)).snd
        (measurableSet_singleton 0).compl)
  have hbridge :=
    lineagePathMeasure_map_aggregate
      params hNeutral hEq0 hEq1 a b
  have hpush := congrArg (fun μ : Measure (Nat → PopState) => μ A) hbridge
  rw [Measure.map_apply hf hA] at hpush
  calc
    P {ω |
        (lineageAggregate a (ω t)).2 = 0 ∧
        (lineageAggregate a (ω (t + 1))).2 ≠ 0}
        = P (f ⁻¹' A) := rfl
    _ = lvPathMeasure .nonSelfDestructive params (a, b) A := hpush
    _ = 0 := nsd_path_no_revival_species1 params (a, b) t

lemma lineage_prefix_consensus_almost_sure_fixed
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    {n : Nat} (a : Nat) (ha : 0 < a) (han : a < n) :
    lineagePathMeasure params n
        {ω | consensusReachedEvent
          (pathMap (lineageAggregate a) ω)} = 1 := by
  have hb : 0 < n - a := Nat.sub_pos_of_lt han
  have hsum : a + (n - a) = n := Nat.add_sub_of_le (Nat.le_of_lt han)
  have h :=
    lineage_prefix_consensus_almost_sure
      params hAlpha hNeutral hEq0 hEq1 a (n - a) ha hb
  rw [hsum] at h
  exact h

lemma lineage_prefix_no_revival_species0_fixed
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    {n : Nat} (a : Nat) (han : a ≤ n) (t : Nat) :
    lineagePathMeasure params n
        {ω |
          (lineageAggregate a (ω t)).1 = 0 ∧
          (lineageAggregate a (ω (t + 1))).1 ≠ 0} = 0 := by
  have hsum : a + (n - a) = n := Nat.add_sub_of_le han
  have h :=
    lineage_prefix_no_revival_species0
      params hNeutral hEq0 hEq1 a (n - a) t
  rw [hsum] at h
  exact h

lemma lineage_prefix_no_revival_species1_fixed
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    {n : Nat} (a : Nat) (han : a ≤ n) (t : Nat) :
    lineagePathMeasure params n
        {ω |
          (lineageAggregate a (ω t)).2 = 0 ∧
          (lineageAggregate a (ω (t + 1))).2 ≠ 0} = 0 := by
  have hsum : a + (n - a) = n := Nat.add_sub_of_le han
  have h :=
    lineage_prefix_no_revival_species1
      params hNeutral hEq0 hEq1 a (n - a) t
  rw [hsum] at h
  exact h

private lemma lineage_sum_update_univ
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → Nat) (i : α) (v : Nat) :
    (∑ x, Function.update f i v x) =
      v + ∑ x ∈ (Finset.univ.erase i), f x := by
  simpa only [Finset.sdiff_singleton_eq_erase] using
    Finset.sum_update_of_mem (Finset.mem_univ i) f v

lemma lineageTotal_birth
    {n : Nat} (L : LinState n) (i : Lineage n) :
    lineageTotal (lineageBirth L i) = lineageTotal L + 1 := by
  classical
  unfold lineageTotal lineageBirth
  rw [lineage_sum_update_univ]
  have h :=
    Finset.sum_erase_add (Finset.univ : Finset (Lineage n)) L
      (Finset.mem_univ i)
  omega

lemma lineageTotal_le_death_add_one
    {n : Nat} (L : LinState n) (i : Lineage n) :
    lineageTotal L ≤ lineageTotal (lineageDeath L i) + 1 := by
  classical
  unfold lineageTotal lineageDeath
  rw [lineage_sum_update_univ]
  have h :=
    Finset.sum_erase_add (Finset.univ : Finset (Lineage n)) L
      (Finset.mem_univ i)
  omega

/-- A lineage reaction cannot lower the total population by more than one. -/
lemma lineageKernel_no_large_total_drop
    (params : LVParams) {n : Nat} (L : LinState n) :
    lineageKernel params n L
        {L' | ¬lineageTotal L ≤ lineageTotal L' + 1} = 0 := by
  classical
  have hmeas :
      MeasurableSet {L' : LinState n |
        ¬lineageTotal L ≤ lineageTotal L' + 1} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  simp only [lineageKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  split_ifs with hmass
  · rw [Measure.dirac_apply' _ hmeas]
    simp
  · rw [Measure.smul_apply]
    unfold lineageRawMeasure
    simp only [Measure.add_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
      Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    have hbirth : ∀ i : Lineage n,
        (if ¬lineageTotal L ≤ lineageTotal (lineageBirth L i) + 1
          then 1 else 0 : ENNReal) = 0 := by
      intro i
      rw [lineageTotal_birth]
      split <;> rename_i h
      · omega
      · rfl
    have hdeath : ∀ i : Lineage n,
        (if ¬lineageTotal L ≤ lineageTotal (lineageDeath L i) + 1
          then 1 else 0 : ENNReal) = 0 := by
      intro i
      rw [if_neg]
      exact not_not_intro (lineageTotal_le_death_add_one L i)
    simp_rw [hbirth, hdeath, mul_zero, Finset.sum_const_zero, add_zero]
    simp

private lemma lineagePath_large_total_drop_from_state
    (params : LVParams) {n : Nat} (t : Nat) (L : LinState n) :
    lineagePathMeasure params n
        {ω | ω t = L ∧
          ¬lineageTotal L ≤ lineageTotal (ω (t + 1)) + 1} = 0 := by
  let K := lineageKernel params n
  let g : LinState n → ENNReal := fun X => if X = L then 1 else 0
  let φ : LinState n → ENNReal := fun Y =>
    if ¬lineageTotal L ≤ lineageTotal Y + 1 then 1 else 0
  have hg : Measurable g := measurable_of_countable _
  have hφ : Measurable φ := measurable_of_countable _
  have hmeas :
      MeasurableSet
        {ω : Nat → LinState n | ω t = L ∧
          ¬lineageTotal L ≤ lineageTotal (ω (t + 1)) + 1} := by
    have hfirst : MeasurableSet {X : LinState n | X = L} :=
      measurableSet_singleton L
    have hsecond :
        MeasurableSet {Y : LinState n |
          ¬lineageTotal L ≤ lineageTotal Y + 1} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    exact (hfirst.preimage (measurable_pi_apply t)).inter
      (hsecond.preimage (measurable_pi_apply (t + 1)))
  unfold lineagePathMeasure
  have hconv :
      homogeneousPathMeasure (Measure.dirac (initialLineages n)) K
          {ω | ω t = L ∧
            ¬lineageTotal L ≤ lineageTotal (ω (t + 1)) + 1} =
        ∫⁻ ω, g (ω t) * φ (ω (t + 1))
          ∂homogeneousPathMeasure (Measure.dirac (initialLineages n)) K := by
    rw [← lintegral_indicator_one hmeas]
    congr 1
    ext ω
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp_all
  rw [hconv,
    homogeneousPathMeasure_joint_lintegral K (initialLineages n)
      t g φ hg hφ]
  have hinner : ∀ X,
      ∫⁻ Y, φ Y ∂K X =
        K X {Y | ¬lineageTotal L ≤ lineageTotal Y + 1} := by
    intro X
    have hφind :
        φ = Set.indicator
          {Y : LinState n | ¬lineageTotal L ≤ lineageTotal Y + 1} 1 := by
      ext Y
      simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [hφind]
    exact lintegral_indicator_one
      (DiscreteMeasurableSpace.forall_measurableSet _)
  simp_rw [hinner]
  have hzero : ∀ X,
      g X * K X {Y | ¬lineageTotal L ≤ lineageTotal Y + 1} = 0 := by
    intro X
    by_cases hXL : X = L
    · subst X
      simp only [g, if_pos, one_mul]
      exact lineageKernel_no_large_total_drop params L
    · simp [g, hXL]
  simp_rw [hzero]
  exact lintegral_zero

lemma lineagePath_no_large_total_drop
    (params : LVParams) {n : Nat} (t : Nat) :
    lineagePathMeasure params n
        {ω | ¬lineageTotal (ω t) ≤
          lineageTotal (ω (t + 1)) + 1} = 0 := by
  have hset :
      {ω : Nat → LinState n |
          ¬lineageTotal (ω t) ≤ lineageTotal (ω (t + 1)) + 1} =
        ⋃ L : LinState n,
          {ω | ω t = L ∧
            ¬lineageTotal L ≤ lineageTotal (ω (t + 1)) + 1} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨ω t, rfl, h⟩
    · rintro ⟨L, hL, h⟩
      simpa [hL] using h
  rw [hset]
  exact measure_iUnion_null fun L =>
    lineagePath_large_total_drop_from_state params t L

lemma lineageAggregate_fst_pos_of_lt
    {n a : Nat} {L : LinState n} (i : Lineage n)
    (hi : (i : Nat) < a) (hLi : 0 < L i) :
    0 < (lineageAggregate a L).1 := by
  classical
  unfold lineageAggregate
  simp only
  have hle :
      L i ≤ ∑ j : Lineage n, if (j : Nat) < a then L j else 0 := by
    calc
      L i = (if (i : Nat) < a then L i else 0) := by simp [hi]
      _ ≤ ∑ j : Lineage n, if (j : Nat) < a then L j else 0 := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Lineage n)))
          (f := fun j : Lineage n =>
            if (j : Nat) < a then L j else 0)
          (fun j _ => Nat.zero_le
            (if (j : Nat) < a then L j else 0))
          (Finset.mem_univ i)
  omega

lemma lineageAggregate_snd_pos_of_ge
    {n a : Nat} {L : LinState n} (i : Lineage n)
    (hi : a ≤ (i : Nat)) (hLi : 0 < L i) :
    0 < (lineageAggregate a L).2 := by
  classical
  unfold lineageAggregate
  simp only
  have hle :
      L i ≤ ∑ j : Lineage n, if a ≤ (j : Nat) then L j else 0 := by
    calc
      L i = (if a ≤ (i : Nat) then L i else 0) := by simp [hi]
      _ ≤ ∑ j : Lineage n, if a ≤ (j : Nat) then L j else 0 := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (Lineage n)))
          (f := fun j : Lineage n =>
            if a ≤ (j : Nat) then L j else 0)
          (fun j _ => Nat.zero_le
            (if a ≤ (j : Nat) then L j else 0))
          (Finset.mem_univ i)
  omega

lemma lineageTotal_initialLineages (n : Nat) :
    lineageTotal (initialLineages n) = n := by
  simp [lineageTotal, initialLineages]

lemma exists_winnerEvent_iff_exists_sole
    {n : Nat} (ω : Nat → LinState n) :
    (∃ i, lineageWinnerEvent i ω) ↔
      ∃ t i, soleLineage i (ω t) := by
  classical
  constructor
  · rintro ⟨i, t, hit, _⟩
    exact ⟨t, i, hit⟩
  · rintro hsole
    let t := Nat.find hsole
    obtain ⟨i, hi⟩ := Nat.find_spec hsole
    refine ⟨i, t, hi, ?_⟩
    intro u hu j hj
    exact Nat.find_min hsole hu ⟨j, hj⟩

lemma exists_positive_lineage_of_total_pos
    {n : Nat} {L : LinState n} (hL : 0 < lineageTotal L) :
    ∃ i, 0 < L i := by
  classical
  by_contra h
  have hnpos : ∀ i, ¬0 < L i := by
    intro i hi
    exact h ⟨i, hi⟩
  have hz : ∀ i, L i = 0 :=
    fun i => Nat.eq_zero_of_not_pos (hnpos i)
  simp [lineageTotal, hz] at hL

lemma exists_soleLineage_of_total_eq_one
    {n : Nat} {L : LinState n} (hL : lineageTotal L = 1) :
    ∃ i, soleLineage i L := by
  classical
  have hpos : 0 < lineageTotal L := by omega
  obtain ⟨i, hi⟩ := exists_positive_lineage_of_total_pos hpos
  refine ⟨i, hi, ?_⟩
  intro j hji
  have hsum :=
    Finset.sum_erase_add (Finset.univ : Finset (Lineage n)) L
      (Finset.mem_univ i)
  have hjmem : j ∈ (Finset.univ : Finset (Lineage n)).erase i := by
    simp [hji]
  have hjle :
      L j ≤ ∑ x ∈ (Finset.univ : Finset (Lineage n)).erase i, L x :=
    Finset.single_le_sum
      (fun x _ => Nat.zero_le (L x)) hjmem
  unfold lineageTotal at hL
  omega

lemma soleLineage_of_pairwise_unique
    {n : Nat} {L : LinState n} (i : Lineage n)
    (hi : 0 < L i)
    (hunique : ∀ j, 0 < L j → i = j) :
    soleLineage i L := by
  refine ⟨hi, ?_⟩
  intro j hji
  by_contra hj0
  have hjpos : 0 < L j := Nat.pos_of_ne_zero hj0
  exact hji (hunique j hjpos).symm

/-- If every nontrivial prefix partition reaches consensus, extinct prefix
groups never revive, and no step removes more than one individual, then some
initial lineage eventually becomes the sole living lineage. -/
lemma exists_winnerEvent_of_good_path
    {n : Nat} (hn : 0 < n) (ω : Nat → LinState n)
    (hinit : ω 0 = initialLineages n)
    (hcons : ∀ a, 0 < a → a < n →
      consensusReachedEvent
        (pathMap (lineageAggregate a) ω))
    (hnr0 : ∀ a, a < n → ∀ t,
      (lineageAggregate a (ω t)).1 = 0 →
        (lineageAggregate a (ω (t + 1))).1 = 0)
    (hnr1 : ∀ a, a < n → ∀ t,
      (lineageAggregate a (ω t)).2 = 0 →
        (lineageAggregate a (ω (t + 1))).2 = 0)
    (hstep : ∀ t,
      lineageTotal (ω t) ≤ lineageTotal (ω (t + 1)) + 1) :
    ∃ i, lineageWinnerEvent i ω := by
  classical
  have hexReach : ∀ a, 0 < a → a < n →
      ∃ t, reachedConsensus (lineageAggregate a (ω t)) := by
    intro a ha han
    have hc := hcons a ha han
    change consensusTime (pathMap (lineageAggregate a) ω) < ⊤ at hc
    have hne :
        consensusTime (pathMap (lineageAggregate a) ω) ≠ ⊤ :=
      WithTop.lt_top_iff_ne_top.mp hc
    rcases WithTop.ne_top_iff_exists.mp hne with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    exact reachedConsensus_at_consensusTime'
      (pathMap (lineageAggregate a) ω) t ht.symm
  let τ : Nat → Nat := fun a =>
    if h : 0 < a ∧ a < n then Classical.choose (hexReach a h.1 h.2) else 0
  have hτReach : ∀ a, 0 < a → a < n →
      reachedConsensus (lineageAggregate a (ω (τ a))) := by
    intro a ha han
    dsimp [τ]
    rw [dif_pos ⟨ha, han⟩]
    exact Classical.choose_spec (hexReach a ha han)
  let T := ∑ a ∈ Finset.range n, τ a
  have hτle : ∀ a, a < n → τ a ≤ T := by
    intro a han
    dsimp [T]
    exact Finset.single_le_sum
      (fun k _ => Nat.zero_le (τ k))
      (Finset.mem_range.mpr han)
  have hforward0 : ∀ a, a < n → ∀ t u, t ≤ u →
      (lineageAggregate a (ω t)).1 = 0 →
        (lineageAggregate a (ω u)).1 = 0 := by
    intro a han t u htu hz
    induction u, htu using Nat.le_induction with
    | base => exact hz
    | succ u _ ih => exact hnr0 a han u ih
  have hforward1 : ∀ a, a < n → ∀ t u, t ≤ u →
      (lineageAggregate a (ω t)).2 = 0 →
        (lineageAggregate a (ω u)).2 = 0 := by
    intro a han t u htu hz
    induction u, htu using Nat.le_induction with
    | base => exact hz
    | succ u _ ih => exact hnr1 a han u ih
  have hprefixT : ∀ a, 0 < a → a < n →
      reachedConsensus (lineageAggregate a (ω T)) := by
    intro a ha han
    have hreach := hτReach a ha han
    rcases hreach with hzero | hzero
    · exact Or.inl (hforward0 a han (τ a) T (hτle a han) hzero)
    · exact Or.inr (hforward1 a han (τ a) T (hτle a han) hzero)
  have hordered : ∀ i j : Lineage n,
      (i : Nat) < (j : Nat) →
      ¬(0 < ω T i ∧ 0 < ω T j) := by
    intro i j hij ⟨hi, hj⟩
    let a := (i : Nat) + 1
    have ha : 0 < a := by simp [a]
    have han : a < n := by
      have hjn := j.isLt
      dsimp [a]
      omega
    have hreach := hprefixT a ha han
    have hleft : 0 < (lineageAggregate a (ω T)).1 :=
      lineageAggregate_fst_pos_of_lt i (by simp [a]) hi
    have hright : 0 < (lineageAggregate a (ω T)).2 :=
      lineageAggregate_snd_pos_of_ge j (by dsimp [a]; omega) hj
    rcases hreach with hzero | hzero
    · omega
    · omega
  have hpair : ∀ i j : Lineage n,
      0 < ω T i → 0 < ω T j → i = j := by
    intro i j hi hj
    by_contra hij
    have hval : (i : Nat) ≠ (j : Nat) := by
      intro h
      exact hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · exact hordered i j hlt ⟨hi, hj⟩
    · exact hordered j i hgt ⟨hj, hi⟩
  have hsole : ∃ t i, soleLineage i (ω t) := by
    by_cases hTpos : 0 < lineageTotal (ω T)
    · obtain ⟨i, hi⟩ := exists_positive_lineage_of_total_pos hTpos
      exact ⟨T, i,
        soleLineage_of_pairwise_unique i hi (fun j hj => hpair i j hi hj)⟩
    · have hTzero : lineageTotal (ω T) = 0 :=
        Nat.eq_zero_of_not_pos hTpos
      have hexZero : ∃ t, lineageTotal (ω t) = 0 := ⟨T, hTzero⟩
      let z := Nat.find hexZero
      have hzZero : lineageTotal (ω z) = 0 := Nat.find_spec hexZero
      have hzeroTotal : lineageTotal (ω 0) = n := by
        rw [hinit]
        exact lineageTotal_initialLineages n
      have hzPos : 0 < z := by
        by_contra hz
        have : z = 0 := Nat.eq_zero_of_not_pos hz
        rw [this, hzeroTotal] at hzZero
        omega
      let u := z - 1
      have huLt : u < z := by dsimp [u]; omega
      have huNeZero : lineageTotal (ω u) ≠ 0 :=
        Nat.find_min hexZero huLt
      have hsucc : u + 1 = z := by dsimp [u]; omega
      have hdrop := hstep u
      rw [hsucc, hzZero] at hdrop
      have huOne : lineageTotal (ω u) = 1 := by omega
      obtain ⟨i, hi⟩ := exists_soleLineage_of_total_eq_one huOne
      exact ⟨u, i, hi⟩
  exact (exists_winnerEvent_iff_exists_sole ω).2 hsole

lemma lineagePath_initial_ne_null
    (params : LVParams) (n : Nat) :
    lineagePathMeasure params n
        {ω | ω 0 ≠ initialLineages n} = 0 := by
  unfold lineagePathMeasure
  rw [show
      ({ω : Nat → LinState n | ω 0 ≠ initialLineages n} :
        Set (Nat → LinState n)) =
        (fun ω : Nat → LinState n => ω 0) ⁻¹'
          ({initialLineages n} : Set (LinState n))ᶜ by
      ext ω
      simp]
  rw [← Measure.map_apply (measurable_pi_apply 0)
    (measurableSet_singleton (initialLineages n)).compl,
    homogeneousPathMeasure_dirac_marginal]
  simp [kernelIter_zero, Kernel.id_apply]

lemma lineage_prefix_no_consensus_null
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    {n : Nat} (a : Nat) (ha : 0 < a) (han : a < n) :
    lineagePathMeasure params n
        {ω | ¬consensusReachedEvent
          (pathMap (lineageAggregate a) ω)} = 0 := by
  let P := lineagePathMeasure params n
  let E : Set (Nat → LinState n) :=
    {ω | consensusReachedEvent (pathMap (lineageAggregate a) ω)}
  have hE : MeasurableSet E := by
    exact measurableSet_consensusReachedEvent_lineage.preimage
      (measurable_pathMap _ (measurable_lineageAggregate a))
  have hprob :=
    lineage_prefix_consensus_almost_sure_fixed
      params hAlpha hNeutral hEq0 hEq1 a ha han
  change P E = 1 at hprob
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lineagePathMeasure, homogeneousPathMeasure]
    infer_instance
  have hcomp :
      {ω : Nat → LinState n |
          ¬consensusReachedEvent (pathMap (lineageAggregate a) ω)} =
        Eᶜ := by
    ext ω
    simp [E]
  rw [hcomp, measure_compl hE (measure_ne_top P E), hprob]
  rw [measure_univ, tsub_self]

/-- With neutral non-self-destructive competition and positive competition
rate, one initial lineage almost surely becomes the sole living lineage. -/
theorem lineage_winner_exists_almost_sure
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (n : Nat) (hn : 0 < n) :
    lineagePathMeasure params n
        (⋃ i : Lineage n, {ω | lineageWinnerEvent i ω}) = 1 := by
  let P := lineagePathMeasure params n
  let W : Set (Nat → LinState n) :=
    ⋃ i : Lineage n, {ω | lineageWinnerEvent i ω}
  let Binit : Set (Nat → LinState n) :=
    {ω | ω 0 ≠ initialLineages n}
  let Bcons : Nat → Set (Nat → LinState n) := fun a =>
    if h : 0 < a ∧ a < n then
      {ω | ¬consensusReachedEvent
        (pathMap (lineageAggregate a) ω)}
    else ∅
  let Brevive0 : Nat → Nat → Set (Nat → LinState n) := fun a t =>
    if h : a < n then
      {ω |
        (lineageAggregate a (ω t)).1 = 0 ∧
        (lineageAggregate a (ω (t + 1))).1 ≠ 0}
    else ∅
  let Brevive1 : Nat → Nat → Set (Nat → LinState n) := fun a t =>
    if h : a < n then
      {ω |
        (lineageAggregate a (ω t)).2 = 0 ∧
        (lineageAggregate a (ω (t + 1))).2 ≠ 0}
    else ∅
  let Bstep : Nat → Set (Nat → LinState n) := fun t =>
    {ω | ¬lineageTotal (ω t) ≤ lineageTotal (ω (t + 1)) + 1}
  let NullCover : Set (Nat → LinState n) :=
    Binit ∪
      (⋃ a, Bcons a) ∪
      (⋃ a, ⋃ t, Brevive0 a t ∪ Brevive1 a t) ∪
      ⋃ t, Bstep t
  let Bad : Set (Nat → LinState n) :=
    {ω |
      ω 0 ≠ initialLineages n ∨
      (∃ a, 0 < a ∧ a < n ∧
        ¬consensusReachedEvent
          (pathMap (lineageAggregate a) ω)) ∨
      (∃ a t, a < n ∧
        (((lineageAggregate a (ω t)).1 = 0 ∧
            (lineageAggregate a (ω (t + 1))).1 ≠ 0) ∨
          ((lineageAggregate a (ω t)).2 = 0 ∧
            (lineageAggregate a (ω (t + 1))).2 ≠ 0))) ∨
      ∃ t, ¬lineageTotal (ω t) ≤ lineageTotal (ω (t + 1)) + 1}
  have hBinit : P Binit = 0 := by
    exact lineagePath_initial_ne_null params n
  have hBcons : ∀ a, P (Bcons a) = 0 := by
    intro a
    dsimp [Bcons]
    split_ifs with h
    · exact lineage_prefix_no_consensus_null
        params hAlpha hNeutral hEq0 hEq1 a h.1 h.2
    · simp
  have hBrevive0 : ∀ a t, P (Brevive0 a t) = 0 := by
    intro a t
    dsimp [Brevive0]
    split_ifs with h
    · exact lineage_prefix_no_revival_species0_fixed
        params hNeutral hEq0 hEq1 a (Nat.le_of_lt h) t
    · simp
  have hBrevive1 : ∀ a t, P (Brevive1 a t) = 0 := by
    intro a t
    dsimp [Brevive1]
    split_ifs with h
    · exact lineage_prefix_no_revival_species1_fixed
        params hNeutral hEq0 hEq1 a (Nat.le_of_lt h) t
    · simp
  have hBstep : ∀ t, P (Bstep t) = 0 := by
    intro t
    exact lineagePath_no_large_total_drop params t
  have hNullCover : P NullCover = 0 := by
    dsimp [NullCover]
    exact measure_union_null
      (measure_union_null
        (measure_union_null hBinit (measure_iUnion_null hBcons))
        (measure_iUnion_null fun a =>
          measure_iUnion_null fun t =>
            measure_union_null
              (hBrevive0 a t) (hBrevive1 a t)))
      (measure_iUnion_null hBstep)
  have hBadSub : Bad ⊆ NullCover := by
    intro ω hω
    rcases hω with hinit | hcons | hrevive | hstep
    · exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_left _ hinit))
    · rcases hcons with ⟨a, ha, han, hfail⟩
      exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_union_right _
          (Set.mem_iUnion.mpr ⟨a, by
            dsimp [Bcons]
            rw [if_pos ⟨ha, han⟩]
            exact hfail⟩)))
    · rcases hrevive with ⟨a, t, han, hzero | hzero⟩
      · exact Set.mem_union_left _ (Set.mem_union_right _
          (Set.mem_iUnion.mpr ⟨a,
            Set.mem_iUnion.mpr ⟨t, Or.inl (by
              dsimp [Brevive0]
              rw [if_pos han]
              exact hzero)⟩⟩))
      · exact Set.mem_union_left _ (Set.mem_union_right _
          (Set.mem_iUnion.mpr ⟨a,
            Set.mem_iUnion.mpr ⟨t, Or.inr (by
              dsimp [Brevive1]
              rw [if_pos han]
              exact hzero)⟩⟩))
    · rcases hstep with ⟨t, ht⟩
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨t, ht⟩)
  have hBad : P Bad = 0 :=
    measure_mono_null hBadSub hNullCover
  have hcover : Set.univ ⊆ W ∪ Bad := by
    intro ω _
    by_cases hωBad : ω ∈ Bad
    · exact Or.inr hωBad
    · apply Or.inl
      have hinit : ω 0 = initialLineages n := by
        by_contra h
        exact hωBad (Or.inl h)
      have hcons : ∀ a, 0 < a → a < n →
          consensusReachedEvent
            (pathMap (lineageAggregate a) ω) := by
        intro a ha han
        by_contra h
        exact hωBad (Or.inr (Or.inl ⟨a, ha, han, h⟩))
      have hnr0 : ∀ a, a < n → ∀ t,
          (lineageAggregate a (ω t)).1 = 0 →
            (lineageAggregate a (ω (t + 1))).1 = 0 := by
        intro a han t hz
        by_contra hnext
        exact hωBad (Or.inr (Or.inr (Or.inl
          ⟨a, t, han, Or.inl ⟨hz, hnext⟩⟩)))
      have hnr1 : ∀ a, a < n → ∀ t,
          (lineageAggregate a (ω t)).2 = 0 →
            (lineageAggregate a (ω (t + 1))).2 = 0 := by
        intro a han t hz
        by_contra hnext
        exact hωBad (Or.inr (Or.inr (Or.inl
          ⟨a, t, han, Or.inr ⟨hz, hnext⟩⟩)))
      have hstep : ∀ t,
          lineageTotal (ω t) ≤ lineageTotal (ω (t + 1)) + 1 := by
        intro t
        by_contra h
        exact hωBad (Or.inr (Or.inr (Or.inr ⟨t, h⟩)))
      obtain ⟨i, hi⟩ :=
        exists_winnerEvent_of_good_path hn ω
          hinit hcons hnr0 hnr1 hstep
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lineagePathMeasure, homogeneousPathMeasure]
    infer_instance
  change P W = 1
  apply le_antisymm prob_le_one
  calc
    1 = P Set.univ := measure_univ.symm
    _ ≤ P (W ∪ Bad) := measure_mono hcover
    _ ≤ P W + P Bad := measure_union_le _ _
    _ = P W := by rw [hBad, add_zero]

/-- The first lineage to become the sole living initial lineage is uniformly
distributed over the initial lineage labels. -/
theorem lineage_winner_uniform
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (n : Nat) (hn : 0 < n) (i : Lineage n) :
    lineagePathMeasure params n
        {ω | lineageWinnerEvent i ω} = (n : ENNReal)⁻¹ := by
  let P := lineagePathMeasure params n
  let E : Lineage n → Set (Nat → LinState n) :=
    fun j => {ω | lineageWinnerEvent j ω}
  have hdisj : Pairwise (fun j k => Disjoint (E j) (E k)) := by
    intro j k hjk
    exact lineageWinnerEvent_disjoint hjk
  have hmeas : ∀ j, MeasurableSet (E j) :=
    fun j => measurableSet_lineageWinnerEvent j
  have hUnion :
      P (⋃ j, E j) = 1 := by
    exact lineage_winner_exists_almost_sure
      params hAlpha hNeutral hEq0 hEq1 n hn
  have hsum : (∑ j : Lineage n, P (E j)) = 1 := by
    have hm := measure_iUnion hdisj hmeas (μ := P)
    rw [tsum_fintype] at hm
    exact hm.symm.trans hUnion
  have heq : ∀ j : Lineage n, P (E j) = P (E i) := by
    intro j
    have h :=
      lineageWinnerEvent_measure_invariant
        params (Equiv.swap j i) j
    simpa [P, E] using h
  have hmul : (n : ENNReal) * P (E i) = 1 := by
    calc
      (n : ENNReal) * P (E i)
          = ∑ j : Lineage n, P (E i) := by simp
      _ = ∑ j : Lineage n, P (E j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (heq j).symm
      _ = 1 := hsum
  have hn0 : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hnTop : (n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  change P (E i) = (n : ENNReal)⁻¹
  calc
    P (E i) = 1 * P (E i) := by simp
    _ = ((n : ENNReal)⁻¹ * (n : ENNReal)) * P (E i) := by
      rw [ENNReal.inv_mul_cancel hn0 hnTop]
    _ = (n : ENNReal)⁻¹ * ((n : ENNReal) * P (E i)) := by
      rw [mul_assoc]
    _ = (n : ENNReal)⁻¹ := by rw [hmul, mul_one]

theorem lineage_winner_finset_probability
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (n : Nat) (hn : 0 < n) (A : Finset (Lineage n)) :
    lineagePathMeasure params n
        (⋃ i ∈ A, {ω | lineageWinnerEvent i ω}) =
      (A.card : ENNReal) * (n : ENNReal)⁻¹ := by
  let P := lineagePathMeasure params n
  let E : Lineage n → Set (Nat → LinState n) :=
    fun i => {ω | lineageWinnerEvent i ω}
  calc
    P (⋃ i ∈ A, E i)
        = ∑ i ∈ A, P (E i) := by
          exact measure_biUnion_finset
            (fun i _ j _ hij => lineageWinnerEvent_disjoint hij)
            (fun i _ => measurableSet_lineageWinnerEvent i)
    _ = ∑ _i ∈ A, (n : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      exact lineage_winner_uniform
        params hAlpha hNeutral hEq0 hEq1 n hn i
    _ = (A.card : ENNReal) * (n : ENNReal)⁻¹ := by simp

lemma card_lineages_before (a b : Nat) :
    ((Finset.univ : Finset (Lineage (a + b))).filter
      (fun i : Lineage (a + b) => (i : Nat) < a)).card = a := by
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_add_right a b)

lemma card_lineages_from (a b : Nat) :
    ((Finset.univ : Finset (Lineage (a + b))).filter
      (fun i : Lineage (a + b) => a ≤ (i : Nat))).card = b := by
  have hsum :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Lineage (a + b))))
      (p := fun i : Lineage (a + b) => (i : Nat) < a)
  rw [card_lineages_before a b] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have heq :
      ((Finset.univ : Finset (Lineage (a + b))).filter
        (fun i : Lineage (a + b) => ¬(i : Nat) < a)).card =
      ((Finset.univ : Finset (Lineage (a + b))).filter
        (fun i : Lineage (a + b) => a ≤ (i : Nat))).card := by
    congr 1
    ext i
    simp
  rw [heq] at hsum
  omega

def lineageMajorityWinnerEvent
    (a b : Nat) (ω : Nat → LinState (a + b)) : Prop :=
  ∃ i, lineageWinnerEvent i ω ∧
    ((species0Majority (a, b) ∧ (i : Nat) < a) ∨
      (¬species0Majority (a, b) ∧ a ≤ (i : Nat)))

theorem lineage_majority_winner_probability
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    lineagePathMeasure params (a + b)
        {ω | lineageMajorityWinnerEvent a b ω} =
      (a : ENNReal) * (a + b : ENNReal)⁻¹ := by
  classical
  have hn : 0 < a + b := by omega
  by_cases hstrict : b < a
  · let A : Finset (Lineage (a + b)) :=
      Finset.univ.filter (fun i => (i : Nat) < a)
    have hset :
        {ω : Nat → LinState (a + b) |
            lineageMajorityWinnerEvent a b ω} =
          ⋃ i ∈ A, {ω | lineageWinnerEvent i ω} := by
      ext ω
      constructor
      · rintro ⟨i, hi, hgroup⟩
        have hmaj : species0Majority (a, b) := by
          simp [species0Majority]
          omega
        rcases hgroup with hgroup0 | hgroup1
        · exact Set.mem_iUnion.mpr ⟨i,
            Set.mem_iUnion.mpr ⟨by simpa [A] using hgroup0.2, hi⟩⟩
        · exact False.elim (hgroup1.1 hmaj)
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hi with ⟨hiA, hiwin⟩
        have hia : (i : Nat) < a := by simpa [A] using hiA
        exact ⟨i, hiwin, Or.inl ⟨by
          simp [species0Majority]
          omega, hia⟩⟩
    rw [hset,
      lineage_winner_finset_probability
        params hAlpha hNeutral hEq0 hEq1 (a + b) hn A]
    rw [show A.card = a by
      exact card_lineages_before a b]
    simp only [Nat.cast_add]
  · have hab : a = b := by omega
    let A : Finset (Lineage (a + b)) :=
      Finset.univ.filter (fun i => (i : Nat) < a)
    have hset :
        {ω : Nat → LinState (a + b) |
            lineageMajorityWinnerEvent a b ω} =
          ⋃ i ∈ A, {ω | lineageWinnerEvent i ω} := by
      ext ω
      constructor
      · rintro ⟨i, hi, hgroup⟩
        have hmaj : species0Majority (a, b) := by
          simp [species0Majority, hab]
        rcases hgroup with hgroup0 | hgroup1
        · exact Set.mem_iUnion.mpr ⟨i,
            Set.mem_iUnion.mpr ⟨by simpa [A] using hgroup0.2, hi⟩⟩
        · exact False.elim (hgroup1.1 hmaj)
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hi with ⟨hiA, hiwin⟩
        have hia : (i : Nat) < a := by simpa [A] using hiA
        exact ⟨i, hiwin, Or.inl ⟨by
          simp [species0Majority, hab], hia⟩⟩
    rw [hset,
      lineage_winner_finset_probability
        params hAlpha hNeutral hEq0 hEq1 (a + b) hn A]
    rw [show A.card = a by
      exact card_lineages_before a b]
    simp only [Nat.cast_add]

lemma zero_forward_of_no_revival
    (x : Nat → Nat)
    (hnr : ∀ t, x t = 0 → x (t + 1) = 0)
    {t u : Nat} (htu : t ≤ u) (hz : x t = 0) :
    x u = 0 := by
  induction u, htu using Nat.le_induction with
  | base => exact hz
  | succ u _ ih => exact hnr u ih

/-- On a path on which a winner lineage exists and extinct aggregate species
do not revive, the Lotka--Volterra majority winner is exactly determined by
the initial species of that lineage. -/
lemma majorityConsensusEvent_iff_lineageWinner
    (a b : Nat) (ω : Nat → LinState (a + b))
    (hwinner : ∃ i, lineageWinnerEvent i ω)
    (hnr0 : ∀ t,
      (lineageAggregate a (ω t)).1 = 0 →
        (lineageAggregate a (ω (t + 1))).1 = 0)
    (hnr1 : ∀ t,
      (lineageAggregate a (ω t)).2 = 0 →
        (lineageAggregate a (ω (t + 1))).2 = 0) :
    majorityConsensusEvent (a, b)
        (pathMap (lineageAggregate a) ω) ↔
      ∃ i, lineageWinnerEvent i ω ∧
        ((species0Majority (a, b) ∧ (i : Nat) < a) ∨
          (¬species0Majority (a, b) ∧ a ≤ (i : Nat))) := by
  let η := pathMap (lineageAggregate a) ω
  have hforward0 : ∀ {t u}, t ≤ u →
      (lineageAggregate a (ω t)).1 = 0 →
        (lineageAggregate a (ω u)).1 = 0 :=
    fun {_ _} htu hz =>
      zero_forward_of_no_revival
        (fun r => (lineageAggregate a (ω r)).1) hnr0 htu hz
  have hforward1 : ∀ {t u}, t ≤ u →
      (lineageAggregate a (ω t)).2 = 0 →
        (lineageAggregate a (ω u)).2 = 0 :=
    fun {_ _} htu hz =>
      zero_forward_of_no_revival
        (fun r => (lineageAggregate a (ω r)).2) hnr1 htu hz
  constructor
  · intro hmajority
    obtain ⟨i, hiwin⟩ := hwinner
    rcases hiwin with ⟨tw, hisole, hfirst⟩
    refine ⟨i, ⟨tw, hisole, hfirst⟩, ?_⟩
    unfold majorityConsensusEvent at hmajority
    cases hct : consensusTime η with
    | top => simp [η, hct] at hmajority
    | coe tc =>
        simp only [η, hct] at hmajority
        have hreachTw : reachedConsensus (η tw) := by
          rcases lt_or_ge (i : Nat) a with hia | hia
          · exact Or.inr (by
              unfold η pathMap
              unfold lineageAggregate
              simp only
              apply Finset.sum_eq_zero
              intro j _
              split_ifs with hj
              · exact hisole.2 j (by
                  intro hji
                  subst j
                  omega)
              · rfl)
          · exact Or.inl (by
              unfold η pathMap
              unfold lineageAggregate
              simp only
              apply Finset.sum_eq_zero
              intro j _
              split_ifs with hj
              · exact hisole.2 j (by
                  intro hji
                  subst j
                  omega)
              · rfl)
        have htcTw : tc ≤ tw := by
          have hle := consensusTime_le_of_reached' η tw hreachTw
          rw [hct] at hle
          exact WithTop.coe_le_coe.mp hle
        rcases hmajority with hspecies0 | hspecies1
        · left
          refine ⟨hspecies0.1, ?_⟩
          by_contra hnot
          have hia : a ≤ (i : Nat) := Nat.le_of_not_gt hnot
          have hposTw :
              0 < (lineageAggregate a (ω tw)).2 :=
            lineageAggregate_snd_pos_of_ge i hia hisole.1
          have hzTw := hforward1 htcTw hspecies0.2.2
          omega
        · right
          refine ⟨hspecies1.1, ?_⟩
          by_contra hnot
          have hia : (i : Nat) < a := Nat.lt_of_not_ge hnot
          have hposTw :
              0 < (lineageAggregate a (ω tw)).1 :=
            lineageAggregate_fst_pos_of_lt i hia hisole.1
          have hzTw := hforward0 htcTw hspecies1.2.2
          omega
  · rintro ⟨i, hiwin, hgroup⟩
    rcases hiwin with ⟨tw, hisole, hfirst⟩
    have hreachTw : reachedConsensus (η tw) := by
      rcases hgroup with hgroup0 | hgroup1
      · exact Or.inr (by
          unfold η pathMap
          unfold lineageAggregate
          simp only
          apply Finset.sum_eq_zero
          intro j _
          split_ifs with hj
          · exact hisole.2 j (by
              intro hji
              subst j
              omega)
          · rfl)
      · exact Or.inl (by
          unfold η pathMap
          unfold lineageAggregate
          simp only
          apply Finset.sum_eq_zero
          intro j _
          split_ifs with hj
          · exact hisole.2 j (by
              intro hji
              subst j
              omega)
          · rfl)
    have hfinite : consensusTime η < ⊤ :=
      lt_of_le_of_lt
        (consensusTime_le_of_reached' η tw hreachTw)
        (WithTop.coe_lt_top tw)
    cases hct : consensusTime η with
    | top => simp [hct] at hfinite
    | coe tc =>
        have htcTw : tc ≤ tw := by
          have hle := consensusTime_le_of_reached' η tw hreachTw
          rw [hct] at hle
          exact WithTop.coe_le_coe.mp hle
        have hreachTc :=
          reachedConsensus_at_consensusTime' η tc hct
        change majorityConsensusEvent (a, b) η
        unfold majorityConsensusEvent
        rw [hct]
        rcases hgroup with hgroup0 | hgroup1
        · apply Or.inl
          refine ⟨hgroup0.1, ?_, ?_⟩
          · have hposTw :
                0 < (lineageAggregate a (ω tw)).1 :=
              lineageAggregate_fst_pos_of_lt i hgroup0.2 hisole.1
            by_contra hz
            have hzTw := hforward0 htcTw (Nat.eq_zero_of_not_pos hz)
            omega
          · rcases hreachTc with hzero | hzero
            · have hposTw :
                  0 < (lineageAggregate a (ω tw)).1 :=
                lineageAggregate_fst_pos_of_lt i hgroup0.2 hisole.1
              have hzTw := hforward0 htcTw hzero
              omega
            · exact hzero
        · apply Or.inr
          refine ⟨hgroup1.1, ?_, ?_⟩
          · have hposTw :
                0 < (lineageAggregate a (ω tw)).2 :=
              lineageAggregate_snd_pos_of_ge i hgroup1.2 hisole.1
            by_contra hz
            have hzTw := hforward1 htcTw (Nat.eq_zero_of_not_pos hz)
            omega
          · rcases hreachTc with hzero | hzero
            · exact hzero
            · have hposTw :
                  0 < (lineageAggregate a (ω tw)).2 :=
                lineageAggregate_snd_pos_of_ge i hgroup1.2 hisole.1
              have hzTw := hforward1 htcTw hzero
              omega

/-- End-to-end lineage proof of the majority probability, stated on the
lineage path space before applying the aggregation bridge. -/
theorem lineage_majority_event_probability
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    lineagePathMeasure params (a + b)
        {ω | majorityConsensusEvent (a, b)
          (pathMap (lineageAggregate a) ω)} =
      (a : ENNReal) * (a + b : ENNReal)⁻¹ := by
  let P := lineagePathMeasure params (a + b)
  let M : Set (Nat → LinState (a + b)) :=
    {ω | majorityConsensusEvent (a, b)
      (pathMap (lineageAggregate a) ω)}
  let G : Set (Nat → LinState (a + b)) :=
    {ω | lineageMajorityWinnerEvent a b ω}
  let W : Set (Nat → LinState (a + b)) :=
    ⋃ i : Lineage (a + b), {ω | lineageWinnerEvent i ω}
  let Bwinner : Set (Nat → LinState (a + b)) := Wᶜ
  let Brevive : Set (Nat → LinState (a + b)) :=
    ⋃ t,
      {ω |
        (lineageAggregate a (ω t)).1 = 0 ∧
        (lineageAggregate a (ω (t + 1))).1 ≠ 0} ∪
      {ω |
        (lineageAggregate a (ω t)).2 = 0 ∧
        (lineageAggregate a (ω (t + 1))).2 ≠ 0}
  let Bad := Bwinner ∪ Brevive
  have hWmeas : MeasurableSet W := by
    exact MeasurableSet.iUnion fun i =>
      measurableSet_lineageWinnerEvent i
  have hW : P W = 1 := by
    exact lineage_winner_exists_almost_sure
      params hAlpha hNeutral hEq0 hEq1 (a + b) (by omega)
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lineagePathMeasure, homogeneousPathMeasure]
    infer_instance
  have hBwinner : P Bwinner = 0 := by
    dsimp [Bwinner]
    rw [measure_compl hWmeas (measure_ne_top P W), hW,
      measure_univ, tsub_self]
  have ha_le : a ≤ a + b := Nat.le_add_right a b
  have hBrevive : P Brevive = 0 := by
    dsimp [Brevive]
    exact measure_iUnion_null fun t =>
      measure_union_null
        (lineage_prefix_no_revival_species0_fixed
          params hNeutral hEq0 hEq1 a ha_le t)
        (lineage_prefix_no_revival_species1_fixed
          params hNeutral hEq0 hEq1 a ha_le t)
  have hBad : P Bad = 0 :=
    measure_union_null hBwinner hBrevive
  have hGoodEquiv : ∀ ω, ω ∉ Bad →
      (ω ∈ M ↔ ω ∈ G) := by
    intro ω hω
    have hwin : ∃ i, lineageWinnerEvent i ω := by
      by_contra h
      apply hω
      exact Or.inl (by
        dsimp [Bwinner, W]
        simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq]
        exact h)
    have hnr0 : ∀ t,
        (lineageAggregate a (ω t)).1 = 0 →
          (lineageAggregate a (ω (t + 1))).1 = 0 := by
      intro t hz
      by_contra hnext
      apply hω
      exact Or.inr (Set.mem_iUnion.mpr ⟨t,
        Or.inl ⟨hz, hnext⟩⟩)
    have hnr1 : ∀ t,
        (lineageAggregate a (ω t)).2 = 0 →
          (lineageAggregate a (ω (t + 1))).2 = 0 := by
      intro t hz
      by_contra hnext
      apply hω
      exact Or.inr (Set.mem_iUnion.mpr ⟨t,
        Or.inr ⟨hz, hnext⟩⟩)
    exact majorityConsensusEvent_iff_lineageWinner
      a b ω hwin hnr0 hnr1
  have hMsub : M ⊆ G ∪ Bad := by
    intro ω hω
    by_cases hbad : ω ∈ Bad
    · exact Or.inr hbad
    · exact Or.inl ((hGoodEquiv ω hbad).mp hω)
  have hGsub : G ⊆ M ∪ Bad := by
    intro ω hω
    by_cases hbad : ω ∈ Bad
    · exact Or.inr hbad
    · exact Or.inl ((hGoodEquiv ω hbad).mpr hω)
  have hMG : P M = P G := le_antisymm
    (calc
      P M ≤ P (G ∪ Bad) := measure_mono hMsub
      _ ≤ P G + P Bad := measure_union_le _ _
      _ = P G := by rw [hBad, add_zero])
    (calc
      P G ≤ P (M ∪ Bad) := measure_mono hGsub
      _ ≤ P M + P Bad := measure_union_le _ _
      _ = P M := by rw [hBad, add_zero])
  calc
    P M = P G := hMG
    _ = (a : ENNReal) * (a + b : ENNReal)⁻¹ :=
      lineage_majority_winner_probability
        params hAlpha hNeutral hEq0 hEq1 a b ha hb hba

/-- The majority-probability theorem obtained through the concrete lineage
chain, its path-law symmetry, and the aggregation bridge to the LV chain. -/
theorem nsd_majority_probability_via_lineages
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    majorityConsensusProb .nonSelfDestructive params (a, b) =
      ENNReal.ofReal ((a : Real) / (a + b)) := by
  let P := lineagePathMeasure params (a + b)
  let f : (Nat → LinState (a + b)) → (Nat → PopState) :=
    pathMap (lineageAggregate a)
  let A : Set (Nat → PopState) :=
    {ω | majorityConsensusEvent (a, b) ω}
  have hf : Measurable f :=
    measurable_pathMap _ (measurable_lineageAggregate a)
  have hA : MeasurableSet A :=
    measurableSet_majorityConsensusEvent (a, b)
  have hbridge :=
    lineagePathMeasure_map_aggregate
      params hNeutral hEq0 hEq1 a b
  have hpush := congrArg (fun μ : Measure (Nat → PopState) => μ A) hbridge
  rw [Measure.map_apply hf hA] at hpush
  have hlineage :=
    lineage_majority_event_probability
      params hAlpha hNeutral hEq0 hEq1 a b ha hb hba
  change P (f ⁻¹' A) =
    (a : ENNReal) * (a + b : ENNReal)⁻¹ at hlineage
  unfold majorityConsensusProb
  calc
    lvPathMeasure .nonSelfDestructive params (a, b) A
        = P (f ⁻¹' A) := hpush.symm
    _ = (a : ENNReal) * (a + b : ENNReal)⁻¹ := hlineage
    _ = ENNReal.ofReal ((a : Real) / (a + b)) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity :
        (0 : Real) < (a + b))]
      rw [ENNReal.ofReal_add
        (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      simp only [ENNReal.ofReal_natCast, div_eq_mul_inv]

end LVConsensus
