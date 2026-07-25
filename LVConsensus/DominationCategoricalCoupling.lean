import LVConsensus.ChainDomination
import LVConsensus.KernelPathMap

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal

namespace LVConsensus

/-!
# The categorical core of the chain-domination pseudo-coupling

At an active step, classify the two-species transition as bad, other, or
good, with probabilities `P`, `1 - P - Q`, and `Q`, where `Q` is the
actual probability of the chosen good-event set.  (In the LV application,
the profile's `goodEvent` is only a lower bound on this `Q`.)  Classify the
birth--death transition as birth, hold, or death, with probabilities `p`,
`1 - p - q`, and `q`.

The domination inequalities `P ≤ p` and `q ≤ Q` are exactly what is needed
to couple these categories so that every bad event is paired with a birth and
every death is paired with a good event.  The construction below is explicit;
it is the finite transport plan behind the interval coupling in the paper.
-/

/-- The six possibly nonzero cells of the categorical transport plan.
Unsupported pairs (bad/hold, bad/death, other/death) have mass zero. -/
structure DominationCategoryCoupling
    (P Q p q : Real) where
  badBirth : Real
  otherBirth : Real
  otherHold : Real
  goodBirth : Real
  goodHold : Real
  goodDeath : Real
  badBirth_nonneg : 0 ≤ badBirth
  otherBirth_nonneg : 0 ≤ otherBirth
  otherHold_nonneg : 0 ≤ otherHold
  goodBirth_nonneg : 0 ≤ goodBirth
  goodHold_nonneg : 0 ≤ goodHold
  goodDeath_nonneg : 0 ≤ goodDeath
  bad_row : badBirth = P
  other_row : otherBirth + otherHold = 1 - P - Q
  good_row : goodBirth + goodHold + goodDeath = Q
  birth_col : badBirth + otherBirth + goodBirth = p
  hold_col : otherHold + goodHold = 1 - p - q
  death_col : goodDeath = q

/-- Explicit construction of the categorical pseudo-coupling from (D1)--(D2).
No coupling object or certificate is assumed. -/
theorem dominationCategoryCoupling_exists
    (P Q p q : Real)
    (hP : 0 ≤ P) (_hQ : 0 ≤ Q)
    (_hp : 0 ≤ p) (hq : 0 ≤ q)
    (hPQ : P + Q ≤ 1)
    (hpq : p + q ≤ 1)
    (hD1 : P ≤ p)
    (hD2 : q ≤ Q) :
    Nonempty (DominationCategoryCoupling P Q p q) := by
  let other : Real := 1 - P - Q
  let goodResidual : Real := Q - q
  let birthResidual : Real := p - P
  let hold : Real := 1 - p - q
  let x : Real := min other birthResidual
  have hother : 0 ≤ other := by
    dsimp [other]
    linarith
  have hgoodResidual : 0 ≤ goodResidual := by
    dsimp [goodResidual]
    linarith
  have hbirthResidual : 0 ≤ birthResidual := by
    dsimp [birthResidual]
    linarith
  have hhold : 0 ≤ hold := by
    dsimp [hold]
    linarith
  have hxother : x ≤ other := min_le_left _ _
  have hxbirth : x ≤ birthResidual := min_le_right _ _
  have hx : 0 ≤ x := le_min hother hbirthResidual
  have hotherHold : 0 ≤ other - x := sub_nonneg.mpr hxother
  have hgoodBirth : 0 ≤ birthResidual - x := sub_nonneg.mpr hxbirth
  have hresidualBalance :
      other + goodResidual = birthResidual + hold := by
    dsimp [other, goodResidual, birthResidual, hold]
    ring
  have hgoodHold :
      0 ≤ goodResidual - (birthResidual - x) := by
    rcases le_total other birthResidual with hob | hbo
    · have hxmin : x = other := min_eq_left hob
      rw [hxmin]
      linarith
    · have hxmin : x = birthResidual := min_eq_right hbo
      rw [hxmin]
      linarith
  exact ⟨
    { badBirth := P
      otherBirth := x
      otherHold := other - x
      goodBirth := birthResidual - x
      goodHold := goodResidual - (birthResidual - x)
      goodDeath := q
      badBirth_nonneg := hP
      otherBirth_nonneg := hx
      otherHold_nonneg := hotherHold
      goodBirth_nonneg := hgoodBirth
      goodHold_nonneg := hgoodHold
      goodDeath_nonneg := hq
      bad_row := rfl
      other_row := by
        dsimp [other]
        ring
      good_row := by
        dsimp [goodResidual, birthResidual]
        ring
      birth_col := by
        dsimp [birthResidual]
        ring
      hold_col := by
        dsimp [other, goodResidual, birthResidual, hold]
        ring
      death_col := rfl }⟩

/-- At an interior LV state, (D1)--(D2) instantiate the explicit categorical
transport plan with the *actual* probabilities of the labelled bad and good
sets.  The profile's good probability is used only as a lower bound. -/
theorem lvDominationCategoryCoupling_exists
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    Nonempty
      (DominationCategoryCoupling
        (lvLabeledKernel v params z
          (dominationBadSet z.1)).toReal
        (lvLabeledKernel v params z
          (dominationGoodSet v z.1)).toReal
        (N.p (Nat.min z.1.1 z.1.2))
        (N.q (Nat.min z.1.1 z.1.2))) := by
  let μ := lvLabeledKernel v params z
  let bad := dominationBadSet z.1
  let good := dominationGoodSet v z.1
  let m := Nat.min z.1.1 z.1.2
  have hbad_ne : μ bad ≠ ⊤ := measure_ne_top μ bad
  have hgood_ne : μ good ≠ ⊤ := measure_ne_top μ good
  have hsum_ne : μ bad + μ good ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hbad_ne, hgood_ne⟩
  have hdisj : Disjoint bad good :=
    dominationBadSet_disjoint_goodSet v z.1
  have hgood_meas : MeasurableSet good :=
    (Set.to_countable _).measurableSet
  have hsum : μ bad + μ good ≤ 1 := by
    rw [← measure_union hdisj hgood_meas]
    calc
      μ (bad ∪ good) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by
        letI : IsProbabilityMeasure μ := by infer_instance
        exact measure_univ
  have hsumReal :
      (μ bad).toReal + (μ good).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono (by simp) hsum
    rw [ENNReal.toReal_add hbad_ne hgood_ne] at h
    simpa using h
  have hD1Real : (μ bad).toReal ≤ N.p m := by
    have hD1Profile := hDom.1 z.1.1 z.1.2
    have hENN :
        μ bad ≤ ENNReal.ofReal (N.p m) := by
      dsimp only [μ, bad, m]
      rw [lvLabeledKernel_dominationBadSet
        v params hGamma0 hGamma1 z.1 z.2 hminpos]
      exact ENNReal.ofReal_le_ofReal hD1Profile
    have h :=
      (ENNReal.toReal_le_toReal hbad_ne ENNReal.ofReal_ne_top).mpr hENN
    simpa [ENNReal.toReal_ofReal (N.p_nonneg m)] using h
  have hD2Real : N.q m ≤ (μ good).toReal := by
    have hD2Profile := hDom.2 z.1.1 z.1.2
    have hENN :
        ENNReal.ofReal (N.q m) ≤ μ good := by
      calc
        ENNReal.ofReal (N.q m) ≤
            ENNReal.ofReal ((lvEventProfile v params).goodEvent z.1) :=
          ENNReal.ofReal_le_ofReal hD2Profile
        _ ≤ μ good := by
          dsimp only [μ, good]
          exact lvLabeledKernel_dominationGoodSet
            v params hGamma0 hGamma1 z.1 z.2 hminpos
    have h :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hgood_ne).mpr hENN
    simpa [ENNReal.toReal_ofReal (N.q_nonneg m)] using h
  exact dominationCategoryCoupling_exists
    (μ bad).toReal (μ good).toReal (N.p m) (N.q m)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (N.p_nonneg m) (N.q_nonneg m)
    hsumReal (N.pq_le_one m) hD1Real hD2Real

/-! ## Lifting the categorical transport to labelled transitions -/

/-- Put a conditioned labelled transition in the left coordinate, a prescribed
birth--death target in the right coordinate, and weight the resulting measure
by one cell of the categorical transport plan. -/
noncomputable def weightedConditionalPair
    (μ : Measure LabeledPopState) (A : Set LabeledPopState)
    (c : Real) (target : Nat) :
    Measure (LabeledPopState × Nat) :=
  ENNReal.ofReal c •
    (ProbabilityTheory.cond μ A).map (fun z => (z, target))

private lemma measureMass_smul_cond
    (μ : Measure LabeledPopState) [IsFiniteMeasure μ]
    (A : Set LabeledPopState) (hA : MeasurableSet A) :
    ENNReal.ofReal (μ A).toReal • ProbabilityTheory.cond μ A =
      μ.restrict A := by
  have htop : μ A ≠ ⊤ := measure_ne_top μ A
  ext T hT
  simp only [Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_toReal htop,
    ProbabilityTheory.cond_apply' hT,
    Measure.restrict_apply hT]
  by_cases hzero : μ A = 0
  · simp [hzero, measure_mono_null (Set.inter_subset_right) hzero]
  · rw [← mul_assoc, ENNReal.mul_inv_cancel hzero htop, one_mul,
      Set.inter_comm]

private lemma weightedConditionalPair_fst
    (μ : Measure LabeledPopState) (A : Set LabeledPopState)
    (c : Real) (target : Nat) :
    (weightedConditionalPair μ A c target).fst =
      ENNReal.ofReal c • ProbabilityTheory.cond μ A := by
  simp only [weightedConditionalPair, Measure.fst,
    Measure.map_smul]
  rw [Measure.map_map measurable_fst (by measurability)]
  have hf :
      (Prod.fst ∘ fun z : LabeledPopState => (z, target)) = id := rfl
  rw [hf, Measure.map_id]

private lemma weightedConditionalPair_snd
    (μ : Measure LabeledPopState) [IsFiniteMeasure μ]
    (A : Set LabeledPopState)
    (c : Real) (target : Nat)
    (hc : 0 ≤ c) (hcA : c ≤ (μ A).toReal) :
    (weightedConditionalPair μ A c target).snd =
      ENNReal.ofReal c • Measure.dirac target := by
  by_cases hzero : μ A = 0
  · have htoReal : (μ A).toReal = 0 := by simp [hzero]
    have hc0 : c = 0 := by linarith
    simp [weightedConditionalPair, hc0]
  · letI : IsProbabilityMeasure (ProbabilityTheory.cond μ A) :=
      ProbabilityTheory.cond_isProbabilityMeasure hzero
    simp only [weightedConditionalPair, Measure.snd,
      Measure.map_smul]
    rw [Measure.map_map measurable_snd (by measurability)]
    have hf :
        (Prod.snd ∘ fun z : LabeledPopState => (z, target)) =
          fun _ => target := rfl
    rw [hf, Measure.map_const, measure_univ, one_smul]

private lemma weightedConditionalPair_ae_support
    (μ : Measure LabeledPopState)
    (A : Set LabeledPopState) (hA : MeasurableSet A)
    (c : Real) (target : Nat)
    {R : LabeledPopState → Prop}
    (hR : ∀ᵐ z ∂μ, R z) :
    ∀ᵐ y ∂weightedConditionalPair μ A c target,
      y.1 ∈ A ∧ y.2 = target ∧ R y.1 := by
  apply Measure.ae_smul_measure
  apply (MeasureTheory.ae_map_iff
    (μ := ProbabilityTheory.cond μ A)
    (f := fun z : LabeledPopState => (z, target))
    (by fun_prop)
    (Set.to_countable _).measurableSet).2
  have hRcond :
      ∀ᵐ z ∂ProbabilityTheory.cond μ A, R z :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le hR
  filter_upwards [ProbabilityTheory.ae_cond_mem hA, hRcond] with z hzA hzR
  exact ⟨hzA, rfl, hzR⟩

/-- The actual six-cell joint transition measure.  Its rows are bad, residual,
and good labelled LV transitions; its columns are birth, hold, and death of
the auxiliary chain. -/
noncomputable def dominationJointMeasure
    (μ : Measure LabeledPopState)
    (bad other good : Set LabeledPopState)
    (n : Nat)
    {P Q p q : Real}
    (c : DominationCategoryCoupling P Q p q) :
    Measure (LabeledPopState × Nat) :=
  weightedConditionalPair μ bad c.badBirth (n + 1) +
    weightedConditionalPair μ other c.otherBirth (n + 1) +
    weightedConditionalPair μ other c.otherHold n +
    weightedConditionalPair μ good c.goodBirth (n + 1) +
    weightedConditionalPair μ good c.goodHold n +
    weightedConditionalPair μ good c.goodDeath (n - 1)

/-- The first marginal of the lifted six-cell plan is exactly the original
labelled transition measure. -/
theorem dominationJointMeasure_fst
    (μ : Measure LabeledPopState) [IsProbabilityMeasure μ]
    (bad good : Set LabeledPopState)
    (hbad : MeasurableSet bad) (hgood : MeasurableSet good)
    (hdisj : Disjoint bad good)
    (n : Nat) (p q : Real)
    (c : DominationCategoryCoupling
      (μ bad).toReal (μ good).toReal p q) :
    (dominationJointMeasure μ bad (bad ∪ good)ᶜ good n c).fst = μ := by
  let other := (bad ∪ good)ᶜ
  have hother : MeasurableSet other := (hbad.union hgood).compl
  have hbad_ne : μ bad ≠ ⊤ := measure_ne_top μ bad
  have hgood_ne : μ good ≠ ⊤ := measure_ne_top μ good
  have hother_ne : μ other ≠ ⊤ := measure_ne_top μ other
  have hbg_ne : μ bad + μ good ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hbad_ne, hgood_ne⟩
  have hmass :
      μ bad + μ good + μ other = 1 := by
    calc
      μ bad + μ good + μ other =
          μ (bad ∪ good) + μ other := by
            rw [measure_union hdisj hgood]
      _ = μ ((bad ∪ good) ∪ other) := by
            rw [measure_union
              (Set.disjoint_left.2 (by
                intro x hx hxcompl
                exact hxcompl hx))
              hother]
      _ = μ Set.univ := by
            congr 1
            dsimp only [other]
            exact Set.union_compl_self (bad ∪ good)
      _ = 1 := measure_univ
  have hotherMass :
      (μ other).toReal =
        1 - (μ bad).toReal - (μ good).toReal := by
    have hmassReal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add hbg_ne hother_ne,
      ENNReal.toReal_add hbad_ne hgood_ne] at hmassReal
    norm_num at hmassReal
    linarith
  rw [dominationJointMeasure]
  simp only [Measure.fst_add, weightedConditionalPair_fst]
  have hbadRow :
      ENNReal.ofReal c.badBirth • ProbabilityTheory.cond μ bad =
        μ.restrict bad := by
    rw [c.bad_row]
    exact measureMass_smul_cond μ bad hbad
  have hotherRow :
      ENNReal.ofReal c.otherBirth • ProbabilityTheory.cond μ other +
          ENNReal.ofReal c.otherHold • ProbabilityTheory.cond μ other =
        μ.restrict other := by
    rw [← add_smul, ← ENNReal.ofReal_add
        c.otherBirth_nonneg c.otherHold_nonneg,
      c.other_row, ← hotherMass]
    exact measureMass_smul_cond μ other hother
  have hgoodRow :
      ENNReal.ofReal c.goodBirth • ProbabilityTheory.cond μ good +
          ENNReal.ofReal c.goodHold • ProbabilityTheory.cond μ good +
          ENNReal.ofReal c.goodDeath • ProbabilityTheory.cond μ good =
        μ.restrict good := by
    rw [← add_smul, ← ENNReal.ofReal_add
        c.goodBirth_nonneg c.goodHold_nonneg,
      ← add_smul, ← ENNReal.ofReal_add
        (add_nonneg c.goodBirth_nonneg c.goodHold_nonneg)
        c.goodDeath_nonneg,
      c.good_row]
    exact measureMass_smul_cond μ good hgood
  calc
    ENNReal.ofReal c.badBirth • ProbabilityTheory.cond μ bad +
          ENNReal.ofReal c.otherBirth • ProbabilityTheory.cond μ other +
          ENNReal.ofReal c.otherHold • ProbabilityTheory.cond μ other +
          ENNReal.ofReal c.goodBirth • ProbabilityTheory.cond μ good +
          ENNReal.ofReal c.goodHold • ProbabilityTheory.cond μ good +
          ENNReal.ofReal c.goodDeath • ProbabilityTheory.cond μ good =
        μ.restrict bad + μ.restrict other + μ.restrict good := by
      calc
        _ =
            (ENNReal.ofReal c.badBirth • ProbabilityTheory.cond μ bad) +
              (ENNReal.ofReal c.otherBirth •
                  ProbabilityTheory.cond μ other +
                ENNReal.ofReal c.otherHold •
                  ProbabilityTheory.cond μ other) +
              (ENNReal.ofReal c.goodBirth •
                  ProbabilityTheory.cond μ good +
                ENNReal.ofReal c.goodHold •
                  ProbabilityTheory.cond μ good +
                ENNReal.ofReal c.goodDeath •
                  ProbabilityTheory.cond μ good) := by
              simp only [add_assoc]
        _ = μ.restrict bad + μ.restrict other + μ.restrict good := by
          rw [hbadRow]
          rw [show
          ENNReal.ofReal c.otherBirth • ProbabilityTheory.cond μ other +
              ENNReal.ofReal c.otherHold • ProbabilityTheory.cond μ other =
            μ.restrict other from hotherRow]
          rw [show
          ENNReal.ofReal c.goodBirth • ProbabilityTheory.cond μ good +
              ENNReal.ofReal c.goodHold • ProbabilityTheory.cond μ good +
              ENNReal.ofReal c.goodDeath • ProbabilityTheory.cond μ good =
            μ.restrict good from hgoodRow]
    _ = μ.restrict bad + μ.restrict good + μ.restrict other := by
      simp only [add_assoc]
      rw [add_comm (μ.restrict other) (μ.restrict good)]
    _ = μ.restrict (bad ∪ good) + μ.restrict other := by
      rw [Measure.restrict_union hdisj hgood]
    _ = μ := by
      dsimp only [other]
      exact Measure.restrict_add_restrict_compl (hbad.union hgood)

/-- The second marginal of the lifted six-cell plan is the prescribed
birth--death transition measure. -/
theorem dominationJointMeasure_snd
    (μ : Measure LabeledPopState) [IsProbabilityMeasure μ]
    (bad good : Set LabeledPopState)
    (hbad : MeasurableSet bad) (hgood : MeasurableSet good)
    (hdisj : Disjoint bad good)
    (n : Nat) (p q : Real)
    (c : DominationCategoryCoupling
      (μ bad).toReal (μ good).toReal p q) :
    (dominationJointMeasure μ bad (bad ∪ good)ᶜ good n c).snd =
      ENNReal.ofReal p • Measure.dirac (n + 1) +
        ENNReal.ofReal q • Measure.dirac (n - 1) +
        ENNReal.ofReal (1 - p - q) • Measure.dirac n := by
  let other := (bad ∪ good)ᶜ
  have hother : MeasurableSet other := (hbad.union hgood).compl
  have hbad_ne : μ bad ≠ ⊤ := measure_ne_top μ bad
  have hgood_ne : μ good ≠ ⊤ := measure_ne_top μ good
  have hother_ne : μ other ≠ ⊤ := measure_ne_top μ other
  have hbg_ne : μ bad + μ good ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hbad_ne, hgood_ne⟩
  have hmass :
      μ bad + μ good + μ other = 1 := by
    calc
      μ bad + μ good + μ other =
          μ (bad ∪ good) + μ other := by
            rw [measure_union hdisj hgood]
      _ = μ ((bad ∪ good) ∪ other) := by
            rw [measure_union
              (Set.disjoint_left.2 (by
                intro x hx hxcompl
                exact hxcompl hx))
              hother]
      _ = μ Set.univ := by
            congr 1
            dsimp only [other]
            exact Set.union_compl_self (bad ∪ good)
      _ = 1 := measure_univ
  have hotherMass :
      (μ other).toReal =
        1 - (μ bad).toReal - (μ good).toReal := by
    have hmassReal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add hbg_ne hother_ne,
      ENNReal.toReal_add hbad_ne hgood_ne] at hmassReal
    norm_num at hmassReal
    linarith
  have hbadBound :
      c.badBirth ≤ (μ bad).toReal := by rw [c.bad_row]
  have hotherBirthBound :
      c.otherBirth ≤ (μ other).toReal := by
    rw [hotherMass, ← c.other_row]
    linarith [c.otherHold_nonneg]
  have hotherHoldBound :
      c.otherHold ≤ (μ other).toReal := by
    rw [hotherMass, ← c.other_row]
    linarith [c.otherBirth_nonneg]
  have hgoodBirthBound :
      c.goodBirth ≤ (μ good).toReal := by
    calc
      c.goodBirth ≤ c.goodBirth + c.goodHold + c.goodDeath := by
        linarith [c.goodHold_nonneg, c.goodDeath_nonneg]
      _ = (μ good).toReal := c.good_row
  have hgoodHoldBound :
      c.goodHold ≤ (μ good).toReal := by
    calc
      c.goodHold ≤ c.goodBirth + c.goodHold + c.goodDeath := by
        linarith [c.goodBirth_nonneg, c.goodDeath_nonneg]
      _ = (μ good).toReal := c.good_row
  have hgoodDeathBound :
      c.goodDeath ≤ (μ good).toReal := by
    calc
      c.goodDeath ≤ c.goodBirth + c.goodHold + c.goodDeath := by
        linarith [c.goodBirth_nonneg, c.goodHold_nonneg]
      _ = (μ good).toReal := c.good_row
  have hbb := weightedConditionalPair_snd μ bad
    c.badBirth (n + 1) c.badBirth_nonneg hbadBound
  have hob := weightedConditionalPair_snd μ other
    c.otherBirth (n + 1) c.otherBirth_nonneg hotherBirthBound
  have hoh := weightedConditionalPair_snd μ other
    c.otherHold n c.otherHold_nonneg hotherHoldBound
  have hgb := weightedConditionalPair_snd μ good
    c.goodBirth (n + 1) c.goodBirth_nonneg hgoodBirthBound
  have hgh := weightedConditionalPair_snd μ good
    c.goodHold n c.goodHold_nonneg hgoodHoldBound
  have hgd := weightedConditionalPair_snd μ good
    c.goodDeath (n - 1) c.goodDeath_nonneg hgoodDeathBound
  have hbirth :
      ENNReal.ofReal c.badBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.otherBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.goodBirth • Measure.dirac (n + 1) =
        ENNReal.ofReal p • Measure.dirac (n + 1) := by
    rw [← add_smul, ← add_smul,
      ← ENNReal.ofReal_add c.badBirth_nonneg c.otherBirth_nonneg,
      ← ENNReal.ofReal_add
        (add_nonneg c.badBirth_nonneg c.otherBirth_nonneg)
        c.goodBirth_nonneg,
      c.birth_col]
  have hhold :
      ENNReal.ofReal c.otherHold • Measure.dirac n +
          ENNReal.ofReal c.goodHold • Measure.dirac n =
        ENNReal.ofReal (1 - p - q) • Measure.dirac n := by
    rw [← add_smul,
      ← ENNReal.ofReal_add c.otherHold_nonneg c.goodHold_nonneg,
      c.hold_col]
  have hdeath :
      ENNReal.ofReal c.goodDeath • Measure.dirac (n - 1) =
        ENNReal.ofReal q • Measure.dirac (n - 1) := by
    rw [c.death_col]
  rw [dominationJointMeasure]
  simp only [Measure.snd_add]
  rw [hbb, hob, hoh, hgb, hgh, hgd]
  calc
    ENNReal.ofReal c.badBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.otherBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.otherHold • Measure.dirac n +
          ENNReal.ofReal c.goodBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.goodHold • Measure.dirac n +
          ENNReal.ofReal c.goodDeath • Measure.dirac (n - 1) =
        (ENNReal.ofReal c.badBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.otherBirth • Measure.dirac (n + 1) +
          ENNReal.ofReal c.goodBirth • Measure.dirac (n + 1)) +
        (ENNReal.ofReal c.otherHold • Measure.dirac n +
          ENNReal.ofReal c.goodHold • Measure.dirac n) +
        ENNReal.ofReal c.goodDeath • Measure.dirac (n - 1) := by
          simp only [add_assoc]
          rw [add_left_comm
            (ENNReal.ofReal c.otherHold • Measure.dirac n)
            (ENNReal.ofReal c.goodBirth • Measure.dirac (n + 1))]
    _ = ENNReal.ofReal p • Measure.dirac (n + 1) +
          ENNReal.ofReal (1 - p - q) • Measure.dirac n +
          ENNReal.ofReal q • Measure.dirac (n - 1) := by
          rw [hbirth, hhold, hdeath]
    _ = ENNReal.ofReal p • Measure.dirac (n + 1) +
          ENNReal.ofReal q • Measure.dirac (n - 1) +
          ENNReal.ofReal (1 - p - q) • Measure.dirac n := by
          simp only [add_assoc]
          rw [add_comm
            (ENNReal.ofReal (1 - p - q) • Measure.dirac n)
            (ENNReal.ofReal q • Measure.dirac (n - 1))]

/-! ## The unconditional LV one-step coupling -/

/-- The explicit categorical transport chosen from the domination
inequalities at an interior labelled LV state. -/
noncomputable def lvDominationCategoryCoupling
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    DominationCategoryCoupling
      (lvLabeledKernel v params z
        (dominationBadSet z.1)).toReal
      (lvLabeledKernel v params z
        (dominationGoodSet v z.1)).toReal
      (N.p (Nat.min z.1.1 z.1.2))
      (N.q (Nat.min z.1.1 z.1.2)) :=
  Classical.choice
    (lvDominationCategoryCoupling_exists v params hGamma0 hGamma1
      N hDom z hminpos)

/-- One active step of the labelled asynchronous pseudo-coupling. -/
noncomputable def lvDominationJointMeasure
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    Measure (LabeledPopState × Nat) :=
  dominationJointMeasure
    (lvLabeledKernel v params z)
    (dominationBadSet z.1)
    (dominationOtherSet v z.1)
    (dominationGoodSet v z.1)
    (Nat.min z.1.1 z.1.2)
    (lvDominationCategoryCoupling v params hGamma0 hGamma1
      N hDom z hminpos)

/-- The active joint step has exactly the labelled LV transition as its first
marginal. -/
theorem lvDominationJointMeasure_fst
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    (lvDominationJointMeasure v params hGamma0 hGamma1
      N hDom z hminpos).fst =
        lvLabeledKernel v params z := by
  rw [lvDominationJointMeasure]
  exact dominationJointMeasure_fst
    (lvLabeledKernel v params z)
    (dominationBadSet z.1)
    (dominationGoodSet v z.1)
    (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet
    (dominationBadSet_disjoint_goodSet v z.1)
    (Nat.min z.1.1 z.1.2)
    (N.p (Nat.min z.1.1 z.1.2))
    (N.q (Nat.min z.1.1 z.1.2))
    (lvDominationCategoryCoupling v params hGamma0 hGamma1
      N hDom z hminpos)

/-- The active joint step has exactly the birth--death transition as its
second marginal. -/
theorem lvDominationJointMeasure_snd
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    (lvDominationJointMeasure v params hGamma0 hGamma1
      N hDom z hminpos).snd =
        bdKernel N (Nat.min z.1.1 z.1.2) := by
  rw [lvDominationJointMeasure]
  simp only [dominationOtherSet]
  rw [dominationJointMeasure_snd
    (lvLabeledKernel v params z)
    (dominationBadSet z.1)
    (dominationGoodSet v z.1)
    (Set.to_countable _).measurableSet
    (Set.to_countable _).measurableSet
    (dominationBadSet_disjoint_goodSet v z.1)]
  rfl

/-- The active labelled joint step satisfies the two support implications
used by the paper's pathwise induction.  A bad labelled reaction forces an
auxiliary birth, and an auxiliary death forces a good labelled reaction.
The reaction label also records its true LV target. -/
theorem lvDominationJointMeasure_ae_category_rules
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    ∀ᵐ y ∂lvDominationJointMeasure v params hGamma0 hGamma1
        N hDom z hminpos,
      (y.1 ∈ dominationBadSet z.1 →
          y.2 = Nat.min z.1.1 z.1.2 + 1) ∧
      (y.2 = Nat.min z.1.1 z.1.2 - 1 →
          y.1 ∈ dominationGoodSet v z.1) ∧
      y.1.1 = lvReactionTarget v z.1 y.1.2 ∧
      (y.2 = Nat.min z.1.1 z.1.2 + 1 ∨
        y.2 = Nat.min z.1.1 z.1.2 ∨
        y.2 = Nat.min z.1.1 z.1.2 - 1) := by
  let μ := lvLabeledKernel v params z
  let bad := dominationBadSet z.1
  let good := dominationGoodSet v z.1
  let other := dominationOtherSet v z.1
  let m := Nat.min z.1.1 z.1.2
  let c := lvDominationCategoryCoupling v params hGamma0 hGamma1
    N hDom z hminpos
  have hvalid :
      ∀ᵐ z' ∂μ, z'.1 = lvReactionTarget v z.1 z'.2 :=
    lvLabeledKernel_ae_reactionTarget v params z
  have hbadMeas : MeasurableSet bad :=
    (Set.to_countable _).measurableSet
  have hgoodMeas : MeasurableSet good :=
    (Set.to_countable _).measurableSet
  have hotherMeas : MeasurableSet other :=
    (Set.to_countable _).measurableSet
  have hdisj : Disjoint bad good :=
    dominationBadSet_disjoint_goodSet v z.1
  let R : LabeledPopState × Nat → Prop := fun y =>
    (y.1 ∈ bad → y.2 = m + 1) ∧
      (y.2 = m - 1 → y.1 ∈ good) ∧
      y.1.1 = lvReactionTarget v z.1 y.1.2 ∧
      (y.2 = m + 1 ∨ y.2 = m ∨ y.2 = m - 1)
  have hbb :
      ∀ᵐ y ∂weightedConditionalPair μ bad c.badBirth (m + 1),
        R y := by
    filter_upwards [weightedConditionalPair_ae_support μ bad hbadMeas
      c.badBirth (m + 1) hvalid] with y hy
    rcases hy with ⟨hybad, htarget, hyvalid⟩
    exact ⟨fun _ => htarget, by omega, hyvalid, Or.inl htarget⟩
  have hob :
      ∀ᵐ y ∂weightedConditionalPair μ other c.otherBirth (m + 1),
        R y := by
    filter_upwards [weightedConditionalPair_ae_support μ other hotherMeas
      c.otherBirth (m + 1) hvalid] with y hy
    rcases hy with ⟨hyother, htarget, hyvalid⟩
    have hnbad : y.1 ∉ bad := by
      intro hybad
      exact hyother (Or.inl hybad)
    exact ⟨fun hybad => (hnbad hybad).elim, by omega, hyvalid,
      Or.inl htarget⟩
  have hoh :
      ∀ᵐ y ∂weightedConditionalPair μ other c.otherHold m,
        R y := by
    filter_upwards [weightedConditionalPair_ae_support μ other hotherMeas
      c.otherHold m hvalid] with y hy
    rcases hy with ⟨hyother, htarget, hyvalid⟩
    have hnbad : y.1 ∉ bad := by
      intro hybad
      exact hyother (Or.inl hybad)
    exact ⟨fun hybad => (hnbad hybad).elim, by omega, hyvalid,
      Or.inr (Or.inl htarget)⟩
  have hgb :
      ∀ᵐ y ∂weightedConditionalPair μ good c.goodBirth (m + 1),
        R y := by
    filter_upwards [weightedConditionalPair_ae_support μ good hgoodMeas
      c.goodBirth (m + 1) hvalid] with y hy
    rcases hy with ⟨hygood, htarget, hyvalid⟩
    have hnbad : y.1 ∉ bad := fun hybad =>
      Set.disjoint_left.1 hdisj hybad hygood
    exact ⟨fun hybad => (hnbad hybad).elim, by omega, hyvalid,
      Or.inl htarget⟩
  have hgh :
      ∀ᵐ y ∂weightedConditionalPair μ good c.goodHold m,
        R y := by
    filter_upwards [weightedConditionalPair_ae_support μ good hgoodMeas
      c.goodHold m hvalid] with y hy
    rcases hy with ⟨hygood, htarget, hyvalid⟩
    have hnbad : y.1 ∉ bad := fun hybad =>
      Set.disjoint_left.1 hdisj hybad hygood
    exact ⟨fun hybad => (hnbad hybad).elim, by omega, hyvalid,
      Or.inr (Or.inl htarget)⟩
  have hgd :
      ∀ᵐ y ∂weightedConditionalPair μ good c.goodDeath (m - 1),
        R y := by
    filter_upwards [weightedConditionalPair_ae_support μ good hgoodMeas
      c.goodDeath (m - 1) hvalid] with y hy
    rcases hy with ⟨hygood, htarget, hyvalid⟩
    have hnbad : y.1 ∉ bad := fun hybad =>
      Set.disjoint_left.1 hdisj hybad hygood
    exact ⟨fun hybad => (hnbad hybad).elim, fun _ => hygood, hyvalid,
      Or.inr (Or.inr htarget)⟩
  have hadd {ρ η : Measure (LabeledPopState × Nat)}
      (hρ : ∀ᵐ y ∂ρ, R y) (hη : ∀ᵐ y ∂η, R y) :
      ∀ᵐ y ∂ρ + η, R y :=
    ae_add_measure_iff.2 ⟨hρ, hη⟩
  have hall :=
    hadd (hadd (hadd (hadd (hadd hbb hob) hoh) hgb) hgh) hgd
  simpa only [lvDominationJointMeasure, dominationJointMeasure,
    μ, bad, good, other, m, c, R] using hall

/-- At an active pseudo-coupling step, the new LV minority is bounded by the
new auxiliary state.  This is the one-step induction asserted in the paper. -/
theorem lvDominationJointMeasure_ae_min_le
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    ∀ᵐ y ∂lvDominationJointMeasure v params hGamma0 hGamma1
        N hDom z hminpos,
      Nat.min y.1.1.1 y.1.1.2 ≤ y.2 := by
  let m := Nat.min z.1.1 z.1.2
  filter_upwards [
    lvDominationJointMeasure_ae_category_rules v params
      hGamma0 hGamma1 N hDom z hminpos] with y hy
  rcases hy with ⟨hbadBirth, hdeathGood, hvalid, hsupport⟩
  have hsucc :
      Nat.min y.1.1.1 y.1.1.2 ≤ m + 1 := by
    rw [hvalid]
    exact lvReactionTarget_min_le_succ v z.1 y.1.2
  rcases hsupport with hbirth | hhold | hdeath
  · simpa only [hbirth] using hsucc
  · have hcat :
        y.1 ∈ dominationBadSet z.1 ∪ dominationGoodSet v z.1 ∪
          dominationOtherSet v z.1 := by
      rw [domination_category_partition]
      exact Set.mem_univ y.1
    rcases hcat with (hbad | hgood) | hother
    · have := hbadBirth hbad
      omega
    · have hgoodTarget :
          (lvReactionTarget v z.1 y.1.2, y.1.2) ∈
            dominationGoodSet v z.1 := by
        simpa [dominationGoodSet] using hgood
      have hdec :=
        lvReactionTarget_min_eq_pred_of_good
          v z.1 y.1.2 hminpos hgoodTarget
      rw [hvalid, hdec, hhold]
      omega
    · have hotherTarget :
          (lvReactionTarget v z.1 y.1.2, y.1.2) ∈
            dominationOtherSet v z.1 := by
        simpa [dominationOtherSet, dominationBadSet,
          dominationGoodSet] using hother
      have hnoninc :=
        lvReactionTarget_min_le_of_other v z.1 y.1.2 hotherTarget
      rw [hvalid, hhold]
      exact hnoninc
  · have hgood := hdeathGood hdeath
    have hgoodTarget :
        (lvReactionTarget v z.1 y.1.2, y.1.2) ∈
          dominationGoodSet v z.1 := by
      simpa [dominationGoodSet] using hgood
    have hdec :=
      lvReactionTarget_min_eq_pred_of_good
        v z.1 y.1.2 hminpos hgoodTarget
    rw [hvalid, hdec, hdeath]

instance lvDominationJointMeasure_isProbabilityMeasure
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z : LabeledPopState)
    (hminpos : 0 < Nat.min z.1.1 z.1.2) :
    IsProbabilityMeasure
      (lvDominationJointMeasure v params hGamma0 hGamma1
        N hDom z hminpos) := by
  constructor
  let ρ :=
    lvDominationJointMeasure v params hGamma0 hGamma1
      N hDom z hminpos
  calc
    ρ Set.univ = ρ.fst Set.univ := Measure.fst_univ.symm
    _ = lvLabeledKernel v params z Set.univ := by
      rw [show ρ.fst = lvLabeledKernel v params z from
        lvDominationJointMeasure_fst v params hGamma0 hGamma1
          N hDom z hminpos]
    _ = 1 := measure_univ

/-! ## The asynchronous joint kernel -/

/-- A physical pseudo-coupling state is active when the LV minority and the
auxiliary coordinate are equal.  Equality at zero is retained so that the
embedded chain is the LV chain stopped at consensus. -/
def isPseudoActive (x : LabeledPopState × Nat) : Prop :=
  Nat.min x.1.1.1 x.1.1.2 = x.2

/-- The labelled LV kernel stopped when consensus has been reached.  Stopping
is needed only after the paper's functionals have terminated; before
consensus this is exactly the original labelled LV kernel. -/
noncomputable def lvStoppedLabeledKernel
    (v : LVVariant) (params : LVParams) :
    Kernel LabeledPopState LabeledPopState :=
  Kernel.ofFunOfCountable fun z =>
    if Nat.min z.1.1 z.1.2 = 0 then
      Measure.dirac z
    else
      lvLabeledKernel v params z

instance lvStoppedLabeledKernel_isMarkovKernel
    (v : LVVariant) (params : LVParams) :
    IsMarkovKernel (lvStoppedLabeledKernel v params) where
  isProbabilityMeasure z := by
    simp only [lvStoppedLabeledKernel, Kernel.ofFunOfCountable,
      Kernel.coe_mk]
    split
    · infer_instance
    · infer_instance

/-- Keep the labelled LV coordinate fixed while taking one birth--death
transition. -/
noncomputable def freezeLVMeasure
    (z : LabeledPopState) (ν : Measure Nat) :
    Measure (LabeledPopState × Nat) :=
  ν.map (fun n => (z, n))

private lemma freezeLVMeasure_fst
    (z : LabeledPopState) (ν : Measure Nat)
    [IsProbabilityMeasure ν] :
    (freezeLVMeasure z ν).fst = Measure.dirac z := by
  rw [freezeLVMeasure, Measure.fst,
    Measure.map_map measurable_fst (by measurability)]
  have hf :
      (Prod.fst ∘ fun n : Nat => (z, n)) = fun _ => z := rfl
  rw [hf, Measure.map_const, measure_univ, one_smul]

private lemma freezeLVMeasure_snd
    (z : LabeledPopState) (ν : Measure Nat) :
    (freezeLVMeasure z ν).snd = ν := by
  rw [freezeLVMeasure, Measure.snd_map_prodMk measurable_const]
  simpa only [Measure.map_id']

instance freezeLVMeasure_isProbabilityMeasure
    (z : LabeledPopState) (ν : Measure Nat)
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (freezeLVMeasure z ν) := by
  constructor
  calc
    freezeLVMeasure z ν Set.univ =
        (freezeLVMeasure z ν).snd Set.univ := Measure.snd_univ.symm
    _ = ν Set.univ := by rw [freezeLVMeasure_snd]
    _ = 1 := measure_univ

/-- Markov kernel of the asynchronous pseudo-coupling.  At a positive equal
minority/auxiliary level it performs the explicit coupled step; at every
other state it advances only the auxiliary birth--death chain. -/
noncomputable def lvPseudoCouplingKernel
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params)) :
    Kernel (LabeledPopState × Nat) (LabeledPopState × Nat) :=
  Kernel.ofFunOfCountable fun x =>
    if hactive :
        Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
          0 < Nat.min x.1.1.1 x.1.1.2 then
      lvDominationJointMeasure v params hGamma0 hGamma1
        N hDom x.1 hactive.2
    else
      freezeLVMeasure x.1 (bdKernel N x.2)

instance lvPseudoCouplingKernel_isMarkovKernel
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params)) :
    IsMarkovKernel
      (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom) where
  isProbabilityMeasure x := by
    simp only [lvPseudoCouplingKernel, Kernel.ofFunOfCountable,
      Kernel.coe_mk]
    split
    · infer_instance
    · infer_instance

/-- At every joint state, the auxiliary marginal transition is exactly the
birth--death kernel. -/
theorem lvPseudoCouplingKernel_snd
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat) :
    (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x).snd =
      bdKernel N x.2 := by
  simp only [lvPseudoCouplingKernel, Kernel.ofFunOfCountable,
    Kernel.coe_mk]
  split_ifs with hactive
  · rw [lvDominationJointMeasure_snd]
    rw [hactive.1]
  · exact freezeLVMeasure_snd x.1 (bdKernel N x.2)

/-- At an active state, the labelled LV marginal transition is exact. -/
theorem lvPseudoCouplingKernel_fst_of_active
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat)
    (hactive :
      Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
        0 < Nat.min x.1.1.1 x.1.1.2) :
    (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x).fst =
      lvLabeledKernel v params x.1 := by
  simp only [lvPseudoCouplingKernel, Kernel.ofFunOfCountable,
    Kernel.coe_mk, dif_pos hactive]
  exact lvDominationJointMeasure_fst v params hGamma0 hGamma1
    N hDom x.1 hactive.2

/-- Away from an active equality, the labelled LV coordinate is frozen. -/
theorem lvPseudoCouplingKernel_fst_of_inactive
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat)
    (hinactive : ¬(Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
      0 < Nat.min x.1.1.1 x.1.1.2)) :
    (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x).fst =
      Measure.dirac x.1 := by
  simp only [lvPseudoCouplingKernel, Kernel.ofFunOfCountable,
    Kernel.coe_mk, dif_neg hinactive]
  exact freezeLVMeasure_fst x.1 (bdKernel N x.2)

/-- At every active equality, including equality at zero, the first marginal
is exactly the stopped labelled LV transition. -/
theorem lvPseudoCouplingKernel_fst_of_pseudoActive
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat)
    (hactive : isPseudoActive x) :
    (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x).fst =
      lvStoppedLabeledKernel v params x.1 := by
  by_cases hpos : 0 < Nat.min x.1.1.1 x.1.1.2
  · rw [lvPseudoCouplingKernel_fst_of_active v params
      hGamma0 hGamma1 N hDom x ⟨hactive, hpos⟩]
    simp only [lvStoppedLabeledKernel, Kernel.ofFunOfCountable,
      Kernel.coe_mk, if_neg (Nat.ne_of_gt hpos)]
  · have hzero : Nat.min x.1.1.1 x.1.1.2 = 0 := by omega
    rw [lvPseudoCouplingKernel_fst_of_inactive v params
      hGamma0 hGamma1 N hDom x]
    · simp only [lvStoppedLabeledKernel, Kernel.ofFunOfCountable,
        Kernel.coe_mk, if_pos hzero]
    · intro h
      exact hpos h.2

/-- A birth--death step is supported on birth, death, and hold. -/
lemma bdKernel_ae_three_transitions
    (N : BirthDeathChain) (n : Nat) :
    ∀ᵐ n' ∂bdKernel N n,
      n' = n + 1 ∨ n' = n - 1 ∨ n' = n := by
  rw [ae_iff]
  rw [bdKernel_apply]
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- The minority domination invariant is preserved by every step of the
asynchronous pseudo-coupling. -/
theorem lvPseudoCouplingKernel_ae_min_le
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat)
    (hx : Nat.min x.1.1.1 x.1.1.2 ≤ x.2) :
    ∀ᵐ y ∂lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x,
      Nat.min y.1.1.1 y.1.1.2 ≤ y.2 := by
  by_cases hactive :
      Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
        0 < Nat.min x.1.1.1 x.1.1.2
  · simpa only [lvPseudoCouplingKernel,
      Kernel.ofFunOfCountable, Kernel.coe_mk, dif_pos hactive] using
      lvDominationJointMeasure_ae_min_le v params
        hGamma0 hGamma1 N hDom x.1 hactive.2
  · simp only [lvPseudoCouplingKernel,
      Kernel.ofFunOfCountable, Kernel.coe_mk, dif_neg hactive,
      freezeLVMeasure]
    apply (MeasureTheory.ae_map_iff
      (μ := bdKernel N x.2)
      (f := fun n : Nat => (x.1, n))
      (by fun_prop)
      (Set.to_countable _).measurableSet).2
    filter_upwards [bdKernel_ae_three_transitions N x.2] with n hn
    have hlevel :
        Nat.min x.1.1.1 x.1.1.2 < x.2 ∨
          (Nat.min x.1.1.1 x.1.1.2 = 0 ∧ x.2 = 0) := by
      by_cases heq : Nat.min x.1.1.1 x.1.1.2 = x.2
      · right
        have hnpos : ¬0 < Nat.min x.1.1.1 x.1.1.2 :=
          fun hpos => hactive ⟨heq, hpos⟩
        omega
      · left
        omega
    rcases hn with rfl | rfl | rfl <;>
      rcases hlevel with hlt | hzero <;> omega

/-- At an active physical step, every bad LV reaction is paired with an
auxiliary birth. -/
theorem lvPseudoCouplingKernel_ae_bad_implies_birth
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat) :
    ∀ᵐ y ∂lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x,
      ((Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
          0 < Nat.min x.1.1.1 x.1.1.2) ∧
        y.1 ∈ dominationBadSet x.1.1) →
          y.2 = x.2 + 1 := by
  by_cases hactive :
      Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
        0 < Nat.min x.1.1.1 x.1.1.2
  · simp only [lvPseudoCouplingKernel,
      Kernel.ofFunOfCountable, Kernel.coe_mk, dif_pos hactive]
    filter_upwards [
      lvDominationJointMeasure_ae_category_rules v params
        hGamma0 hGamma1 N hDom x.1 hactive.2] with y hy
    intro hbad
    have hybirth := hy.1 hbad.2
    simpa only [hactive.1] using hybirth
  · exact Filter.Eventually.of_forall fun _ hy =>
      (hactive hy.1).elim

/-- At a strict inequality between the minority and auxiliary coordinates,
the labelled LV coordinate is frozen. -/
theorem lvPseudoCouplingKernel_ae_left_frozen
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (x : LabeledPopState × Nat)
    (hinactive : ¬isPseudoActive x) :
    ∀ᵐ y ∂lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom x,
      y.1 = x.1 := by
  have hnotpositive :
      ¬(Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
        0 < Nat.min x.1.1.1 x.1.1.2) :=
    fun h => hinactive h.1
  simp only [lvPseudoCouplingKernel,
    Kernel.ofFunOfCountable, Kernel.coe_mk, dif_neg hnotpositive,
    freezeLVMeasure]
  apply (MeasureTheory.ae_map_iff
    (μ := bdKernel N x.2)
    (f := fun n : Nat => (x.1, n))
    (by fun_prop)
    (Set.to_countable _).measurableSet).2
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Path law of the asynchronous labelled pseudo-coupling. -/
noncomputable def lvPseudoCouplingPathMeasure
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat) :
    Measure (Nat → (LabeledPopState × Nat)) :=
  homogeneousPathMeasure (Measure.dirac (z0, n0))
    (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom)

/-- Starting from a dominated state, the LV minority stays below the
auxiliary birth--death coordinate at every physical time, almost surely. -/
theorem lvPseudoCouplingPathMeasure_min_le
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (h0 : Nat.min z0.1.1 z0.1.2 ≤ n0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      ∀ t : Nat,
        Nat.min (ω t).1.1.1 (ω t).1.1.2 ≤ (ω t).2 := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  let K :=
    lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom
  let Inv : LabeledPopState × Nat → Prop := fun x =>
    Nat.min x.1.1.1 x.1.1.2 ≤ x.2
  have hstep :
      ∀ x, ∀ᵐ y ∂K x, Inv x → Inv y := by
    intro x
    by_cases hx : Inv x
    · filter_upwards [
        lvPseudoCouplingKernel_ae_min_le v params
          hGamma0 hGamma1 N hDom x hx] with y hy
      exact fun _ => hy
    · exact Filter.Eventually.of_forall fun _ hy => (hx hy).elim
  have htrans :
      ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
          N hDom z0 n0,
        ∀ t : Nat, Inv (ω t) → Inv (ω (t + 1)) := by
    simpa only [lvPseudoCouplingPathMeasure, K] using
      homogeneousPathMeasure_transition_ae K (z0, n0)
        (fun x y => Inv x → Inv y) hstep
  have hinitial :
      ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
          N hDom z0 n0,
        ω 0 = (z0, n0) := by
    rw [ae_iff]
    simpa only [lvPseudoCouplingPathMeasure, K] using
      homogeneousPathMeasure_initial_ne_null K (z0, n0)
  filter_upwards [htrans, hinitial] with ω hω hω0
  intro t
  induction t with
  | zero =>
      simpa only [hω0, Inv] using h0
  | succ t ih =>
      exact hω t ih

/-- Number of bad LV reactions performed by active pseudo-coupling steps
during the first `t` physical transitions.  Frozen waiting steps contribute
zero even though their stored reaction label is unchanged. -/
noncomputable def pseudoBadCountUpTo
    (v : LVVariant)
    (ω : Nat → (LabeledPopState × Nat)) (t : Nat) : Nat := by
  classical
  exact Finset.sum (Finset.range t) fun i =>
    if (Nat.min (ω i).1.1.1 (ω i).1.1.2 = (ω i).2 ∧
          0 < Nat.min (ω i).1.1.1 (ω i).1.1.2) ∧
        (ω (i + 1)).1 ∈ dominationBadSet (ω i).1.1
    then 1 else 0

lemma pseudoBadCountUpTo_mono
    (v : LVVariant)
    (ω : Nat → (LabeledPopState × Nat))
    {s t : Nat} (hst : s ≤ t) :
    pseudoBadCountUpTo v ω s ≤ pseudoBadCountUpTo v ω t := by
  induction t, hst using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ t _ ih =>
      calc
        pseudoBadCountUpTo v ω s ≤
            pseudoBadCountUpTo v ω t := ih
        _ ≤ pseudoBadCountUpTo v ω (t + 1) := by
          unfold pseudoBadCountUpTo
          rw [Finset.sum_range_succ]
          omega

lemma birthsUpTo_mono
    (η : Nat → Nat) {s t : Nat} (hst : s ≤ t) :
    birthsUpTo η s ≤ birthsUpTo η t := by
  induction t, hst using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ t _ ih =>
      calc
        birthsUpTo η s ≤ birthsUpTo η t := ih
        _ ≤ birthsUpTo η (t + 1) := by
          unfold birthsUpTo
          rw [Finset.sum_range_succ]
          omega

lemma birthsUpTo_eq_of_zero_from
    (η : Nat → Nat) {τ t : Nat} (hτt : τ ≤ t)
    (hzero : ∀ u, τ ≤ u → η u = 0) :
    birthsUpTo η t = birthsUpTo η τ := by
  induction t, hτt using Nat.le_induction with
  | base =>
      rfl
  | succ t hτt ih =>
      unfold birthsUpTo at ih ⊢
      rw [Finset.sum_range_succ, ih,
        hzero t hτt, hzero (t + 1) (by omega)]
      simp

/-- First active physical time no earlier than `start`, with a harmless
fallback to `start` on paths on which no such time exists. -/
noncomputable def firstPseudoActiveAfter
    (ω : Nat → (LabeledPopState × Nat)) (start : Nat) : Nat := by
  classical
  exact if h : ∃ t, start ≤ t ∧ isPseudoActive (ω t)
    then Nat.find h else start

lemma firstPseudoActiveAfter_spec
    (ω : Nat → (LabeledPopState × Nat)) (start : Nat)
    (h : ∃ t, start ≤ t ∧ isPseudoActive (ω t)) :
    start ≤ firstPseudoActiveAfter ω start ∧
      isPseudoActive (ω (firstPseudoActiveAfter ω start)) := by
  classical
  rw [firstPseudoActiveAfter, dif_pos h]
  exact Nat.find_spec h

lemma firstPseudoActiveAfter_minimal
    (ω : Nat → (LabeledPopState × Nat)) (start t : Nat)
    (h : ∃ u, start ≤ u ∧ isPseudoActive (ω u))
    (ht : start ≤ t) (hactive : isPseudoActive (ω t)) :
    firstPseudoActiveAfter ω start ≤ t := by
  classical
  rw [firstPseudoActiveAfter, dif_pos h]
  exact Nat.find_min' h ⟨ht, hactive⟩

/-- Successive active equality times of a physical pseudo-coupling path. -/
noncomputable def lvPseudoActiveTime
    (ω : Nat → (LabeledPopState × Nat)) : Nat → Nat
  | 0 => firstPseudoActiveAfter ω 0
  | k + 1 =>
      firstPseudoActiveAfter ω (lvPseudoActiveTime ω k + 1)

/-- `pseudoKthActiveAt k t ω` says that `t` is the `(k+1)`-st active
physical time of `ω`.  This bounded-prefix formulation is convenient for
the stopping-time calculation below. -/
def pseudoKthActiveAt :
    Nat → Nat → (Nat → (LabeledPopState × Nat)) → Prop
  | 0, t, ω =>
      isPseudoActive (ω t) ∧
        ∀ u, u < t → ¬isPseudoActive (ω u)
  | k + 1, t, ω =>
      isPseudoActive (ω t) ∧
        ∃ s, s < t ∧ pseudoKthActiveAt k s ω ∧
          ∀ u, s < u → u < t → ¬isPseudoActive (ω u)

lemma measurableSet_pseudoActiveAt (t : Nat) :
    MeasurableSet
      {ω : Nat → (LabeledPopState × Nat) |
        isPseudoActive (ω t)} := by
  exact (Set.to_countable
    {x : LabeledPopState × Nat | isPseudoActive x}).measurableSet.preimage
      (measurable_pi_apply t)

lemma measurableSet_pseudoKthActiveAt (k t : Nat) :
    MeasurableSet
      {ω : Nat → (LabeledPopState × Nat) |
        pseudoKthActiveAt k t ω} := by
  induction k generalizing t with
  | zero =>
      apply (measurableSet_pseudoActiveAt t).inter
      change MeasurableSet
        ({ω : Nat → (LabeledPopState × Nat) |
          ∀ u, u < t → ¬isPseudoActive (ω u)} : Set _)
      rw [show
        {ω : Nat → (LabeledPopState × Nat) |
          ∀ u, u < t → ¬isPseudoActive (ω u)} =
            ⋂ u : Nat,
              {ω : Nat → (LabeledPopState × Nat) |
                u < t → ¬isPseudoActive (ω u)} by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iInter]]
      apply MeasurableSet.iInter
      intro u
      by_cases hut : u < t
      · simp only [hut, true_implies]
        rw [show
          {ω : Nat → (LabeledPopState × Nat) |
              ¬isPseudoActive (ω u)} =
            {ω : Nat → (LabeledPopState × Nat) |
              isPseudoActive (ω u)}ᶜ by
            ext ω
            simp]
        exact (measurableSet_pseudoActiveAt u).compl
      · simp only [hut, false_implies, Set.setOf_true]
        exact MeasurableSet.univ
  | succ k ih =>
      apply (measurableSet_pseudoActiveAt t).inter
      change MeasurableSet
        ({ω : Nat → (LabeledPopState × Nat) |
          ∃ s, s < t ∧ pseudoKthActiveAt k s ω ∧
            ∀ u, s < u → u < t →
              ¬isPseudoActive (ω u)} : Set _)
      rw [show
        {ω : Nat → (LabeledPopState × Nat) |
          ∃ s, s < t ∧ pseudoKthActiveAt k s ω ∧
            ∀ u, s < u → u < t →
              ¬isPseudoActive (ω u)} =
            ⋃ s : Nat,
              {ω : Nat → (LabeledPopState × Nat) |
                s < t ∧ pseudoKthActiveAt k s ω ∧
                  ∀ u, s < u → u < t →
                    ¬isPseudoActive (ω u)} by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]]
      apply MeasurableSet.iUnion
      intro s
      by_cases hst : s < t
      · have hbetween :
            MeasurableSet
              {ω : Nat → (LabeledPopState × Nat) |
                ∀ u, s < u → u < t →
                  ¬isPseudoActive (ω u)} := by
          rw [show
            {ω : Nat → (LabeledPopState × Nat) |
              ∀ u, s < u → u < t →
                ¬isPseudoActive (ω u)} =
                ⋂ u : Nat,
                  {ω : Nat → (LabeledPopState × Nat) |
                    s < u → u < t →
                      ¬isPseudoActive (ω u)} by
              ext ω
              simp only [Set.mem_setOf_eq, Set.mem_iInter]]
          apply MeasurableSet.iInter
          intro u
          by_cases hsu : s < u
          · by_cases hut : u < t
            · simp only [hsu, hut, true_implies]
              rw [show
                {ω : Nat → (LabeledPopState × Nat) |
                    ¬isPseudoActive (ω u)} =
                  {ω : Nat → (LabeledPopState × Nat) |
                    isPseudoActive (ω u)}ᶜ by
                  ext ω
                  simp]
              exact (measurableSet_pseudoActiveAt u).compl
            · simp only [hsu, hut, true_implies, false_implies,
                Set.setOf_true]
              exact MeasurableSet.univ
          · simp only [hsu, false_implies, Set.setOf_true]
            exact MeasurableSet.univ
        simp only [hst, true_and]
        rw [show
          {ω : Nat → (LabeledPopState × Nat) |
              pseudoKthActiveAt k s ω ∧
                ∀ u, s < u → u < t → ¬isPseudoActive (ω u)} =
            {ω : Nat → (LabeledPopState × Nat) |
              pseudoKthActiveAt k s ω} ∩
            {ω : Nat → (LabeledPopState × Nat) |
              ∀ u, s < u → u < t → ¬isPseudoActive (ω u)} by
              rfl]
        exact (ih s).inter hbetween
      · simp only [hst, false_and, Set.setOf_false]
        exact MeasurableSet.empty

/-- The finite-prefix cylinder in which `t` is the `k`-th active time and
the first `k+1` labelled LV states have the prescribed values `q`. -/
def pseudoTraceCylinderAt
    (k : Nat) (q : ∀ _ : Finset.Iic k, LabeledPopState)
    (t : Nat) : Set (Nat → (LabeledPopState × Nat)) :=
  {ω | pseudoKthActiveAt k t ω ∧
    ∀ i : Finset.Iic k, ∃ u, u ≤ t ∧
      pseudoKthActiveAt i.1 u ω ∧ (ω u).1 = q i}

lemma measurableSet_pseudoTraceCylinderAt
    (k : Nat) (q : ∀ _ : Finset.Iic k, LabeledPopState)
    (t : Nat) :
    MeasurableSet (pseudoTraceCylinderAt k q t) := by
  apply (measurableSet_pseudoKthActiveAt k t).inter
  change MeasurableSet
    ({ω : Nat → (LabeledPopState × Nat) |
      ∀ i : Finset.Iic k, ∃ u, u ≤ t ∧
        pseudoKthActiveAt i.1 u ω ∧ (ω u).1 = q i} : Set _)
  rw [show
    {ω : Nat → (LabeledPopState × Nat) |
      ∀ i : Finset.Iic k, ∃ u, u ≤ t ∧
        pseudoKthActiveAt i.1 u ω ∧ (ω u).1 = q i} =
        ⋂ i : Finset.Iic k,
          ⋃ u : Nat,
            {ω : Nat → (LabeledPopState × Nat) |
              u ≤ t ∧ pseudoKthActiveAt i.1 u ω ∧
                (ω u).1 = q i} by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter,
        Set.mem_iUnion]]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iUnion
  intro u
  by_cases hut : u ≤ t
  · have heq :
        MeasurableSet
          {ω : Nat → (LabeledPopState × Nat) |
            (ω u).1 = q i} := by
        exact (measurableSet_singleton (q i)).preimage
          (measurable_fst.comp (measurable_pi_apply u))
    simp only [hut, true_and]
    rw [show
      {ω : Nat → (LabeledPopState × Nat) |
          pseudoKthActiveAt i.1 u ω ∧ (ω u).1 = q i} =
        {ω : Nat → (LabeledPopState × Nat) |
          pseudoKthActiveAt i.1 u ω} ∩
        {ω : Nat → (LabeledPopState × Nat) |
          (ω u).1 = q i} by
          rfl]
    exact (measurableSet_pseudoKthActiveAt i.1 u).inter heq
  · simp only [hut, false_and, Set.setOf_false]
    exact MeasurableSet.empty

lemma pseudoKthActiveAt_unique
    {k s t : Nat} {ω : Nat → (LabeledPopState × Nat)}
    (hs : pseudoKthActiveAt k s ω)
    (ht : pseudoKthActiveAt k t ω) :
    s = t := by
  induction k generalizing s t with
  | zero =>
      rcases hs with ⟨hsa, hsmin⟩
      rcases ht with ⟨hta, htmin⟩
      rcases lt_trichotomy s t with hlt | heq | hgt
      · exact (htmin s hlt hsa).elim
      · exact heq
      · exact (hsmin t hgt hta).elim
  | succ k ih =>
      rcases hs with ⟨hsa, s0, hs0, hks0, hsbetween⟩
      rcases ht with ⟨hta, t0, ht0, hkt0, htbetween⟩
      have hpred : s0 = t0 := ih hks0 hkt0
      subst t0
      rcases lt_trichotomy s t with hlt | heq | hgt
      · exact (htbetween s hs0 hlt hsa).elim
      · exact heq
      · exact (hsbetween t ht0 hgt hta).elim

lemma pseudoKthActiveAt_active
    {k t : Nat} {ω : Nat → (LabeledPopState × Nat)}
    (h : pseudoKthActiveAt k t ω) :
    isPseudoActive (ω t) := by
  cases k <;> exact h.1

lemma pseudoKthActiveAt_time_le
    {i k s t : Nat} {ω : Nat → (LabeledPopState × Nat)}
    (hik : i ≤ k)
    (his : pseudoKthActiveAt i s ω)
    (hkt : pseudoKthActiveAt k t ω) :
    s ≤ t := by
  induction k generalizing i s t with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact (pseudoKthActiveAt_unique his hkt).le
  | succ k ih =>
      by_cases hi : i = k + 1
      · subst i
        exact (pseudoKthActiveAt_unique his hkt).le
      · have hik' : i ≤ k := by omega
        rcases hkt with
          ⟨_, r, hrt, hkr, _⟩
        exact (ih hik' his hkr).trans (Nat.le_of_lt hrt)

lemma pseudoKthActiveAt_index_le_time
    {k t : Nat} {ω : Nat → (LabeledPopState × Nat)}
    (hkt : pseudoKthActiveAt k t ω) :
    k ≤ t := by
  induction k generalizing t with
  | zero =>
      exact Nat.zero_le t
  | succ k ih =>
      rcases hkt with ⟨_, s, hst, hks, _⟩
      have hle := ih hks
      omega

lemma pseudoTraceCylinderAt_pairwise
    (k : Nat) (q : ∀ _ : Finset.Iic k, LabeledPopState) :
    Pairwise fun s t =>
      Disjoint (pseudoTraceCylinderAt k q s)
        (pseudoTraceCylinderAt k q t) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro ω hωs hωt
  exact hst (pseudoKthActiveAt_unique hωs.1 hωt.1)

/-- Complete a finite pseudo-coupling history by a fixed dummy state.  Only
the coordinates through `t` are used in the stopping-time calculation. -/
def extendPseudoHistory
    (t : Nat)
    (h : ∀ _ : Finset.Iic t, LabeledPopState × Nat) :
    Nat → (LabeledPopState × Nat) :=
  fun u =>
    if hu : u ≤ t then h ⟨u, Finset.mem_Iic.mpr hu⟩
    else (((0, 0), .idle), 0)

lemma extendPseudoHistory_frestrictLe
    (ω : Nat → (LabeledPopState × Nat))
    (t u : Nat) (hu : u ≤ t) :
    extendPseudoHistory t (frestrictLe t ω) u = ω u := by
  simp only [extendPseudoHistory, hu, ↓reduceDIte,
    frestrictLe_apply]

lemma pseudoKthActiveAt_congr_up_to
    {ω ω' : Nat → (LabeledPopState × Nat)}
    {k s t : Nat} (hst : s ≤ t)
    (hEq : ∀ u, u ≤ t → ω u = ω' u) :
    pseudoKthActiveAt k s ω ↔
      pseudoKthActiveAt k s ω' := by
  induction k generalizing s with
  | zero =>
      constructor
      · rintro ⟨hactive, hminimal⟩
        refine ⟨?_, ?_⟩
        · simpa only [hEq s hst] using hactive
        · intro u hus
          simpa only [hEq u (by omega)] using hminimal u hus
      · rintro ⟨hactive, hminimal⟩
        refine ⟨?_, ?_⟩
        · simpa only [hEq s hst] using hactive
        · intro u hus
          simpa only [hEq u (by omega)] using hminimal u hus
  | succ k ih =>
      constructor
      · rintro ⟨hactive, r, hrs, hkr, hbetween⟩
        refine ⟨?_, r, hrs, ?_, ?_⟩
        · simpa only [hEq s hst] using hactive
        · exact (ih (Nat.le_trans (Nat.le_of_lt hrs) hst)).1 hkr
        · intro u hru hus
          simpa only [hEq u (by omega)] using
            hbetween u hru hus
      · rintro ⟨hactive, r, hrs, hkr, hbetween⟩
        refine ⟨?_, r, hrs, ?_, ?_⟩
        · simpa only [hEq s hst] using hactive
        · exact (ih (Nat.le_trans (Nat.le_of_lt hrs) hst)).2 hkr
        · intro u hru hus
          simpa only [hEq u (by omega)] using
            hbetween u hru hus

lemma pseudoTraceCylinderAt_congr_up_to
    {ω ω' : Nat → (LabeledPopState × Nat)}
    {k t : Nat}
    {q : ∀ _ : Finset.Iic k, LabeledPopState}
    (hEq : ∀ u, u ≤ t → ω u = ω' u) :
    ω ∈ pseudoTraceCylinderAt k q t ↔
      ω' ∈ pseudoTraceCylinderAt k q t := by
  constructor
  · rintro ⟨hkt, hvalues⟩
    refine ⟨(pseudoKthActiveAt_congr_up_to le_rfl hEq).1 hkt,
      fun i => ?_⟩
    obtain ⟨u, hut, hki, hvalue⟩ := hvalues i
    exact ⟨u, hut,
      (pseudoKthActiveAt_congr_up_to hut hEq).1 hki,
      by simpa only [hEq u hut] using hvalue⟩
  · rintro ⟨hkt, hvalues⟩
    refine ⟨(pseudoKthActiveAt_congr_up_to le_rfl hEq).2 hkt,
      fun i => ?_⟩
    obtain ⟨u, hut, hki, hvalue⟩ := hvalues i
    exact ⟨u, hut,
      (pseudoKthActiveAt_congr_up_to hut hEq).2 hki,
      by simpa only [hEq u hut] using hvalue⟩

lemma pseudoTraceCylinderAt_extend_frestrictLe
    (ω : Nat → (LabeledPopState × Nat))
    (k : Nat) (q : ∀ _ : Finset.Iic k, LabeledPopState)
    (t : Nat) :
    extendPseudoHistory t (frestrictLe t ω) ∈
        pseudoTraceCylinderAt k q t ↔
      ω ∈ pseudoTraceCylinderAt k q t := by
  exact pseudoTraceCylinderAt_congr_up_to fun u hu =>
    extendPseudoHistory_frestrictLe ω t u hu

/-- On one stopping-time fiber, the next labelled LV state is distributed
by the stopped LV kernel.  This is the finite-history Markov calculation
needed for the embedded-chain proof; no conditional-independence axiom is
used. -/
theorem lvPseudoCouplingPathMeasure_traceCylinderAt_next
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (k t : Nat)
    (q : ∀ _ : Finset.Iic k, LabeledPopState)
    (b : LabeledPopState) :
    let P := lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0
    let A := pseudoTraceCylinderAt k q t
    P (A ∩ {ω | (ω (t + 1)).1 = b}) =
      lvStoppedLabeledKernel v params
          (q ⟨k, Finset.mem_Iic.mpr le_rfl⟩) {b} *
        P A := by
  classical
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  let K :=
    lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom
  let P := lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
    N hDom z0 n0
  let A := pseudoTraceCylinderAt k q t
  let qlast := q ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  let c := lvStoppedLabeledKernel v params qlast {b}
  let g : (∀ _ : Finset.Iic t,
      LabeledPopState × Nat) → ℝ≥0∞ :=
    fun h => if extendPseudoHistory t h ∈ A then 1 else 0
  let φ : (LabeledPopState × Nat) → ℝ≥0∞ :=
    fun y => if y.1 = b then 1 else 0
  have hg : Measurable g := measurable_of_countable g
  have hφ : Measurable φ := measurable_of_countable φ
  have hAmeas : MeasurableSet A :=
    measurableSet_pseudoTraceCylinderAt k q t
  have hnextmeas :
      MeasurableSet
        {ω : Nat → (LabeledPopState × Nat) |
          (ω (t + 1)).1 = b} :=
    (measurableSet_singleton b).preimage
      (measurable_fst.comp (measurable_pi_apply (t + 1)))
  have hpoint :
      ∀ ω : Nat → (LabeledPopState × Nat),
        (A ∩ {ω | (ω (t + 1)).1 = b}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω =
          g (frestrictLe t ω) * φ (ω (t + 1)) := by
    intro ω
    have hpref :=
      pseudoTraceCylinderAt_extend_frestrictLe ω k q t
    by_cases hAω : ω ∈ A
    · have hext :
          extendPseudoHistory t (frestrictLe t ω) ∈ A :=
        hpref.2 hAω
      by_cases hnext : (ω (t + 1)).1 = b
      · simp [Set.indicator, g, φ, hAω, hext, hnext]
      · simp [Set.indicator, g, φ, hAω, hext, hnext]
    · have hext :
          extendPseudoHistory t (frestrictLe t ω) ∉ A :=
        fun h => hAω (hpref.1 h)
      simp [Set.indicator, g, φ, hAω, hext]
  have hintegrand :
      ∀ h : ∀ _ : Finset.Iic t,
          LabeledPopState × Nat,
        g h * ∫⁻ y, φ y ∂K (finiteHistoryLast t h) =
          c * g h := by
    intro h
    by_cases hmem : extendPseudoHistory t h ∈ A
    · have hkt : pseudoKthActiveAt k t
          (extendPseudoHistory t h) := hmem.1
      have hactive :
          isPseudoActive (finiteHistoryLast t h) := by
        have := pseudoKthActiveAt_active hkt
        simpa only [finiteHistoryLast, extendPseudoHistory,
          le_rfl, ↓reduceDIte] using this
      obtain ⟨u, hut, hku, huvalue⟩ :=
        hmem.2 ⟨k, Finset.mem_Iic.mpr le_rfl⟩
      have hutEq : u = t :=
        pseudoKthActiveAt_unique hku hkt
      subst u
      have hlastValue :
          (finiteHistoryLast t h).1 = qlast := by
        simpa only [finiteHistoryLast, extendPseudoHistory,
          le_rfl, ↓reduceDIte, qlast] using huvalue
      have hkernel :
          (K (finiteHistoryLast t h)).fst =
            lvStoppedLabeledKernel v params
              (finiteHistoryLast t h).1 := by
        exact lvPseudoCouplingKernel_fst_of_pseudoActive
          v params hGamma0 hGamma1 N hDom
            (finiteHistoryLast t h) hactive
      have hφint :
          ∫⁻ y, φ y ∂K (finiteHistoryLast t h) = c := by
        calc
          ∫⁻ y, φ y ∂K (finiteHistoryLast t h) =
              K (finiteHistoryLast t h)
                (Prod.fst ⁻¹' ({b} : Set LabeledPopState)) := by
            rw [← lintegral_indicator_one
              ((measurableSet_singleton b).preimage measurable_fst)]
            congr 1
            funext y
            simp [φ, Set.indicator]
          _ = (K (finiteHistoryLast t h)).fst {b} := by
            rw [Measure.fst_apply (measurableSet_singleton b)]
          _ = lvStoppedLabeledKernel v params
                (finiteHistoryLast t h).1 {b} := by
            rw [hkernel]
          _ = c := by
            rw [hlastValue]
      simp only [g, hmem, ↓reduceIte, one_mul, mul_one]
      exact hφint
    · simp only [g, hmem, ↓reduceIte, mul_zero]
      exact zero_mul _
  have hmapIntegral :
      ∫⁻ h, g h ∂P.map (frestrictLe t) =
        ∫⁻ ω, g (frestrictLe t ω) ∂P :=
    lintegral_map hg (measurable_frestrictLe t)
  have hgIndicator :
      ∀ ω : Nat → (LabeledPopState × Nat),
        g (frestrictLe t ω) =
          A.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    have hpref :=
      pseudoTraceCylinderAt_extend_frestrictLe ω k q t
    by_cases hω : ω ∈ A
    · have hext :
          extendPseudoHistory t (frestrictLe t ω) ∈ A :=
        hpref.2 hω
      simp [g, Set.indicator, hω, hext]
    · have hext :
          extendPseudoHistory t (frestrictLe t ω) ∉ A :=
        fun h => hω (hpref.1 h)
      simp [g, Set.indicator, hω, hext]
  change P (A ∩ {ω | (ω (t + 1)).1 = b}) = c * P A
  calc
    P (A ∩ {ω | (ω (t + 1)).1 = b}) =
        ∫⁻ ω,
          (A ∩ {ω | (ω (t + 1)).1 = b}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
      exact (lintegral_indicator_one
        (μ := P) (hAmeas.inter hnextmeas)).symm
    _ = ∫⁻ ω, g (frestrictLe t ω) * φ (ω (t + 1))
          ∂P := by
      apply lintegral_congr
      exact hpoint
    _ = ∫⁻ h, g h * ∫⁻ y, φ y
          ∂K (finiteHistoryLast t h)
          ∂P.map (frestrictLe t) := by
      simpa only [P, lvPseudoCouplingPathMeasure, K] using
        homogeneousPathMeasure_history_next_lintegral
          K (z0, n0) t g φ hg hφ
    _ = ∫⁻ h, c * g h ∂P.map (frestrictLe t) := by
      apply lintegral_congr
      exact hintegrand
    _ = c * ∫⁻ h, g h ∂P.map (frestrictLe t) := by
      rw [lintegral_const_mul c hg]
    _ = c * ∫⁻ ω, g (frestrictLe t ω) ∂P := by
      rw [hmapIntegral]
    _ = c * ∫⁻ ω, A.indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
      congr 1
      apply lintegral_congr
      exact hgIndicator
    _ = c * P A := by
      congr 1
      exact lintegral_indicator_one (μ := P) hAmeas

/-- Infinitely many active physical times give a unique time of every active
ordinal. -/
lemma pseudoKthActiveAt_exists
    (ω : Nat → (LabeledPopState × Nat))
    (hinfinite : ∀ start, ∃ t, start ≤ t ∧
      isPseudoActive (ω t)) :
    ∀ k, ∃ t, pseudoKthActiveAt k t ω := by
  intro k
  induction k with
  | zero =>
      let t := firstPseudoActiveAfter ω 0
      have hspec :=
        firstPseudoActiveAfter_spec ω 0 (hinfinite 0)
      refine ⟨t, hspec.2, ?_⟩
      intro u hut hactive
      have hminimal :=
        firstPseudoActiveAfter_minimal ω 0 u
          (hinfinite 0) (Nat.zero_le u) hactive
      exact (Nat.not_lt_of_ge hminimal hut)
  | succ k ih =>
      obtain ⟨s, hks⟩ := ih
      let t := firstPseudoActiveAfter ω (s + 1)
      have hspec :=
        firstPseudoActiveAfter_spec ω (s + 1)
          (hinfinite (s + 1))
      refine ⟨t, hspec.2, s, ?_, hks, ?_⟩
      · exact lt_of_lt_of_le (Nat.lt_succ_self s) hspec.1
      · intro u hsu hut hactive
        have hminimal :=
          firstPseudoActiveAfter_minimal ω (s + 1) u
            (hinfinite (s + 1)) (by omega) hactive
        exact (Nat.not_lt_of_ge hminimal hut)

/-- If the labelled coordinate freezes at non-active times, it has the same
value immediately after one active time and at the next active time. -/
lemma pseudoLeft_frozen_between_active
    (ω : Nat → (LabeledPopState × Nat))
    (hfreeze : ∀ r, ¬isPseudoActive (ω r) →
      (ω (r + 1)).1 = (ω r).1)
    {s t : Nat} (hst : s < t)
    (hbetween : ∀ r, s < r → r < t →
      ¬isPseudoActive (ω r)) :
    (ω t).1 = (ω (s + 1)).1 := by
  have hstart : s + 1 ≤ t := by omega
  induction t, hstart using Nat.le_induction with
  | base => rfl
  | succ t hst' ih =>
      have hstlt : s < t := by omega
      rw [hfreeze t (hbetween t hstlt (by omega)),
        ih hstlt (fun r hsr hrt =>
          hbetween r hsr (by omega))]

/-- Successive trace cylinders are related by the immediate transition
following the current active time. -/
lemma pseudoTraceCylinder_succ_iff
    (ω : Nat → (LabeledPopState × Nat))
    (hinfinite : ∀ start, ∃ t, start ≤ t ∧
      isPseudoActive (ω t))
    (hfreeze : ∀ r, ¬isPseudoActive (ω r) →
      (ω (r + 1)).1 = (ω r).1)
    (k : Nat)
    (qnext : ∀ _ : Finset.Iic (k + 1), LabeledPopState) :
    let q : ∀ _ : Finset.Iic k, LabeledPopState :=
      fun i => qnext
        ⟨i.1, Finset.mem_Iic.mpr
          (Nat.le_trans (Finset.mem_Iic.mp i.2)
            (Nat.le_succ k))⟩
    let b := qnext
      ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
    ω ∈ ⋃ t, pseudoTraceCylinderAt (k + 1) qnext t ↔
      ω ∈ ⋃ t,
        pseudoTraceCylinderAt k q t ∩
          {ω | (ω (t + 1)).1 = b} := by
  let q : ∀ _ : Finset.Iic k, LabeledPopState :=
    fun i => qnext
      ⟨i.1, Finset.mem_Iic.mpr
        (Nat.le_trans (Finset.mem_Iic.mp i.2)
          (Nat.le_succ k))⟩
  let b := qnext
    ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
  constructor
  · intro hleft
    rw [Set.mem_iUnion] at hleft
    obtain ⟨u, huC⟩ := hleft
    rcases huC.1 with
      ⟨huactive, t, htu, hkt, hbetween⟩
    have hCt : ω ∈ pseudoTraceCylinderAt k q t := by
      refine ⟨hkt, fun i => ?_⟩
      let i' : Finset.Iic (k + 1) :=
        ⟨i.1, Finset.mem_Iic.mpr
          (Nat.le_trans (Finset.mem_Iic.mp i.2)
            (Nat.le_succ k))⟩
      obtain ⟨r, hru, hri, hrvalue⟩ := huC.2 i'
      have hrt : r ≤ t :=
        pseudoKthActiveAt_time_le
          (Finset.mem_Iic.mp i.2) hri hkt
      exact ⟨r, hrt, hri, by simpa only [q, i'] using hrvalue⟩
    have huvalue : (ω u).1 = b := by
      obtain ⟨r, hru, hri, hrvalue⟩ :=
        huC.2 ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
      have hre : r = u :=
        pseudoKthActiveAt_unique hri huC.1
      subst r
      simpa only [b] using hrvalue
    have hfrozen :
        (ω u).1 = (ω (t + 1)).1 :=
      pseudoLeft_frozen_between_active ω hfreeze htu
        hbetween
    rw [Set.mem_iUnion]
    refine ⟨t, hCt, ?_⟩
    exact hfrozen.symm.trans huvalue
  · intro hright
    rw [Set.mem_iUnion] at hright
    obtain ⟨t, hCt, hnext⟩ := hright
    let u := firstPseudoActiveAfter ω (t + 1)
    have huspec :=
      firstPseudoActiveAfter_spec ω (t + 1)
        (hinfinite (t + 1))
    have htu : t < u := by
      exact lt_of_lt_of_le (Nat.lt_succ_self t) huspec.1
    have hbetween : ∀ r, t < r → r < u →
        ¬isPseudoActive (ω r) := by
      intro r htr hru hactive
      have hminimal :=
        firstPseudoActiveAfter_minimal ω (t + 1) r
          (hinfinite (t + 1)) (by omega) hactive
      exact (Nat.not_lt_of_ge hminimal hru)
    have hk1u : pseudoKthActiveAt (k + 1) u ω :=
      ⟨huspec.2, t, htu, hCt.1, hbetween⟩
    have hfrozen :
        (ω u).1 = (ω (t + 1)).1 :=
      pseudoLeft_frozen_between_active ω hfreeze htu
        hbetween
    rw [Set.mem_iUnion]
    refine ⟨u, hk1u, fun i => ?_⟩
    by_cases hik : i.1 ≤ k
    · let j : Finset.Iic k :=
        ⟨i.1, Finset.mem_Iic.mpr hik⟩
      obtain ⟨r, hrt, hri, hrvalue⟩ := hCt.2 j
      exact ⟨r, Nat.le_trans hrt (Nat.le_of_lt htu),
        hri, by simpa only [q, j] using hrvalue⟩
    · have hi : i.1 = k + 1 := by
        have := Finset.mem_Iic.mp i.2
        omega
      have hieq :
          i = ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
        Subtype.ext hi
      rw [hieq]
      exact ⟨u, le_rfl, hk1u,
        by simpa only [b] using hfrozen.trans hnext⟩

lemma pseudoLeft_eq_initial_before_first
    (ω : Nat → (LabeledPopState × Nat))
    (hfreeze : ∀ r, ¬isPseudoActive (ω r) →
      (ω (r + 1)).1 = (ω r).1)
    (t : Nat)
    (hminimal : ∀ r, r < t →
      ¬isPseudoActive (ω r)) :
    (ω t).1 = (ω 0).1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [hfreeze t (hminimal t (Nat.lt_succ_self t))]
      exact ih fun r hrt =>
        hminimal r (Nat.lt_trans hrt (Nat.lt_succ_self t))

/-- Cylinder event for a prescribed finite prefix of the active embedded
labelled LV chain. -/
def pseudoTraceCylinder
    (k : Nat) (q : ∀ _ : Finset.Iic k, LabeledPopState) :
    Set (Nat → (LabeledPopState × Nat)) :=
  ⋃ t, pseudoTraceCylinderAt k q t

lemma measurableSet_pseudoTraceCylinder
    (k : Nat) (q : ∀ _ : Finset.Iic k, LabeledPopState) :
    MeasurableSet (pseudoTraceCylinder k q) :=
  MeasurableSet.iUnion fun t =>
    measurableSet_pseudoTraceCylinderAt k q t

lemma pseudoTraceCylinder_zero_iff
    (ω : Nat → (LabeledPopState × Nat))
    (hinfinite : ∀ start, ∃ t, start ≤ t ∧
      isPseudoActive (ω t))
    (hfreeze : ∀ r, ¬isPseudoActive (ω r) →
      (ω (r + 1)).1 = (ω r).1)
    (q : ∀ _ : Finset.Iic 0, LabeledPopState) :
    ω ∈ pseudoTraceCylinder 0 q ↔
      q ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = (ω 0).1 := by
  constructor
  · intro h
    rw [pseudoTraceCylinder, Set.mem_iUnion] at h
    obtain ⟨t, hCt⟩ := h
    obtain ⟨r, hrt, hkr, hrvalue⟩ :=
      hCt.2 ⟨0, Finset.mem_Iic.mpr le_rfl⟩
    have hre : r = t :=
      pseudoKthActiveAt_unique hkr hCt.1
    subst r
    have hfirst :
        (ω t).1 = (ω 0).1 :=
      pseudoLeft_eq_initial_before_first
        ω hfreeze t hCt.1.2
    exact hrvalue.symm.trans hfirst
  · intro hq
    obtain ⟨t, hkt⟩ :=
      pseudoKthActiveAt_exists ω hinfinite 0
    rw [pseudoTraceCylinder, Set.mem_iUnion]
    refine ⟨t, hkt, fun i => ?_⟩
    have hi : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
      apply Subtype.ext
      exact Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
    rw [hi]
    refine ⟨t, le_rfl, hkt, ?_⟩
    have hfirst :
        (ω t).1 = (ω 0).1 :=
      pseudoLeft_eq_initial_before_first
        ω hfreeze t hkt.2
    exact hfirst.trans hq.symm

/-- A total predicate selecting the `k`-th active time, with time zero as a
fallback only on paths having fewer than `k+1` active times. -/
def pseudoOrdinalPredicate
    (k : Nat) (ω : Nat → (LabeledPopState × Nat))
    (t : Nat) : Prop :=
  pseudoKthActiveAt k t ω ∨
    ((∀ u, ¬pseudoKthActiveAt k u ω) ∧ t = 0)

lemma pseudoOrdinalPredicate_exists
    (k : Nat) (ω : Nat → (LabeledPopState × Nat)) :
    ∃ t, pseudoOrdinalPredicate k ω t := by
  classical
  by_cases h : ∃ t, pseudoKthActiveAt k t ω
  · obtain ⟨t, ht⟩ := h
    exact ⟨t, Or.inl ht⟩
  · push_neg at h
    exact ⟨0, Or.inr ⟨h, rfl⟩⟩

/-- Physical time of the `k`-th active update, with the fallback specified
by `pseudoOrdinalPredicate`. -/
noncomputable def pseudoActiveOrdinalTime
    (k : Nat) (ω : Nat → (LabeledPopState × Nat)) : Nat := by
  classical
  exact Nat.find (pseudoOrdinalPredicate_exists k ω)

lemma measurableSet_pseudoOrdinalPredicate
    (k t : Nat) :
    MeasurableSet
      {ω : Nat → (LabeledPopState × Nat) |
        pseudoOrdinalPredicate k ω t} := by
  let E : Set (Nat → (LabeledPopState × Nat)) :=
    ⋃ u, {ω | pseudoKthActiveAt k u ω}
  have hE : MeasurableSet E :=
    MeasurableSet.iUnion fun u =>
      measurableSet_pseudoKthActiveAt k u
  have hnone :
      MeasurableSet
        {ω : Nat → (LabeledPopState × Nat) |
          ∀ u, ¬pseudoKthActiveAt k u ω} := by
    rw [show
      {ω : Nat → (LabeledPopState × Nat) |
        ∀ u, ¬pseudoKthActiveAt k u ω} = Eᶜ by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
        Set.mem_iUnion, E, not_exists]]
    exact hE.compl
  by_cases ht : t = 0
  · subst t
    simp only [pseudoOrdinalPredicate, and_true]
    rw [show
      {ω : Nat → (LabeledPopState × Nat) |
          pseudoKthActiveAt k 0 ω ∨
            ∀ u, ¬pseudoKthActiveAt k u ω} =
        {ω : Nat → (LabeledPopState × Nat) |
          pseudoKthActiveAt k 0 ω} ∪
        {ω : Nat → (LabeledPopState × Nat) |
          ∀ u, ¬pseudoKthActiveAt k u ω} by
          rfl]
    exact (measurableSet_pseudoKthActiveAt k 0).union hnone
  · simpa only [pseudoOrdinalPredicate, ht, and_false, or_false] using
      measurableSet_pseudoKthActiveAt k t

lemma measurable_pseudoActiveOrdinalTime (k : Nat) :
    Measurable (pseudoActiveOrdinalTime k) := by
  classical
  exact measurable_find
    (pseudoOrdinalPredicate_exists k)
    (measurableSet_pseudoOrdinalPredicate k)

lemma pseudoActiveOrdinalTime_isKth
    {k : Nat} {ω : Nat → (LabeledPopState × Nat)}
    (h : ∃ t, pseudoKthActiveAt k t ω) :
    pseudoKthActiveAt k (pseudoActiveOrdinalTime k ω) ω := by
  classical
  have hspec :=
    Nat.find_spec (pseudoOrdinalPredicate_exists k ω)
  have hspec' :
      pseudoOrdinalPredicate k ω
        (pseudoActiveOrdinalTime k ω) := by
    simpa only [pseudoActiveOrdinalTime] using hspec
  rcases hspec' with hspec' | ⟨hnone, _⟩
  · exact hspec'
  · obtain ⟨t, ht⟩ := h
    exact (hnone t ht).elim

/-- The labelled LV path observed only at active equality times. -/
noncomputable def pseudoEmbeddedLabeledPath
    (ω : Nat → (LabeledPopState × Nat)) :
    Nat → LabeledPopState :=
  fun k => (ω (pseudoActiveOrdinalTime k ω)).1

lemma measurable_pseudoEmbeddedLabeledPath :
    Measurable pseudoEmbeddedLabeledPath := by
  apply measurable_pi_lambda
  intro k
  let eval :
      (Nat → (LabeledPopState × Nat)) × Nat →
        LabeledPopState :=
    fun p => (p.1 p.2).1
  have heval : Measurable eval :=
    measurable_from_prod_countable_left fun t =>
      measurable_fst.comp (measurable_pi_apply t)
  exact heval.comp
    (Measurable.prodMk measurable_id
      (measurable_pseudoActiveOrdinalTime k))

lemma pseudoEmbeddedLabeledPath_prefix_iff
    (ω : Nat → (LabeledPopState × Nat))
    (hinfinite : ∀ start, ∃ t, start ≤ t ∧
      isPseudoActive (ω t))
    (k : Nat)
    (q : ∀ _ : Finset.Iic k, LabeledPopState) :
    frestrictLe k (pseudoEmbeddedLabeledPath ω) = q ↔
      ω ∈ pseudoTraceCylinder k q := by
  have hexists : ∀ i, ∃ t, pseudoKthActiveAt i t ω :=
    pseudoKthActiveAt_exists ω hinfinite
  constructor
  · intro hprefix
    let t := pseudoActiveOrdinalTime k ω
    have hkt : pseudoKthActiveAt k t ω :=
      pseudoActiveOrdinalTime_isKth (hexists k)
    rw [pseudoTraceCylinder, Set.mem_iUnion]
    refine ⟨t, hkt, fun i => ?_⟩
    let u := pseudoActiveOrdinalTime i.1 ω
    have hiu : pseudoKthActiveAt i.1 u ω :=
      pseudoActiveOrdinalTime_isKth (hexists i.1)
    have hut : u ≤ t :=
      pseudoKthActiveAt_time_le
        (Finset.mem_Iic.mp i.2) hiu hkt
    refine ⟨u, hut, hiu, ?_⟩
    have := congrFun hprefix i
    simpa only [frestrictLe_apply,
      pseudoEmbeddedLabeledPath, u] using this
  · intro hC
    rw [pseudoTraceCylinder, Set.mem_iUnion] at hC
    obtain ⟨t, hCt⟩ := hC
    funext i
    obtain ⟨u, hut, hiu, huvalue⟩ := hCt.2 i
    have hiOrdinal :
        pseudoActiveOrdinalTime i.1 ω = u :=
      pseudoKthActiveAt_unique
        (pseudoActiveOrdinalTime_isKth (hexists i.1)) hiu
    simpa only [frestrictLe_apply,
      pseudoEmbeddedLabeledPath, hiOrdinal] using huvalue

/-- The pathwise hypotheses already proved for the pseudo-coupling imply that
every successive active equality time exists and that the active times are
strictly increasing. -/
lemma lvPseudoActiveTime_spec
    (ω : Nat → (LabeledPopState × Nat))
    (hdom : ∀ t,
      Nat.min (ω t).1.1.1 (ω t).1.1.2 ≤ (ω t).2)
    (hextinct : ∀ start, ∃ T, start ≤ T ∧ (ω T).2 = 0) :
    (∀ k, isPseudoActive (ω (lvPseudoActiveTime ω k))) ∧
      StrictMono (lvPseudoActiveTime ω) := by
  have hexists : ∀ start,
      ∃ t, start ≤ t ∧ isPseudoActive (ω t) := by
    intro start
    obtain ⟨T, hT, hzero⟩ := hextinct start
    refine ⟨T, hT, ?_⟩
    unfold isPseudoActive
    have := hdom T
    omega
  have hactive : ∀ k,
      isPseudoActive (ω (lvPseudoActiveTime ω k)) := by
    intro k
    cases k with
    | zero =>
        exact (firstPseudoActiveAfter_spec ω 0
          (hexists 0)).2
    | succ k =>
        exact (firstPseudoActiveAfter_spec ω
          (lvPseudoActiveTime ω k + 1)
          (hexists (lvPseudoActiveTime ω k + 1))).2
  refine ⟨hactive, strictMono_nat_of_lt_succ fun k => ?_⟩
  exact (firstPseudoActiveAfter_spec ω
    (lvPseudoActiveTime ω k + 1)
    (hexists (lvPseudoActiveTime ω k + 1))).1

/-- Between the step immediately following one active equality and the next
active equality, the labelled LV coordinate is constant. -/
lemma lvPseudoActiveTime_left_frozen
    (ω : Nat → (LabeledPopState × Nat))
    (hdom : ∀ t,
      Nat.min (ω t).1.1.1 (ω t).1.1.2 ≤ (ω t).2)
    (hextinct : ∀ start, ∃ T, start ≤ T ∧ (ω T).2 = 0)
    (hfreeze : ∀ t, ¬isPseudoActive (ω t) →
      (ω (t + 1)).1 = (ω t).1)
    (k : Nat) :
    (ω (lvPseudoActiveTime ω (k + 1))).1 =
      (ω (lvPseudoActiveTime ω k + 1)).1 := by
  let start := lvPseudoActiveTime ω k + 1
  let finish := lvPseudoActiveTime ω (k + 1)
  have hexists : ∃ t, start ≤ t ∧ isPseudoActive (ω t) := by
    obtain ⟨T, hT, hzero⟩ := hextinct start
    refine ⟨T, hT, ?_⟩
    unfold isPseudoActive
    have := hdom T
    omega
  have hstartfinish : start ≤ finish := by
    simpa only [start, finish, lvPseudoActiveTime] using
      (firstPseudoActiveAfter_spec ω start hexists).1
  suffices hconst : ∀ t, start ≤ t → t ≤ finish →
      (ω t).1 = (ω start).1 by
    exact hconst finish hstartfinish le_rfl
  intro t htstart htfinish
  induction t, htstart using Nat.le_induction with
  | base => rfl
  | succ t htstart ih =>
      by_cases htfinish' : t + 1 ≤ finish
      · have htlt : t < finish := by omega
        have hnotactive : ¬isPseudoActive (ω t) := by
          intro hactive
          have hminimal :
              finish ≤ t := by
            simpa only [finish, lvPseudoActiveTime] using
              firstPseudoActiveAfter_minimal ω start t
                hexists htstart hactive
          omega
        rw [hfreeze t hnotactive, ih (by omega)]
      · omega

/-- On almost every pseudo-coupling path, the number of active bad LV
reactions is at most the number of auxiliary births, at every horizon. -/
theorem lvPseudoCouplingPathMeasure_bad_le_births
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      ∀ t : Nat,
        pseudoBadCountUpTo v ω t ≤
          birthsUpTo (fun i => (ω i).2) t := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  let K :=
    lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom
  have hsteps :
      ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
          N hDom z0 n0,
        ∀ i : Nat,
          (((Nat.min (ω i).1.1.1 (ω i).1.1.2 = (ω i).2 ∧
              0 < Nat.min (ω i).1.1.1 (ω i).1.1.2) ∧
            (ω (i + 1)).1 ∈ dominationBadSet (ω i).1.1) →
              (ω (i + 1)).2 = (ω i).2 + 1) := by
    simpa only [lvPseudoCouplingPathMeasure, K] using
      homogeneousPathMeasure_transition_ae K (z0, n0)
        (fun x y =>
          ((Nat.min x.1.1.1 x.1.1.2 = x.2 ∧
              0 < Nat.min x.1.1.1 x.1.1.2) ∧
            y.1 ∈ dominationBadSet x.1.1) →
              y.2 = x.2 + 1)
        (lvPseudoCouplingKernel_ae_bad_implies_birth
          v params hGamma0 hGamma1 N hDom)
  filter_upwards [hsteps] with ω hω
  intro t
  unfold pseudoBadCountUpTo birthsUpTo
  apply Finset.sum_le_sum
  intro i hi
  by_cases hbad :
      ((Nat.min (ω i).1.1.1 (ω i).1.1.2 = (ω i).2 ∧
          0 < Nat.min (ω i).1.1.1 (ω i).1.1.2) ∧
        (ω (i + 1)).1 ∈ dominationBadSet (ω i).1.1)
  · rw [if_pos hbad, if_pos]
    exact hω i hbad
  · rw [if_neg hbad]
    exact Nat.zero_le _

/-- Project a joint trajectory to its auxiliary birth--death trajectory. -/
def pseudoAuxPath
    (ω : Nat → (LabeledPopState × Nat)) : Nat → Nat :=
  pathMap Prod.snd ω

lemma measurable_pseudoAuxPath : Measurable pseudoAuxPath :=
  measurable_pathMap Prod.snd measurable_snd

/-- The full auxiliary path, not merely its fixed-time marginals, has exactly
the law of the prescribed birth--death chain. -/
theorem lvPseudoCouplingPathMeasure_map_aux
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat) :
    (lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0).map pseudoAuxPath =
        bdPathMeasure N n0 := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  exact homogeneousPathMeasure_map_pathMap
    (lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom)
    (bdKernel N)
    Prod.snd measurable_snd
    (fun x => lvPseudoCouplingKernel_snd
      v params hGamma0 hGamma1 N hDom x)
    (z0, n0)

theorem lvPseudoCouplingPathMeasure_aux_extinction_finite
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      extinctionTime (pseudoAuxPath ω) ≠ ⊤ := by
  let P :=
    lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0
  have hmap :
      P.map pseudoAuxPath = bdPathMeasure N n0 :=
    lvPseudoCouplingPathMeasure_map_aux v params
      hGamma0 hGamma1 N hDom z0 n0
  have hfiniteMap :
      ∀ᵐ η ∂P.map pseudoAuxPath, extinctionTime η ≠ ⊤ := by
    rw [hmap, ae_iff]
    simpa only [not_not] using hExtinct
  have hfiniteMeas :
      MeasurableSet {η : Nat → Nat | extinctionTime η ≠ ⊤} :=
    (measurableSet_singleton (⊤ : WithTop Nat)).compl.preimage
      extinctionTime_measurable
  exact
    (MeasureTheory.ae_map_iff measurable_pseudoAuxPath.aemeasurable
      hfiniteMeas).1 hfiniteMap

theorem lvPseudoCouplingPathMeasure_aux_absorbing
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      ∀ t : Nat, (ω t).2 = 0 → (ω (t + 1)).2 = 0 := by
  let P :=
    lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0
  have hmap :
      P.map pseudoAuxPath = bdPathMeasure N n0 :=
    lvPseudoCouplingPathMeasure_map_aux v params
      hGamma0 hGamma1 N hDom z0 n0
  rw [ae_all_iff]
  intro t
  have hbd :
      ∀ᵐ η ∂bdPathMeasure N n0,
        η t = 0 → η (t + 1) = 0 := by
    rw [ae_iff]
    rw [show
        {η : Nat → Nat | ¬(η t = 0 → η (t + 1) = 0)} =
          {η | η t = 0 ∧ η (t + 1) ≠ 0} by
      ext η
      simp only [Set.mem_setOf_eq]
      tauto]
    exact bdPathMeasure_absorbing_step N n0 t
  have hmapAE :
      ∀ᵐ η ∂P.map pseudoAuxPath,
        η t = 0 → η (t + 1) = 0 := by
    rw [hmap]
    exact hbd
  have hmeas :
      MeasurableSet
        {η : Nat → Nat | η t = 0 → η (t + 1) = 0} := by
    rw [show
        {η : Nat → Nat | η t = 0 → η (t + 1) = 0} =
          {η | η t ≠ 0} ∪ {η | η (t + 1) = 0} by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_union]
      tauto]
    exact
      ((measurableSet_singleton 0).compl.preimage
        (measurable_pi_apply t)).union
      ((measurableSet_singleton 0).preimage
        (measurable_pi_apply (t + 1)))
  simpa only [pseudoAuxPath, pathMap] using
    (MeasureTheory.ae_map_iff measurable_pseudoAuxPath.aemeasurable
      hmeas).1 hmapAE

/-- On almost every physical pseudo-coupling path, every non-active step
freezes the labelled LV coordinate. -/
theorem lvPseudoCouplingPathMeasure_left_frozen
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      ∀ t : Nat, ¬isPseudoActive (ω t) →
        (ω (t + 1)).1 = (ω t).1 := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  let K :=
    lvPseudoCouplingKernel v params hGamma0 hGamma1 N hDom
  have hstep :
      ∀ x, ∀ᵐ y ∂K x,
        ¬isPseudoActive x → y.1 = x.1 := by
    intro x
    by_cases hx : isPseudoActive x
    · exact Filter.Eventually.of_forall fun _ hnot =>
        (hnot hx).elim
    · filter_upwards [
        lvPseudoCouplingKernel_ae_left_frozen v params
          hGamma0 hGamma1 N hDom x hx] with y hy
      exact fun _ => hy
  simpa only [lvPseudoCouplingPathMeasure, K] using
    homogeneousPathMeasure_transition_ae K (z0, n0)
      (fun x y => ¬isPseudoActive x → y.1 = x.1)
      hstep

/-- Almost-sure extinction of the prescribed auxiliary chain transfers to
the auxiliary coordinate of the pseudo-coupling, including a zero at or
after every requested physical time. -/
theorem lvPseudoCouplingPathMeasure_aux_eventually_zero
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      ∀ start, ∃ T, start ≤ T ∧ (ω T).2 = 0 := by
  let P :=
    lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0
  have hmap :
      P.map pseudoAuxPath = bdPathMeasure N n0 := by
    exact lvPseudoCouplingPathMeasure_map_aux v params
      hGamma0 hGamma1 N hDom z0 n0
  have hfiniteMap :
      ∀ᵐ η ∂P.map pseudoAuxPath, extinctionTime η ≠ ⊤ := by
    rw [hmap, ae_iff]
    simpa only [not_not] using hExtinct
  have hfiniteMeas :
      MeasurableSet {η : Nat → Nat | extinctionTime η ≠ ⊤} := by
    exact (measurableSet_singleton (⊤ : WithTop Nat)).compl.preimage
      extinctionTime_measurable
  have hfinite :
      ∀ᵐ ω ∂P, extinctionTime (pseudoAuxPath ω) ≠ ⊤ :=
    (MeasureTheory.ae_map_iff measurable_pseudoAuxPath.aemeasurable
      hfiniteMeas).1 hfiniteMap
  have habsorb :
      ∀ᵐ ω ∂P, ∀ t : Nat,
        (ω t).2 = 0 → (ω (t + 1)).2 = 0 := by
    rw [ae_all_iff]
    intro t
    have hbd :
        ∀ᵐ η ∂bdPathMeasure N n0,
          η t = 0 → η (t + 1) = 0 := by
      rw [ae_iff]
      rw [show
          {η : Nat → Nat | ¬(η t = 0 → η (t + 1) = 0)} =
            {η | η t = 0 ∧ η (t + 1) ≠ 0} by
        ext η
        simp only [Set.mem_setOf_eq]
        tauto]
      exact bdPathMeasure_absorbing_step N n0 t
    have hmapAE :
        ∀ᵐ η ∂P.map pseudoAuxPath,
          η t = 0 → η (t + 1) = 0 := by
      rw [hmap]
      exact hbd
    have hmeas :
        MeasurableSet
          {η : Nat → Nat | η t = 0 → η (t + 1) = 0} := by
      rw [show
          {η : Nat → Nat | η t = 0 → η (t + 1) = 0} =
            {η | η t ≠ 0} ∪ {η | η (t + 1) = 0} by
        ext η
        simp only [Set.mem_setOf_eq, Set.mem_union]
        tauto]
      exact
        ((measurableSet_singleton 0).compl.preimage
          (measurable_pi_apply t)).union
        ((measurableSet_singleton 0).preimage
          (measurable_pi_apply (t + 1)))
    simpa only [pseudoAuxPath, pathMap] using
      (MeasureTheory.ae_map_iff measurable_pseudoAuxPath.aemeasurable
        hmeas).1 hmapAE
  filter_upwards [hfinite, habsorb] with ω hfin habs
  have hhit :
      ∃ τ : Nat, (ω τ).2 = 0 := by
    let η := pseudoAuxPath ω
    have hmem := hittingAfter_mem_set_of_ne_top
      (u := natCoord) (s := ({0} : Set Nat)) (n := 0)
      (ω := η) hfin
    refine ⟨(extinctionTime η).untopA, ?_⟩
    change natCoord (extinctionTime η).untopA η ∈ ({0} : Set Nat) at hmem
    simpa [natCoord, η, pseudoAuxPath, pathMap] using hmem
  obtain ⟨τ, hτ⟩ := hhit
  have hstay : ∀ t, τ ≤ t → (ω t).2 = 0 := by
    intro t hτt
    induction t, hτt using Nat.le_induction with
    | base => exact hτ
    | succ t _ ih => exact habs t ih
  intro start
  exact ⟨max start τ, le_max_left _ _, hstay _ (le_max_right _ _)⟩

/-- Under the paper's start domination and almost-sure auxiliary extinction,
all equality times exist, are strictly increasing, and the LV coordinate is
frozen between successive active updates. -/
theorem lvPseudoCouplingPathMeasure_active_times
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      (∀ k, isPseudoActive (ω (lvPseudoActiveTime ω k))) ∧
      StrictMono (lvPseudoActiveTime ω) ∧
      (∀ k,
        (ω (lvPseudoActiveTime ω (k + 1))).1 =
          (ω (lvPseudoActiveTime ω k + 1)).1) := by
  filter_upwards [
    lvPseudoCouplingPathMeasure_min_le v params hGamma0 hGamma1
      N hDom z0 n0 hStart,
    lvPseudoCouplingPathMeasure_aux_eventually_zero v params
      hGamma0 hGamma1 N hDom z0 n0 hExtinct,
    lvPseudoCouplingPathMeasure_left_frozen v params
      hGamma0 hGamma1 N hDom z0 n0] with ω hminor hext hfreeze
  have hspec := lvPseudoActiveTime_spec ω hminor hext
  exact ⟨hspec.1, hspec.2,
    fun k => lvPseudoActiveTime_left_frozen
      ω hminor hext hfreeze k⟩

/-- The first active embedded state is the prescribed initial labelled LV
state. -/
theorem lvPseudoCouplingPathMeasure_traceCylinder_zero
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0)
    (q : ∀ _ : Finset.Iic 0, LabeledPopState) :
    lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0 (pseudoTraceCylinder 0 q) =
      Measure.dirac z0
        {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  let P := lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
    N hDom z0 n0
  haveI : IsProbabilityMeasure P := by
    simp only [P, lvPseudoCouplingPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  have hgood :
      ∀ᵐ ω ∂P,
        ω 0 = (z0, n0) ∧
        (∀ start, ∃ t, start ≤ t ∧
          isPseudoActive (ω t)) ∧
        (∀ r, ¬isPseudoActive (ω r) →
          (ω (r + 1)).1 = (ω r).1) := by
    filter_upwards [
      show ∀ᵐ ω ∂P, ω 0 = (z0, n0) by
        rw [ae_iff]
        simpa only [P, lvPseudoCouplingPathMeasure] using
          homogeneousPathMeasure_initial_ne_null
            (lvPseudoCouplingKernel v params
              hGamma0 hGamma1 N hDom) (z0, n0),
      lvPseudoCouplingPathMeasure_min_le v params
        hGamma0 hGamma1 N hDom z0 n0 hStart,
      lvPseudoCouplingPathMeasure_aux_eventually_zero v params
        hGamma0 hGamma1 N hDom z0 n0 hExtinct,
      lvPseudoCouplingPathMeasure_left_frozen v params
        hGamma0 hGamma1 N hDom z0 n0] with
        ω hinitial hminor hextinct hfreeze
    refine ⟨hinitial, fun start => ?_, hfreeze⟩
    obtain ⟨t, hst, htzero⟩ := hextinct start
    refine ⟨t, hst, ?_⟩
    unfold isPseudoActive
    have hmin := hminor t
    omega
  by_cases hq :
      q ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = z0
  · calc
      P (pseudoTraceCylinder 0 q) = P Set.univ := by
        apply measure_congr
        filter_upwards [hgood] with ω hω
        apply propext
        constructor
        · exact fun _ => Set.mem_univ ω
        · intro _
          exact (pseudoTraceCylinder_zero_iff
            ω hω.2.1 hω.2.2 q).2 (by
              simpa only [hω.1] using hq)
      _ = 1 := measure_univ
      _ = Measure.dirac z0
          {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
        simp [hq]
  · calc
      P (pseudoTraceCylinder 0 q) = P ∅ := by
        apply measure_congr
        filter_upwards [hgood] with ω hω
        apply propext
        constructor
        · intro hC
          have hEq := (pseudoTraceCylinder_zero_iff
            ω hω.2.1 hω.2.2 q).1 hC
          have : q ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = z0 := by
            simpa only [hω.1] using hEq
          exact (hq this).elim
        · exact fun h => h.elim
      _ = 0 := measure_empty
      _ = Measure.dirac z0
          {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
        simp [hq]

/-- The finite cylinders of the active embedded process obey exactly the
one-step recursion of the stopped labelled LV kernel. -/
theorem lvPseudoCouplingPathMeasure_traceCylinder_succ
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0)
    (k : Nat)
    (qnext : ∀ _ : Finset.Iic (k + 1), LabeledPopState) :
    let P := lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0
    let q : ∀ _ : Finset.Iic k, LabeledPopState :=
      fun i => qnext
        ⟨i.1, Finset.mem_Iic.mpr
          (Nat.le_trans (Finset.mem_Iic.mp i.2)
            (Nat.le_succ k))⟩
    let b := qnext
      ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
    P (pseudoTraceCylinder (k + 1) qnext) =
      lvStoppedLabeledKernel v params
          (q ⟨k, Finset.mem_Iic.mpr le_rfl⟩) {b} *
        P (pseudoTraceCylinder k q) := by
  let P := lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
    N hDom z0 n0
  let q : ∀ _ : Finset.Iic k, LabeledPopState :=
    fun i => qnext
      ⟨i.1, Finset.mem_Iic.mpr
        (Nat.le_trans (Finset.mem_Iic.mp i.2)
          (Nat.le_succ k))⟩
  let b := qnext
    ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
  let c :=
    lvStoppedLabeledKernel v params
      (q ⟨k, Finset.mem_Iic.mpr le_rfl⟩) {b}
  have hgood :
      ∀ᵐ ω ∂P,
        (∀ start, ∃ t, start ≤ t ∧
          isPseudoActive (ω t)) ∧
        (∀ r, ¬isPseudoActive (ω r) →
          (ω (r + 1)).1 = (ω r).1) := by
    filter_upwards [
      lvPseudoCouplingPathMeasure_min_le v params
        hGamma0 hGamma1 N hDom z0 n0 hStart,
      lvPseudoCouplingPathMeasure_aux_eventually_zero v params
        hGamma0 hGamma1 N hDom z0 n0 hExtinct,
      lvPseudoCouplingPathMeasure_left_frozen v params
        hGamma0 hGamma1 N hDom z0 n0] with
        ω hminor hextinct hfreeze
    refine ⟨fun start => ?_, hfreeze⟩
    obtain ⟨t, hst, htzero⟩ := hextinct start
    refine ⟨t, hst, ?_⟩
    unfold isPseudoActive
    have hmin := hminor t
    omega
  have hevent :
      P (pseudoTraceCylinder (k + 1) qnext) =
        P (⋃ t,
          pseudoTraceCylinderAt k q t ∩
            {ω | (ω (t + 1)).1 = b}) := by
    apply measure_congr
    filter_upwards [hgood] with ω hω
    apply propext
    exact pseudoTraceCylinder_succ_iff
      ω hω.1 hω.2 k qnext
  have hpair :
      Pairwise fun s t =>
        Disjoint
          (pseudoTraceCylinderAt k q s ∩
            {ω | (ω (s + 1)).1 = b})
          (pseudoTraceCylinderAt k q t ∩
            {ω | (ω (t + 1)).1 = b}) := by
    intro s t hst
    rw [Set.disjoint_left]
    intro ω hωs hωt
    exact (Set.disjoint_left.1
      (pseudoTraceCylinderAt_pairwise k q hst))
        hωs.1 hωt.1
  have hmeas :
      ∀ t,
        MeasurableSet
          (pseudoTraceCylinderAt k q t ∩
            {ω : Nat → (LabeledPopState × Nat) |
              (ω (t + 1)).1 = b}) := by
    intro t
    exact (measurableSet_pseudoTraceCylinderAt k q t).inter
      ((measurableSet_singleton b).preimage
        (measurable_fst.comp
          (measurable_pi_apply (t + 1))))
  have hterm : ∀ t,
      P (pseudoTraceCylinderAt k q t ∩
          {ω | (ω (t + 1)).1 = b}) =
        c * P (pseudoTraceCylinderAt k q t) := by
    intro t
    simpa only [P, c] using
      lvPseudoCouplingPathMeasure_traceCylinderAt_next
        v params hGamma0 hGamma1 N hDom z0 n0
          k t q b
  change P (pseudoTraceCylinder (k + 1) qnext) =
    c * P (pseudoTraceCylinder k q)
  rw [hevent, measure_iUnion hpair hmeas]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  rw [← measure_iUnion
    (pseudoTraceCylinderAt_pairwise k q)
    (fun t => measurableSet_pseudoTraceCylinderAt k q t)]
  rfl

/-- Every finite active-state cylinder has exactly the law of the
corresponding stopped labelled LV cylinder. -/
theorem lvPseudoCouplingPathMeasure_traceCylinder_eq_stopped
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0)
    (k : Nat)
    (q : ∀ _ : Finset.Iic k, LabeledPopState) :
    lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0 (pseudoTraceCylinder k q) =
      homogeneousPathMeasure (Measure.dirac z0)
        (lvStoppedLabeledKernel v params)
          {η | frestrictLe k η = q} := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  induction k with
  | zero =>
      rw [lvPseudoCouplingPathMeasure_traceCylinder_zero
        v params hGamma0 hGamma1 N hDom z0 n0
          hStart hExtinct q]
      exact
        (homogeneousPathMeasure_frestrictLe_singleton_zero
          (lvStoppedLabeledKernel v params) z0 q).symm
  | succ k ih =>
      let qprev : ∀ _ : Finset.Iic k, LabeledPopState :=
        fun i => q
          ⟨i.1, Finset.mem_Iic.mpr
            (Nat.le_trans (Finset.mem_Iic.mp i.2)
              (Nat.le_succ k))⟩
      let b := q
        ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
      let c :=
        lvStoppedLabeledKernel v params
          (qprev ⟨k, Finset.mem_Iic.mpr le_rfl⟩) {b}
      calc
        lvPseudoCouplingPathMeasure v params
            hGamma0 hGamma1 N hDom z0 n0
              (pseudoTraceCylinder (k + 1) q) =
            c * lvPseudoCouplingPathMeasure v params
              hGamma0 hGamma1 N hDom z0 n0
                (pseudoTraceCylinder k qprev) := by
          simpa only [qprev, b, c] using
            lvPseudoCouplingPathMeasure_traceCylinder_succ
              v params hGamma0 hGamma1 N hDom z0 n0
                hStart hExtinct k q
        _ = c * homogeneousPathMeasure (Measure.dirac z0)
              (lvStoppedLabeledKernel v params)
                {η | frestrictLe k η = qprev} := by
          rw [ih qprev]
        _ = homogeneousPathMeasure (Measure.dirac z0)
              (lvStoppedLabeledKernel v params)
                {η | frestrictLe (k + 1) η = q} := by
          exact
            (homogeneousPathMeasure_frestrictLe_singleton_succ
              (lvStoppedLabeledKernel v params) z0 k q).symm

/-- The entire active embedded labelled path has exactly the stopped
labelled LV path law.  This closes the stopping-time marginal gap in the
paper's pseudo-coupling argument. -/
theorem lvPseudoCouplingPathMeasure_map_embedded
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    (lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0).map pseudoEmbeddedLabeledPath =
        homogeneousPathMeasure (Measure.dirac z0)
          (lvStoppedLabeledKernel v params) := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  letI : Nonempty (LabeledPopState × Nat) := inferInstance
  let P := lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
    N hDom z0 n0
  let Q := homogeneousPathMeasure (Measure.dirac z0)
    (lvStoppedLabeledKernel v params)
  let M := P.map pseudoEmbeddedLabeledPath
  haveI : IsProbabilityMeasure Q := by
    simp only [Q, homogeneousPathMeasure]
    infer_instance
  have hInfinite :
      ∀ᵐ ω ∂P,
        ∀ start, ∃ t, start ≤ t ∧
          isPseudoActive (ω t) := by
    filter_upwards [
      lvPseudoCouplingPathMeasure_min_le v params
        hGamma0 hGamma1 N hDom z0 n0 hStart,
      lvPseudoCouplingPathMeasure_aux_eventually_zero v params
        hGamma0 hGamma1 N hDom z0 n0 hExtinct] with
        ω hminor hextinct
    intro start
    obtain ⟨t, hst, htzero⟩ := hextinct start
    refine ⟨t, hst, ?_⟩
    unfold isPseudoActive
    have hmin := hminor t
    omega
  have hprefixMap : ∀ k,
      M.map (frestrictLe k) =
        Q.map (frestrictLe k) := by
    intro k
    apply Measure.ext_of_singleton
    intro q
    have hqmeas :
        MeasurableSet
          ({q} : Set (∀ _ : Finset.Iic k,
            LabeledPopState)) :=
      measurableSet_singleton q
    calc
      M.map (frestrictLe k) {q} =
          M ((frestrictLe k) ⁻¹' {q}) := by
        rw [Measure.map_apply (measurable_frestrictLe k)
          hqmeas]
      _ = P (pseudoEmbeddedLabeledPath ⁻¹'
            ((frestrictLe k) ⁻¹' {q})) := by
        rw [show M = P.map pseudoEmbeddedLabeledPath from rfl,
          Measure.map_apply measurable_pseudoEmbeddedLabeledPath
            (hqmeas.preimage (measurable_frestrictLe k))]
      _ = P (pseudoTraceCylinder k q) := by
        apply measure_congr
        filter_upwards [hInfinite] with ω hω
        apply propext
        change frestrictLe k (pseudoEmbeddedLabeledPath ω) = q ↔
          ω ∈ pseudoTraceCylinder k q
        exact pseudoEmbeddedLabeledPath_prefix_iff ω hω k q
      _ = Q {η | frestrictLe k η = q} := by
        simpa only [P, Q] using
          lvPseudoCouplingPathMeasure_traceCylinder_eq_stopped
            v params hGamma0 hGamma1 N hDom z0 n0
              hStart hExtinct k q
      _ = Q.map (frestrictLe k) {q} := by
        rw [Measure.map_apply (measurable_frestrictLe k)
          hqmeas]
        rfl
  let F : (I : Finset Nat) →
      Measure (∀ _ : I, LabeledPopState) :=
    fun I => Q.map I.restrict
  have hFprojective :
      IsProjectiveMeasureFamily
        (α := fun _ : Nat => LabeledPopState) F := by
    exact isProjectiveMeasureFamily_map_restrict
      (P := Q)
      (X := fun t (η : Nat → LabeledPopState) => η t)
      (fun t => (measurable_pi_apply t).aemeasurable)
  have hQlimit :
      IsProjectiveLimit
        (α := fun _ : Nat => LabeledPopState) Q F := by
    intro I
    rfl
  have hMlimit :
      IsProjectiveLimit
        (α := fun _ : Nat => LabeledPopState) M F := by
    rw [isProjectiveLimit_nat_iff hFprojective]
    intro k
    change Measure.map (frestrictLe k) M =
      Measure.map ((Finset.Iic k).restrict) Q
    rw [show (Finset.Iic k).restrict = frestrictLe k by rfl]
    exact hprefixMap k
  haveI (I : Finset Nat) : IsFiniteMeasure (F I) := by
    simp only [F]
    infer_instance
  exact hMlimit.unique hQlimit

/-- On the explicit pseudo-coupling, the consensus time of the active
embedded LV path is bounded pathwise by the extinction time of the auxiliary
birth--death path. -/
theorem lvPseudoCouplingPathMeasure_consensus_le_extinction
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      consensusTime
          (forgetLVLabels (pseudoEmbeddedLabeledPath ω)) ≤
        extinctionTime (pseudoAuxPath ω) := by
  let P :=
    lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
      N hDom z0 n0
  filter_upwards [
    lvPseudoCouplingPathMeasure_min_le v params
      hGamma0 hGamma1 N hDom z0 n0 hStart,
    lvPseudoCouplingPathMeasure_aux_eventually_zero v params
      hGamma0 hGamma1 N hDom z0 n0 hExtinct,
    lvPseudoCouplingPathMeasure_aux_extinction_finite v params
      hGamma0 hGamma1 N hDom z0 n0 hExtinct,
    lvPseudoCouplingPathMeasure_aux_absorbing v params
      hGamma0 hGamma1 N hDom z0 n0] with
      ω hminor heventually hfinite habsorb
  let η := pseudoAuxPath ω
  let ζ := pseudoEmbeddedLabeledPath ω
  have hinfinite :
      ∀ start, ∃ t, start ≤ t ∧ isPseudoActive (ω t) := by
    intro start
    obtain ⟨t, hst, hzero⟩ := heventually start
    refine ⟨t, hst, ?_⟩
    unfold isPseudoActive
    have hle := hminor t
    omega
  cases hext : extinctionTime η with
  | top =>
      exact (hfinite hext).elim
  | coe τ =>
      have hητ : η τ = 0 := by
        have hhit := at_hitting_time'
          (u := natCoord) (s := ({0} : Set Nat))
          (n := 0) (ω := η) hext
        simpa only [natCoord, Set.mem_singleton_iff] using hhit
      have hzeroAfter : ∀ u, τ ≤ u → η u = 0 := by
        intro u hτu
        induction u, hτu using Nat.le_induction with
        | base =>
            exact hητ
        | succ u _ ih =>
            exact habsorb u ih
      obtain ⟨u, hku⟩ :=
        pseudoKthActiveAt_exists ω hinfinite τ
      have hτu : τ ≤ u :=
        pseudoKthActiveAt_index_le_time hku
      have hactive := pseudoKthActiveAt_active hku
      have hminzero :
          Nat.min (ω u).1.1.1 (ω u).1.1.2 = 0 := by
        unfold isPseudoActive at hactive
        rw [hactive]
        exact hzeroAfter u hτu
      have hselected :
          pseudoActiveOrdinalTime τ ω = u :=
        pseudoKthActiveAt_unique
          (pseudoActiveOrdinalTime_isKth
            (pseudoKthActiveAt_exists ω hinfinite τ)) hku
      have hreach :
          reachedConsensus (forgetLVLabels ζ τ) := by
        change reachedConsensus
          (ω (pseudoActiveOrdinalTime τ ω)).1.1
        rw [hselected]
        exact (Nat.min_eq_zero_iff.mp hminzero)
      have hle :
          consensusTime (forgetLVLabels ζ) ≤
            (τ : WithTop Nat) :=
        consensusTime_le_of_reached'
          (forgetLVLabels ζ) τ hreach
      exact hle

/-! ## Relating the stopped labelled path to the original LV path -/

def labeledConsensusSet : Set LabeledPopState :=
  {z | Nat.min z.1.1 z.1.2 = 0}

lemma measurableSet_labeledConsensusSet :
    MeasurableSet labeledConsensusSet :=
  (Set.to_countable labeledConsensusSet).measurableSet

lemma kernelStoppedAt_labeledConsensusSet
    (v : LVVariant) (params : LVParams) :
    kernelStoppedAt labeledConsensusSet
        (lvLabeledKernel v params) =
      lvStoppedLabeledKernel v params := by
  ext z U hU
  by_cases hz : Nat.min z.1.1 z.1.2 = 0 <;>
    simp [kernelStoppedAt, lvStoppedLabeledKernel,
      labeledConsensusSet, hz]

/-- The stopped labelled LV path is obtained by deterministically freezing
an ordinary labelled LV path when one population first reaches zero. -/
theorem lvLabeledPathMeasure_map_stopped
    (v : LVVariant) (params : LVParams) (s0 : PopState) :
    (lvLabeledPathMeasure v params s0).map
        (pathStoppedAt labeledConsensusSet) =
      homogeneousPathMeasure (Measure.dirac (s0, .idle))
        (lvStoppedLabeledKernel v params) := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  rw [lvLabeledPathMeasure,
    homogeneousPathMeasure_map_pathStoppedAt
      labeledConsensusSet measurableSet_labeledConsensusSet
      (lvLabeledKernel v params) (s0, .idle)]
  congr 1
  exact kernelStoppedAt_labeledConsensusSet v params

lemma mem_labeledConsensusSet_iff
    (z : LabeledPopState) :
    z ∈ labeledConsensusSet ↔ reachedConsensus z.1 := by
  simp [labeledConsensusSet, reachedConsensus,
    Nat.min_eq_zero_iff]

lemma first_consensus_pathStoppedAt_iff
    (ω : Nat → LabeledPopState) (t : Nat) :
    (reachedConsensus
          (forgetLVLabels
            (pathStoppedAt labeledConsensusSet ω) t) ∧
        ∀ j < t,
          ¬reachedConsensus
            (forgetLVLabels
              (pathStoppedAt labeledConsensusSet ω) j)) ↔
      (reachedConsensus (forgetLVLabels ω t) ∧
        ∀ j < t,
          ¬reachedConsensus (forgetLVLabels ω j)) := by
  simpa only [forgetLVLabels, mem_labeledConsensusSet_iff] using
    pathStoppedAt_first_mem_iff labeledConsensusSet ω t

/-- Freezing a labelled path at its first consensus state leaves its first
consensus time unchanged. -/
lemma consensusTime_forget_pathStoppedAt
    (ω : Nat → LabeledPopState) :
    consensusTime
        (forgetLVLabels
          (pathStoppedAt labeledConsensusSet ω)) =
      consensusTime (forgetLVLabels ω) := by
  cases hraw : consensusTime (forgetLVLabels ω) with
  | top =>
      cases hstop :
          consensusTime
            (forgetLVLabels
              (pathStoppedAt labeledConsensusSet ω)) with
      | top => rfl
      | coe t =>
          exfalso
          have hfirstStop :=
            (consensusTime_eq_coe_iff
              (forgetLVLabels
                (pathStoppedAt labeledConsensusSet ω)) t).1 hstop
          have hfirstRaw :=
            (first_consensus_pathStoppedAt_iff ω t).1 hfirstStop
          have hrawFinite :=
            (consensusTime_eq_coe_iff
              (forgetLVLabels ω) t).2 hfirstRaw
          rw [hraw] at hrawFinite
          exact WithTop.top_ne_coe hrawFinite
  | coe t =>
      have hfirstRaw :=
        (consensusTime_eq_coe_iff
          (forgetLVLabels ω) t).1 hraw
      exact
        (consensusTime_eq_coe_iff
          (forgetLVLabels
            (pathStoppedAt labeledConsensusSet ω)) t).2
          ((first_consensus_pathStoppedAt_iff ω t).2 hfirstRaw)

/-- Freezing after consensus does not alter any labelled bad reaction counted
before consensus. -/
lemma labeledBadCountBeforeConsensus_pathStoppedAt
    (ω : Nat → LabeledPopState) :
    labeledBadCountBeforeConsensus
        (pathStoppedAt labeledConsensusSet ω) =
      labeledBadCountBeforeConsensus ω := by
  have htime := consensusTime_forget_pathStoppedAt ω
  cases hraw : consensusTime (forgetLVLabels ω) with
  | top =>
      have hstop :
          consensusTime
              (forgetLVLabels
                (pathStoppedAt labeledConsensusSet ω)) = ⊤ := by
        rw [htime, hraw]
      simp [labeledBadCountBeforeConsensus, hraw, hstop]
  | coe t =>
      have hfirst :=
        (consensusTime_eq_coe_iff
          (forgetLVLabels ω) t).1 hraw
      have hbeforeA :
          ∀ u < t, ω u ∉ labeledConsensusSet := by
        intro u hu
        rw [mem_labeledConsensusSet_iff]
        exact hfirst.2 u hu
      have hstop :
          consensusTime
              (forgetLVLabels
                (pathStoppedAt labeledConsensusSet ω)) =
            (t : WithTop Nat) := by
        rw [htime, hraw]
        rfl
      simp only [labeledBadCountBeforeConsensus, hraw, hstop]
      unfold labeledBadCountUpTo
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i < t := Finset.mem_range.mp hi
      have hei :
          pathStoppedAt labeledConsensusSet ω i = ω i :=
        pathStoppedAt_eq_of_forall_not_mem_before
          labeledConsensusSet ω i
            (fun u hu => hbeforeA u (by omega))
      have heis :
          pathStoppedAt labeledConsensusSet ω (i + 1) =
            ω (i + 1) :=
        pathStoppedAt_eq_of_forall_not_mem_before
          labeledConsensusSet ω (i + 1)
            (fun u hu => hbeforeA u (by omega))
      rw [hei, heis]

lemma measurableSet_consensusTailEvent (t : Nat) :
    MeasurableSet
      {ω : Nat → PopState |
        (t : WithTop Nat) ≤ consensusTime ω} := by
  let E : Set (Nat → PopState) :=
    ⋃ j : Fin t, {ω | consensusTime ω = (j.1 : WithTop Nat)}
  have hE : MeasurableSet E :=
    MeasurableSet.iUnion fun j =>
      measurableSet_consensusTime_eq_coe j.1
  have heq :
      {ω : Nat → PopState |
          (t : WithTop Nat) ≤ consensusTime ω} = Eᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    cases hct : consensusTime ω with
    | top =>
        simp [E, hct]
    | coe c =>
        simp only [hct, WithTop.coe_le_coe, E,
          Set.mem_iUnion, Set.mem_setOf_eq,
          WithTop.coe_eq_coe]
        constructor
        · intro htc ⟨j, hcj⟩
          have htcNat : t ≤ c :=
            WithTop.coe_le_coe.mp htc
          have hcjNat : c = j.1 :=
            WithTop.coe_eq_coe.mp hcj
          have hjt : j.1 < t := j.2
          omega
        · intro hnone
          by_contra htc
          have htcNat : ¬t ≤ c := fun h =>
            htc (WithTop.coe_le_coe.mpr h)
          have hct' : c < t := Nat.lt_of_not_ge htcNat
          exact hnone
            ⟨⟨c, hct'⟩, rfl⟩
  rw [heq]
  exact hE.compl

/-- While species `0` is ahead, one labelled self-destructive transition can
decrease the signed gap by one only if its reaction is counted by `J`. -/
lemma selfDestructive_gap_step_le_labeled_bad
    (s s' : PopState) (r : LVReaction)
    (hpositive : 0 < Nat.min s.1 s.2)
    (hgap : 0 < gap s)
    (htarget : s' = lvReactionTarget .selfDestructive s r)
    (hnot0 : r ≠ .intra0)
    (hnot1 : r ≠ .intra1) :
    (isBadNoncompetitiveReaction s r → gap s ≤ gap s' + 1) ∧
      (¬isBadNoncompetitiveReaction s r → gap s ≤ gap s') := by
  classical
  subst s'
  rcases s with ⟨a, b⟩
  cases r <;>
    simp_all [lvReactionTarget, gap, isBadNoncompetitiveReaction] <;>
    omega

/-- If the intraspecific rates vanish, an intraspecific reaction label has
zero probability in every one-step labelled kernel. -/
lemma lvLabeledKernel_ae_no_intra
    (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (z : LabeledPopState) :
    ∀ᵐ z' ∂lvLabeledKernel .selfDestructive params z,
      z'.2 ≠ .intra0 ∧ z'.2 ≠ .intra1 := by
  have h0 :
      ∀ᵐ z' ∂lvLabeledKernel .selfDestructive params z,
        z'.2 ≠ .intra0 := by
    rw [ae_iff]
    calc
      lvLabeledKernel .selfDestructive params z
          {z' | ¬z'.2 ≠ LVReaction.intra0} =
          lvLabeledKernel .selfDestructive params z
            {z' | z'.2 = LVReaction.intra0} := by
              congr 1
              ext z'
              simp
      _ = 0 := by
        rw [lvLabeledKernel_reaction_probability]
        simp [lvReactionWeight, hGamma0]
  have h1 :
      ∀ᵐ z' ∂lvLabeledKernel .selfDestructive params z,
        z'.2 ≠ .intra1 := by
    rw [ae_iff]
    calc
      lvLabeledKernel .selfDestructive params z
          {z' | ¬z'.2 ≠ LVReaction.intra1} =
          lvLabeledKernel .selfDestructive params z
            {z' | z'.2 = LVReaction.intra1} := by
              congr 1
              ext z'
              simp
      _ = 0 := by
        rw [lvLabeledKernel_reaction_probability]
        simp [lvReactionWeight, hGamma1]
  filter_upwards [h0, h1] with z' hz0 hz1
  exact ⟨hz0, hz1⟩

/-- Almost every labelled self-destructive path records the reaction target at
each step and, when `γ₀ = γ₁ = 0`, never records an intraspecific reaction. -/
lemma lvLabeledPathMeasure_valid_selfDestructive_ae
    (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) :
    ∀ᵐ ζ ∂lvLabeledPathMeasure .selfDestructive params s0,
      ∀ t : Nat,
        (ζ (t + 1)).1 =
            lvReactionTarget .selfDestructive
              (ζ t).1 (ζ (t + 1)).2 ∧
          (ζ (t + 1)).2 ≠ .intra0 ∧
          (ζ (t + 1)).2 ≠ .intra1 := by
  letI : Nonempty LabeledPopState := ⟨(s0, .idle)⟩
  unfold lvLabeledPathMeasure
  let R : LabeledPopState → LabeledPopState → Prop :=
    fun z z' =>
      z'.1 = lvReactionTarget .selfDestructive z.1 z'.2 ∧
        z'.2 ≠ .intra0 ∧ z'.2 ≠ .intra1
  have hstep : ∀ z, ∀ᵐ z' ∂lvLabeledKernel .selfDestructive params z,
      R z z' := by
    intro z
    filter_upwards [
      lvLabeledKernel_ae_reactionTarget
        .selfDestructive params z,
      lvLabeledKernel_ae_no_intra
        params hGamma0 hGamma1 z] with z' htarget hno
    exact ⟨htarget, hno⟩
  exact homogeneousPathMeasure_transition_ae
    (lvLabeledKernel .selfDestructive params)
    (s0, .idle) R hstep

/-- Before the signed gap first becomes nonpositive, its decrease from the
initial value is at most the number of reactions counted by `J`. -/
lemma labeled_gap_invariant_before_nonpositive
    (ζ : Nat → LabeledPopState)
    (hvalid : ∀ t : Nat,
      (ζ (t + 1)).1 =
          lvReactionTarget .selfDestructive
            (ζ t).1 (ζ (t + 1)).2 ∧
        (ζ (t + 1)).2 ≠ .intra0 ∧
        (ζ (t + 1)).2 ≠ .intra1)
    (t : Nat)
    (hbefore : ∀ i < t,
      0 < gap (ζ i).1 ∧
        0 < Nat.min (ζ i).1.1 (ζ i).1.2) :
    gap (ζ 0).1 ≤
      gap (ζ t).1 + (labeledBadCountUpTo ζ t : Int) := by
  classical
  induction t with
  | zero =>
      simp [labeledBadCountUpTo]
  | succ t ih =>
      have hbefore' : ∀ i < t,
          0 < gap (ζ i).1 ∧
            0 < Nat.min (ζ i).1.1 (ζ i).1.2 := by
        intro i hi
        exact hbefore i (by omega)
      have hprev := ih hbefore'
      have ht := hbefore t (Nat.lt_succ_self t)
      have hstep := selfDestructive_gap_step_le_labeled_bad
        (ζ t).1 (ζ (t + 1)).1 (ζ (t + 1)).2
        ht.2 ht.1 (hvalid t).1 (hvalid t).2.1 (hvalid t).2.2
      have hcount :
          labeledBadCountUpTo ζ (t + 1) =
            labeledBadCountUpTo ζ t +
              if isBadNoncompetitiveReaction
                  (ζ t).1 (ζ (t + 1)).2 then 1 else 0 := by
        unfold labeledBadCountUpTo
        rw [Finset.sum_range_succ]
      rw [hcount]
      by_cases hbad :
          isBadNoncompetitiveReaction (ζ t).1 (ζ (t + 1)).2
      · rw [if_pos hbad]
        push_cast
        linarith [hstep.1 hbad]
      · rw [if_neg hbad, add_zero]
        linarith [hstep.2 hbad]

lemma labeledBadCountUpTo_mono
    (ζ : Nat → LabeledPopState) {s t : Nat} (hst : s ≤ t) :
    labeledBadCountUpTo ζ s ≤ labeledBadCountUpTo ζ t := by
  classical
  unfold labeledBadCountUpTo
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono hst

/-- If species `0` starts with a strict majority and consensus is reached,
then fewer than `a-b` reactions counted by `J` imply that species `0` wins. -/
lemma labeled_gap_majority_argument
    (a b : Nat) (ζ : Nat → LabeledPopState)
    (hab : b < a)
    (hζ0 : (ζ 0).1 = (a, b))
    (hvalid : ∀ t : Nat,
      (ζ (t + 1)).1 =
          lvReactionTarget .selfDestructive
            (ζ t).1 (ζ (t + 1)).2 ∧
        (ζ (t + 1)).2 ≠ .intra0 ∧
        (ζ (t + 1)).2 ≠ .intra1)
    (τ : Nat)
    (hτ : consensusTime (forgetLVLabels ζ) = (τ : WithTop Nat))
    (hBad :
      labeledBadCountBeforeConsensus ζ < a - b) :
    majorityConsensusEvent (a, b) (forgetLVLabels ζ) := by
  classical
  by_contra hnot
  have hcons :=
    reachedConsensus_at_consensusTime'
      (forgetLVLabels ζ) τ hτ
  have hmaj : species0Majority (a, b) := by
    simp [species0Majority]
    omega
  have hend : gap (ζ τ).1 ≤ 0 := by
    simp only [majorityConsensusEvent, hτ, hmaj, true_and,
      forgetLVLabels] at hnot
    simp only [reachedConsensus, forgetLVLabels] at hcons
    rcases hcons with hzero0 | hzero1
    · simp [gap, hzero0]
    · have hzero0 : (ζ τ).1.1 = 0 := by
        by_contra hpos
        apply hnot
        exact Or.inl ⟨Nat.pos_of_ne_zero hpos, hzero1⟩
      simp [gap, hzero0, hzero1]
  let p : Nat → Prop :=
    fun t => t ≤ τ ∧ gap (ζ t).1 ≤ 0
  have hex : ∃ t, p t := ⟨τ, le_rfl, hend⟩
  let j : Nat := Nat.find hex
  have hj : p j := Nat.find_spec hex
  have hbeforeGap :
      ∀ i < j, 0 < gap (ζ i).1 := by
    intro i hi
    have hnotp : ¬p i := Nat.find_min hex hi
    have hiτ : i ≤ τ :=
      le_trans (Nat.le_of_lt hi) hj.1
    exact lt_of_not_ge fun hle => hnotp ⟨hiτ, hle⟩
  have hbefore :
      ∀ i < j,
        0 < gap (ζ i).1 ∧
          0 < Nat.min (ζ i).1.1 (ζ i).1.2 := by
    intro i hi
    refine ⟨hbeforeGap i hi, ?_⟩
    have hne :
        ¬reachedConsensus (forgetLVLabels ζ i) :=
      ((consensusTime_eq_coe_iff
        (forgetLVLabels ζ) τ).mp hτ).2 i
          (lt_of_lt_of_le hi hj.1)
    simp only [reachedConsensus, forgetLVLabels, not_or] at hne
    exact Nat.lt_min.mpr
      ⟨Nat.pos_of_ne_zero hne.1,
        Nat.pos_of_ne_zero hne.2⟩
  have hinv :=
    labeled_gap_invariant_before_nonpositive ζ hvalid j hbefore
  have hgap0 :
      gap (ζ 0).1 = (a : Int) - (b : Int) := by
    simp [hζ0, gap]
  rw [hgap0] at hinv
  have hcountj :
      a - b ≤ labeledBadCountUpTo ζ j := by
    have hcast :
        (a : Int) - (b : Int) ≤
          (labeledBadCountUpTo ζ j : Int) := by
      linarith [hj.2]
    rw [← Nat.cast_sub hab.le] at hcast
    exact_mod_cast hcast
  have hcountτ :
      labeledBadCountUpTo ζ j ≤
        labeledBadCountUpTo ζ τ :=
    labeledBadCountUpTo_mono ζ hj.1
  have hbeforeEq :
      labeledBadCountBeforeConsensus ζ =
        labeledBadCountUpTo ζ τ := by
    simp [labeledBadCountBeforeConsensus, hτ]
  rw [hbeforeEq] at hBad
  omega

lemma measurable_labeledBadCountUpTo (t : Nat) :
    Measurable
      (fun ω : Nat → LabeledPopState =>
        labeledBadCountUpTo ω t) := by
  classical
  unfold labeledBadCountUpTo
  apply Finset.measurable_sum
  intro i _
  let f : LabeledPopState × LabeledPopState → Nat :=
    fun z =>
      if isBadNoncompetitiveReaction z.1.1 z.2.2 then 1 else 0
  have hf : Measurable f :=
    measurable_of_countable f
  have hp :
      Measurable
        (fun ω : Nat → LabeledPopState =>
          (ω i, ω (i + 1))) :=
    (measurable_pi_apply i).prodMk
      (measurable_pi_apply (i + 1))
  exact hf.comp hp

lemma measurableSet_labeledBadTailEvent (L : Nat) :
    MeasurableSet
      {ω : Nat → LabeledPopState |
        L ≤ labeledBadCountBeforeConsensus ω} := by
  cases L with
  | zero =>
      convert MeasurableSet.univ using 1
      ext ω
      simp
  | succ L =>
      have heq :
          {ω : Nat → LabeledPopState |
              L + 1 ≤ labeledBadCountBeforeConsensus ω} =
            ⋃ t : Nat,
              {ω | consensusTime (forgetLVLabels ω) =
                  (t : WithTop Nat)} ∩
                {ω | L + 1 ≤ labeledBadCountUpTo ω t} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iUnion,
          Set.mem_inter_iff]
        cases hct : consensusTime (forgetLVLabels ω) with
        | top =>
            simp [labeledBadCountBeforeConsensus, hct]
        | coe t =>
            simp only [labeledBadCountBeforeConsensus, hct]
            constructor
            · intro h
              exact ⟨t, rfl, h⟩
            · rintro ⟨u, hu, hcount⟩
              have hut : u = t :=
                (WithTop.coe_eq_coe.mp hu).symm
              simpa only [hut] using hcount
      rw [heq]
      apply MeasurableSet.iUnion
      intro t
      exact
        ((measurableSet_consensusTime_eq_coe t).preimage
          measurable_forgetLVLabels).inter
        ((measurable_labeledBadCountUpTo t)
          measurableSet_Ici)

theorem lvPseudoCouplingPathMeasure_consensusTail_law
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (s0 : PopState) (n0 : Nat)
    (hStart : Nat.min s0.1 s0.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0)
    (t : Nat) :
    consensusTail v params s0 t =
      lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom (s0, .idle) n0
        {ω | (t : WithTop Nat) ≤
          consensusTime
            (forgetLVLabels
              (pseudoEmbeddedLabeledPath ω))} := by
  let R := lvLabeledPathMeasure v params s0
  let Q := homogeneousPathMeasure
    (Measure.dirac (s0, .idle))
      (lvStoppedLabeledKernel v params)
  let P := lvPseudoCouplingPathMeasure v params
    hGamma0 hGamma1 N hDom (s0, .idle) n0
  let G : Set (Nat → PopState) :=
    {η | (t : WithTop Nat) ≤ consensusTime η}
  let F : Set (Nat → LabeledPopState) :=
    {ζ | (t : WithTop Nat) ≤
      consensusTime (forgetLVLabels ζ)}
  have hG : MeasurableSet G :=
    measurableSet_consensusTailEvent t
  have hF : MeasurableSet F :=
    hG.preimage measurable_forgetLVLabels
  have hstop :
      R.map (pathStoppedAt labeledConsensusSet) = Q := by
    exact lvLabeledPathMeasure_map_stopped v params s0
  have hembed :
      P.map pseudoEmbeddedLabeledPath = Q := by
    exact lvPseudoCouplingPathMeasure_map_embedded
      v params hGamma0 hGamma1 N hDom
        (s0, .idle) n0 hStart hExtinct
  calc
    consensusTail v params s0 t =
        lvPathMeasure v params s0 G := rfl
    _ = (R.map forgetLVLabels) G := by
      rw [show R.map forgetLVLabels =
          lvPathMeasure v params s0 by
        exact lvLabeledPathMeasure_map_forget v params s0]
    _ = R F := by
      rw [Measure.map_apply measurable_forgetLVLabels hG]
      rfl
    _ = (R.map (pathStoppedAt labeledConsensusSet)) F := by
      rw [Measure.map_apply
        (measurable_pathStoppedAt labeledConsensusSet
          measurableSet_labeledConsensusSet) hF]
      apply congrArg R
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, F]
      rw [consensusTime_forget_pathStoppedAt]
    _ = Q F := by rw [hstop]
    _ = (P.map pseudoEmbeddedLabeledPath) F := by
      rw [hembed]
    _ = P {ω | (t : WithTop Nat) ≤
          consensusTime
            (forgetLVLabels
              (pseudoEmbeddedLabeledPath ω))} := by
      rw [Measure.map_apply
        measurable_pseudoEmbeddedLabeledPath hF]
      rfl

theorem lvPseudoCouplingPathMeasure_labeledBadTail_law
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (s0 : PopState) (n0 : Nat)
    (hStart : Nat.min s0.1 s0.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0)
    (L : Nat) :
    labeledBadTail v params s0 L =
      lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom (s0, .idle) n0
        {ω | L ≤ labeledBadCountBeforeConsensus
          (pseudoEmbeddedLabeledPath ω)} := by
  let R := lvLabeledPathMeasure v params s0
  let Q := homogeneousPathMeasure
    (Measure.dirac (s0, .idle))
      (lvStoppedLabeledKernel v params)
  let P := lvPseudoCouplingPathMeasure v params
    hGamma0 hGamma1 N hDom (s0, .idle) n0
  let F : Set (Nat → LabeledPopState) :=
    {ζ | L ≤ labeledBadCountBeforeConsensus ζ}
  have hF : MeasurableSet F :=
    measurableSet_labeledBadTailEvent L
  have hstop :
      R.map (pathStoppedAt labeledConsensusSet) = Q := by
    exact lvLabeledPathMeasure_map_stopped v params s0
  have hembed :
      P.map pseudoEmbeddedLabeledPath = Q := by
    exact lvPseudoCouplingPathMeasure_map_embedded
      v params hGamma0 hGamma1 N hDom
        (s0, .idle) n0 hStart hExtinct
  calc
    labeledBadTail v params s0 L = R F := rfl
    _ = (R.map (pathStoppedAt labeledConsensusSet)) F := by
      rw [Measure.map_apply
        (measurable_pathStoppedAt labeledConsensusSet
          measurableSet_labeledConsensusSet) hF]
      apply congrArg R
      ext ζ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, F]
      rw [labeledBadCountBeforeConsensus_pathStoppedAt]
    _ = Q F := by rw [hstop]
    _ = (P.map pseudoEmbeddedLabeledPath) F := by
      rw [hembed]
    _ = P {ω | L ≤ labeledBadCountBeforeConsensus
          (pseudoEmbeddedLabeledPath ω)} := by
      rw [Measure.map_apply
        measurable_pseudoEmbeddedLabeledPath hF]
      rfl

theorem lvPseudoCouplingPathMeasure_extinctionTail_law
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 t : Nat) :
    extinctionTail N n0 t =
      lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0
        {ω | (t : WithTop Nat) ≤
          extinctionTime (pseudoAuxPath ω)} := by
  let P := lvPseudoCouplingPathMeasure v params
    hGamma0 hGamma1 N hDom z0 n0
  let F : Set (Nat → Nat) :=
    {η | (t : WithTop Nat) ≤ extinctionTime η}
  have hF : MeasurableSet F :=
    extinctionTime_measurable measurableSet_Ici
  have hmap :
      P.map pseudoAuxPath = bdPathMeasure N n0 :=
    lvPseudoCouplingPathMeasure_map_aux v params
      hGamma0 hGamma1 N hDom z0 n0
  calc
    extinctionTail N n0 t = bdPathMeasure N n0 F := rfl
    _ = (P.map pseudoAuxPath) F := by rw [hmap]
    _ = P {ω | (t : WithTop Nat) ≤
          extinctionTime (pseudoAuxPath ω)} := by
      rw [Measure.map_apply measurable_pseudoAuxPath hF]
      rfl

theorem lvPseudoCouplingPathMeasure_birthTail_law
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 L : Nat) :
    birthTail N n0 L =
      lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0
        {ω | L ≤ birthsBeforeExtinction (pseudoAuxPath ω)} := by
  let P := lvPseudoCouplingPathMeasure v params
    hGamma0 hGamma1 N hDom z0 n0
  let F : Set (Nat → Nat) :=
    {η | L ≤ birthsBeforeExtinction η}
  have hF : MeasurableSet F :=
    measurable_birthsBeforeExtinction measurableSet_Ici
  have hmap :
      P.map pseudoAuxPath = bdPathMeasure N n0 :=
    lvPseudoCouplingPathMeasure_map_aux v params
      hGamma0 hGamma1 N hDom z0 n0
  calc
    birthTail N n0 L = bdPathMeasure N n0 F := rfl
    _ = (P.map pseudoAuxPath) F := by rw [hmap]
    _ = P {ω | L ≤
          birthsBeforeExtinction (pseudoAuxPath ω)} := by
      rw [Measure.map_apply measurable_pseudoAuxPath hF]
      rfl

lemma labeledBadCountUpTo_embedded_le_pseudo
    (v : LVVariant)
    (ω : Nat → (LabeledPopState × Nat))
    (hinfinite : ∀ start, ∃ t, start ≤ t ∧
      isPseudoActive (ω t))
    (hfreeze : ∀ r, ¬isPseudoActive (ω r) →
      (ω (r + 1)).1 = (ω r).1)
    (k : Nat)
    (hpositive : ∀ i < k,
      0 < Nat.min
        (pseudoEmbeddedLabeledPath ω i).1.1
        (pseudoEmbeddedLabeledPath ω i).1.2) :
    labeledBadCountUpTo (pseudoEmbeddedLabeledPath ω) k ≤
      pseudoBadCountUpTo v ω
        (pseudoActiveOrdinalTime k ω) := by
  classical
  induction k with
  | zero =>
      simp [labeledBadCountUpTo]
  | succ k ih =>
      let ζ := pseudoEmbeddedLabeledPath ω
      let s := pseudoActiveOrdinalTime k ω
      let t := pseudoActiveOrdinalTime (k + 1) ω
      have hs :
          pseudoKthActiveAt k s ω :=
        pseudoActiveOrdinalTime_isKth
          (pseudoKthActiveAt_exists ω hinfinite k)
      have ht :
          pseudoKthActiveAt (k + 1) t ω :=
        pseudoActiveOrdinalTime_isKth
          (pseudoKthActiveAt_exists ω hinfinite (k + 1))
      rcases ht with
        ⟨htactive, r, hrt, hkr, hbetween⟩
      have hrs : r = s :=
        pseudoKthActiveAt_unique hkr hs
      subst r
      have hst : s < t := hrt
      have hfrozen :
          (ω t).1 = (ω (s + 1)).1 :=
        pseudoLeft_frozen_between_active
          ω hfreeze hst hbetween
      have hζk : ζ k = (ω s).1 := rfl
      have hζnext : ζ (k + 1) = (ω (s + 1)).1 := by
        change (ω t).1 = (ω (s + 1)).1
        exact hfrozen
      have hactive := pseudoKthActiveAt_active hs
      have hactiveEq :
          Nat.min (ω s).1.1.1 (ω s).1.1.2 = (ω s).2 := by
        exact hactive
      have hpos :
          0 < Nat.min (ω s).1.1.1 (ω s).1.1.2 := by
        have := hpositive k (Nat.lt_succ_self k)
        simpa only [ζ, hζk] using this
      let bad : Prop :=
        isBadNoncompetitiveReaction (ζ k).1 (ζ (k + 1)).2
      have hbadLabel :
          (ω (s + 1)).1 ∈
              dominationBadSet (ω s).1.1 ↔ bad := by
        simp only [dominationBadSet, Set.mem_setOf_eq, bad]
        rw [← hζk, ← hζnext]
      have hphysical :
          (((Nat.min (ω s).1.1.1 (ω s).1.1.2 = (ω s).2 ∧
                0 < Nat.min (ω s).1.1.1 (ω s).1.1.2) ∧
              (ω (s + 1)).1 ∈
                dominationBadSet (ω s).1.1)) ↔ bad := by
        constructor
        · rintro ⟨_, hlabel⟩
          exact hbadLabel.mp hlabel
        · intro hbad
          exact ⟨⟨hactiveEq, hpos⟩, hbadLabel.mpr hbad⟩
      have hlabelSucc :
          labeledBadCountUpTo ζ (k + 1) =
            labeledBadCountUpTo ζ k + if bad then 1 else 0 := by
        unfold labeledBadCountUpTo
        rw [Finset.sum_range_succ]
      have hpseudoSucc :
          pseudoBadCountUpTo v ω (s + 1) =
            pseudoBadCountUpTo v ω s + if bad then 1 else 0 := by
        unfold pseudoBadCountUpTo
        rw [Finset.sum_range_succ]
        by_cases hbad : bad
        · rw [if_pos hbad, if_pos (hphysical.mpr hbad)]
        · rw [if_neg hbad, if_neg (fun h => hbad (hphysical.mp h))]
      have ih' :
          labeledBadCountUpTo ζ k ≤
            pseudoBadCountUpTo v ω s := by
        exact ih
          (fun i hi => hpositive i (by omega))
      calc
        labeledBadCountUpTo ζ (k + 1) =
            labeledBadCountUpTo ζ k +
              (if bad then 1 else 0) := hlabelSucc
        _ ≤ pseudoBadCountUpTo v ω s +
              (if bad then 1 else 0) :=
          Nat.add_le_add_right ih' _
        _ = pseudoBadCountUpTo v ω (s + 1) :=
          hpseudoSucc.symm
        _ ≤ pseudoBadCountUpTo v ω t :=
          pseudoBadCountUpTo_mono v ω (by omega)

/-- On the explicit pseudo-coupling, the number of labelled bad
non-competitive LV reactions before consensus is bounded pathwise by the
number of auxiliary births before extinction. -/
theorem lvPseudoCouplingPathMeasure_badBefore_le_birthsBefore
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : BirthDeathChain)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (z0 : LabeledPopState) (n0 : Nat)
    (hStart : Nat.min z0.1.1 z0.1.2 ≤ n0)
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    ∀ᵐ ω ∂lvPseudoCouplingPathMeasure v params hGamma0 hGamma1
        N hDom z0 n0,
      labeledBadCountBeforeConsensus
          (pseudoEmbeddedLabeledPath ω) ≤
        birthsBeforeExtinction (pseudoAuxPath ω) := by
  filter_upwards [
    lvPseudoCouplingPathMeasure_min_le v params
      hGamma0 hGamma1 N hDom z0 n0 hStart,
    lvPseudoCouplingPathMeasure_aux_eventually_zero v params
      hGamma0 hGamma1 N hDom z0 n0 hExtinct,
    lvPseudoCouplingPathMeasure_aux_extinction_finite v params
      hGamma0 hGamma1 N hDom z0 n0 hExtinct,
    lvPseudoCouplingPathMeasure_aux_absorbing v params
      hGamma0 hGamma1 N hDom z0 n0,
    lvPseudoCouplingPathMeasure_left_frozen v params
      hGamma0 hGamma1 N hDom z0 n0,
    lvPseudoCouplingPathMeasure_bad_le_births v params
      hGamma0 hGamma1 N hDom z0 n0,
    lvPseudoCouplingPathMeasure_consensus_le_extinction v params
      hGamma0 hGamma1 N hDom z0 n0 hStart hExtinct] with
      ω hminor heventually hfinite habsorb hfreeze
        hbadPhysical htime
  let η := pseudoAuxPath ω
  let ζ := pseudoEmbeddedLabeledPath ω
  have htime' :
      consensusTime (forgetLVLabels ζ) ≤ extinctionTime η := by
    exact htime
  have hinfinite :
      ∀ start, ∃ t, start ≤ t ∧ isPseudoActive (ω t) := by
    intro start
    obtain ⟨t, hst, hzero⟩ := heventually start
    refine ⟨t, hst, ?_⟩
    unfold isPseudoActive
    have hle := hminor t
    omega
  cases hext : extinctionTime η with
  | top =>
      exact (hfinite hext).elim
  | coe τ =>
      have hητ : η τ = 0 := by
        have hhit := at_hitting_time'
          (u := natCoord) (s := ({0} : Set Nat))
          (n := 0) (ω := η) hext
        simpa only [natCoord, Set.mem_singleton_iff] using hhit
      have hzeroAfter : ∀ u, τ ≤ u → η u = 0 := by
        intro u hτu
        induction u, hτu using Nat.le_induction with
        | base =>
            exact hητ
        | succ u _ ih =>
            exact habsorb u ih
      cases hcons : consensusTime (forgetLVLabels ζ) with
      | top =>
          have hfalse :
              ¬(⊤ : WithTop Nat) ≤ (τ : WithTop Nat) := by
            simp
          have hle := htime'
          rw [hcons, hext] at hle
          exact (hfalse hle).elim
      | coe c =>
          have hcτTop :
              (c : WithTop Nat) ≤ (τ : WithTop Nat) := by
            have hle := htime'
            rw [hcons, hext] at hle
            exact hle
          have hcτ : c ≤ τ :=
            WithTop.coe_le_coe.mp hcτTop
          have hfirst :=
            (consensusTime_eq_coe_iff
              (forgetLVLabels ζ) c).1 hcons
          have hpositive :
              ∀ i < c,
                0 < Nat.min (ζ i).1.1 (ζ i).1.2 := by
            intro i hi
            have hnot := hfirst.2 i hi
            simp only [forgetLVLabels, reachedConsensus,
              not_or] at hnot
            exact Nat.lt_min.mpr
              ⟨Nat.pos_of_ne_zero hnot.1,
                Nat.pos_of_ne_zero hnot.2⟩
          have hlabel :
              labeledBadCountUpTo ζ c ≤
                pseudoBadCountUpTo v ω
                  (pseudoActiveOrdinalTime c ω) :=
            labeledBadCountUpTo_embedded_le_pseudo
              v ω hinfinite hfreeze c hpositive
          have hcActive :
              pseudoKthActiveAt c
                (pseudoActiveOrdinalTime c ω) ω :=
            pseudoActiveOrdinalTime_isKth
              (pseudoKthActiveAt_exists ω hinfinite c)
          have hτActive :
              pseudoKthActiveAt τ
                (pseudoActiveOrdinalTime τ ω) ω :=
            pseudoActiveOrdinalTime_isKth
              (pseudoKthActiveAt_exists ω hinfinite τ)
          have hactiveLe :
              pseudoActiveOrdinalTime c ω ≤
                pseudoActiveOrdinalTime τ ω :=
            pseudoKthActiveAt_time_le
              hcτ hcActive hτActive
          have hbirthEq :
              birthsUpTo η
                  (pseudoActiveOrdinalTime τ ω) =
                birthsUpTo η τ := by
            apply birthsUpTo_eq_of_zero_from
            · exact pseudoKthActiveAt_index_le_time hτActive
            · exact hzeroAfter
          have hbound :
              labeledBadCountUpTo ζ c ≤
                birthsUpTo η τ := by
            calc
              labeledBadCountUpTo ζ c ≤
                  pseudoBadCountUpTo v ω
                    (pseudoActiveOrdinalTime c ω) := hlabel
              _ ≤ pseudoBadCountUpTo v ω
                    (pseudoActiveOrdinalTime τ ω) :=
                pseudoBadCountUpTo_mono v ω hactiveLe
              _ ≤ birthsUpTo η
                    (pseudoActiveOrdinalTime τ ω) := by
                change pseudoBadCountUpTo v ω
                    (pseudoActiveOrdinalTime τ ω) ≤
                  birthsUpTo (fun i => (ω i).2)
                    (pseudoActiveOrdinalTime τ ω)
                exact hbadPhysical
                  (pseudoActiveOrdinalTime τ ω)
              _ = birthsUpTo η τ := hbirthEq
          simpa only [ζ, η, labeledBadCountBeforeConsensus,
            birthsBeforeExtinction, hcons, hext] using hbound

/-- Unconditional chain domination obtained directly from (D1)--(D2), the
start domination, and almost-sure extinction of the auxiliary chain. -/
theorem chain_domination_unconditional
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState)
    (N : BirthDeathChain) (n0 : Nat)
    (hStart : Nat.min s0.1 s0.2 ≤ n0)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    (∀ t : Nat,
      consensusTail v params s0 t ≤ extinctionTail N n0 t) ∧
    (∀ L : Nat,
      labeledBadTail v params s0 L ≤ birthTail N n0 L) := by
  let P := lvPseudoCouplingPathMeasure v params
    hGamma0 hGamma1 N hDom (s0, .idle) n0
  constructor
  · intro t
    rw [
      lvPseudoCouplingPathMeasure_consensusTail_law
        v params hGamma0 hGamma1 N hDom s0 n0
          hStart hExtinct t,
      lvPseudoCouplingPathMeasure_extinctionTail_law
        v params hGamma0 hGamma1 N hDom
          (s0, .idle) n0 t]
    apply measure_mono_ae
    filter_upwards [
      lvPseudoCouplingPathMeasure_consensus_le_extinction
        v params hGamma0 hGamma1 N hDom
          (s0, .idle) n0 hStart hExtinct] with ω hdom
    exact fun htail => htail.trans hdom
  · intro L
    rw [
      lvPseudoCouplingPathMeasure_labeledBadTail_law
        v params hGamma0 hGamma1 N hDom s0 n0
          hStart hExtinct L,
      lvPseudoCouplingPathMeasure_birthTail_law
        v params hGamma0 hGamma1 N hDom
          (s0, .idle) n0 L]
    apply measure_mono_ae
    filter_upwards [
      lvPseudoCouplingPathMeasure_badBefore_le_birthsBefore
        v params hGamma0 hGamma1 N hDom
          (s0, .idle) n0 hStart hExtinct] with ω hdom
    exact fun htail => htail.trans hdom

end LVConsensus
