import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal

namespace LVConsensus

/-!
# Reaction-labelled Lotka--Volterra dynamics

The ordinary `lvKernel` records only the population after a jump.  In the NSD
model an individual death and a competitive death can have the same source and
target states, so the reaction count `J` from the paper is not a functional of
an ordinary state path.  This file retains the reaction that produced every
new state.  Forgetting the label recovers `lvKernel` exactly.
-/

/-- The reaction used in one jump of the LV chain.  `idle` is used only when
the total propensity is zero and the state is held fixed. -/
inductive LVReaction where
  | idle
  | birth0
  | birth1
  | death0
  | death1
  | inter0
  | inter1
  | intra0
  | intra1
  deriving DecidableEq, Repr, Countable

/-- A labelled state stores the population and the reaction used to enter it.
The label in the initial state is `idle`. -/
abbrev LabeledPopState := PopState × LVReaction

instance : MeasurableSpace LVReaction := ⊤
instance : MeasurableSingletonClass LVReaction := by infer_instance

/-- Population reached by a reaction.  The two interspecific reactions have
the same target in the SD model but retain different labels. -/
def lvReactionTarget (v : LVVariant) (s : PopState) : LVReaction → PopState
  | .idle => s
  | .birth0 => (s.1 + 1, s.2)
  | .birth1 => (s.1, s.2 + 1)
  | .death0 => (s.1 - 1, s.2)
  | .death1 => (s.1, s.2 - 1)
  | .inter0 =>
      match v with
      | .selfDestructive => (s.1 - 1, s.2 - 1)
      | .nonSelfDestructive => (s.1, s.2 - 1)
  | .inter1 =>
      match v with
      | .selfDestructive => (s.1 - 1, s.2 - 1)
      | .nonSelfDestructive => (s.1 - 1, s.2)
  | .intra0 =>
      match v with
      | .selfDestructive => (s.1 - 2, s.2)
      | .nonSelfDestructive => (s.1 - 1, s.2)
  | .intra1 =>
      match v with
      | .selfDestructive => (s.1, s.2 - 2)
      | .nonSelfDestructive => (s.1, s.2 - 1)

/-- Unnormalised propensity of a labelled reaction. -/
noncomputable def lvReactionWeight (params : LVParams) (s : PopState) :
    LVReaction → ℝ
  | .idle => 0
  | .birth0 => params.beta * s.1
  | .birth1 => params.beta * s.2
  | .death0 => params.delta * s.1
  | .death1 => params.delta * s.2
  | .inter0 => params.alpha0 * s.1 * s.2
  | .inter1 => params.alpha1 * s.1 * s.2
  | .intra0 => params.gamma0 * (s.1 * (s.1 - 1) / 2)
  | .intra1 => params.gamma1 * (s.2 * (s.2 - 1) / 2)

/-- One-step labelled LV kernel.  Its first-coordinate pushforward is
`lvKernel v params`. -/
noncomputable def lvLabeledKernel (v : LVVariant) (params : LVParams) :
    Kernel LabeledPopState LabeledPopState :=
  Kernel.ofFunOfCountable fun z : LabeledPopState =>
    let s := z.1
    let φ := lvTotalPropensity params s
    if _hφ : φ = 0 then
      Measure.dirac (s, .idle)
    else
      let invφ := ENNReal.ofReal (1 / φ)
      invφ •
        (ENNReal.ofReal (lvReactionWeight params s .birth0) •
              Measure.dirac (lvReactionTarget v s .birth0, .birth0) +
          ENNReal.ofReal (lvReactionWeight params s .birth1) •
              Measure.dirac (lvReactionTarget v s .birth1, .birth1) +
          ENNReal.ofReal (lvReactionWeight params s .death0) •
              Measure.dirac (lvReactionTarget v s .death0, .death0) +
          ENNReal.ofReal (lvReactionWeight params s .death1) •
              Measure.dirac (lvReactionTarget v s .death1, .death1) +
          ENNReal.ofReal (lvReactionWeight params s .inter0) •
              Measure.dirac (lvReactionTarget v s .inter0, .inter0) +
          ENNReal.ofReal (lvReactionWeight params s .inter1) •
              Measure.dirac (lvReactionTarget v s .inter1, .inter1) +
          ENNReal.ofReal (lvReactionWeight params s .intra0) •
              Measure.dirac (lvReactionTarget v s .intra0, .intra0) +
          ENNReal.ofReal (lvReactionWeight params s .intra1) •
              Measure.dirac (lvReactionTarget v s .intra1, .intra1))

private lemma lvReactionWeight_nonneg
    (params : LVParams) (s : PopState) (r : LVReaction) :
    0 ≤ lvReactionWeight params s r := by
  rcases s with ⟨a, b⟩
  cases r <;> simp only [lvReactionWeight]
  · exact le_rfl
  · exact mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  · exact mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
  · exact mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  · exact mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
  · exact mul_nonneg
      (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  · exact mul_nonneg
      (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  · apply mul_nonneg params.gamma0_nonneg
    apply div_nonneg _ (by norm_num)
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · norm_num
    · exact mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr ha))
  · apply mul_nonneg params.gamma1_nonneg
    apply div_nonneg _ (by norm_num)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · norm_num
    · exact mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr hb))

private lemma lvReactionWeight_sum
    (params : LVParams) (s : PopState) :
    lvReactionWeight params s .birth0 +
      lvReactionWeight params s .birth1 +
      lvReactionWeight params s .death0 +
      lvReactionWeight params s .death1 +
      lvReactionWeight params s .inter0 +
      lvReactionWeight params s .inter1 +
      lvReactionWeight params s .intra0 +
      lvReactionWeight params s .intra1 =
        lvTotalPropensity params s := by
  rcases s with ⟨a, b⟩
  simp only [lvReactionWeight, lvTotalPropensity]
  ring

instance lvLabeledKernel_isMarkovKernel
    (v : LVVariant) (params : LVParams) :
    IsMarkovKernel (lvLabeledKernel v params) where
  isProbabilityMeasure z := ⟨by
    rcases z with ⟨s, old⟩
    simp only [lvLabeledKernel, Kernel.ofFunOfCountable,
      Kernel.coe_mk]
    by_cases hφ : lvTotalPropensity params s = 0
    · simp [hφ]
    · rw [dif_neg hφ]
      simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      have h0 := lvReactionWeight_nonneg params s .birth0
      have h1 := lvReactionWeight_nonneg params s .birth1
      have h2 := lvReactionWeight_nonneg params s .death0
      have h3 := lvReactionWeight_nonneg params s .death1
      have h4 := lvReactionWeight_nonneg params s .inter0
      have h5 := lvReactionWeight_nonneg params s .inter1
      have h6 := lvReactionWeight_nonneg params s .intra0
      have h7 := lvReactionWeight_nonneg params s .intra1
      have hφnn : 0 ≤ lvTotalPropensity params s := by
        rw [← lvReactionWeight_sum params s]
        positivity
      have hφpos : 0 < lvTotalPropensity params s :=
        lt_of_le_of_ne hφnn (Ne.symm hφ)
      rw [← ENNReal.ofReal_add h0 h1,
        ← ENNReal.ofReal_add (by positivity : 0 ≤
          lvReactionWeight params s .birth0 +
            lvReactionWeight params s .birth1) h2,
        ← ENNReal.ofReal_add (by positivity : 0 ≤
          lvReactionWeight params s .birth0 +
            lvReactionWeight params s .birth1 +
            lvReactionWeight params s .death0) h3,
        ← ENNReal.ofReal_add (by positivity : 0 ≤
          lvReactionWeight params s .birth0 +
            lvReactionWeight params s .birth1 +
            lvReactionWeight params s .death0 +
            lvReactionWeight params s .death1) h4,
        ← ENNReal.ofReal_add (by positivity : 0 ≤
          lvReactionWeight params s .birth0 +
            lvReactionWeight params s .birth1 +
            lvReactionWeight params s .death0 +
            lvReactionWeight params s .death1 +
            lvReactionWeight params s .inter0) h5,
        ← ENNReal.ofReal_add (by positivity : 0 ≤
          lvReactionWeight params s .birth0 +
            lvReactionWeight params s .birth1 +
            lvReactionWeight params s .death0 +
            lvReactionWeight params s .death1 +
            lvReactionWeight params s .inter0 +
            lvReactionWeight params s .inter1) h6,
        ← ENNReal.ofReal_add (by positivity : 0 ≤
          lvReactionWeight params s .birth0 +
            lvReactionWeight params s .birth1 +
            lvReactionWeight params s .death0 +
            lvReactionWeight params s .death1 +
            lvReactionWeight params s .inter0 +
            lvReactionWeight params s .inter1 +
            lvReactionWeight params s .intra0) h7,
        lvReactionWeight_sum,
        ← ENNReal.ofReal_mul (by positivity :
          0 ≤ 1 / lvTotalPropensity params s),
        one_div_mul_cancel hφ, ENNReal.ofReal_one]⟩

/-- Forgetting a one-step reaction label gives exactly the original LV
transition kernel.  This is the local consistency fact used to identify the
state-path projection of the labelled chain. -/
theorem lvLabeledKernel_map_fst
    (v : LVVariant) (params : LVParams) (z : LabeledPopState) :
    (lvLabeledKernel v params z).map Prod.fst =
      lvKernel v params z.1 := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  rcases z with ⟨s, old⟩
  simp only [lvLabeledKernel, lvKernel, Kernel.ofFunOfCountable,
    Kernel.coe_mk]
  have hind : ∀ (x : PopState) (r : LVReaction),
      (Prod.fst ⁻¹' A).indicator (1 : LabeledPopState → ℝ≥0∞) (x, r) =
        A.indicator (1 : PopState → ℝ≥0∞) x := by
    intro x r
    rfl
  by_cases hφ : lvTotalPropensity params s = 0
  · simp only [hφ, dif_pos, Measure.dirac_apply]
    exact hind s .idle
  · rw [dif_neg hφ, dif_neg hφ]
    rcases s with ⟨a, b⟩
    cases v <;>
      simp only [lvReactionWeight, lvReactionTarget,
        Measure.smul_apply, Measure.add_apply, smul_eq_mul,
        Measure.dirac_apply] <;>
      rw [hind, hind, hind, hind, hind, hind, hind, hind]

/-- The second coordinate exposes the exact reaction probability, including
when several reactions have the same population-state target. -/
theorem lvLabeledKernel_reaction_probability
    (v : LVVariant) (params : LVParams) (z : LabeledPopState)
    (r : LVReaction) :
    lvLabeledKernel v params z {z' | z'.2 = r} =
      if hφ : lvTotalPropensity params z.1 = 0 then
        if r = .idle then 1 else 0
      else
        ENNReal.ofReal (1 / lvTotalPropensity params z.1) *
          ENNReal.ofReal (lvReactionWeight params z.1 r) := by
  rcases z with ⟨s, old⟩
  simp only [lvLabeledKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  by_cases hφ : lvTotalPropensity params s = 0
  · rw [dif_pos hφ, dif_pos hφ]
    cases r <;> simp [Measure.dirac_apply]
  · rw [dif_neg hφ, dif_neg hφ]
    cases r <;>
      simp [lvReactionWeight, Measure.smul_apply, Measure.add_apply,
        Measure.dirac_apply]

/-- A labelled one-step sample records the actual target of its reaction
label almost surely. -/
theorem lvLabeledKernel_ae_reactionTarget
    (v : LVVariant) (params : LVParams) (z : LabeledPopState) :
    ∀ᵐ z' ∂lvLabeledKernel v params z,
      z'.1 = lvReactionTarget v z.1 z'.2 := by
  rw [ae_iff]
  rcases z with ⟨s, old⟩
  simp only [lvLabeledKernel, Kernel.ofFunOfCountable,
    Kernel.coe_mk]
  by_cases hφ : lvTotalPropensity params s = 0
  · rw [dif_pos hφ]
    simp [Measure.dirac_apply, lvReactionTarget]
  · rw [dif_neg hφ]
    cases v <;>
      simp [Measure.smul_apply, Measure.add_apply,
        Measure.dirac_apply, lvReactionTarget]

private lemma compProd_map_prodMap
    {A A' B B' : Type*}
    [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [MeasurableSpace B']
    (μ : Measure A) (ν : Measure A')
    (κ : Kernel A B) (κ' : Kernel A' B')
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    (f : A → A') (g : B → B')
    (hf : Measurable f) (hg : Measurable g)
    (hμ : μ.map f = ν)
    (hκ : ∀ a, (κ a).map g = κ' (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = ν ⊗ₘ κ' := by
  letI : SFinite ν := hμ ▸ (inferInstance : SFinite (μ.map f))
  ext S hS
  rw [Measure.map_apply (hf.prodMap hg) hS,
    Measure.compProd_apply (hS.preimage (hf.prodMap hg)),
    Measure.compProd_apply hS]
  rw [← hμ, MeasureTheory.lintegral_map
    (Kernel.measurable_kernel_prodMk_left hS) hf]
  apply lintegral_congr
  intro a
  have hpre :
      Prod.mk a ⁻¹' (Prod.map f g ⁻¹' S) =
        g ⁻¹' (Prod.mk (f a) ⁻¹' S) := rfl
  rw [hpre, ← hκ a]
  exact (Measure.map_apply hg
    (hS.preimage (Measurable.prodMk measurable_const measurable_id))).symm

private def forgetIic (n : ℕ)
    (h : ∀ _ : Finset.Iic n, LabeledPopState) :
    ∀ _ : Finset.Iic n, PopState :=
  fun i => (h i).1

private lemma measurable_forgetIic (n : ℕ) :
    Measurable (forgetIic n) :=
  measurable_pi_lambda _ fun i =>
    measurable_fst.comp (measurable_pi_apply i)

private def forgetIocSingleton (n : ℕ)
    (h : ∀ _ : Finset.Ioc n (n + 1), LabeledPopState) :
    ∀ _ : Finset.Ioc n (n + 1), PopState :=
  fun i => (h i).1

private lemma measurable_forgetIocSingleton (n : ℕ) :
    Measurable (forgetIocSingleton n) :=
  measurable_pi_lambda _ fun i =>
    measurable_fst.comp (measurable_pi_apply i)

private lemma forgetIic_comp_IicProdIoc (n : ℕ) :
    (forgetIic (n + 1)) ∘
        (IicProdIoc (X := fun _ => LabeledPopState) n (n + 1)) =
      (IicProdIoc (X := fun _ => PopState) n (n + 1)) ∘
        Prod.map (forgetIic n) (forgetIocSingleton n) := by
  funext ⟨x, y⟩ ⟨i, hi⟩
  simp only [Function.comp_apply, Prod.map_apply, forgetIic,
    forgetIocSingleton, IicProdIoc]
  by_cases h : i ≤ n <;> simp [h]

private lemma forgetIocSingleton_comp_piSingleton (n : ℕ) :
    (forgetIocSingleton n) ∘
        (MeasurableEquiv.piSingleton
          (X := fun _ => LabeledPopState) n) =
      (MeasurableEquiv.piSingleton
          (X := fun _ => PopState) n) ∘ Prod.fst := by
  funext z i
  simp [Function.comp_apply, forgetIocSingleton,
    MeasurableEquiv.piSingleton]

private lemma homogeneousHistoryKernel_map_forget
    (v : LVVariant) (params : LVParams) (n : ℕ)
    (h : ∀ _ : Finset.Iic n, LabeledPopState) :
    (homogeneousHistoryKernel (lvLabeledKernel v params) n h).map
        Prod.fst =
      homogeneousHistoryKernel (lvKernel v params) n
        (forgetIic n h) := by
  unfold homogeneousHistoryKernel
  rw [Kernel.comp_apply, Kernel.deterministic_apply (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _) _,
    Kernel.comp_apply, Kernel.deterministic_apply (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _) _]
  exact lvLabeledKernel_map_fst v params _

private lemma partialTraj_map_forget
    (v : LVVariant) (params : LVParams) (s0 : PopState) (n : ℕ) :
    let XL : ℕ → Type _ := fun _ => LabeledPopState
    let X : ℕ → Type _ := fun _ => PopState
    let κL : (t : ℕ) →
        Kernel (∀ i : Finset.Iic t, XL i) (XL (t + 1)) :=
      fun t => homogeneousHistoryKernel (lvLabeledKernel v params) t
    let κ : (t : ℕ) →
        Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
      fun t => homogeneousHistoryKernel (lvKernel v params) t
    let z0 : ∀ _ : Finset.Iic 0, XL 0 := fun _ => (s0, .idle)
    let x0 : ∀ _ : Finset.Iic 0, X 0 := fun _ => s0
    (partialTraj (X := XL) κL 0 n z0).map (forgetIic n) =
      partialTraj (X := X) κ 0 n x0 := by
  intro XL X κL κ z0 x0
  haveI : ∀ t, IsMarkovKernel (κL t) := fun t => by
    simp only [κL, XL, homogeneousHistoryKernel]
    infer_instance
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]
    infer_instance
  induction n with
  | zero =>
      rw [partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_forgetIic 0),
        partialTraj_self, Kernel.id_apply]
      congr 1
  | succ n ih =>
      rw [partialTraj_succ_of_le (Nat.zero_le n)]
      rw [Kernel.map_apply _ measurable_IicProdIoc, Kernel.comp_apply]
      have hPairMeas : Measurable
          (Prod.map (forgetIic n) (forgetIocSingleton n)) :=
        (measurable_forgetIic n).prodMap
          (measurable_forgetIocSingleton n)
      have hIicMeas : Measurable
          (IicProdIoc (X := fun _ => PopState) n (n + 1)) :=
        measurable_IicProdIoc
      rw [Measure.map_map (measurable_forgetIic (n + 1))
          measurable_IicProdIoc,
        forgetIic_comp_IicProdIoc n,
        ← Measure.map_map hIicMeas hPairMeas]
      rw [← Measure.compProd_eq_comp_prod]
      have hstep :
          ∀ h,
            (((κL n).map
                (MeasurableEquiv.piSingleton
                  (X := fun _ => LabeledPopState) n)) h).map
                (forgetIocSingleton n) =
              ((κ n).map
                (MeasurableEquiv.piSingleton
                  (X := fun _ => PopState) n)) (forgetIic n h) := by
        intro h
        rw [← Kernel.map_apply _ (measurable_forgetIocSingleton n),
          ← Kernel.map_comp_right _
            (MeasurableEquiv.piSingleton
              (X := fun _ => LabeledPopState) n).measurable
            (measurable_forgetIocSingleton n),
          forgetIocSingleton_comp_piSingleton n,
          Kernel.map_comp_right _ measurable_fst
            (MeasurableEquiv.piSingleton
              (X := fun _ => PopState) n).measurable,
          Kernel.map_apply _
            (MeasurableEquiv.piSingleton
              (X := fun _ => PopState) n).measurable,
          Kernel.map_apply _ measurable_fst,
          homogeneousHistoryKernel_map_forget v params n h,
          Kernel.map_apply _
            (MeasurableEquiv.piSingleton
              (X := fun _ => PopState) n).measurable]
      rw [compProd_map_prodMap
        (partialTraj (X := XL) κL 0 n z0)
        (partialTraj (X := X) κ 0 n x0)
        ((κL n).map
          (MeasurableEquiv.piSingleton
            (X := fun _ => LabeledPopState) n))
        ((κ n).map
          (MeasurableEquiv.piSingleton
            (X := fun _ => PopState) n))
        (forgetIic n) (forgetIocSingleton n)
        (measurable_forgetIic n)
        (measurable_forgetIocSingleton n) ih hstep]
      rw [Measure.compProd_eq_comp_prod,
        ← Kernel.comp_apply,
        ← Kernel.map_apply _ hIicMeas]
      exact congrArg
        (fun J : Kernel (∀ i : Finset.Iic 0, X i)
            (∀ i : Finset.Iic (n + 1), X i) => J x0)
        (partialTraj_succ_of_le (X := X) (κ := κ) (Nat.zero_le n)).symm

/-- Forget the reaction labels along a labelled trajectory. -/
def forgetLVLabels (ω : ℕ → LabeledPopState) : ℕ → PopState :=
  fun t => (ω t).1

lemma measurable_forgetLVLabels :
    Measurable forgetLVLabels :=
  measurable_pi_lambda _ fun t =>
    measurable_fst.comp (measurable_pi_apply t)

/-- Path-space law of the labelled chain. -/
noncomputable def lvLabeledPathMeasure
    (v : LVVariant) (params : LVParams) (s0 : PopState) :
    Measure (ℕ → LabeledPopState) :=
  homogeneousPathMeasure (Measure.dirac (s0, .idle))
    (lvLabeledKernel v params)

/-- The state-path projection of the labelled chain has exactly the original
LV path law.  Thus labels add reaction information without changing any event
that depends only on population states. -/
theorem lvLabeledPathMeasure_map_forget
    (v : LVVariant) (params : LVParams) (s0 : PopState) :
    (lvLabeledPathMeasure v params s0).map forgetLVLabels =
      lvPathMeasure v params s0 := by
  let XL : ℕ → Type _ := fun _ => LabeledPopState
  let X : ℕ → Type _ := fun _ => PopState
  let κL : (t : ℕ) →
      Kernel (∀ i : Finset.Iic t, XL i) (XL (t + 1)) :=
    fun t => homogeneousHistoryKernel (lvLabeledKernel v params) t
  let κ : (t : ℕ) →
      Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel (lvKernel v params) t
  haveI : ∀ t, IsMarkovKernel (κL t) := fun t => by
    simp only [κL, XL, homogeneousHistoryKernel]
    infer_instance
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]
    infer_instance
  let z0 : ∀ _ : Finset.Iic 0, XL 0 := fun _ => (s0, .idle)
  let x0 : ∀ _ : Finset.Iic 0, X 0 := fun _ => s0
  have hL :
      lvLabeledPathMeasure v params s0 =
        traj (X := XL) κL 0 z0 := by
    simp only [lvLabeledPathMeasure, homogeneousPathMeasure,
      trajMeasure, κL, XL, z0]
    rw [Measure.map_dirac'
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => LabeledPopState)).symm.measurable]
    exact Measure.dirac_bind (Kernel.measurable _) _
  have hR :
      lvPathMeasure v params s0 =
        traj (X := X) κ 0 x0 := by
    simp only [lvPathMeasure, homogeneousPathMeasure,
      trajMeasure, κ, X, x0]
    rw [Measure.map_dirac'
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => PopState)).symm.measurable]
    exact Measure.dirac_bind (Kernel.measurable _) _
  rw [hL, hR]
  have hprojected :
      IsProjectiveLimit
        ((traj (X := XL) κL 0 z0).map forgetLVLabels)
        (inducedFamily
          (fun n => partialTraj (X := X) κ 0 n x0)) := by
    rw [isProjectiveLimit_nat_iff
      (isProjectiveMeasureFamily_partialTraj κ x0)]
    intro n
    rw [inducedFamily_Iic,
      Measure.map_map (measurable_frestrictLe n)
        measurable_forgetLVLabels,
      show (frestrictLe n : (ℕ → PopState) → _) ∘
          forgetLVLabels =
        forgetIic n ∘
          (frestrictLe n : (ℕ → LabeledPopState) → _) by
        funext ω i
        rfl,
      ← Measure.map_map (measurable_forgetIic n)
        (measurable_frestrictLe n),
      traj_map_frestrictLe_apply]
    exact partialTraj_map_forget v params s0 n
  have horiginal :
      IsProjectiveLimit
        (traj (X := X) κ 0 x0)
        (inducedFamily
          (fun n => partialTraj (X := X) κ 0 n x0)) := by
    rw [traj_apply]
    exact isProjectiveLimit_trajFun
      (X := X) (κ := κ) 0 x0
  exact hprojected.unique horiginal

/-- A labelled non-competitive event is bad when it reduces the absolute gap
between the currently larger and smaller populations. -/
def isBadNoncompetitiveReaction (s : PopState) (r : LVReaction) : Prop :=
  if s.2 < s.1 then
    r = .death0 ∨ r = .birth1
  else if s.1 < s.2 then
    r = .death1 ∨ r = .birth0
  else
    False

/-- Number of bad non-competitive reactions in the first `t` labelled jumps.
The reaction stored at coordinate `i+1` labels the jump out of coordinate `i`. -/
noncomputable def labeledBadCountUpTo
    (ω : ℕ → LabeledPopState) (t : ℕ) : ℕ := by
  classical
  exact Finset.sum (Finset.range t) fun i =>
    if isBadNoncompetitiveReaction (ω i).1 (ω (i + 1)).2 then 1 else 0

/-- Number of labelled bad non-competitive reactions before the projected
population path reaches consensus.  As for the original path functional, this
is defined as zero on paths that never reach consensus. -/
noncomputable def labeledBadCountBeforeConsensus
    (ω : ℕ → LabeledPopState) : ℕ :=
  match consensusTime (forgetLVLabels ω) with
  | ⊤ => 0
  | (t : ℕ) => labeledBadCountUpTo ω t

/-- Tail probability of the paper's reaction-level count `J`. -/
noncomputable def labeledBadTail
    (v : LVVariant) (params : LVParams) (s0 : PopState) (t : ℕ) :
    ℝ≥0∞ :=
  lvLabeledPathMeasure v params s0
    {ω | labeledBadCountBeforeConsensus ω ≥ t}

/-- Extended expectation of the consensus time, expressed by its tail sum.
This assigns infinite expectation to a positive-probability non-consensus
event, unlike the legacy `untopD 0` path functional. -/
noncomputable def expectedConsensusTimeTail
    (v : LVVariant) (params : LVParams) (s0 : PopState) : ℝ≥0∞ :=
  ∑' t : ℕ, consensusTail v params s0 (t + 1)

/-- Expected number of the paper's labelled bad non-competitive reactions,
expressed by the discrete tail-sum formula. -/
noncomputable def expectedLabeledBadCount
    (v : LVVariant) (params : LVParams) (s0 : PopState) : ℝ≥0∞ :=
  ∑' t : ℕ, labeledBadTail v params s0 (t + 1)

/-- Births and individual deaths are precisely the paper's non-competitive
individual reactions. -/
def isIndividualReaction : LVReaction → Prop
  | .birth0 | .birth1 | .death0 | .death1 => True
  | _ => False

/-- Number of individual reactions in the first `t` labelled jumps. -/
noncomputable def labeledIndividualCountUpTo
    (ω : ℕ → LabeledPopState) (t : ℕ) : ℕ := by
  classical
  exact Finset.sum (Finset.range t) fun i =>
    if isIndividualReaction (ω (i + 1)).2 then 1 else 0

/-- Number of individual reactions before projected consensus. -/
noncomputable def labeledIndividualCountBeforeConsensus
    (ω : ℕ → LabeledPopState) : ℕ :=
  match consensusTime (forgetLVLabels ω) with
  | ⊤ => 0
  | (t : ℕ) => labeledIndividualCountUpTo ω t

/-- The two interspecific labels are precisely the competitive reactions. -/
def isCompetitiveReaction : LVReaction → Prop
  | .inter0 | .inter1 => True
  | _ => False

/-- Number of competitive reactions in the first `t` labelled jumps. -/
noncomputable def labeledCompetitiveCountUpTo
    (ω : ℕ → LabeledPopState) (t : ℕ) : ℕ := by
  classical
  exact Finset.sum (Finset.range t) fun i =>
    if isCompetitiveReaction (ω (i + 1)).2 then 1 else 0

/-- Number of competitive reactions before projected consensus. -/
noncomputable def labeledCompetitiveCountBeforeConsensus
    (ω : ℕ → LabeledPopState) : ℕ :=
  match consensusTime (forgetLVLabels ω) with
  | ⊤ => 0
  | (t : ℕ) => labeledCompetitiveCountUpTo ω t

private lemma consensusTime_forget_eq_one_of_two_one_to_two_zero
    (ω : ℕ → LabeledPopState)
    (h0 : (ω 0).1 = (2, 1))
    (h1 : (ω 1).1 = (2, 0)) :
    consensusTime (forgetLVLabels ω) = (1 : ℕ) := by
  rw [consensusTime_eq_coe_iff]
  constructor
  · simp [forgetLVLabels, h1, reachedConsensus]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp [forgetLVLabels, h0, reachedConsensus]

/-- Audit lemma for the SD lower-bound proof: from `(2,1)`, an individual
death of the lone minority reaches consensus immediately.  Hence the event
that at least two individual reactions occur excludes this possible first
individual mark; conditioning on that event cannot preserve the original
i.i.d. fair-mark law. -/
theorem sd_conditioning_on_two_individuals_excludes_first_minority_death
    (ω : ℕ → LabeledPopState)
    (h0 : (ω 0).1 = (2, 1))
    (h1 : (ω 1).1 = (2, 0))
    (hr : (ω 1).2 = .death1) :
    labeledIndividualCountBeforeConsensus ω = 1 := by
  classical
  rw [labeledIndividualCountBeforeConsensus,
    consensusTime_forget_eq_one_of_two_one_to_two_zero ω h0 h1]
  change (if isIndividualReaction (ω 1).2 then 1 else 0) = 1
  simp [hr, isIndividualReaction]

/-- Audit lemma for the NSD upper-bound proof: from `(2,1)`, a competitive
death of the lone minority reaches consensus immediately.  Hence conditioning
on two or more competitive reactions reveals that the first competitive mark
was not this mark. -/
theorem nsd_conditioning_on_two_competitions_excludes_first_minority_death
    (ω : ℕ → LabeledPopState)
    (h0 : (ω 0).1 = (2, 1))
    (h1 : (ω 1).1 = (2, 0))
    (hr : (ω 1).2 = .inter0) :
    labeledCompetitiveCountBeforeConsensus ω = 1 := by
  classical
  rw [labeledCompetitiveCountBeforeConsensus,
    consensusTime_forget_eq_one_of_two_one_to_two_zero ω h0 h1]
  change (if isCompetitiveReaction (ω 1).2 then 1 else 0) = 1
  simp [hr, isCompetitiveReaction]

end LVConsensus
