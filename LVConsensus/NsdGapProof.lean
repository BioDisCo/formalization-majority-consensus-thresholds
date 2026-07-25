import LVConsensus.NsdGapSymmetry
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus

noncomputable def fairCoin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac false +
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac true

instance : IsProbabilityMeasure fairCoin := by
  refine ⟨?_⟩
  simp [fairCoin]
  calc
    (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 2 * 2⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

noncomputable def fairCoins : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => fairCoin)

instance : IsProbabilityMeasure fairCoins := by
  unfold fairCoins
  infer_instance

def fairStep (i : ℕ) (ω : ℕ → Bool) : ℝ :=
  if ω i then 1 else -1

private lemma fairStep_measurable (i : ℕ) :
    Measurable (fairStep i) := by
  unfold fairStep
  refine Measurable.ite ?_ measurable_const measurable_const
  change MeasurableSet ((fun ω : ℕ → Bool => ω i) ⁻¹' {true})
  exact (measurable_pi_apply i) (measurableSet_singleton true)

private lemma fairStep_indep :
    iIndepFun fairStep fairCoins := by
  have h := iIndepFun_infinitePi
    (P := fun _ : ℕ => fairCoin)
    (X := fun _ : ℕ => fun b : Bool => if b then (1 : ℝ) else -1)
    (fun _ => measurable_of_finite _)
  change iIndepFun
    (fun i ω => if ω i then (1 : ℝ) else -1)
    (Measure.infinitePi fun _ : ℕ => fairCoin)
  exact h

private lemma fairCoin_false :
    fairCoin {false} = (2 : ℝ≥0∞)⁻¹ := by
  simp [fairCoin, Measure.smul_apply]

private lemma fairCoin_true :
    fairCoin {true} = (2 : ℝ≥0∞)⁻¹ := by
  simp [fairCoin, Measure.smul_apply]

private lemma fairStep_ident (i j : ℕ) :
    IdentDistrib (fairStep i) (fairStep j) fairCoins fairCoins := by
  refine ⟨(fairStep_measurable i).aemeasurable,
    (fairStep_measurable j).aemeasurable, ?_⟩
  let f : Bool → ℝ := fun b => if b then 1 else -1
  change Measure.map (f ∘ fun ω : ℕ → Bool => ω i)
      (Measure.infinitePi fun _ : ℕ => fairCoin) =
    Measure.map (f ∘ fun ω : ℕ → Bool => ω j)
      (Measure.infinitePi fun _ : ℕ => fairCoin)
  calc
    Measure.map (f ∘ fun ω : ℕ → Bool => ω i)
        (Measure.infinitePi fun _ : ℕ => fairCoin) =
      Measure.map f
        (Measure.map (fun ω : ℕ → Bool => ω i)
          (Measure.infinitePi fun _ : ℕ => fairCoin)) := by
            exact (Measure.map_map (measurable_of_finite _)
              (measurable_pi_apply i)).symm
    _ = Measure.map f fairCoin := by
          rw [Measure.infinitePi_map_eval]
    _ = Measure.map f
        (Measure.map (fun ω : ℕ → Bool => ω j)
          (Measure.infinitePi fun _ : ℕ => fairCoin)) := by
          rw [Measure.infinitePi_map_eval]
    _ = Measure.map (f ∘ fun ω : ℕ → Bool => ω j)
        (Measure.infinitePi fun _ : ℕ => fairCoin) := by
          exact Measure.map_map (measurable_of_finite _)
            (measurable_pi_apply j)

private lemma fairStep_mean (i : ℕ) :
    ∫ ω, fairStep i ω ∂fairCoins = 0 := by
  let f : Bool → ℝ := fun b => if b then 1 else -1
  change (∫ ω, f (ω i)
      ∂Measure.infinitePi (fun _ : ℕ => fairCoin)) = 0
  have heval :
      Measure.map (fun ω : ℕ → Bool => ω i)
          (Measure.infinitePi (fun _ : ℕ => fairCoin)) = fairCoin :=
    Measure.infinitePi_map_eval (fun _ : ℕ => fairCoin) i
  calc
    (∫ ω, f (ω i)
        ∂Measure.infinitePi (fun _ : ℕ => fairCoin)) =
      ∫ b, f b ∂Measure.map (fun ω : ℕ → Bool => ω i)
        (Measure.infinitePi (fun _ : ℕ => fairCoin)) := by
        exact (integral_map
          (μ := Measure.infinitePi (fun _ : ℕ => fairCoin))
          (φ := fun ω : ℕ → Bool => ω i)
          (measurable_pi_apply i).aemeasurable
          (measurable_of_finite f).aestronglyMeasurable).symm
    _ = ∫ b, f b ∂fairCoin := by rw [heval]
    _ = 0 := by
      have hfint : Integrable f fairCoin :=
        (integrable_const (1 : ℝ)).mono
          (measurable_of_finite _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun b => by cases b <;> simp [f])
      rw [integral_fintype hfint]
      simp [fairCoin_false, fairCoin_true, Measure.real, f]

private lemma fairStep_variance (i : ℕ) :
    variance (fairStep i) fairCoins = 1 := by
  rw [variance_eq_integral (fairStep_measurable i).aemeasurable]
  rw [fairStep_mean]
  simp only [Pi.zero_apply, sub_zero]
  have hsquare : (fun ω => fairStep i ω ^ 2) = fun _ => (1 : ℝ) := by
    funext ω
    simp [fairStep]
  rw [hsquare, integral_const]
  simp

theorem fair_clt
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ θ : Real, 0 < θ ∧ ∃ n₀ : Nat, ∀ n, n₀ ≤ n →
      ENNReal.ofReal ε ≤ fairCoins {ω | ∃ k ∈ Finset.range (n + 1),
        θ * Real.sqrt n ≤ ∑ i ∈ Finset.range k, fairStep i ω} := by
  apply lemma_clt fairCoins fairStep
  · intro i
    filter_upwards [] with ω
    cases h : ω i <;> norm_num [fairStep, h]
  · exact fairStep_measurable
  · exact fairStep_indep
  · exact fairStep_ident
  · exact fairStep_mean
  · exact fairStep_variance
  · exact hε0
  · exact hε1

private lemma nsd_gap_kernel_fair
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (lvKernel .nonSelfDestructive params (a, b))
        {s : PopState | gap s = gap (a, b) + 1} = (2 : ℝ≥0∞)⁻¹ ∧
      (lvKernel .nonSelfDestructive params (a, b))
        {s : PopState | gap s = gap (a, b) - 1} = (2 : ℝ≥0∞)⁻¹ := by
  let K := lvKernel .nonSelfDestructive params
  let P : Set PopState := {s | gap s = gap (a, b) + 1}
  let M : Set PopState := {s | gap s = gap (a, b) - 1}
  have hsym : K (a, b) P = K (a, b) M :=
    nsd_gap_kernel_symmetric_unconditional params hNeutral hBetaDelta hGamma0 hGamma1
      a b ha hb
  have hφ : lvTotalPropensity params (a, b) ≠ 0 := by
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hmain : 0 < (params.alpha0 + params.alpha1) * (a : ℝ) * (b : ℝ) := by
      positivity
    have hβ := params.beta_nonneg
    have hδ := params.delta_nonneg
    have hγ0 := params.gamma0_nonneg
    have hγ1 := params.gamma1_nonneg
    have htot : 0 < lvTotalPropensity params (a, b) := by
      simp only [lvTotalPropensity]
      have h1 : 0 ≤ params.beta * (a : ℝ) := by positivity
      have h2 : 0 ≤ params.beta * (b : ℝ) := by positivity
      have h3 : 0 ≤ params.delta * (a : ℝ) := by positivity
      have h4 : 0 ≤ params.delta * (b : ℝ) := by positivity
      have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have haquad : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := by
        have : 0 ≤ (a : ℝ) - 1 := by linarith
        positivity
      have hbquad : 0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 := by
        have : 0 ≤ (b : ℝ) - 1 := by linarith
        positivity
      have h5 : 0 ≤ params.gamma0 *
          ((a : ℝ) * ((a : ℝ) - 1) / 2) :=
        mul_nonneg hγ0 haquad
      have h6 : 0 ≤ params.gamma1 *
          ((b : ℝ) * ((b : ℝ) - 1) / 2) :=
        mul_nonneg hγ1 hbquad
      linarith
    exact ne_of_gt htot
  have hsupport : K (a, b) (P ∪ M) = 1 := by
    have hp0 : (a + 1, b) ∈ P := by simp [P, gap]; omega
    have hm0 : (a, b + 1) ∈ M := by simp [M, gap]; omega
    have hm1 : (a - 1, b) ∈ M := by simp [M, gap]; omega
    have hp1 : (a, b - 1) ∈ P := by simp [P, gap]; omega
    have hall : (a + 1, b) ∈ P ∪ M ∧
        (a, b + 1) ∈ P ∪ M ∧
        (a - 1, b) ∈ P ∪ M ∧
        (a, b - 1) ∈ P ∪ M :=
      ⟨Or.inl hp0, Or.inr hm0, Or.inr hm1, Or.inl hp1⟩
    have hform := lvKernel_nsd_apply params a b hφ
    haveI : IsProbabilityMeasure (K (a, b)) :=
      IsMarkovKernel.isProbabilityMeasure (a, b)
    have huniv : K (a, b) Set.univ = 1 := measure_univ
    change (lvKernel .nonSelfDestructive params) (a, b) (P ∪ M) = 1
    change (lvKernel .nonSelfDestructive params) (a, b) Set.univ = 1 at huniv
    rw [hform] at huniv ⊢
    simpa only [Measure.smul_apply, Measure.add_apply,
      Measure.dirac_apply_of_mem hall.1,
      Measure.dirac_apply_of_mem hall.2.1,
      Measure.dirac_apply_of_mem hall.2.2.1,
      Measure.dirac_apply_of_mem hall.2.2.2,
      Measure.dirac_apply_of_mem (Set.mem_univ (a + 1, b)),
      Measure.dirac_apply_of_mem (Set.mem_univ (a, b + 1)),
      Measure.dirac_apply_of_mem (Set.mem_univ (a - 1, b)),
      Measure.dirac_apply_of_mem (Set.mem_univ (a, b - 1)),
      smul_eq_mul, mul_one] using huniv
  have hdisj : Disjoint P M := by
    rw [Set.disjoint_left]
    intro s hp hm
    simp only [P, M, Set.mem_setOf_eq] at hp hm
    omega
  have hMmeas : MeasurableSet M :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hsum : K (a, b) P + K (a, b) M = 1 := by
    rw [← measure_union hdisj hMmeas]
    exact hsupport
  have hmul : K (a, b) P * 2 = 1 := by
    calc
      K (a, b) P * 2 = K (a, b) P + K (a, b) P := by ring
      _ = K (a, b) P + K (a, b) M := by rw [hsym]
      _ = 1 := hsum
  have hP : K (a, b) P = (2 : ℝ≥0∞)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left hmul
  exact ⟨hP, hsym.symm.trans hP⟩

private lemma nsd_kernel_no_large_coordinate_drop
    (params : LVParams) (s : PopState) :
    (lvKernel .nonSelfDestructive params) s
      {s' : PopState | s'.1 + 1 < s.1 ∨ s'.2 + 1 < s.2} = 0 := by
  rcases s with ⟨a, b⟩
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    rw [Measure.dirac_apply]
    simp
  · rw [lvKernel_nsd_apply params a b hφ]
    simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul,
      Measure.dirac_apply]
    rcases Nat.eq_zero_or_pos a with rfl | ha <;>
      rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have hbsub : b - 1 + 1 = b := by omega
      simp [hbsub] <;> omega
    · have hasub : a - 1 + 1 = a := by omega
      simp [hasub] <;> omega
    · have hasub : a - 1 + 1 = a := by omega
      have hbsub : b - 1 + 1 = b := by omega
      simp [hasub, hbsub] <;> omega

private lemma nsd_kernelIter_reachable
    (params : LVParams) (a b m : ℕ) :
    (kernelIter (lvKernel .nonSelfDestructive params) m) (a, b)
      {s : PopState | s.1 < a - m ∨ s.2 < b - m} = 0 := by
  let K := lvKernel .nonSelfDestructive params
  induction m with
  | zero =>
      simp [kernelIter_zero, Kernel.id_apply, Measure.dirac_apply]
  | succ m ih =>
      let Bad : Set PopState :=
        {s | s.1 < a - (m + 1) ∨ s.2 < b - (m + 1)}
      have hBad : MeasurableSet Bad :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [kernelIter_succ, Kernel.comp_apply' _ _ _ hBad]
      apply le_antisymm _ zero_le
      calc
        (∫⁻ y, K y Bad ∂(kernelIter K m) (a, b)) ≤
            ∫⁻ _y, (0 : ℝ≥0∞) ∂(kernelIter K m) (a, b) := by
          apply lintegral_mono_ae
          have hae :
              ∀ᵐ y ∂(kernelIter K m) (a, b),
                ¬(y.1 < a - m ∨ y.2 < b - m) :=
            compl_mem_ae_iff.mpr ih
          filter_upwards [hae] with y hy
          change K y Bad ≤ 0
          calc
            K y Bad ≤ K y
                {z : PopState | z.1 + 1 < y.1 ∨ z.2 + 1 < y.2} := by
              apply measure_mono
              intro z hz
              simp only [Bad, Set.mem_setOf_eq] at hz ⊢
              push_neg at hy
              omega
            _ = 0 := nsd_kernel_no_large_coordinate_drop params y
        _ = 0 := lintegral_zero

private lemma lvPathMeasure_reachable
    (params : LVParams) (a b m : ℕ) :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | (ω m).1 < a - m ∨ (ω m).2 < b - m} = 0 := by
  let K := lvKernel .nonSelfDestructive params
  let Bad : Set PopState := {s | s.1 < a - m ∨ s.2 < b - m}
  have hBad : MeasurableSet Bad :=
    DiscreteMeasurableSpace.forall_measurableSet _
  change homogeneousPathMeasure (Measure.dirac (a, b)) K
      ((fun ω : ℕ → PopState => ω m) ⁻¹' Bad) = 0
  rw [← Measure.map_apply (measurable_pi_apply m) hBad,
    homogeneousPathMeasure_dirac_marginal]
  exact nsd_kernelIter_reachable params a b m

private def closingBit (i : ℕ) (ω : ℕ → PopState) : Bool :=
  decide (gap (ω (i + 1)) = gap (ω i) - 1)

private def closingBits (m : ℕ) (ω : ℕ → PopState) : Fin m → Bool :=
  fun i => closingBit i ω

private lemma measurable_closingBits (m : ℕ) :
    Measurable (closingBits m) := by
  apply measurable_pi_lambda
  intro i
  unfold closingBits closingBit
  apply measurable_to_bool
  have heq :
      (fun c : ℕ → PopState =>
        decide (gap (c (i.val + 1)) = gap (c i.val) - 1)) ⁻¹' {true} =
        {c | gap (c (i.val + 1)) = gap (c i.val) - 1} := by
    ext c
    simp
  rw [heq]
  measurability

private def gapBitAtom (m : ℕ) (u : Fin m → Bool) :
    Set (ℕ → PopState) :=
  {ω | closingBits m ω = u}

private lemma measurableSet_gapBitAtom (m : ℕ) (u : Fin m → Bool) :
    MeasurableSet (gapBitAtom m u) :=
  (measurable_closingBits m) (measurableSet_singleton u)

private lemma gapBitAtom_cylinder (m : ℕ) (u : Fin m → Bool) :
    isCylinderUpTo m (gapBitAtom m u) := by
  intro ω η heq hω
  unfold gapBitAtom at hω ⊢
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [← hω]
  funext i
  unfold closingBits closingBit
  have hi : i.val + 1 ≤ m := by omega
  rw [heq i.val (by omega), heq (i.val + 1) hi]

private lemma closingBits_succ_iff
    (m : ℕ) (u : Fin (m + 1) → Bool) (ω : ℕ → PopState) :
    closingBits (m + 1) ω = u ↔
      closingBits m ω = (fun i => u i.castSucc) ∧
        closingBit m ω = u (Fin.last m) := by
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h i.castSucc
    · exact congrFun h (Fin.last m)
  · rintro ⟨hinit, hlast⟩
    funext i
    refine Fin.lastCases hlast (fun j => ?_) i
    exact congrFun hinit j

private def gapBitFuture (x : PopState) (bit : Bool) :
    Set (ℕ → PopState) :=
  if bit then
    {η | gap (η 1) = gap x - 1}
  else
    {η | gap (η 1) ≠ gap x - 1}

private lemma measurableSet_gapBitFuture (x : PopState) (bit : Bool) :
    MeasurableSet (gapBitFuture x bit) := by
  unfold gapBitFuture
  split <;> measurability

private lemma fresh_gapBitFuture_half
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (x : PopState) (hx0 : 0 < x.1) (hx1 : 0 < x.2) (bit : Bool) :
    homogeneousPathMeasure (Measure.dirac x)
        (lvKernel .nonSelfDestructive params) (gapBitFuture x bit) =
      (2 : ℝ≥0∞)⁻¹ := by
  let K := lvKernel .nonSelfDestructive params
  let T : Set PopState := {y | gap y = gap x - 1}
  have hT : MeasurableSet T :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hhalf := (nsd_gap_kernel_fair params hNeutral hInter hBetaDelta
    hGamma0 hGamma1 x.1 x.2 hx0 hx1).2
  have hmarg :
      homogeneousPathMeasure (Measure.dirac x) K
          ((fun η : ℕ → PopState => η 1) ⁻¹' T) = K x T := by
    rw [← Measure.map_apply (measurable_pi_apply 1) hT,
      homogeneousPathMeasure_dirac_marginal]
    simp [kernelIter_succ, kernelIter_zero, Kernel.comp_id]
  cases bit with
  | false =>
      change homogeneousPathMeasure (Measure.dirac x) K
          ((fun η : ℕ → PopState => η 1) ⁻¹' Tᶜ) = _
      rw [← Measure.map_apply (measurable_pi_apply 1) hT.compl,
        homogeneousPathMeasure_dirac_marginal]
      simp only [kernelIter_succ, kernelIter_zero, Kernel.comp_id]
      haveI : IsProbabilityMeasure (K x) :=
        IsMarkovKernel.isProbabilityMeasure x
      rw [prob_compl_eq_one_sub hT, hhalf]
      have hadd : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
        calc
          (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 2 * 2⁻¹ := by ring
          _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [← hadd]
      exact ENNReal.add_sub_cancel_left (by norm_num)
  | true =>
      change homogeneousPathMeasure (Measure.dirac x) K
          ((fun η : ℕ → PopState => η 1) ⁻¹' T) = _
      exact hmarg.trans hhalf

private def gapBitAtomState (m : ℕ) (u : Fin m → Bool) (x : PopState) :
    Set (ℕ → PopState) :=
  gapBitAtom m u ∩ {ω | ω m = x}

private lemma measurableSet_gapBitAtomState
    (m : ℕ) (u : Fin m → Bool) (x : PopState) :
    MeasurableSet (gapBitAtomState m u x) :=
  (measurableSet_gapBitAtom m u).inter (by measurability)

private lemma gapBitAtomState_cylinder
    (m : ℕ) (u : Fin m → Bool) (x : PopState) :
    isCylinderUpTo m (gapBitAtomState m u x) := by
  intro ω η heq hω
  exact ⟨gapBitAtom_cylinder m u ω η heq hω.1,
    (heq m le_rfl).symm.trans hω.2⟩

private lemma gapBitAtomState_pairwise
    (m : ℕ) (u : Fin m → Bool) :
    Pairwise fun x y : PopState =>
      Disjoint (gapBitAtomState m u x) (gapBitAtomState m u y) := by
  intro x y hxy
  rw [Set.disjoint_left]
  intro ω hx hy
  exact hxy (hx.2.symm.trans hy.2)

private lemma gapBitAtom_iUnion_state
    (m : ℕ) (u : Fin m → Bool) :
    gapBitAtom m u = ⋃ x : PopState, gapBitAtomState m u x := by
  ext ω
  simp [gapBitAtomState]

private lemma gapBitAtom_succ_iUnion
    (m : ℕ) (u : Fin (m + 1) → Bool) :
    gapBitAtom (m + 1) u =
      ⋃ x : PopState,
        gapBitAtomState m (fun i => u i.castSucc) x ∩
          (pathShift m) ⁻¹' gapBitFuture x (u (Fin.last m)) := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    have hs := (closingBits_succ_iff m u ω).mp h
    refine ⟨ω m, ⟨hs.1, rfl⟩, ?_⟩
    unfold gapBitFuture closingBit at *
    cases hbit : u (Fin.last m) <;> simp [hbit] at hs ⊢
    · simpa [pathShift] using hs.2
    · simpa [pathShift] using hs.2
  · rintro ⟨x, ⟨hprefix, hx⟩, hfuture⟩
    have hx' : ω m = x := hx
    apply (closingBits_succ_iff m u ω).mpr
    refine ⟨hprefix, ?_⟩
    unfold gapBitFuture at hfuture
    unfold closingBit
    cases hbit : u (Fin.last m) <;> simp [hbit] at hfuture ⊢
    · simpa [pathShift, hx'] using hfuture
    · simpa [pathShift, hx'] using hfuture

private lemma gapBitAtom_measure_le
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (m : ℕ) (hm : m ≤ b) (u : Fin m → Bool) :
    (lvPathMeasure .nonSelfDestructive params (a, b)) (gapBitAtom m u) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ m := by
  induction m with
  | zero =>
      haveI : IsProbabilityMeasure
          (lvPathMeasure .nonSelfDestructive params (a, b)) := by
        unfold lvPathMeasure homogeneousPathMeasure
        infer_instance
      have hatom : gapBitAtom 0 u = Set.univ := by
        ext ω
        simp only [gapBitAtom, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Subsingleton.elim _ _
      rw [hatom]
      simpa using (prob_le_one
        (μ := lvPathMeasure .nonSelfDestructive params (a, b))
        (s := Set.univ))
  | succ m ih =>
      have hm' : m ≤ b := by omega
      let prefBits : Fin m → Bool := fun i => u i.castSucc
      let lastBit : Bool := u (Fin.last m)
      let P := lvPathMeasure .nonSelfDestructive params (a, b)
      let B : PopState → Set (ℕ → PopState) :=
        fun x => gapBitAtomState m prefBits x
      let C : PopState → Set (ℕ → PopState) :=
        fun x => gapBitFuture x lastBit
      have hpiece (x : PopState) :
          P (B x ∩ (pathShift m) ⁻¹' C x) ≤
            (2 : ℝ≥0∞)⁻¹ * P (B x) := by
        by_cases hx : a - m ≤ x.1 ∧ b - m ≤ x.2
        · have hmx0 : 0 < x.1 := by
            have ham : m < a := lt_of_lt_of_le (by omega) hab
            exact lt_of_lt_of_le (Nat.sub_pos_of_lt ham) hx.1
          have hmx1 : 0 < x.2 := by
            exact lt_of_lt_of_le (Nat.sub_pos_of_lt (by omega)) hx.2
          unfold P lvPathMeasure
          apply homogeneousPathMeasure_markov_bound
              (lvKernel .nonSelfDestructive params) (a, b) m
              (2 : ℝ≥0∞)⁻¹ (B x) (C x)
              (measurableSet_gapBitAtomState m prefBits x)
              (measurableSet_gapBitFuture x lastBit)
              (gapBitAtomState_cylinder m prefBits x)
          intro ω hω
          have hstate : ω m = x := hω.2
          rw [hstate]
          exact le_of_eq (fresh_gapBitFuture_half params hNeutral hInter
            hBetaDelta hGamma0 hGamma1 x hmx0 hmx1 lastBit)
        · have hbad : x.1 < a - m ∨ x.2 < b - m := by omega
          have hzero : P (B x) = 0 := by
            apply le_antisymm
            · calc
                P (B x) ≤
                    P {ω | (ω m).1 < a - m ∨ (ω m).2 < b - m} := by
                      apply measure_mono
                      intro ω hω
                      have hstate : ω m = x := hω.2
                      change (ω m).1 < a - m ∨ (ω m).2 < b - m
                      rw [hstate]
                      exact hbad
                _ = 0 := lvPathMeasure_reachable params a b m
            · exact zero_le
          rw [hzero, mul_zero]
          calc
            P (B x ∩ (pathShift m) ⁻¹' C x) ≤ P (B x) :=
              measure_mono Set.inter_subset_left
            _ = 0 := hzero
      calc
        (lvPathMeasure .nonSelfDestructive params (a, b))
            (gapBitAtom (m + 1) u) =
            P (⋃ x : PopState,
              B x ∩ (pathShift m) ⁻¹' C x) := by
                simp only [P, B, C]
                rw [← gapBitAtom_succ_iUnion m u]
        _ ≤ ∑' x : PopState, P (B x ∩ (pathShift m) ⁻¹' C x) :=
          measure_iUnion_le _
        _ ≤ ∑' x : PopState, (2 : ℝ≥0∞)⁻¹ * P (B x) :=
          ENNReal.tsum_le_tsum hpiece
        _ = (2 : ℝ≥0∞)⁻¹ * ∑' x : PopState, P (B x) := by
          rw [ENNReal.tsum_mul_left]
        _ = (2 : ℝ≥0∞)⁻¹ * P (gapBitAtom m prefBits) := by
          rw [gapBitAtom_iUnion_state]
          rw [measure_iUnion (gapBitAtomState_pairwise m prefBits)
            (fun x => measurableSet_gapBitAtomState m prefBits x)]
        _ ≤ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ m :=
          mul_le_mul_left' (ih hm' prefBits) _
        _ = ((2 : ℝ≥0∞)⁻¹) ^ (m + 1) := by
          rw [pow_succ']

noncomputable def uniformBits (m : ℕ) :
    Measure (Fin m → Bool) :=
  Measure.infinitePi (fun _ : Fin m => fairCoin)

instance (m : ℕ) : IsProbabilityMeasure (uniformBits m) := by
  unfold uniformBits
  infer_instance

lemma uniformBits_singleton (m : ℕ) (u : Fin m → Bool) :
    uniformBits m {u} = ((2 : ℝ≥0∞)⁻¹) ^ m := by
  unfold uniformBits
  rw [Measure.infinitePi_singleton_of_fintype]
  calc
    ∏ i : Fin m, fairCoin {u i} =
        ∏ _i : Fin m, (2 : ℝ≥0∞)⁻¹ := by
          apply Finset.prod_congr rfl
          intro i _
          cases h : u i <;> simp [h, fairCoin_false, fairCoin_true]
    _ = ((2 : ℝ≥0∞)⁻¹) ^ m := by simp

private lemma closingBits_map_eq_uniform
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    Measure.map (closingBits b)
        (lvPathMeasure .nonSelfDestructive params (a, b)) =
      uniformBits b := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let μ := Measure.map (closingBits b) P
  let ν := uniformBits b
  haveI : IsProbabilityMeasure P := by
    unfold P lvPathMeasure homogeneousPathMeasure
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    unfold μ
    exact Measure.isProbabilityMeasure_map
      (measurable_closingBits b).aemeasurable
  haveI : IsProbabilityMeasure ν := by
    unfold ν
    infer_instance
  have hsingle (u : Fin b → Bool) : μ {u} ≤ ν {u} := by
    unfold μ ν
    rw [Measure.map_apply (measurable_closingBits b)
      (measurableSet_singleton u)]
    change P (gapBitAtom b u) ≤ uniformBits b {u}
    rw [uniformBits_singleton]
    exact gapBitAtom_measure_le params hNeutral hInter hBetaDelta
      hGamma0 hGamma1 a b ha hb hab b le_rfl u
  have hle : μ ≤ ν := by
    apply Measure.le_intro
    intro S _hS _hne
    have hUnion :
        S = ⋃ u : S, ({u.1} : Set (Fin b → Bool)) := by
      ext u
      simp
    have hdisj :
        Pairwise (Function.onFun Disjoint
          (fun u : S => ({u.1} : Set (Fin b → Bool)))) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_singleton]
      exact Subtype.coe_ne_coe.mpr hij
    have hmeas :
        ∀ u : S, MeasurableSet ({u.1} : Set (Fin b → Bool)) :=
      fun u => measurableSet_singleton u.1
    have hμsum :
        μ (⋃ u : S, ({u.1} : Set (Fin b → Bool))) =
          ∑' u : S, μ {u.1} :=
      measure_iUnion hdisj hmeas
    have hνsum :
        ν (⋃ u : S, ({u.1} : Set (Fin b → Bool))) =
          ∑' u : S, ν {u.1} :=
      measure_iUnion hdisj hmeas
    rw [hUnion]
    rw [hμsum, hνsum]
    exact ENNReal.tsum_le_tsum fun i => hsingle i.1
  exact Measure.eq_of_le_of_isProbabilityMeasure hle

private def firstBits (m : ℕ) (ω : ℕ → Bool) : Fin m → Bool :=
  fun i => ω i

private lemma measurable_firstBits (m : ℕ) :
    Measurable (firstBits m) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.val

private lemma firstBits_fair_atom (m : ℕ) (u : Fin m → Bool) :
    fairCoins {ω | firstBits m ω = u} = ((2 : ℝ≥0∞)⁻¹) ^ m := by
  let T : ℕ → Set Bool := fun i =>
    if hi : i < m then {u ⟨i, hi⟩} else Set.univ
  have hAtom :
      {ω : ℕ → Bool | firstBits m ω = u} =
        Set.pi (Finset.range m) T := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_range]
    constructor
    · intro h i hi
      have him : i < m := Finset.mem_range.mp hi
      simp only [T, dif_pos him, Set.mem_singleton_iff]
      exact congrFun h ⟨i, him⟩
    · intro h
      funext i
      have hi := h i.val (Finset.mem_range.mpr i.isLt)
      simpa only [firstBits, T, dif_pos i.isLt,
        Set.mem_singleton_iff] using hi
  rw [hAtom]
  unfold fairCoins
  rw [Measure.infinitePi_pi]
  · calc
      ∏ i ∈ Finset.range m, fairCoin (T i) =
          ∏ _i ∈ Finset.range m, (2 : ℝ≥0∞)⁻¹ := by
            apply Finset.prod_congr rfl
            intro i hi
            have him : i < m := Finset.mem_range.mp hi
            simp only [T, dif_pos him]
            cases h : u ⟨i, him⟩ <;>
              simp [h, fairCoin_false, fairCoin_true]
      _ = ((2 : ℝ≥0∞)⁻¹) ^ m := by simp
  · intro i hi
    have him : i < m := Finset.mem_range.mp hi
    simp only [T, dif_pos him]
    exact measurableSet_singleton _

private lemma firstBits_map_eq_uniform (m : ℕ) :
    Measure.map (firstBits m) fairCoins = uniformBits m := by
  let μ := Measure.map (firstBits m) fairCoins
  let ν := uniformBits m
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_firstBits m).aemeasurable
  haveI : IsProbabilityMeasure ν := by
    unfold ν
    infer_instance
  have hsingle (u : Fin m → Bool) : μ {u} ≤ ν {u} := by
    unfold μ ν
    rw [Measure.map_apply (measurable_firstBits m)
      (measurableSet_singleton u)]
    change fairCoins {ω | firstBits m ω = u} ≤ uniformBits m {u}
    rw [firstBits_fair_atom, uniformBits_singleton]
  have hle : μ ≤ ν := by
    apply Measure.le_intro
    intro S _hS _hne
    have hUnion :
        S = ⋃ u : S, ({u.1} : Set (Fin m → Bool)) := by
      ext u
      simp
    have hdisj :
        Pairwise (Function.onFun Disjoint
          (fun u : S => ({u.1} : Set (Fin m → Bool)))) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_singleton]
      exact Subtype.coe_ne_coe.mpr hij
    have hmeas :
        ∀ u : S, MeasurableSet ({u.1} : Set (Fin m → Bool)) :=
      fun u => measurableSet_singleton u.1
    have hμsum :
        μ (⋃ u : S, ({u.1} : Set (Fin m → Bool))) =
          ∑' u : S, μ {u.1} :=
      measure_iUnion hdisj hmeas
    have hνsum :
        ν (⋃ u : S, ({u.1} : Set (Fin m → Bool))) =
          ∑' u : S, ν {u.1} :=
      measure_iUnion hdisj hmeas
    rw [hUnion, hμsum, hνsum]
    exact ENNReal.tsum_le_tsum fun i => hsingle i.1
  exact Measure.eq_of_le_of_isProbabilityMeasure hle

def finiteBitStep (m : ℕ) (u : Fin m → Bool) (i : ℕ) : ℝ :=
  if hi : i < m then if u ⟨i, hi⟩ then 1 else -1 else 0

def bitMaxEvent (θ : ℝ) (m : ℕ) : Set (Fin m → Bool) :=
  {u | ∃ k ∈ Finset.range (m + 1),
    θ * Real.sqrt m ≤ ∑ i ∈ Finset.range k, finiteBitStep m u i}

lemma measurableSet_bitMaxEvent (θ : ℝ) (m : ℕ) :
    MeasurableSet (bitMaxEvent θ m) :=
  DiscreteMeasurableSpace.forall_measurableSet _

private lemma fairStep_sum_firstBits
    (m k : ℕ) (hk : k ≤ m) (ω : ℕ → Bool) :
    ∑ i ∈ Finset.range k, fairStep i ω =
      ∑ i ∈ Finset.range k, finiteBitStep m (firstBits m ω) i := by
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  simp [fairStep, finiteBitStep, firstBits, him]

private lemma closingStep_sum_closingBits
    (m k : ℕ) (hk : k ≤ m) (ω : ℕ → PopState) :
    ∑ i ∈ Finset.range k,
        (if closingBit i ω then (1 : ℝ) else -1) =
      ∑ i ∈ Finset.range k, finiteBitStep m (closingBits m ω) i := by
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < m := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  simp [finiteBitStep, closingBits, him]

private lemma fairMaxEvent_preimage (θ : ℝ) (m : ℕ) :
    {ω : ℕ → Bool | ∃ k ∈ Finset.range (m + 1),
        θ * Real.sqrt m ≤ ∑ i ∈ Finset.range k, fairStep i ω} =
      (firstBits m) ⁻¹' bitMaxEvent θ m := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, bitMaxEvent]
  constructor
  · rintro ⟨k, hk, hbound⟩
    refine ⟨k, hk, ?_⟩
    rw [← fairStep_sum_firstBits m k (by
      have := Finset.mem_range.mp hk
      omega)]
    exact hbound
  · rintro ⟨k, hk, hbound⟩
    refine ⟨k, hk, ?_⟩
    rw [fairStep_sum_firstBits m k (by
      have := Finset.mem_range.mp hk
      omega)]
    exact hbound

/-- Finite-vector form of the Rademacher running-maximum estimate. -/
theorem uniformBits_bitMaxEvent_lower
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ENNReal.ofReal ε ≤ uniformBits n (bitMaxEvent θ n) := by
  obtain ⟨θ, hθ, n₀, hmax⟩ := fair_clt ε hε0 hε1
  refine ⟨θ, hθ, n₀, ?_⟩
  intro n hn
  calc
    ENNReal.ofReal ε ≤
        fairCoins {ω | ∃ k ∈ Finset.range (n + 1),
          θ * Real.sqrt n ≤
            ∑ i ∈ Finset.range k, fairStep i ω} :=
      hmax n hn
    _ = fairCoins ((firstBits n) ⁻¹' bitMaxEvent θ n) := by
      rw [← fairMaxEvent_preimage]
    _ = Measure.map (firstBits n) fairCoins (bitMaxEvent θ n) := by
      rw [Measure.map_apply (measurable_firstBits n)
        (measurableSet_bitMaxEvent θ n)]
    _ = uniformBits n (bitMaxEvent θ n) := by
      rw [firstBits_map_eq_uniform]

private lemma closingMaxEvent_preimage (θ : ℝ) (m : ℕ) :
    {ω : ℕ → PopState | ∃ k ∈ Finset.range (m + 1),
        θ * Real.sqrt m ≤
          ∑ i ∈ Finset.range k,
            (if closingBit i ω then (1 : ℝ) else -1)} =
      (closingBits m) ⁻¹' bitMaxEvent θ m := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, bitMaxEvent]
  constructor
  · rintro ⟨k, hk, hbound⟩
    refine ⟨k, hk, ?_⟩
    rw [← closingStep_sum_closingBits m k (by
      have := Finset.mem_range.mp hk
      omega)]
    exact hbound
  · rintro ⟨k, hk, hbound⟩
    refine ⟨k, hk, ?_⟩
    rw [closingStep_sum_closingBits m k (by
      have := Finset.mem_range.mp hk
      omega)]
    exact hbound

private lemma closingMaxEvent_probability
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (θ : ℝ) :
    (lvPathMeasure .nonSelfDestructive params (a, b))
        {ω | ∃ k ∈ Finset.range (b + 1),
          θ * Real.sqrt b ≤
            ∑ i ∈ Finset.range k,
              (if closingBit i ω then (1 : ℝ) else -1)} =
      fairCoins {ω | ∃ k ∈ Finset.range (b + 1),
        θ * Real.sqrt b ≤ ∑ i ∈ Finset.range k, fairStep i ω} := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let E := bitMaxEvent θ b
  have hclose := closingBits_map_eq_uniform params hNeutral hInter
    hBetaDelta hGamma0 hGamma1 a b ha hb hab
  have hfair := firstBits_map_eq_uniform b
  rw [closingMaxEvent_preimage, fairMaxEvent_preimage]
  calc
    P ((closingBits b) ⁻¹' E) =
        Measure.map (closingBits b) P E := by
          rw [Measure.map_apply (measurable_closingBits b)
            (measurableSet_bitMaxEvent θ b)]
    _ = uniformBits b E := by rw [hclose]
    _ = Measure.map (firstBits b) fairCoins E := by rw [hfair]
    _ = fairCoins ((firstBits b) ⁻¹' E) := by
          rw [Measure.map_apply (measurable_firstBits b)
            (measurableSet_bitMaxEvent θ b)]

private lemma nsd_gap_kernel_bad_zero
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (x : PopState) (hx0 : 0 < x.1) (hx1 : 0 < x.2) :
    (lvKernel .nonSelfDestructive params) x
      {y | gap y ≠ gap x - 1 ∧ gap y ≠ gap x + 1} = 0 := by
  let K := lvKernel .nonSelfDestructive params
  let M : Set PopState := {y | gap y = gap x - 1}
  let Q : Set PopState := {y | gap y = gap x + 1}
  let Bad : Set PopState := {y | gap y ≠ gap x - 1 ∧ gap y ≠ gap x + 1}
  have hfair := nsd_gap_kernel_fair params hNeutral hInter hBetaDelta
    hGamma0 hGamma1 x.1 x.2 hx0 hx1
  have hM : K x M = (2 : ℝ≥0∞)⁻¹ := hfair.2
  have hQ : K x Q = (2 : ℝ≥0∞)⁻¹ := hfair.1
  have hdisj : Disjoint M Q := by
    rw [Set.disjoint_left]
    intro y hyM hyQ
    simp only [M, Q, Set.mem_setOf_eq] at hyM hyQ
    omega
  have hMmeas : MeasurableSet M :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hQmeas : MeasurableSet Q :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hBadEq : Bad = (M ∪ Q)ᶜ := by
    ext y
    simp [Bad, M, Q]
  haveI : IsProbabilityMeasure (K x) :=
    IsMarkovKernel.isProbabilityMeasure x
  change K x Bad = 0
  rw [hBadEq, prob_compl_eq_one_sub (hMmeas.union hQmeas),
    measure_union hdisj hQmeas, hM, hQ]
  have hadd : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
    calc
      (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 2 * 2⁻¹ := by ring
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [hadd]
  simp

private def gapBadFuture (x : PopState) : Set (ℕ → PopState) :=
  {η | gap (η 1) ≠ gap x - 1 ∧ gap (η 1) ≠ gap x + 1}

private lemma measurableSet_gapBadFuture (x : PopState) :
    MeasurableSet (gapBadFuture x) := by
  unfold gapBadFuture
  measurability

private lemma fresh_gapBadFuture_zero
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (x : PopState) (hx0 : 0 < x.1) (hx1 : 0 < x.2) :
    homogeneousPathMeasure (Measure.dirac x)
        (lvKernel .nonSelfDestructive params) (gapBadFuture x) = 0 := by
  let K := lvKernel .nonSelfDestructive params
  let Bad : Set PopState :=
    {y | gap y ≠ gap x - 1 ∧ gap y ≠ gap x + 1}
  have hBad : MeasurableSet Bad :=
    DiscreteMeasurableSpace.forall_measurableSet _
  change homogeneousPathMeasure (Measure.dirac x) K
      ((fun η : ℕ → PopState => η 1) ⁻¹' Bad) = 0
  rw [← Measure.map_apply (measurable_pi_apply 1) hBad,
    homogeneousPathMeasure_dirac_marginal]
  simp only [kernelIter_succ, kernelIter_zero, Kernel.comp_id]
  exact nsd_gap_kernel_bad_zero params hNeutral hInter hBetaDelta
    hGamma0 hGamma1 x hx0 hx1

private def positiveStateAt (t : ℕ) (x : PopState) :
    Set (ℕ → PopState) :=
  {ω | ω t = x ∧ 0 < x.1 ∧ 0 < x.2}

private lemma measurableSet_positiveStateAt (t : ℕ) (x : PopState) :
    MeasurableSet (positiveStateAt t x) := by
  unfold positiveStateAt
  measurability

private lemma positiveStateAt_cylinder (t : ℕ) (x : PopState) :
    isCylinderUpTo t (positiveStateAt t x) := by
  intro ω η heq hω
  exact ⟨(heq t le_rfl).symm.trans hω.1, hω.2⟩

private lemma positive_gap_bad_at_zero
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (a b t : ℕ) :
    (lvPathMeasure .nonSelfDestructive params (a, b))
      {ω | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧
        gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
        gap (ω (t + 1)) ≠ gap (ω t) + 1} = 0 := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  have hUnion :
      {ω : ℕ → PopState | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧
          gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
          gap (ω (t + 1)) ≠ gap (ω t) + 1} =
        ⋃ x : PopState,
          positiveStateAt t x ∩ (pathShift t) ⁻¹' gapBadFuture x := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage]
    constructor
    · intro h
      refine ⟨ω t, ⟨rfl, h.1, h.2.1⟩, ?_⟩
      simpa [gapBadFuture, pathShift] using h.2.2
    · rintro ⟨x, ⟨hx, hx0, hx1⟩, hbad⟩
      subst x
      simpa [gapBadFuture, pathShift] using And.intro hx0 (And.intro hx1 hbad)
  rw [hUnion]
  apply le_antisymm
  · calc
      P (⋃ x : PopState,
          positiveStateAt t x ∩ (pathShift t) ⁻¹' gapBadFuture x) ≤
          ∑' x : PopState,
            P (positiveStateAt t x ∩
              (pathShift t) ⁻¹' gapBadFuture x) :=
        measure_iUnion_le _
      _ ≤ ∑' _x : PopState, (0 : ℝ≥0∞) := by
        apply ENNReal.tsum_le_tsum
        intro x
        unfold P lvPathMeasure
        have hmark := homogeneousPathMeasure_markov_bound
            (lvKernel .nonSelfDestructive params) (a, b) t 0
            (positiveStateAt t x) (gapBadFuture x)
            (measurableSet_positiveStateAt t x)
            (measurableSet_gapBadFuture x)
            (positiveStateAt_cylinder t x)
            (fun ω hω => by
              rw [hω.1]
              exact le_of_eq (fresh_gapBadFuture_zero params hNeutral hInter
                hBetaDelta hGamma0 hGamma1 x hω.2.1 hω.2.2))
        simpa using hmark
      _ = 0 := tsum_zero
  · exact zero_le

private lemma raw_gap_bad_at_zero
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (a b t : ℕ) (ht : t < b) (hab : b ≤ a) :
    (lvPathMeasure .nonSelfDestructive params (a, b))
      {ω | gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
        gap (ω (t + 1)) ≠ gap (ω t) + 1} = 0 := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let PosBad : Set (ℕ → PopState) :=
    {ω | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧
      gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
      gap (ω (t + 1)) ≠ gap (ω t) + 1}
  let Boundary : Set (ℕ → PopState) :=
    {ω | (ω t).1 = 0 ∨ (ω t).2 = 0}
  have hBoundary : P Boundary = 0 := by
    apply measure_mono_null
      (t := {ω | (ω t).1 < a - t ∨ (ω t).2 < b - t})
    · intro ω hω
      simp only [Boundary, Set.mem_setOf_eq] at hω
      simp only [Set.mem_setOf_eq]
      have hat : 0 < a - t := Nat.sub_pos_of_lt (lt_of_lt_of_le ht hab)
      have hbt : 0 < b - t := Nat.sub_pos_of_lt ht
      omega
    · exact lvPathMeasure_reachable params a b t
  have hsub :
      {ω : ℕ → PopState | gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
          gap (ω (t + 1)) ≠ gap (ω t) + 1} ⊆ PosBad ∪ Boundary := by
    intro ω hω
    by_cases h0 : 0 < (ω t).1 ∧ 0 < (ω t).2
    · left
      exact ⟨h0.1, h0.2, hω⟩
    · right
      simp only [Boundary, Set.mem_setOf_eq]
      omega
  apply le_antisymm
  · calc
      P {ω | gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
          gap (ω (t + 1)) ≠ gap (ω t) + 1} ≤
          P (PosBad ∪ Boundary) := measure_mono hsub
      _ ≤ P PosBad + P Boundary := measure_union_le _ _
      _ = 0 := by
        rw [hBoundary, add_zero]
        exact positive_gap_bad_at_zero params hNeutral hInter hBetaDelta
          hGamma0 hGamma1 a b t
  · exact zero_le

private def invalidGapPath (b : ℕ) : Set (ℕ → PopState) :=
  {ω | ∃ t ∈ Finset.range b,
    gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
      gap (ω (t + 1)) ≠ gap (ω t) + 1}

private lemma invalidGapPath_zero
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : ℕ) (hab : b ≤ a) :
    (lvPathMeasure .nonSelfDestructive params (a, b))
      (invalidGapPath b) = 0 := by
  have hUnion :
      invalidGapPath b =
        ⋃ t ∈ Finset.range b,
          {ω | gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
            gap (ω (t + 1)) ≠ gap (ω t) + 1} := by
    ext ω
    simp only [invalidGapPath, Set.mem_setOf_eq, Set.mem_iUnion,
      Finset.mem_range]
    constructor
    · rintro ⟨t, ht, hbad⟩
      exact ⟨t, ht, hbad⟩
    · rintro ⟨t, ht, hbad⟩
      exact ⟨t, ht, hbad⟩
  rw [hUnion]
  apply le_antisymm
  · calc
      (lvPathMeasure .nonSelfDestructive params (a, b))
          (⋃ t ∈ Finset.range b,
            {ω | gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
              gap (ω (t + 1)) ≠ gap (ω t) + 1}) ≤
          ∑ t ∈ Finset.range b,
            (lvPathMeasure .nonSelfDestructive params (a, b))
              {ω | gap (ω (t + 1)) ≠ gap (ω t) - 1 ∧
                gap (ω (t + 1)) ≠ gap (ω t) + 1} :=
        measure_biUnion_finset_le _ _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        exact raw_gap_bad_at_zero params hNeutral hInter hBetaDelta
          hGamma0 hGamma1 a b t (Finset.mem_range.mp ht) hab
  · exact zero_le

private lemma nsd_kernel_no_large_total_drop
    (params : LVParams) (s : PopState) :
    (lvKernel .nonSelfDestructive params) s
      {s' : PopState | s'.1 + s'.2 + 1 < s.1 + s.2} = 0 := by
  rcases s with ⟨a, b⟩
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    rw [Measure.dirac_apply]
    simp
  · rw [lvKernel_nsd_apply params a b hφ]
    simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul,
      Measure.dirac_apply]
    rcases Nat.eq_zero_or_pos a with rfl | ha <;>
      rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have hbsub : b - 1 + 1 = b := by omega
      simp [hbsub] <;> omega
    · have hasub : a - 1 + 1 = a := by omega
      simp [hasub] <;> omega
    · have hasub : a - 1 + 1 = a := by omega
      have hbsub : b - 1 + 1 = b := by omega
      simp [hasub, hbsub] <;> omega

private lemma nsd_kernelIter_total_reachable
    (params : LVParams) (a b m : ℕ) :
    (kernelIter (lvKernel .nonSelfDestructive params) m) (a, b)
      {s : PopState | s.1 + s.2 < a + b - m} = 0 := by
  let K := lvKernel .nonSelfDestructive params
  induction m with
  | zero =>
      simp [kernelIter_zero, Kernel.id_apply, Measure.dirac_apply]
  | succ m ih =>
      let Bad : Set PopState :=
        {s | s.1 + s.2 < a + b - (m + 1)}
      have hBad : MeasurableSet Bad :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [kernelIter_succ, Kernel.comp_apply' _ _ _ hBad]
      apply le_antisymm _ zero_le
      calc
        (∫⁻ y, K y Bad ∂(kernelIter K m) (a, b)) ≤
            ∫⁻ _y, (0 : ℝ≥0∞) ∂(kernelIter K m) (a, b) := by
          apply lintegral_mono_ae
          have hae :
              ∀ᵐ y ∂(kernelIter K m) (a, b),
                ¬(y.1 + y.2 < a + b - m) :=
            compl_mem_ae_iff.mpr ih
          filter_upwards [hae] with y hy
          calc
            K y Bad ≤ K y
                {z : PopState | z.1 + z.2 + 1 < y.1 + y.2} := by
              apply measure_mono
              intro z hz
              simp only [Bad, Set.mem_setOf_eq] at hz ⊢
              omega
            _ = 0 := nsd_kernel_no_large_total_drop params y
        _ = 0 := lintegral_zero

private lemma lvPathMeasure_total_reachable
    (params : LVParams) (a b m : ℕ) :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | (ω m).1 + (ω m).2 < a + b - m} = 0 := by
  let K := lvKernel .nonSelfDestructive params
  let Bad : Set PopState := {s | s.1 + s.2 < a + b - m}
  have hBad : MeasurableSet Bad :=
    DiscreteMeasurableSpace.forall_measurableSet _
  change homogeneousPathMeasure (Measure.dirac (a, b)) K
      ((fun ω : ℕ → PopState => ω m) ⁻¹' Bad) = 0
  rw [← Measure.map_apply (measurable_pi_apply m) hBad,
    homogeneousPathMeasure_dirac_marginal]
  exact nsd_kernelIter_total_reachable params a b m

private lemma lvPathMeasure_initial_ne
    (params : LVParams) (a b : ℕ) :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | ω 0 ≠ (a, b)} = 0 := by
  let K := lvKernel .nonSelfDestructive params
  let Bad : Set PopState := ({(a, b)} : Set PopState)ᶜ
  have hBad : MeasurableSet Bad :=
    (measurableSet_singleton (a, b)).compl
  change homogeneousPathMeasure (Measure.dirac (a, b)) K
      ((fun ω : ℕ → PopState => ω 0) ⁻¹' Bad) = 0
  rw [← Measure.map_apply (measurable_pi_apply 0) hBad,
    homogeneousPathMeasure_dirac_marginal]
  simp [kernelIter_zero, Kernel.id_apply, Bad]

private def invalidTotalPath (a b : ℕ) : Set (ℕ → PopState) :=
  {ω | ∃ t ∈ Finset.range (b + 1),
    (ω t).1 + (ω t).2 < a + b - t}

private lemma invalidTotalPath_zero
    (params : LVParams) (a b : ℕ) :
    lvPathMeasure .nonSelfDestructive params (a, b)
      (invalidTotalPath a b) = 0 := by
  have hUnion :
      invalidTotalPath a b =
        ⋃ t ∈ Finset.range (b + 1),
          {ω | (ω t).1 + (ω t).2 < a + b - t} := by
    ext ω
    simp only [invalidTotalPath, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, hbad⟩
      exact ⟨t, ht, hbad⟩
    · rintro ⟨t, ht, hbad⟩
      exact ⟨t, ht, hbad⟩
  rw [hUnion]
  apply le_antisymm
  · calc
      (lvPathMeasure .nonSelfDestructive params (a, b))
          (⋃ t ∈ Finset.range (b + 1),
            {ω | (ω t).1 + (ω t).2 < a + b - t}) ≤
          ∑ t ∈ Finset.range (b + 1),
            (lvPathMeasure .nonSelfDestructive params (a, b))
              {ω | (ω t).1 + (ω t).2 < a + b - t} :=
        measure_biUnion_finset_le _ _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro t _ht
        exact lvPathMeasure_total_reachable params a b t
  · exact zero_le

private lemma gap_telescope
    (b : ℕ) (ω : ℕ → PopState)
    (hvalid : ω ∉ invalidGapPath b) :
    ∀ k, k ≤ b →
      (gap (ω k) : ℝ) =
        (gap (ω 0) : ℝ) -
          ∑ i ∈ Finset.range k,
            (if closingBit i ω then (1 : ℝ) else -1) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hkb : k < b := by omega
      have hstep :
          gap (ω (k + 1)) = gap (ω k) - 1 ∨
            gap (ω (k + 1)) = gap (ω k) + 1 := by
        by_contra h
        push_neg at h
        exact hvalid ⟨k, Finset.mem_range.mpr hkb, h.1, h.2⟩
      have hi := ih (by omega)
      rw [Finset.sum_range_succ]
      cases hstep with
      | inl hminus =>
          have hreal :
              (gap (ω (k + 1)) : ℝ) = (gap (ω k) : ℝ) - 1 := by
            exact_mod_cast hminus
          have hclose : closingBit k ω = true := by
            simp [closingBit, hminus]
          rw [hreal]
          simp only [hclose, Bool.true_eq, if_true]
          linarith
      | inr hplus =>
          have hne : gap (ω (k + 1)) ≠ gap (ω k) - 1 := by omega
          have hreal :
              (gap (ω (k + 1)) : ℝ) = (gap (ω k) : ℝ) + 1 := by
            exact_mod_cast hplus
          have hclose : closingBit k ω = false := by
            simp [closingBit, hne]
          rw [hreal]
          simp only [hclose, Bool.false_eq_true, if_false]
          linarith

private lemma integer_walk_hits_zero
    (g : ℕ → ℤ) (k : ℕ)
    (h0 : 0 ≤ g 0) (hk : g k ≤ 0)
    (hstep : ∀ i, i < k → g (i + 1) = g i - 1 ∨
      g (i + 1) = g i + 1) :
    ∃ j ∈ Finset.range (k + 1), g j = 0 := by
  induction k with
  | zero =>
      refine ⟨0, by simp, ?_⟩
      omega
  | succ k ih =>
      by_cases hprev : g k ≤ 0
      · obtain ⟨j, hj, hgj⟩ := ih hprev (fun i hi => hstep i (by omega))
        exact ⟨j, Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hj
          omega), hgj⟩
      · have hpos : 0 < g k := by omega
        have hlast := hstep k (by omega)
        refine ⟨k + 1, by simp, ?_⟩
        omega

private lemma closing_max_good_subset_diagonal
    (a b : ℕ) (hb : 0 < b) (hab : b ≤ a)
    (θ : ℝ)
    (hgap : (a : ℝ) - b ≤ θ * Real.sqrt b) :
    {ω : ℕ → PopState | ∃ k ∈ Finset.range (b + 1),
        θ * Real.sqrt b ≤
          ∑ i ∈ Finset.range k,
            (if closingBit i ω then (1 : ℝ) else -1)} ∩
      {ω | ω 0 = (a, b)} ∩
      (invalidGapPath b)ᶜ ∩
      (invalidTotalPath a b)ᶜ ⊆
        {ω | ∃ k ∈ Finset.range (b + 1),
          (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} := by
  intro ω hω
  rcases hω with ⟨hgoodGap, htotal⟩
  rcases hgoodGap with ⟨hmaxInit, hvalid⟩
  rcases hmaxInit with ⟨hmax, hinit⟩
  rcases hmax with ⟨k, hk, hbound⟩
  have hkb : k ≤ b := by
    have := Finset.mem_range.mp hk
    omega
  have htel := gap_telescope b ω hvalid k hkb
  have hgap0 : (gap (ω 0) : ℝ) = (a : ℝ) - b := by
    rw [hinit]
    simp [gap]
  have hgapkReal : (gap (ω k) : ℝ) ≤ 0 := by
    rw [htel, hgap0]
    linarith
  have hgapk : gap (ω k) ≤ 0 := by
    exact_mod_cast hgapkReal
  have hgap0Int : 0 ≤ gap (ω 0) := by
    rw [hinit]
    simp [gap]
    omega
  have hsteps : ∀ i, i < k →
      gap (ω (i + 1)) = gap (ω i) - 1 ∨
        gap (ω (i + 1)) = gap (ω i) + 1 := by
    intro i hi
    by_contra h
    push_neg at h
    exact hvalid ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le hi hkb),
      h.1, h.2⟩
  obtain ⟨j, hj, hgj⟩ :=
    integer_walk_hits_zero (fun t => gap (ω t)) k hgap0Int hgapk hsteps
  have hjk : j ≤ k := by
    have := Finset.mem_range.mp hj
    omega
  have hjb : j ≤ b := le_trans hjk hkb
  have hjRange : j ∈ Finset.range (b + 1) :=
    Finset.mem_range.mpr (by omega)
  have htotalLower : a + b - j ≤ (ω j).1 + (ω j).2 := by
    by_contra h
    exact htotal ⟨j, hjRange, by omega⟩
  have htotalPos : 0 < (ω j).1 + (ω j).2 := by
    have ha : 0 < a := lt_of_lt_of_le hb hab
    have : a ≤ a + b - j := by omega
    omega
  have heq : (ω j).1 = (ω j).2 := by
    simp only [gap] at hgj
    omega
  have hpos : 0 < (ω j).1 := by omega
  exact ⟨j, hjRange, heq, hpos⟩

theorem nsd_gap_clt_markov_bound_unconditional
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)]
    (ε : Real) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ θ : Real, 0 < θ ∧ ∃ n₀ : Nat,
      ∀ a b : Nat, n₀ ≤ b → 0 < b → b ≤ a →
        (a : Real) - b ≤ θ * Real.sqrt b →
          ENNReal.ofReal (1 - ε) ≤
            (lvPathMeasure LVVariant.nonSelfDestructive params (a, b))
              {ω | ∃ k ∈ Finset.range (b + 1),
                (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} := by
  have honePos : 0 < 1 - ε := by linarith
  have honeLt : 1 - ε < 1 := by linarith
  obtain ⟨θ, hθ, n₀, hCLT⟩ := fair_clt (1 - ε) honePos honeLt
  refine ⟨θ, hθ, n₀, ?_⟩
  intro a b hn hb hab hgap
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let A : Set (ℕ → PopState) :=
    {ω | ∃ k ∈ Finset.range (b + 1),
      θ * Real.sqrt b ≤
        ∑ i ∈ Finset.range k,
          (if closingBit i ω then (1 : ℝ) else -1)}
  let D : Set (ℕ → PopState) :=
    {ω | ∃ k ∈ Finset.range (b + 1),
      (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}
  let B₀ : Set (ℕ → PopState) := {ω | ω 0 ≠ (a, b)}
  let Bgap : Set (ℕ → PopState) := invalidGapPath b
  let Btotal : Set (ℕ → PopState) := invalidTotalPath a b
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hAprob :
      ENNReal.ofReal (1 - ε) ≤ P A := by
    calc
      ENNReal.ofReal (1 - ε) ≤
          fairCoins {ω | ∃ k ∈ Finset.range (b + 1),
            θ * Real.sqrt b ≤
              ∑ i ∈ Finset.range k, fairStep i ω} :=
        hCLT b hn
      _ = P A := by
        symm
        exact closingMaxEvent_probability params hNeutral hInter hBetaDelta
          hGamma0 hGamma1 a b ha hb hab θ
  have hsub : A ⊆ ((D ∪ B₀) ∪ Bgap) ∪ Btotal := by
    intro ω hω
    by_cases hinit : ω 0 = (a, b)
    · by_cases hbadGap : ω ∈ Bgap
      · exact Or.inl (Or.inr hbadGap)
      · by_cases hbadTotal : ω ∈ Btotal
        · exact Or.inr hbadTotal
        · left
          left
          left
          apply closing_max_good_subset_diagonal a b hb hab θ hgap
          exact ⟨⟨⟨hω, hinit⟩, hbadGap⟩, hbadTotal⟩
    · exact Or.inl (Or.inl (Or.inr hinit))
  have hB₀ : P B₀ = 0 :=
    lvPathMeasure_initial_ne params a b
  have hBgap : P Bgap = 0 :=
    invalidGapPath_zero params hNeutral hInter hBetaDelta hGamma0 hGamma1
      a b hab
  have hBtotal : P Btotal = 0 :=
    invalidTotalPath_zero params a b
  have hAleD : P A ≤ P D := by
    calc
      P A ≤ P (((D ∪ B₀) ∪ Bgap) ∪ Btotal) := measure_mono hsub
      _ ≤ P ((D ∪ B₀) ∪ Bgap) + P Btotal := measure_union_le _ _
      _ ≤ (P (D ∪ B₀) + P Bgap) + P Btotal :=
        by
          gcongr
          exact measure_union_le _ _
      _ ≤ ((P D + P B₀) + P Bgap) + P Btotal :=
        by
          gcongr
          exact measure_union_le _ _
      _ = P D := by rw [hB₀, hBgap, hBtotal]; simp
  exact hAprob.trans hAleD

end LVConsensus
