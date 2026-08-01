import LVConsensus.DominationCategoricalCoupling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

/-!
# Concentration of the NSD interaction noise

The score is `+1` when an interspecific reaction removes one individual of
species 0, `-1` when it removes one individual of species 1, and `0` for all
other reactions.  Under `alpha1 ≤ alpha0` its conditional mean is nonpositive.
-/

def nsdInteractionScore : LVReaction → ℤ
  | .inter1 => 1
  | .inter0 => -1
  | _ => 0

lemma nsdInteractionScore_mem_Icc (r : LVReaction) :
    ((nsdInteractionScore r : ℤ) : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
  cases r <;> simp [nsdInteractionScore]

lemma measurable_nsdInteractionScore :
    Measurable (fun r : LVReaction => ((nsdInteractionScore r : ℤ) : ℝ)) :=
  measurable_of_countable _

noncomputable def nsdInteractionSumUpTo
    (ζ : ℕ → LabeledPopState) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range t,
    nsdInteractionScore (ζ (i + 1)).2

lemma measurable_nsdInteractionSumUpTo (t : ℕ) :
    Measurable (fun ζ : ℕ → LabeledPopState =>
      nsdInteractionSumUpTo ζ t) := by
  unfold nsdInteractionSumUpTo
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_of_countable
    (fun z : LabeledPopState =>
      nsdInteractionScore z.2)).comp
        (measurable_pi_apply (i + 1))

lemma nsdInteractionScore_integral_nonpos
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (z : LabeledPopState) :
    ∫ z', ((nsdInteractionScore z'.2 : ℤ) : ℝ)
        ∂lvLabeledKernel .nonSelfDestructive params z ≤ 0 := by
  let μ := lvLabeledKernel .nonSelfDestructive params z
  let A : Set LabeledPopState := {z' | z'.2 = .inter1}
  let B : Set LabeledPopState := {z' | z'.2 = .inter0}
  have hA : MeasurableSet A := by measurability
  have hB : MeasurableSet B := by measurability
  have hfun :
      (fun z' : LabeledPopState =>
        ((nsdInteractionScore z'.2 : ℤ) : ℝ)) =
        A.indicator (fun _ => (1 : ℝ)) -
          B.indicator (fun _ => (1 : ℝ)) := by
    funext z'
    rcases z' with ⟨s', r⟩
    cases r <;> simp [A, B, nsdInteractionScore, Set.indicator]
  have hAint :
      Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (μ := μ) (1 : ℝ)).indicator hA
  have hBint :
      Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (μ := μ) (1 : ℝ)).indicator hB
  rw [hfun]
  change
    (∫ z', A.indicator (fun _ => (1 : ℝ)) z' -
        B.indicator (fun _ => (1 : ℝ)) z' ∂μ) ≤ 0
  rw [integral_sub hAint hBint,
    integral_indicator_const (1 : ℝ) hA,
    integral_indicator_const (1 : ℝ) hB]
  simp only [smul_eq_mul, mul_one]
  change μ.real A - μ.real B ≤ 0
  simp only [Measure.real]
  rw [show μ A =
      if hφ : lvTotalPropensity params z.1 = 0 then
        if LVReaction.inter1 = .idle then 1 else 0
      else
        ENNReal.ofReal (1 / lvTotalPropensity params z.1) *
          ENNReal.ofReal
            (lvReactionWeight params z.1 .inter1) by
      simpa only [A] using
        lvLabeledKernel_reaction_probability
          .nonSelfDestructive params z .inter1,
    show μ B =
      if hφ : lvTotalPropensity params z.1 = 0 then
        if LVReaction.inter0 = .idle then 1 else 0
      else
        ENNReal.ofReal (1 / lvTotalPropensity params z.1) *
          ENNReal.ofReal
            (lvReactionWeight params z.1 .inter0) by
      simpa only [B] using
        lvLabeledKernel_reaction_probability
          .nonSelfDestructive params z .inter0]
  by_cases hφ : lvTotalPropensity params z.1 = 0
  · simp [hφ]
  · simp only [hφ, ↓reduceDIte, reduceCtorEq, if_false,
      Measure.real, ENNReal.toReal_mul]
    have hφnn :
        0 ≤ lvTotalPropensity params z.1 :=
      lvTotalPropensity_nonneg params z.1
    have hweight0 :
        0 ≤ lvReactionWeight params z.1 .inter0 := by
      simp only [lvReactionWeight]
      exact mul_nonneg
        (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    have hweight1 :
        0 ≤ lvReactionWeight params z.1 .inter1 := by
      simp only [lvReactionWeight]
      exact mul_nonneg
        (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr hφnn),
      ENNReal.toReal_ofReal hweight1,
      ENNReal.toReal_ofReal hweight0]
    simp only [lvReactionWeight]
    have hab :
        params.alpha1 * (z.1.1 : ℝ) * (z.1.2 : ℝ) ≤
          params.alpha0 * (z.1.1 : ℝ) * (z.1.2 : ℝ) := by
      gcongr
    exact sub_nonpos.mpr
      (mul_le_mul_of_nonneg_left hab
        (one_div_nonneg.mpr hφnn))

/-- The labelled chain augmented by the running interaction score and time. -/
structure NsdAccumState where
  labeled : LabeledPopState
  score : ℤ
  time : ℕ
  deriving DecidableEq, Repr, Countable

instance : MeasurableSpace NsdAccumState := ⊤
instance : MeasurableSingletonClass NsdAccumState := by infer_instance
instance : Nonempty NsdAccumState :=
  ⟨⟨((0, 0), .idle), 0, 0⟩⟩

def nsdAccumNext (x : NsdAccumState)
    (z' : LabeledPopState) : NsdAccumState where
  labeled := z'
  score := x.score + nsdInteractionScore z'.2
  time := x.time + 1

noncomputable def nsdAccumKernel (params : LVParams) :
    Kernel NsdAccumState NsdAccumState :=
  Kernel.ofFunOfCountable fun x =>
    (lvLabeledKernel .nonSelfDestructive params x.labeled).map
      (nsdAccumNext x)

instance nsdAccumKernel_isMarkovKernel (params : LVParams) :
    IsMarkovKernel (nsdAccumKernel params) where
  isProbabilityMeasure x := by
    unfold nsdAccumKernel
    simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
    refine ⟨?_⟩
    rw [Measure.map_apply
      (measurable_of_countable (nsdAccumNext x))
      MeasurableSet.univ]
    simp

noncomputable def nsdAccumPathMeasure
    (params : LVParams) (s0 : PopState) :
    Measure (ℕ → NsdAccumState) :=
  homogeneousPathMeasure
    (Measure.dirac (⟨(s0, .idle), 0, 0⟩ : NsdAccumState))
    (nsdAccumKernel params)

lemma nsdAccumKernel_ae_next (params : LVParams)
    (x : NsdAccumState) :
    ∀ᵐ y ∂nsdAccumKernel params x,
      y = nsdAccumNext x y.labeled := by
  unfold nsdAccumKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [ae_map_iff
    (μ := lvLabeledKernel .nonSelfDestructive params x.labeled)
    (measurable_of_countable (nsdAccumNext x)).aemeasurable
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact Filter.Eventually.of_forall fun z' => by
    rfl

lemma nsdAccumKernel_map_labeled (params : LVParams)
    (x : NsdAccumState) :
    (nsdAccumKernel params x).map NsdAccumState.labeled =
      lvLabeledKernel .nonSelfDestructive params x.labeled := by
  unfold nsdAccumKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [Measure.map_map
    (measurable_of_countable NsdAccumState.labeled)
    (measurable_of_countable (nsdAccumNext x))]
  simpa only [Function.comp_def, nsdAccumNext] using
    (Measure.map_id' :
      (lvLabeledKernel .nonSelfDestructive params x.labeled).map
      (fun z => z) =
        lvLabeledKernel .nonSelfDestructive params x.labeled)

theorem nsdAccumPathMeasure_map_labeled
    (params : LVParams) (s0 : PopState) :
    (nsdAccumPathMeasure params s0).map
        (pathMap NsdAccumState.labeled) =
      lvLabeledPathMeasure .nonSelfDestructive params s0 := by
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), .idle)⟩
  unfold nsdAccumPathMeasure lvLabeledPathMeasure
  simpa using
    homogeneousPathMeasure_map_pathMap
      (nsdAccumKernel params)
      (lvLabeledKernel .nonSelfDestructive params)
      NsdAccumState.labeled
      (measurable_of_countable NsdAccumState.labeled)
      (nsdAccumKernel_map_labeled params)
      (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)

lemma nsdAccumPathMeasure_score_eq_sum_ae
    (params : LVParams) (s0 : PopState) :
    ∀ᵐ ω ∂nsdAccumPathMeasure params s0,
      ∀ t : ℕ,
        (ω t).score =
          nsdInteractionSumUpTo
            (pathMap NsdAccumState.labeled ω) t := by
  let x0 : NsdAccumState := ⟨(s0, .idle), 0, 0⟩
  have htrans :
      ∀ᵐ ω ∂nsdAccumPathMeasure params s0,
        ∀ t : ℕ,
          ω (t + 1) =
            nsdAccumNext (ω t) (ω (t + 1)).labeled := by
    simpa only [nsdAccumPathMeasure] using
      homogeneousPathMeasure_transition_ae
        (nsdAccumKernel params) x0
        (fun x y => y = nsdAccumNext x y.labeled)
        (nsdAccumKernel_ae_next params)
  have hinitial :
      ∀ᵐ ω ∂nsdAccumPathMeasure params s0,
        ω 0 = x0 := by
    rw [ae_iff]
    simpa only [nsdAccumPathMeasure, x0] using
      homogeneousPathMeasure_initial_ne_null
        (nsdAccumKernel params) x0
  filter_upwards [htrans, hinitial] with ω hstep h0
  intro t
  induction t with
  | zero =>
      simp [nsdInteractionSumUpTo, h0, x0]
  | succ t ih =>
      rw [hstep t]
      unfold nsdAccumNext
      rw [ih]
      unfold nsdInteractionSumUpTo
      rw [Finset.sum_range_succ]
      rfl

lemma nsdInteractionScore_mgf_le
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (z : LabeledPopState) (lam : ℝ) (hlam : 0 ≤ lam) :
    mgf
        (fun z' => ((nsdInteractionScore z'.2 : ℤ) : ℝ))
        (lvLabeledKernel .nonSelfDestructive params z) lam ≤
      Real.exp (lam ^ 2 / 2) := by
  let μ := lvLabeledKernel .nonSelfDestructive params z
  let X : LabeledPopState → ℝ :=
    fun z' => ((nsdInteractionScore z'.2 : ℤ) : ℝ)
  let m : ℝ := ∫ z', X z' ∂μ
  have hXmeas : Measurable X := by
    exact measurable_nsdInteractionScore.comp measurable_snd
  have hXbound : ∀ᵐ z' ∂μ, X z' ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun z' =>
      nsdInteractionScore_mem_Icc z'.2
  have hmean : m ≤ 0 := by
    exact nsdInteractionScore_integral_nonpos params hBias z
  exact lemma_hoeffding_mgf
    μ X hXbound hXmeas.aemeasurable hmean lam hlam

noncomputable def nsdExpPotential (lam : ℝ) (x : NsdAccumState) : ℝ :=
  Real.exp
    (lam * (x.score : ℝ) -
      (x.time : ℝ) * lam ^ 2 / 2)

lemma nsdAccumKernel_exp_supermartingale
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (lam : ℝ) (hlam : 0 ≤ lam) (x : NsdAccumState) :
    ∫ y, nsdExpPotential lam y ∂nsdAccumKernel params x ≤
      nsdExpPotential lam x := by
  unfold nsdAccumKernel
  simp only [Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [integral_map
    (measurable_of_countable (nsdAccumNext x)).aemeasurable
    (measurable_of_countable
      (nsdExpPotential lam)).aestronglyMeasurable]
  have hpoint : ∀ z' : LabeledPopState,
      nsdExpPotential lam (nsdAccumNext x z') =
        nsdExpPotential lam x *
          Real.exp (-(lam ^ 2 / 2)) *
          Real.exp
            (lam *
              ((nsdInteractionScore z'.2 : ℤ) : ℝ)) := by
    intro z'
    unfold nsdExpPotential nsdAccumNext
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [integral_congr_ae
    (Filter.Eventually.of_forall hpoint)]
  rw [integral_const_mul]
  change
    nsdExpPotential lam x * Real.exp (-(lam ^ 2 / 2)) *
        mgf
          (fun z' =>
            ((nsdInteractionScore z'.2 : ℤ) : ℝ))
          (lvLabeledKernel .nonSelfDestructive params x.labeled)
          lam ≤
      nsdExpPotential lam x
  have hmgf :=
    nsdInteractionScore_mgf_le
      params hBias x.labeled lam hlam
  calc
    nsdExpPotential lam x * Real.exp (-(lam ^ 2 / 2)) *
        mgf
          (fun z' =>
            ((nsdInteractionScore z'.2 : ℤ) : ℝ))
          (lvLabeledKernel .nonSelfDestructive params x.labeled)
          lam
        ≤
      nsdExpPotential lam x * Real.exp (-(lam ^ 2 / 2)) *
        Real.exp (lam ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left hmgf
            (mul_nonneg
              (by
                unfold nsdExpPotential
                exact (Real.exp_pos _).le)
              (Real.exp_pos _).le)
    _ = nsdExpPotential lam x := by
      rw [mul_assoc]
      rw [← Real.exp_add]
      ring_nf
      simp

def nsdAccumReachable (k : ℕ) (x : NsdAccumState) : Prop :=
  x.time = k ∧
    -((k : ℕ) : ℤ) ≤ x.score ∧
      x.score ≤ ((k : ℕ) : ℤ)

lemma nsdAccumKernel_reachable_step
    (params : LVParams) (k : ℕ) (x : NsdAccumState)
    (hx : nsdAccumReachable k x) :
    ∀ᵐ y ∂nsdAccumKernel params x,
      nsdAccumReachable (k + 1) y := by
  filter_upwards [nsdAccumKernel_ae_next params x] with y hy
  rw [hy]
  rcases hx with ⟨htime, hlower, hupper⟩
  unfold nsdAccumReachable nsdAccumNext
  constructor
  · simp [htime]
  · cases y.labeled.2 <;>
      simp [nsdInteractionScore] <;>
      omega

lemma nsdAccumKernel_reachable
    (params : LVParams) (s0 : PopState) (k : ℕ) :
    (kernelIter (nsdAccumKernel params) k)
        ⟨(s0, .idle), 0, 0⟩
        {x | nsdAccumReachable k x}ᶜ = 0 := by
  induction k with
  | zero =>
      rw [kernelIter_zero, Kernel.id_apply]
      simp [nsdAccumReachable]
  | succ k ih =>
      apply kernelIter_concentrated_step
        (nsdAccumKernel params)
        (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)
        k
        {x | nsdAccumReachable k x}
        {x | nsdAccumReachable (k + 1) x}
        (DiscreteMeasurableSpace.forall_measurableSet _)
        (DiscreteMeasurableSpace.forall_measurableSet _)
        ih
      intro x hx
      have hnext :=
        nsdAccumKernel_reachable_step params k x hx
      rw [ae_iff] at hnext
      rw [show
        {y : NsdAccumState | nsdAccumReachable (k + 1) y}ᶜ =
          {y : NsdAccumState | ¬nsdAccumReachable (k + 1) y} by
            ext y
            simp]
      exact hnext

lemma nsdExpPotential_integrable
    (params : LVParams) (s0 : PopState)
    (lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    Integrable (nsdExpPotential lam)
      ((kernelIter (nsdAccumKernel params) k)
        ⟨(s0, .idle), 0, 0⟩) := by
  let μ :=
    (kernelIter (nsdAccumKernel params) k)
      (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact
      (kernelIter_isMarkov
        (K := nsdAccumKernel params) k).isProbabilityMeasure
          ⟨(s0, .idle), 0, 0⟩
  have hreach :
      ∀ᵐ x ∂μ, nsdAccumReachable k x := by
    rw [ae_iff]
    rw [show
      {x : NsdAccumState | ¬nsdAccumReachable k x} =
        {x : NsdAccumState | nsdAccumReachable k x}ᶜ by
          ext x
          simp]
    exact nsdAccumKernel_reachable params s0 k
  apply Integrable.of_mem_Icc 0 (Real.exp (lam * k))
    (measurable_of_countable
      (nsdExpPotential lam)).aemeasurable
  filter_upwards [hreach] with x hx
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    rcases hx with ⟨htime, _hlower, hupper⟩
    rw [htime]
    have hscore :
        (x.score : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hupper
    have hmul :
        lam * (x.score : ℝ) ≤ lam * k :=
      mul_le_mul_of_nonneg_left hscore hlam
    nlinarith [sq_nonneg lam,
      (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]

lemma nsdAccumKernel_exp_iter_le_one
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (s0 : PopState) (lam : ℝ) (hlam : 0 ≤ lam) (R : ℕ) :
    ∫ x, nsdExpPotential lam x
        ∂(kernelIter (nsdAccumKernel params) R)
          ⟨(s0, .idle), 0, 0⟩ ≤ 1 := by
  have h :=
    kernelIter_superharmonic_integral_le_at
      (nsdAccumKernel params)
      (nsdExpPotential lam)
      (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)
      R
      (fun _ => Set.univ)
      (fun k hk => by simp)
      (fun k hk x hx =>
        nsdAccumKernel_exp_supermartingale
          params hBias lam hlam x)
      (fun k hk =>
        nsdExpPotential_integrable
          params s0 lam hlam k)
  simpa [nsdExpPotential] using h

lemma nsdAccumScore_mgf_le
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (s0 : PopState) (lam : ℝ) (hlam : 0 ≤ lam) (R : ℕ) :
    mgf (fun x : NsdAccumState => (x.score : ℝ))
        ((kernelIter (nsdAccumKernel params) R)
          ⟨(s0, .idle), 0, 0⟩) lam ≤
      Real.exp ((R : ℝ) * lam ^ 2 / 2) := by
  let μ :=
    (kernelIter (nsdAccumKernel params) R)
      (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)
  have hreach :
      ∀ᵐ x ∂μ, nsdAccumReachable R x := by
    rw [ae_iff]
    rw [show
      {x : NsdAccumState | ¬nsdAccumReachable R x} =
        {x : NsdAccumState | nsdAccumReachable R x}ᶜ by
          ext x
          simp]
    exact nsdAccumKernel_reachable params s0 R
  have hpoint :
      ∀ᵐ x ∂μ,
        nsdExpPotential lam x =
          Real.exp (-((R : ℝ) * lam ^ 2 / 2)) *
            Real.exp (lam * (x.score : ℝ)) := by
    filter_upwards [hreach] with x hx
    unfold nsdExpPotential
    rw [hx.1]
    rw [← Real.exp_add]
    congr 1
    ring
  have hEq :
      ∫ x, nsdExpPotential lam x ∂μ =
        Real.exp (-((R : ℝ) * lam ^ 2 / 2)) *
          mgf (fun x : NsdAccumState => (x.score : ℝ))
            μ lam := by
    rw [integral_congr_ae hpoint, integral_const_mul]
    rfl
  have hIter :=
    nsdAccumKernel_exp_iter_le_one
      params hBias s0 lam hlam R
  have hmul :
      Real.exp (-((R : ℝ) * lam ^ 2 / 2)) *
          mgf (fun x : NsdAccumState => (x.score : ℝ))
            μ lam ≤
        Real.exp (-((R : ℝ) * lam ^ 2 / 2)) *
          Real.exp ((R : ℝ) * lam ^ 2 / 2) := by
    rw [← hEq]
    calc
      ∫ x, nsdExpPotential lam x ∂μ ≤ 1 := by
        simpa only [μ] using hIter
      _ = Real.exp (-((R : ℝ) * lam ^ 2 / 2)) *
          Real.exp ((R : ℝ) * lam ^ 2 / 2) := by
            rw [← Real.exp_add]
            ring_nf
            simp
  exact le_of_mul_le_mul_left hmul
    (Real.exp_pos (-((R : ℝ) * lam ^ 2 / 2)))

lemma nsdAccumScore_tail
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (s0 : PopState) (R : ℕ) (hR : 0 < R)
    (t : ℝ) (ht : 0 ≤ t) :
    ((kernelIter (nsdAccumKernel params) R)
        ⟨(s0, .idle), 0, 0⟩).real
        {x | t ≤ (x.score : ℝ)} ≤
      Real.exp (-(t ^ 2) / (2 * R)) := by
  let μ :=
    (kernelIter (nsdAccumKernel params) R)
      (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact
      (kernelIter_isMarkov
        (K := nsdAccumKernel params) R).isProbabilityMeasure
          ⟨(s0, .idle), 0, 0⟩
  let lam : ℝ := t / R
  have hlam : 0 ≤ lam := div_nonneg ht (Nat.cast_nonneg R)
  have hExpInt :
      Integrable
        (fun x : NsdAccumState =>
          Real.exp (lam * (x.score : ℝ))) μ := by
    have hreach :
        ∀ᵐ x ∂μ, nsdAccumReachable R x := by
      rw [ae_iff]
      rw [show
        {x : NsdAccumState | ¬nsdAccumReachable R x} =
          {x : NsdAccumState | nsdAccumReachable R x}ᶜ by
            ext x
            simp]
      exact nsdAccumKernel_reachable params s0 R
    apply Integrable.of_mem_Icc
      (Real.exp (-(lam * R)))
      (Real.exp (lam * R))
      (measurable_of_countable _).aemeasurable
    filter_upwards [hreach] with x hx
    constructor <;> apply Real.exp_le_exp.mpr
    · have hscore :
          -((R : ℕ) : ℤ) ≤ x.score := hx.2.1
      have hscoreReal :
          -(R : ℝ) ≤ (x.score : ℝ) := by
        exact_mod_cast hscore
      simpa only [mul_neg, neg_mul] using
        (mul_le_mul_of_nonneg_left hscoreReal hlam)
    · have hscore :
          (x.score : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hx.2.2
      exact mul_le_mul_of_nonneg_left hscore hlam
  have hMarkov :=
    measure_ge_le_exp_mul_mgf
      (μ := μ)
      (X := fun x : NsdAccumState => (x.score : ℝ))
      t hlam hExpInt
  have hMgf :=
    nsdAccumScore_mgf_le
      params hBias s0 lam hlam R
  calc
    μ.real {x | t ≤ (x.score : ℝ)}
        ≤ Real.exp (-lam * t) *
          mgf (fun x : NsdAccumState => (x.score : ℝ))
            μ lam := hMarkov
    _ ≤ Real.exp (-lam * t) *
        Real.exp ((R : ℝ) * lam ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hMgf (Real.exp_pos _).le
    _ = Real.exp (-(t ^ 2) / (2 * R)) := by
      rw [← Real.exp_add]
      apply congrArg Real.exp
      dsimp only [lam]
      field_simp
      ring

theorem lvLabeledPathMeasure_nsdInteractionSum_tail
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (s0 : PopState) (R : ℕ) (hR : 0 < R)
    (t : ℝ) (ht : 0 ≤ t) :
    lvLabeledPathMeasure .nonSelfDestructive params s0
        {ζ |
          t ≤
            ((nsdInteractionSumUpTo ζ R : ℤ) : ℝ)} ≤
      ENNReal.ofReal
        (Real.exp (-(t ^ 2) / (2 * R))) := by
  let P := nsdAccumPathMeasure params s0
  let A : Set (ℕ → LabeledPopState) :=
    {ζ |
      t ≤ ((nsdInteractionSumUpTo ζ R : ℤ) : ℝ)}
  let B : Set (ℕ → NsdAccumState) :=
    {ω |
      t ≤
        ((nsdInteractionSumUpTo
          (pathMap NsdAccumState.labeled ω) R : ℤ) : ℝ)}
  let C : Set (ℕ → NsdAccumState) :=
    {ω | t ≤ ((ω R).score : ℝ)}
  let D : Set NsdAccumState :=
    {x | t ≤ (x.score : ℝ)}
  have hAmeas : MeasurableSet A := by
    have hcast : Measurable (fun z : ℤ => (z : ℝ)) :=
      measurable_of_countable _
    exact
      (hcast.comp
        (measurable_nsdInteractionSumUpTo R))
          measurableSet_Ici
  have hDmeas : MeasurableSet D := by
    measurability
  have hAB :
      lvLabeledPathMeasure .nonSelfDestructive params s0 A =
        P B := by
    rw [← nsdAccumPathMeasure_map_labeled params s0]
    rw [Measure.map_apply
      (measurable_pathMap NsdAccumState.labeled
        (measurable_of_countable NsdAccumState.labeled))
      hAmeas]
    rfl
  have hBC : P B = P C := by
    apply measure_congr
    filter_upwards [
      nsdAccumPathMeasure_score_eq_sum_ae
        params s0] with ω hω
    change
      (t ≤
        ((nsdInteractionSumUpTo
          (pathMap NsdAccumState.labeled ω) R : ℤ) : ℝ)) =
        (t ≤ ((ω R).score : ℝ))
    apply propext
    rw [hω R]
  have hCD :
      P C =
        ((kernelIter (nsdAccumKernel params) R)
          (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)) D := by
    calc
      P C =
          (P.map (fun ω : ℕ → NsdAccumState => ω R)) D := by
            symm
            exact Measure.map_apply
              (measurable_pi_apply R) hDmeas
      _ =
          ((kernelIter (nsdAccumKernel params) R)
            (⟨(s0, .idle), 0, 0⟩ :
              NsdAccumState)) D := by
            rw [show P =
                homogeneousPathMeasure
                  (Measure.dirac
                    (⟨(s0, .idle), 0, 0⟩ :
                      NsdAccumState))
                  (nsdAccumKernel params) by
              rfl,
              homogeneousPathMeasure_dirac_marginal]
  have htail :=
    nsdAccumScore_tail
      params hBias s0 R hR t ht
  letI : IsProbabilityMeasure
      ((kernelIter (nsdAccumKernel params) R)
        (⟨(s0, .idle), 0, 0⟩ :
          NsdAccumState)) :=
    (kernelIter_isMarkov
      (K := nsdAccumKernel params) R).isProbabilityMeasure
        ⟨(s0, .idle), 0, 0⟩
  rw [show
      lvLabeledPathMeasure .nonSelfDestructive params s0
          {ζ |
            t ≤
              ((nsdInteractionSumUpTo ζ R : ℤ) : ℝ)} =
        lvLabeledPathMeasure .nonSelfDestructive params s0 A by
      rfl,
    hAB, hBC, hCD]
  rw [← ENNReal.toReal_le_toReal
    (measure_ne_top
      ((kernelIter (nsdAccumKernel params) R)
        (⟨(s0, .idle), 0, 0⟩ :
          NsdAccumState)) D)
    ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change Measure.real
      ((kernelIter (nsdAccumKernel params) R)
        (⟨(s0, .idle), 0, 0⟩ : NsdAccumState)) D ≤
    Real.exp (-t ^ 2 / (2 * (R : ℝ)))
  simpa only [D] using htail

theorem lvLabeledPathMeasure_nsdInteractionMax_tail
    (params : LVParams) (hBias : params.alpha1 ≤ params.alpha0)
    (s0 : PopState) (R : ℕ) (hR : 0 < R)
    (t : ℝ) (ht : 0 ≤ t) :
    lvLabeledPathMeasure .nonSelfDestructive params s0
        {ζ |
          ∃ i ∈ Finset.range R,
            t ≤
              ((nsdInteractionSumUpTo ζ (i + 1) : ℤ) :
                ℝ)} ≤
      (R : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-(t ^ 2) / (2 * R))) := by
  let P :=
    lvLabeledPathMeasure
      .nonSelfDestructive params s0
  let E : ℕ → Set (ℕ → LabeledPopState) :=
    fun i =>
      {ζ |
        t ≤
          ((nsdInteractionSumUpTo ζ (i + 1) : ℤ) :
            ℝ)}
  have hUnion :
      {ζ |
        ∃ i ∈ Finset.range R,
          t ≤
            ((nsdInteractionSumUpTo ζ (i + 1) : ℤ) :
              ℝ)} =
        ⋃ i ∈ Finset.range R, E i := by
    ext ζ
    simp [E]
  rw [hUnion]
  calc
    P (⋃ i ∈ Finset.range R, E i)
        ≤ ∑ i ∈ Finset.range R, P (E i) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range R,
        ENNReal.ofReal
          (Real.exp (-(t ^ 2) / (2 * R))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiR : i + 1 ≤ R := by
        have := Finset.mem_range.mp hi
        omega
      calc
        P (E i) ≤
            ENNReal.ofReal
              (Real.exp
                (-(t ^ 2) /
                  (2 * (((i + 1 : ℕ) : ℝ))))) := by
          simpa only [P, E] using
            lvLabeledPathMeasure_nsdInteractionSum_tail
              params hBias s0 (i + 1)
                (by omega) t ht
        _ ≤ ENNReal.ofReal
              (Real.exp
                (-(t ^ 2) / (2 * R))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have hfrac :
              t ^ 2 / (2 * (R : ℝ)) ≤
                t ^ 2 / (2 * ((i + 1 : ℕ) : ℝ)) := by
            gcongr
          simpa only [neg_div] using neg_le_neg hfrac
    _ = (R : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-(t ^ 2) / (2 * R))) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Almost every labelled NSD path records the reaction target and has no
intraspecific reaction when both intraspecific rates vanish. -/
lemma lvLabeledPathMeasure_valid_nonSelfDestructive_ae
    (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState) :
    ∀ᵐ ζ ∂lvLabeledPathMeasure .nonSelfDestructive params s0,
      ∀ t : Nat,
        (ζ (t + 1)).1 =
            lvReactionTarget .nonSelfDestructive
              (ζ t).1 (ζ (t + 1)).2 ∧
          (ζ (t + 1)).2 ≠ .intra0 ∧
          (ζ (t + 1)).2 ≠ .intra1 := by
  letI : Nonempty LabeledPopState := ⟨(s0, .idle)⟩
  unfold lvLabeledPathMeasure
  let Rel : LabeledPopState → LabeledPopState → Prop :=
    fun z z' =>
      z'.1 =
          lvReactionTarget .nonSelfDestructive z.1 z'.2 ∧
        z'.2 ≠ .intra0 ∧ z'.2 ≠ .intra1
  have hstep :
      ∀ z, ∀ᵐ z' ∂lvLabeledKernel
          .nonSelfDestructive params z,
        Rel z z' := by
    intro z
    have hno0 :
        ∀ᵐ z' ∂lvLabeledKernel
            .nonSelfDestructive params z,
          z'.2 ≠ .intra0 := by
      rw [ae_iff]
      calc
        lvLabeledKernel .nonSelfDestructive params z
            {z' | ¬z'.2 ≠ LVReaction.intra0} =
            lvLabeledKernel .nonSelfDestructive params z
              {z' | z'.2 = LVReaction.intra0} := by
                congr 1
                ext z'
                simp
        _ = 0 := by
          rw [lvLabeledKernel_reaction_probability]
          simp [lvReactionWeight, hGamma0]
    have hno1 :
        ∀ᵐ z' ∂lvLabeledKernel
            .nonSelfDestructive params z,
          z'.2 ≠ .intra1 := by
      rw [ae_iff]
      calc
        lvLabeledKernel .nonSelfDestructive params z
            {z' | ¬z'.2 ≠ LVReaction.intra1} =
            lvLabeledKernel .nonSelfDestructive params z
              {z' | z'.2 = LVReaction.intra1} := by
                congr 1
                ext z'
                simp
        _ = 0 := by
          rw [lvLabeledKernel_reaction_probability]
          simp [lvReactionWeight, hGamma1]
    filter_upwards [
      lvLabeledKernel_ae_reactionTarget
        .nonSelfDestructive params z,
      hno0, hno1] with z' htarget h0 h1
    exact ⟨htarget, h0, h1⟩
  exact homogeneousPathMeasure_transition_ae
    (lvLabeledKernel .nonSelfDestructive params)
    (s0, .idle) Rel hstep

noncomputable def badNoncompetitiveScore
    (s : PopState) (r : LVReaction) : ℤ := by
  classical
  exact if isBadNoncompetitiveReaction s r then 1 else 0

lemma nonSelfDestructive_gap_step_bound
    (s s' : PopState) (r : LVReaction)
    (hpositive : 0 < Nat.min s.1 s.2)
    (hgap : 0 < gap s)
    (htarget :
      s' = lvReactionTarget .nonSelfDestructive s r)
    (hnot0 : r ≠ .intra0)
    (hnot1 : r ≠ .intra1) :
    (gap s : ℤ) ≤
      (gap s' : ℤ) +
        badNoncompetitiveScore s r +
        nsdInteractionScore r := by
  classical
  subst s'
  rcases s with ⟨a, b⟩
  cases r <;>
    simp_all [lvReactionTarget, gap,
      isBadNoncompetitiveReaction, badNoncompetitiveScore,
      nsdInteractionScore] <;>
    omega

lemma nsd_gap_invariant_before_nonpositive
    (ζ : Nat → LabeledPopState)
    (hvalid : ∀ t : Nat,
      (ζ (t + 1)).1 =
          lvReactionTarget .nonSelfDestructive
            (ζ t).1 (ζ (t + 1)).2 ∧
        (ζ (t + 1)).2 ≠ .intra0 ∧
        (ζ (t + 1)).2 ≠ .intra1)
    (t : Nat)
    (hbefore : ∀ i < t,
      0 < gap (ζ i).1 ∧
        0 < Nat.min (ζ i).1.1 (ζ i).1.2) :
    gap (ζ 0).1 ≤
      gap (ζ t).1 +
        (labeledBadCountUpTo ζ t : ℤ) +
        nsdInteractionSumUpTo ζ t := by
  classical
  induction t with
  | zero =>
      simp [labeledBadCountUpTo,
        nsdInteractionSumUpTo]
  | succ t ih =>
      have hbefore' : ∀ i < t,
          0 < gap (ζ i).1 ∧
            0 < Nat.min (ζ i).1.1 (ζ i).1.2 := by
        intro i hi
        exact hbefore i (by omega)
      have hprev := ih hbefore'
      have ht := hbefore t (Nat.lt_succ_self t)
      have hstep :=
        nonSelfDestructive_gap_step_bound
          (ζ t).1 (ζ (t + 1)).1
          (ζ (t + 1)).2 ht.2 ht.1
          (hvalid t).1 (hvalid t).2.1
          (hvalid t).2.2
      have hbad :
          labeledBadCountUpTo ζ (t + 1) =
            labeledBadCountUpTo ζ t +
              if isBadNoncompetitiveReaction
                  (ζ t).1 (ζ (t + 1)).2
                then 1 else 0 := by
        unfold labeledBadCountUpTo
        rw [Finset.sum_range_succ]
      have hscore :
          nsdInteractionSumUpTo ζ (t + 1) =
            nsdInteractionSumUpTo ζ t +
              nsdInteractionScore
                (ζ (t + 1)).2 := by
        unfold nsdInteractionSumUpTo
        rw [Finset.sum_range_succ]
      have hbadScore :
          badNoncompetitiveScore
              (ζ t).1 (ζ (t + 1)).2 =
            ((if isBadNoncompetitiveReaction
                (ζ t).1 (ζ (t + 1)).2
              then 1 else 0 : ℕ) : ℤ) := by
        unfold badNoncompetitiveScore
        by_cases h :
            isBadNoncompetitiveReaction
              (ζ t).1 (ζ (t + 1)).2 <;>
          simp [h]
      rw [hbadScore] at hstep
      calc
        gap (ζ 0).1 ≤
            gap (ζ t).1 +
              (labeledBadCountUpTo ζ t : ℤ) +
              nsdInteractionSumUpTo ζ t :=
          hprev
        _ ≤
            (gap (ζ (t + 1)).1 : ℤ) +
              ((if isBadNoncompetitiveReaction
                  (ζ t).1 (ζ (t + 1)).2
                then 1 else 0 : ℕ) : ℤ) +
              nsdInteractionScore (ζ (t + 1)).2 +
              (labeledBadCountUpTo ζ t : ℤ) +
              nsdInteractionSumUpTo ζ t := by
          omega
        _ =
            gap (ζ (t + 1)).1 +
              (labeledBadCountUpTo ζ (t + 1) : ℤ) +
              nsdInteractionSumUpTo ζ (t + 1) := by
          rw [hbad, hscore]
          push_cast
          ring

lemma nsd_failure_implies_interaction_max
    (a b : Nat) (ζ : Nat → LabeledPopState)
    (hab : b < a)
    (hζ0 : (ζ 0).1 = (a, b))
    (hvalid : ∀ t : Nat,
      (ζ (t + 1)).1 =
          lvReactionTarget .nonSelfDestructive
            (ζ t).1 (ζ (t + 1)).2 ∧
        (ζ (t + 1)).2 ≠ .intra0 ∧
        (ζ (t + 1)).2 ≠ .intra1)
    (τ R L : Nat)
    (hτ :
      consensusTime (forgetLVLabels ζ) =
        (τ : WithTop Nat))
    (hτR : τ < R)
    (hBad :
      labeledBadCountBeforeConsensus ζ < L)
    (t : ℝ)
    (hgap :
      (L : ℝ) + t ≤ (a : ℝ) - (b : ℝ))
    (hnot :
      ¬majorityConsensusEvent
        (a, b) (forgetLVLabels ζ)) :
    ∃ i ∈ Finset.range R,
      t ≤
        ((nsdInteractionSumUpTo ζ (i + 1) : ℤ) :
          ℝ) := by
  classical
  have hcons :=
    reachedConsensus_at_consensusTime'
      (forgetLVLabels ζ) τ hτ
  have hmaj : species0Majority (a, b) := by
    simp [species0Majority]
    omega
  have hend : gap (ζ τ).1 ≤ 0 := by
    simp only [majorityConsensusEvent, hτ, hmaj,
      true_and, forgetLVLabels] at hnot
    simp only [reachedConsensus, forgetLVLabels] at hcons
    rcases hcons with hzero0 | hzero1
    · simp [gap, hzero0]
    · have hzero0 : (ζ τ).1.1 = 0 := by
        by_contra hpos
        apply hnot
        exact Or.inl
          ⟨Nat.pos_of_ne_zero hpos, hzero1⟩
      simp [gap, hzero0, hzero1]
  let p : Nat → Prop :=
    fun u => u ≤ τ ∧ gap (ζ u).1 ≤ 0
  have hex : ∃ u, p u := ⟨τ, le_rfl, hend⟩
  let j : Nat := Nat.find hex
  have hj : p j := Nat.find_spec hex
  have hbeforeGap :
      ∀ i < j, 0 < gap (ζ i).1 := by
    intro i hi
    have hnotp : ¬p i := Nat.find_min hex hi
    have hiτ : i ≤ τ :=
      le_trans (Nat.le_of_lt hi) hj.1
    exact lt_of_not_ge fun hle =>
      hnotp ⟨hiτ, hle⟩
  have hbefore :
      ∀ i < j,
        0 < gap (ζ i).1 ∧
          0 < Nat.min (ζ i).1.1 (ζ i).1.2 := by
    intro i hi
    refine ⟨hbeforeGap i hi, ?_⟩
    have hne :
        ¬reachedConsensus
          (forgetLVLabels ζ i) :=
      ((consensusTime_eq_coe_iff
        (forgetLVLabels ζ) τ).mp hτ).2 i
          (lt_of_lt_of_le hi hj.1)
    simp only [reachedConsensus, forgetLVLabels,
      not_or] at hne
    exact Nat.lt_min.mpr
      ⟨Nat.pos_of_ne_zero hne.1,
        Nat.pos_of_ne_zero hne.2⟩
  have hinv :=
    nsd_gap_invariant_before_nonpositive
      ζ hvalid j hbefore
  have hgap0 :
      gap (ζ 0).1 = (a : Int) - (b : Int) := by
    simp [hζ0, gap]
  rw [hgap0] at hinv
  have hcountj :
      labeledBadCountUpTo ζ j ≤
        labeledBadCountUpTo ζ τ :=
    labeledBadCountUpTo_mono ζ hj.1
  have hbeforeEq :
      labeledBadCountBeforeConsensus ζ =
        labeledBadCountUpTo ζ τ := by
    simp [labeledBadCountBeforeConsensus, hτ]
  rw [hbeforeEq] at hBad
  have hjpos : 0 < j := by
    have hj' :
        j ≤ τ ∧ gap (ζ j).1 ≤ 0 := by
      simpa only [p] using hj
    by_contra hj0
    have : j = 0 := Nat.eq_zero_of_not_pos hj0
    rw [this] at hj'
    rw [hζ0] at hj'
    simp only [gap] at hj'
    omega
  refine ⟨j - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hsum :
      nsdInteractionSumUpTo ζ (j - 1 + 1) =
        nsdInteractionSumUpTo ζ j := by
    congr 1
    omega
  rw [hsum]
  have hinvReal :
      (a : ℝ) - (b : ℝ) ≤
        (labeledBadCountUpTo ζ j : ℝ) +
          (nsdInteractionSumUpTo ζ j : ℝ) := by
    exact_mod_cast
      (show
        (a : ℤ) - (b : ℤ) ≤
          (labeledBadCountUpTo ζ j : ℤ) +
            nsdInteractionSumUpTo ζ j by
        linarith [hinv, hj.2])
  have hcountReal :
      (labeledBadCountUpTo ζ j : ℝ) ≤ L := by
    exact_mod_cast
      (le_trans hcountj
        (Nat.le_of_lt hBad))
  linarith

end LVConsensus
