import LVConsensus.Definitions
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CentralLimitTheorem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Topology
open scoped BigOperators

namespace LVConsensus

/-! ## Key real-analysis inequality for the Chernoff bound -/

/-- `log(u) ≥ 2(u-1)/(u+1)` for `u ≥ 1`.
Proof: the function `g(u) = log(u) + 4/(u+1) - 2` satisfies `g(1) = 0` and
`g'(u) = (u-1)²/(u(u+1)²) ≥ 0`, so `g` is monotone on `[1,∞)`. -/
private lemma log_ge_two_sub_div {u : ℝ} (hu : 1 ≤ u) :
    2 * (u - 1) / (u + 1) ≤ Real.log u := by
  have hu_pos : (0 : ℝ) < u := by linarith
  have hu1_pos : (0 : ℝ) < u + 1 := by linarith
  suffices h : 0 ≤ Real.log u + 4 / (u + 1) - 2 by
    have : 2 * (u - 1) / (u + 1) = 2 - 4 / (u + 1) := by field_simp; ring
    linarith
  set g : ℝ → ℝ := fun x => Real.log x + 4 / (x + 1) - 2
  change 0 ≤ g u
  have hg1 : g 1 = 0 := by simp [g, Real.log_one]; norm_num
  suffices hmono : MonotoneOn g (Set.Ici 1) by
    have h1mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := Set.mem_Ici.mpr (le_refl 1)
    have humem : u ∈ Set.Ici (1 : ℝ) := hu
    linarith [hmono h1mem humem hu]
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
  · -- ContinuousOn g [1, ∞)
    apply ContinuousOn.sub
    · exact ContinuousOn.add
        (Real.continuousOn_log.mono fun x hx => ne_of_gt (by linarith [Set.mem_Ici.mp hx]))
        (continuousOn_const.div (continuousOn_id.add continuousOn_const)
          fun x hx => ne_of_gt (by linarith [Set.mem_Ici.mp hx]))
    · exact continuousOn_const
  · -- DifferentiableOn g (interior [1, ∞)) = (1, ∞)
    rw [interior_Ici]
    intro x hx
    have hx_pos : 0 < x := by linarith [Set.mem_Ioi.mp hx]
    have hx1_ne : x + 1 ≠ 0 := ne_of_gt (by linarith)
    apply DifferentiableAt.differentiableWithinAt
    exact ((Real.differentiableAt_log (ne_of_gt hx_pos)).add
      (differentiableAt_const _ |>.div (differentiableAt_id.add (differentiableAt_const _))
        hx1_ne)).sub (differentiableAt_const _)
  · -- 0 ≤ deriv g x for x ∈ (1, ∞)
    rw [interior_Ici]
    intro x hx
    have hx_pos : 0 < x := by linarith [Set.mem_Ioi.mp hx]
    have hx1_pos : 0 < x + 1 := by linarith
    have hx1_ne : x + 1 ≠ 0 := ne_of_gt hx1_pos
    -- Compute HasDerivAt for g
    have d_log : HasDerivAt Real.log x⁻¹ x :=
      Real.hasDerivAt_log (ne_of_gt hx_pos)
    have d_inv : HasDerivAt (fun x => (x + 1)⁻¹) (-(1 / (x + 1) ^ 2)) x := by
      have h := ((hasDerivAt_id x).add (hasDerivAt_const x 1)).inv hx1_ne
      simp only [id, Pi.add_apply] at h
      convert h using 1
      all_goals first
        | rfl
        | (funext y; simp [add_comm])
        | ring
    have d_frac : HasDerivAt (fun x => 4 / (x + 1)) (-(4 / (x + 1) ^ 2)) x := by
      have := (hasDerivAt_const x (4 : ℝ)).mul d_inv
      simp only [div_eq_mul_inv] at this ⊢
      convert this using 1
      all_goals first
        | rfl
        | (funext y; ring)
        | ring
    have d_g : HasDerivAt g (x⁻¹ - 4 / (x + 1) ^ 2) x := by
      have := (d_log.add d_frac).sub (hasDerivAt_const x 2)
      convert this using 1
      all_goals first
        | rfl
        | (funext y; simp [g, div_eq_mul_inv]; ring)
        | ring
    rw [d_g.deriv]
    -- Show x⁻¹ - 4/(x+1)² ≥ 0 ↔ 4x ≤ (x+1)² ↔ (x-1)² ≥ 0
    have : x⁻¹ - 4 / (x + 1) ^ 2 = ((x + 1) ^ 2 - 4 * x) / (x * (x + 1) ^ 2) := by
      field_simp
    rw [this]
    apply div_nonneg
    · nlinarith [sq_nonneg (x - 1)]
    · exact mul_nonneg (le_of_lt hx_pos) (le_of_lt (pow_pos hx1_pos 2))

/-- From `log_ge_two_sub_div`: `(1+ε)·log(1+ε) - ε ≥ ε²/(2+ε)` for `ε > 0`. -/
private lemma chernoff_exponent_bound {ε : ℝ} (hε : 0 < ε) :
    ε ^ 2 / (2 + ε) ≤ (1 + ε) * Real.log (1 + ε) - ε := by
  have h2ε : (0 : ℝ) < 2 + ε := by linarith
  have hlog := log_ge_two_sub_div (by linarith : (1 : ℝ) ≤ 1 + ε)
  -- hlog : 2 * (1 + ε - 1) / (1 + ε + 1) ≤ log (1 + ε)
  -- Simplify: 2 * ε / (2 + ε) ≤ log(1 + ε)
  -- Multiply by (1+ε) ≥ 0: (1+ε) * 2ε/(2+ε) ≤ (1+ε)*log(1+ε)
  -- LHS = 2ε(1+ε)/(2+ε) = (2ε+2ε²)/(2+ε) = ε + ε²/(2+ε)
  -- So: ε + ε²/(2+ε) ≤ (1+ε)*log(1+ε), hence ε²/(2+ε) ≤ (1+ε)*log(1+ε) - ε
  have hε_nn : (0 : ℝ) ≤ 1 + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hε_nn
  -- hmul : (1+ε) * (2*(1+ε-1)/(1+ε+1)) ≤ (1+ε) * log(1+ε)
  have hlhs : (1 + ε) * (2 * (1 + ε - 1) / (1 + ε + 1)) = ε + ε ^ 2 / (2 + ε) := by
    field_simp; ring
  linarith

/-- The elementary exponent estimate used in the lower-tail Chernoff bound:
`ε²/2 ≤ ε + (1-ε) log(1-ε)` for `0 < ε < 1`. -/
private lemma chernoff_lower_exponent_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ε ^ 2 / 2 ≤ ε + (1 - ε) * Real.log (1 - ε) := by
  let g : ℝ → ℝ := fun x => x + (1 - x) * Real.log (1 - x) - x ^ 2 / 2
  have hg0 : g 0 = 0 := by simp [g]
  have hmono : MonotoneOn g (Set.Icc 0 ε) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 ε)
    · apply ContinuousOn.sub
      · apply ContinuousOn.add continuousOn_id
        apply ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
        exact (continuousOn_const.sub continuousOn_id).log fun x hx => by
          change 1 - x ≠ 0
          exact ne_of_gt (by
            have hxε : x ≤ ε := hx.2
            linarith)
      · exact (continuousOn_id.pow 2).div_const 2
    · rw [interior_Icc]
      intro x hx
      have hxε : x < ε := hx.2
      have hx1 : x < 1 := lt_trans hxε hε1
      have hne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
      have hbase : DifferentiableAt ℝ (fun y : ℝ => 1 - y) x :=
        (differentiableAt_const 1).sub differentiableAt_id
      have hlog : DifferentiableAt ℝ (fun y : ℝ => Real.log (1 - y)) x :=
        hbase.log hne
      exact ((differentiableAt_id.add (hbase.mul hlog)).sub
        ((differentiableAt_id.pow 2).div_const 2)).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hxε : x < ε := hx.2
      have hx1 : x < 1 := lt_trans hxε hε1
      have hpos : 0 < 1 - x := sub_pos.mpr hx1
      have hderiv : HasDerivAt g (-Real.log (1 - x) - x) x := by
        have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-(1 - x)⁻¹) x := by
          convert (Real.hasDerivAt_log (ne_of_gt hpos)).comp x
            ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1
          all_goals first | rfl | ring
        have hmul := ((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul hlog
        have hsq := ((hasDerivAt_id x).pow 2).div_const 2
        convert ((hasDerivAt_id x).add hmul).sub hsq using 1
        all_goals first
          | rfl
          | (funext y; simp [g, id_eq]; ring)
          | (simp only [Pi.sub_apply, id_eq]; field_simp; ring)
      rw [hderiv.deriv]
      have hlog_le : Real.log (1 - x) ≤ -x := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 ε := ⟨le_rfl, hε.le⟩
  have hεmem : ε ∈ Set.Icc 0 ε := ⟨hε.le, le_rfl⟩
  have := hmono h0mem hεmem hε.le
  rw [hg0] at this
  change 0 ≤ ε + (1 - ε) * Real.log (1 - ε) - ε ^ 2 / 2 at this
  linarith

/-- Stochastic dominance: f is stochastically dominated by g under μ,
    meaning P[f ≥ t] ≤ P[g ≥ t] for all thresholds t. -/
def StochDom {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → Real) : Prop :=
  ∀ t : Real, μ {ω | t ≤ f ω} ≤ μ {ω | t ≤ g ω}

/-- Chernoff bound for sums of independent Bernoulli random variables.
    Paper `lemma:chernoff`: P[S ≥ (1+ε)·E[S]] ≤ exp(-E[S]·ε²/(2+ε)).
    Here S = Σᵢ 𝟙[Xᵢ = true] is the sum of independent indicators.

    Proof: Use Mathlib's CGF Chernoff bound `measure_ge_le_exp_cgf` with
    t = log(1+ε). Decompose cgf via `iIndepFun.cgf_sum`, bound each
    cgf(Z_i, t) ≤ E[Z_i]·(eᵗ-1) via `log(1+x) ≤ x`, optimize.
    The key inequality (1+ε)·log(1+ε) - ε ≥ ε²/(2+ε) is proved
    via `log_ge_two_sub_div`. -/
theorem lemma_chernoff_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Bool) (S : Ω → Real)
    (hRep : ∀ ω, S ω = ∑ i : Fin n, if X i ω then (1 : Real) else 0)
    (hXMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (ε : Real) (hε : 0 < ε) :
    μ {ω | S ω ≥ (1 + ε) * (∫ x, S x ∂μ)} ≤
      ENNReal.ofReal (Real.exp (-(∫ x, S x ∂μ) * ε ^ (2 : Nat) / (2 + ε))) := by
  -- Define real-valued indicators Z_i(ω) = if X_i(ω) then 1 else 0
  set Z : Fin n → Ω → ℝ := fun i ω => if X i ω then 1 else 0 with hZ_def
  -- S and ∑ Z_i agree pointwise
  have hSZ : ∀ ω, S ω = ∑ i : Fin n, Z i ω := hRep
  -- Bool → ℝ indicator is measurable
  have hf_meas : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
    measurable_of_finite _
  -- Z_i are measurable and independent
  have hZ_meas : ∀ i, Measurable (Z i) := fun i => hf_meas.comp (hXMeas i)
  have hZ_indep : iIndepFun Z μ := hIndep.comp _ (fun _ => hf_meas)
  -- Z_i are integrable (bounded in [0,1])
  have hZ_bound : ∀ i ω, Z i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i ω; simp only [Z]; cases X i ω <;> simp
  have hZ_int : ∀ i, Integrable (Z i) μ := fun i =>
    Integrable.of_mem_Icc 0 1 (hZ_meas i).aemeasurable (ae_of_all _ fun ω => hZ_bound i ω)
  -- E[S] = ∑ E[Z_i]
  have hμS : ∫ x, S x ∂μ = ∑ i : Fin n, ∫ ω, Z i ω ∂μ := by
    conv_lhs => rw [show (fun x => S x) = fun x => ∑ i, Z i x from funext hSZ]
    exact integral_finset_sum _ fun i _ => hZ_int i
  -- Choose t₀ = log(1+ε) > 0
  set t₀ := Real.log (1 + ε)
  have ht₀_pos : 0 < t₀ := Real.log_pos (by linarith)
  -- exp(t₀ * Z_i(ω)) = 1 + Z_i(ω)*(exp(t₀)-1) pointwise (for {0,1}-valued Z_i)
  have hpw : ∀ i ω, exp (t₀ * Z i ω) = 1 + Z i ω * (exp t₀ - 1) := by
    intro i ω; simp only [Z]; cases X i ω <;> simp [mul_comm]
  -- exp(t₀ * Z_i) is integrable (bounded, hence integrable by rewriting via hpw)
  have hZ_int_exp : ∀ i, Integrable (fun ω => exp (t₀ * Z i ω)) μ := fun i => by
    apply Integrable.congr (((hZ_int i).const_mul (exp t₀ - 1)).add (integrable_const 1))
    filter_upwards with ω
    simp only [Pi.add_apply]
    linarith [hpw i ω]
  -- E[Z_i] ≥ 0
  have hEZ_nn : ∀ i, 0 ≤ ∫ ω, Z i ω ∂μ := fun i =>
    integral_nonneg (fun ω => (hZ_bound i ω).1)
  -- E[S] ≥ 0
  have hμS_nn : 0 ≤ ∫ x, S x ∂μ := by rw [hμS]; exact Finset.sum_nonneg fun i _ => hEZ_nn i
  -- MGF of Z_i: mgf(Z_i, t₀) = 1 + (e^t₀ - 1) * E[Z_i]
  have hmgf : ∀ i, mgf (Z i) μ t₀ = 1 + (exp t₀ - 1) * ∫ ω, Z i ω ∂μ := by
    intro i; simp only [mgf]
    have hcongr : ∫ ω, exp (t₀ * Z i ω) ∂μ = ∫ ω, (1 + Z i ω * (exp t₀ - 1)) ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => hpw i ω)
    rw [hcongr, integral_add (integrable_const 1) ((hZ_int i).mul_const _),
      integral_const, probReal_univ, one_smul, integral_mul_const]
    ring
  -- CGF of Z_i: cgf(Z_i, t₀) ≤ E[Z_i] * (e^t₀ - 1) via log(1+x) ≤ x
  have hcgf_bound : ∀ i, cgf (Z i) μ t₀ ≤ (∫ ω, Z i ω ∂μ) * (exp t₀ - 1) := by
    intro i; simp only [cgf, hmgf i]
    have hy : 0 ≤ (exp t₀ - 1) * ∫ ω, Z i ω ∂μ :=
      mul_nonneg (by linarith [Real.exp_pos t₀, Real.add_one_le_exp t₀]) (hEZ_nn i)
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + (exp t₀ - 1) * ∫ ω, Z i ω ∂μ by linarith)
    linarith [mul_comm (∫ ω, Z i ω ∂μ) (exp t₀ - 1)]
  -- CGF of S via independence: cgf(∑ Z_i, t₀) = ∑ cgf(Z_i, t₀)
  have hcgf_sum : cgf (∑ i : Fin n, Z i) μ t₀ = ∑ i, cgf (Z i) μ t₀ :=
    hZ_indep.cgf_sum hZ_meas (fun i _ => hZ_int_exp i)
  -- Combined CGF bound: cgf(∑ Z_i, t₀) ≤ E[S] * (e^t₀ - 1)
  have hcgf_total : cgf (∑ i : Fin n, Z i) μ t₀ ≤ (∫ x, S x ∂μ) * (exp t₀ - 1) := by
    rw [hcgf_sum, hμS]
    calc ∑ i, cgf (Z i) μ t₀
        ≤ ∑ i, (∫ ω, Z i ω ∂μ) * (exp t₀ - 1) :=
          Finset.sum_le_sum fun i _ => hcgf_bound i
      _ = (∑ i, ∫ ω, Z i ω ∂μ) * (exp t₀ - 1) := (Finset.sum_mul _ _ _).symm
  -- exp(t₀ * ∑ Z_i) is integrable (bounded since Z_i ∈ [0,1])
  have hS_int_exp : Integrable (fun ω => exp (t₀ * (∑ i : Fin n, Z i ω))) μ := by
    apply Integrable.of_mem_Icc 1 (exp (t₀ * ↑n))
    · exact ((Finset.measurable_sum _ (fun i _ => hZ_meas i)).const_mul t₀ |>.exp).aemeasurable
    · refine ae_of_all _ fun ω => ⟨?_, ?_⟩
      · exact Real.one_le_exp (mul_nonneg ht₀_pos.le
          (Finset.sum_nonneg fun i _ => (hZ_bound i ω).1))
      · apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ ht₀_pos.le
        calc ∑ i : Fin n, Z i ω
            ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hZ_bound i ω).2
          _ = ↑n := by simp [Finset.sum_const, nsmul_eq_mul]
  -- Apply Mathlib Chernoff: μ.real{(1+ε)μ_S ≤ ∑ Z_i} ≤ exp(-t₀(1+ε)μ_S + cgf(∑ Z_i, t₀))
  set μ_S := ∫ x, S x ∂μ
  have hreal : μ.real {ω | (1 + ε) * μ_S ≤ ∑ i : Fin n, Z i ω} ≤
      exp (-μ_S * ε ^ (2 : Nat) / (2 + ε)) := by
    -- Step 1: Apply Mathlib's CGF Chernoff bound
    have hchernoff := measure_ge_le_exp_cgf (μ := μ) ((1 + ε) * μ_S)
      (le_of_lt ht₀_pos) hS_int_exp
    -- cgf from measure_ge_le_exp_cgf uses (fun ω => ∑ i, Z i ω), convert to (∑ i, Z i)
    have hcgf_eq : cgf (fun ω => ∑ i : Fin n, Z i ω) μ t₀ =
        cgf (∑ i : Fin n, Z i) μ t₀ := by
      simp only [cgf, mgf]; congr 1; congr 1; ext ω; simp [Finset.sum_apply]
    rw [hcgf_eq] at hchernoff
    -- Step 2: Bound the CGF
    have hstep2 : exp (-t₀ * ((1 + ε) * μ_S) + cgf (∑ i : Fin n, Z i) μ t₀) ≤
        exp (-t₀ * ((1 + ε) * μ_S) + μ_S * (exp t₀ - 1)) :=
      Real.exp_le_exp.mpr (by linarith [hcgf_total])
    -- Step 3: Simplify exponent using exp(log(1+ε)) = 1+ε
    have hexp_t₀ : Real.exp t₀ = 1 + ε := Real.exp_log (by linarith)
    have hstep3 : -t₀ * ((1 + ε) * μ_S) + μ_S * (exp t₀ - 1) =
        -μ_S * ((1 + ε) * t₀ - ε) := by rw [hexp_t₀]; ring
    -- Step 4: Apply chernoff_exponent_bound
    have hexpo := chernoff_exponent_bound hε
    have hstep4 : -μ_S * ((1 + ε) * t₀ - ε) ≤ -μ_S * (ε ^ 2 / (2 + ε)) :=
      mul_le_mul_of_nonpos_left hexpo (neg_nonpos.mpr hμS_nn)
    -- Step 5: Combine
    calc μ.real {ω | (1 + ε) * μ_S ≤ ∑ i : Fin n, Z i ω}
        ≤ exp (-t₀ * ((1 + ε) * μ_S) + cgf (∑ i : Fin n, Z i) μ t₀) := hchernoff
      _ ≤ exp (-t₀ * ((1 + ε) * μ_S) + μ_S * (exp t₀ - 1)) := hstep2
      _ = exp (-μ_S * ((1 + ε) * t₀ - ε)) := by rw [hstep3]
      _ ≤ exp (-μ_S * (ε ^ 2 / (2 + ε))) := Real.exp_le_exp.mpr hstep4
      _ = exp (-μ_S * ε ^ (2 : Nat) / (2 + ε)) := by ring_nf
  -- Convert from μ.real to μ (ENNReal)
  have hset_eq : {ω | S ω ≥ (1 + ε) * μ_S} =
      {ω | (1 + ε) * μ_S ≤ ∑ i : Fin n, Z i ω} := by
    ext ω; simp [ge_iff_le, hSZ ω]
  rw [hset_eq]
  have hfin : μ {ω | (1 + ε) * μ_S ≤ ∑ i : Fin n, Z i ω} ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Lower-tail Chernoff bound for sums of independent Bernoulli random variables:
`P[S ≤ (1-ε) E[S]] ≤ exp (-E[S] ε²/2)` for `0 < ε < 1`. -/
theorem lemma_chernoff_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Bool) (S : Ω → Real)
    (hRep : ∀ ω, S ω = ∑ i : Fin n, if X i ω then (1 : Real) else 0)
    (hXMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (ε : Real) (hε : 0 < ε) (hε1 : ε < 1) :
    μ {ω | S ω ≤ (1 - ε) * (∫ x, S x ∂μ)} ≤
      ENNReal.ofReal (Real.exp (-(∫ x, S x ∂μ) * ε ^ (2 : Nat) / 2)) := by
  set Z : Fin n → Ω → ℝ := fun i ω => if X i ω then 1 else 0 with hZ_def
  have hSZ : ∀ ω, S ω = ∑ i : Fin n, Z i ω := hRep
  have hf_meas : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
    measurable_of_finite _
  have hZ_meas : ∀ i, Measurable (Z i) := fun i => hf_meas.comp (hXMeas i)
  have hZ_indep : iIndepFun Z μ := hIndep.comp _ (fun _ => hf_meas)
  have hZ_bound : ∀ i ω, Z i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i ω
    simp only [Z]
    cases X i ω <;> simp
  have hZ_int : ∀ i, Integrable (Z i) μ := fun i =>
    Integrable.of_mem_Icc 0 1 (hZ_meas i).aemeasurable
      (ae_of_all _ fun ω => hZ_bound i ω)
  have hμS : ∫ x, S x ∂μ = ∑ i : Fin n, ∫ ω, Z i ω ∂μ := by
    conv_lhs => rw [show (fun x => S x) = fun x => ∑ i, Z i x from funext hSZ]
    exact integral_finset_sum _ fun i _ => hZ_int i
  have hEZ_nn : ∀ i, 0 ≤ ∫ ω, Z i ω ∂μ := fun i =>
    integral_nonneg (fun ω => (hZ_bound i ω).1)
  have hμS_nn : 0 ≤ ∫ x, S x ∂μ := by
    rw [hμS]
    exact Finset.sum_nonneg fun i _ => hEZ_nn i
  set t₀ := Real.log (1 - ε)
  have h1ε_pos : 0 < 1 - ε := by linarith
  have ht₀_neg : t₀ < 0 := Real.log_neg h1ε_pos (by linarith)
  have hpw : ∀ i ω, exp (t₀ * Z i ω) = 1 + Z i ω * (exp t₀ - 1) := by
    intro i ω
    simp only [Z]
    cases X i ω <;> simp [mul_comm]
  have hZ_int_exp : ∀ i, Integrable (fun ω => exp (t₀ * Z i ω)) μ := fun i => by
    apply Integrable.congr (((hZ_int i).const_mul (exp t₀ - 1)).add (integrable_const 1))
    filter_upwards with ω
    simp only [Pi.add_apply]
    linarith [hpw i ω]
  have hmgf : ∀ i, mgf (Z i) μ t₀ =
      1 + (exp t₀ - 1) * ∫ ω, Z i ω ∂μ := by
    intro i
    simp only [mgf]
    have hcongr : ∫ ω, exp (t₀ * Z i ω) ∂μ =
        ∫ ω, (1 + Z i ω * (exp t₀ - 1)) ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => hpw i ω)
    rw [hcongr, integral_add (integrable_const 1) ((hZ_int i).mul_const _),
      integral_const, probReal_univ, one_smul, integral_mul_const]
    ring
  have hcgf_bound : ∀ i, cgf (Z i) μ t₀ ≤
      (∫ ω, Z i ω ∂μ) * (exp t₀ - 1) := by
    intro i
    rw [cgf, hmgf i]
    have hpos : 0 < 1 + (exp t₀ - 1) * ∫ ω, Z i ω ∂μ := by
      rw [← hmgf i]
      exact mgf_pos (hZ_int_exp i)
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith [mul_comm (∫ ω, Z i ω ∂μ) (exp t₀ - 1)]
  have hcgf_sum : cgf (∑ i : Fin n, Z i) μ t₀ = ∑ i, cgf (Z i) μ t₀ :=
    hZ_indep.cgf_sum hZ_meas (fun i _ => hZ_int_exp i)
  have hcgf_total : cgf (∑ i : Fin n, Z i) μ t₀ ≤
      (∫ x, S x ∂μ) * (exp t₀ - 1) := by
    rw [hcgf_sum, hμS]
    calc ∑ i, cgf (Z i) μ t₀
        ≤ ∑ i, (∫ ω, Z i ω ∂μ) * (exp t₀ - 1) :=
          Finset.sum_le_sum fun i _ => hcgf_bound i
      _ = (∑ i, ∫ ω, Z i ω ∂μ) * (exp t₀ - 1) := (Finset.sum_mul _ _ _).symm
  have hS_int_exp : Integrable (fun ω => exp (t₀ * (∑ i : Fin n, Z i ω))) μ := by
    apply Integrable.of_mem_Icc (exp (t₀ * (n : ℝ))) 1
    · exact ((Finset.measurable_sum _ (fun i _ => hZ_meas i)).const_mul t₀ |>.exp).aemeasurable
    · refine ae_of_all _ fun ω => ⟨?_, ?_⟩
      · apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonpos_left _ ht₀_neg.le
        calc ∑ i : Fin n, Z i ω
            ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hZ_bound i ω).2
          _ = ↑n := by simp [Finset.sum_const, nsmul_eq_mul]
      · exact Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg ht₀_neg.le
            (Finset.sum_nonneg fun i _ => (hZ_bound i ω).1))
  set μ_S := ∫ x, S x ∂μ
  have hreal : μ.real {ω | ∑ i : Fin n, Z i ω ≤ (1 - ε) * μ_S} ≤
      exp (-μ_S * ε ^ (2 : Nat) / 2) := by
    have hchernoff := measure_le_le_exp_cgf (μ := μ) ((1 - ε) * μ_S)
      ht₀_neg.le hS_int_exp
    have hcgf_eq : cgf (fun ω => ∑ i : Fin n, Z i ω) μ t₀ =
        cgf (∑ i : Fin n, Z i) μ t₀ := by
      simp only [cgf, mgf]
      congr 1
      congr 1
      ext ω
      simp [Finset.sum_apply]
    rw [hcgf_eq] at hchernoff
    have hstep2 :
        exp (-t₀ * ((1 - ε) * μ_S) + cgf (∑ i : Fin n, Z i) μ t₀) ≤
          exp (-t₀ * ((1 - ε) * μ_S) + μ_S * (exp t₀ - 1)) :=
      Real.exp_le_exp.mpr (by linarith [hcgf_total])
    have hexp_t₀ : Real.exp t₀ = 1 - ε := Real.exp_log h1ε_pos
    have hstep3 :
        -t₀ * ((1 - ε) * μ_S) + μ_S * (exp t₀ - 1) =
          -μ_S * (ε + (1 - ε) * Real.log (1 - ε)) := by
      rw [hexp_t₀]
      change -Real.log (1 - ε) * ((1 - ε) * μ_S) +
          μ_S * ((1 - ε) - 1) =
        -μ_S * (ε + (1 - ε) * Real.log (1 - ε))
      ring
    have hexpo := chernoff_lower_exponent_bound hε hε1
    have hstep4 :
        -μ_S * (ε + (1 - ε) * Real.log (1 - ε)) ≤ -μ_S * (ε ^ 2 / 2) :=
      mul_le_mul_of_nonpos_left hexpo (neg_nonpos.mpr hμS_nn)
    calc μ.real {ω | ∑ i : Fin n, Z i ω ≤ (1 - ε) * μ_S}
        ≤ exp (-t₀ * ((1 - ε) * μ_S) + cgf (∑ i : Fin n, Z i) μ t₀) := hchernoff
      _ ≤ exp (-t₀ * ((1 - ε) * μ_S) + μ_S * (exp t₀ - 1)) := hstep2
      _ = exp (-μ_S * (ε + (1 - ε) * Real.log (1 - ε))) := by rw [hstep3]
      _ ≤ exp (-μ_S * (ε ^ 2 / 2)) := Real.exp_le_exp.mpr hstep4
      _ = exp (-μ_S * ε ^ (2 : Nat) / 2) := by ring_nf
  have hset_eq : {ω | S ω ≤ (1 - ε) * μ_S} =
      {ω | ∑ i : Fin n, Z i ω ≤ (1 - ε) * μ_S} := by
    ext ω
    simp [hSZ ω]
  rw [hset_eq]
  have hfin : μ {ω | ∑ i : Fin n, Z i ω ≤ (1 - ε) * μ_S} ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Paper `lemma:chernoff`, with both the upper and lower tails. -/
theorem lemma_chernoff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Bool) (S : Ω → Real)
    (hRep : ∀ ω, S ω = ∑ i : Fin n, if X i ω then (1 : Real) else 0)
    (hXMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ) :
    (∀ ε : Real, 0 < ε →
      μ {ω | S ω ≥ (1 + ε) * (∫ x, S x ∂μ)} ≤
        ENNReal.ofReal (Real.exp (-(∫ x, S x ∂μ) * ε ^ (2 : Nat) / (2 + ε)))) ∧
    (∀ ε : Real, 0 < ε → ε < 1 →
      μ {ω | S ω ≤ (1 - ε) * (∫ x, S x ∂μ)} ≤
        ENNReal.ofReal (Real.exp (-(∫ x, S x ∂μ) * ε ^ (2 : Nat) / 2))) := by
  constructor
  · intro ε hε
    exact lemma_chernoff_upper μ n X S hRep hXMeas hIndep ε hε
  · intro ε hε hε1
    exact lemma_chernoff_lower μ n X S hRep hXMeas hIndep ε hε hε1

/-- Hoeffding inequality for sums of independent bounded random variables:
    P[|Σ Xᵢ - E[Σ Xᵢ]| ≥ t] ≤ 2·exp(-t²/(2n)) when each Xᵢ ∈ [-1, 1].

    Proof: By `hasSubgaussianMGF_of_mem_Icc`, each Xᵢ - E[Xᵢ] is sub-Gaussian
    with parameter ((‖1-(-1)‖₊/2)²) = 1. The centered variables are independent
    (from `iIndepFun.comp`). By Mathlib's `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`,
    P[Σ(Xᵢ-E[Xᵢ]) ≥ t] ≤ exp(-t²/(2n)). A union bound gives the two-sided
    version with factor 2. -/
theorem lemma_hoeffding
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Real)
    (hBound : ∀ i ω, X i ω ∈ Set.Icc (-1 : Real) 1)
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (t : Real) (ht : 0 ≤ t) :
    μ {ω | t ≤ |(∑ i : Fin n, X i ω) - (∫ x, (∑ i : Fin n, X i x) ∂μ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ (2 : Nat)) / (2 * n))) := by
  -- Define centered variables Y_i(ω) = X_i(ω) - E[X_i]
  set Y : Fin n → Ω → ℝ := fun i ω => X i ω - ∫ x, X i x ∂μ with hY_def
  -- Integrable X_i (bounded in [-1,1])
  have hX_int : ∀ i, Integrable (X i) μ := fun i =>
    Integrable.of_mem_Icc (-1) 1 (hMeas i).aemeasurable (ae_of_all _ fun ω => hBound i ω)
  -- Y_i are measurable
  have hY_meas : ∀ i, Measurable (Y i) := fun i => (hMeas i).sub measurable_const
  -- Y_i are independent (subtracting constants preserves independence)
  have hY_indep : iIndepFun Y μ :=
    hIndep.comp (fun i => fun x => x - ∫ ω, X i ω ∂μ) (fun _ => measurable_sub_const _)
  -- Each Y_i is sub-Gaussian with parameter ((‖1-(-1)‖₊/2)²) = 1
  have hY_subG : ∀ i, HasSubgaussianMGF (Y i) ((‖(1:ℝ) - (-1)‖₊ / 2) ^ 2) μ := fun i =>
    hasSubgaussianMGF_of_mem_Icc (hMeas i).aemeasurable
      (ae_of_all _ fun ω => hBound i ω)
  -- Simplify the parameter: ((‖2‖₊/2))² = 1
  have hparam : (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2 = 1 := by norm_num
  -- ∑ Y_i = ∑ X_i - E[∑ X_i]
  have hSY : ∀ ω, ∑ i : Fin n, Y i ω =
      (∑ i : Fin n, X i ω) - ∫ x, (∑ i : Fin n, X i x) ∂μ := by
    intro ω
    simp only [Y, Finset.sum_sub_distrib]
    congr 1
    rw [integral_finset_sum _ (fun i _ => hX_int i)]
  -- Upper tail: P[∑ Y_i ≥ t] ≤ exp(-t²/(2n))
  have h_upper : μ.real {ω | t ≤ ∑ i : Fin n, Y i ω} ≤
      exp (-(t ^ (2 : Nat)) / (2 * n)) := by
    have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY_indep
      (c := fun _ => (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2)
      (s := Finset.univ)
      (fun i _ => hY_subG i) ht
    simp only [hparam, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at this
    convert this using 2 <;> norm_num
  -- Lower tail: P[∑ Y_i ≤ -t] ≤ exp(-t²/(2n))
  -- Use negated variables: P[-∑ Y_i ≥ t] ≤ exp(-t²/(2n))
  have hY_neg_subG : ∀ i, HasSubgaussianMGF (fun ω => -(Y i ω))
      ((‖(1:ℝ) - (-1)‖₊ / 2) ^ 2) μ := fun i => (hY_subG i).neg
  have hY_neg_indep : iIndepFun (fun i => fun ω => -(Y i ω)) μ :=
    hY_indep.comp (fun _ => fun x => -x) (fun _ => measurable_neg)
  have h_lower : μ.real {ω | t ≤ ∑ i : Fin n, (-(Y i ω))} ≤
      exp (-(t ^ (2 : Nat)) / (2 * n)) := by
    have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY_neg_indep
      (c := fun _ => (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2)
      (s := Finset.univ)
      (fun i _ => hY_neg_subG i) ht
    simp only [hparam, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at this
    convert this using 2 <;> norm_num
  -- |∑ Y_i| ≥ t ↔ ∑ Y_i ≥ t ∨ ∑ Y_i ≤ -t
  have hset : {ω | t ≤ |(∑ i : Fin n, X i ω) - ∫ x, (∑ i : Fin n, X i x) ∂μ|} ⊆
      {ω | t ≤ ∑ i : Fin n, Y i ω} ∪ {ω | t ≤ ∑ i : Fin n, (-(Y i ω))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [← hSY ω] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib]
    by_cases h : (0 : ℝ) ≤ ∑ i : Fin n, Y i ω
    · left; rwa [abs_of_nonneg h] at hω
    · right; push_neg at h; rwa [abs_of_neg h] at hω
  -- Union bound
  calc μ {ω | t ≤ |(∑ i : Fin n, X i ω) - ∫ x, (∑ i : Fin n, X i x) ∂μ|}
      ≤ μ ({ω | t ≤ ∑ i : Fin n, Y i ω} ∪
           {ω | t ≤ ∑ i : Fin n, (-(Y i ω))}) :=
        measure_mono hset
    _ ≤ μ {ω | t ≤ ∑ i : Fin n, Y i ω} +
        μ {ω | t ≤ ∑ i : Fin n, (-(Y i ω))} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (exp (-(t ^ (2 : Nat)) / (2 * n))) +
        ENNReal.ofReal (exp (-(t ^ (2 : Nat)) / (2 * n))) := by
        apply add_le_add
        · rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal h_upper
        · rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal h_lower
    _ = ENNReal.ofReal (2 * exp (-(t ^ (2 : Nat)) / (2 * n))) := by
        rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]; ring_nf

/-- Paper `lemma:hoeffding`. Hoeffding's lemma in the one-sided form used in
    the paper. If a random
    variable is supported on `[-1, 1]` and has nonpositive mean, then its MGF
    at every nonnegative argument is bounded by `exp (λ² / 2)`. -/
theorem lemma_hoeffding_mgf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Real)
    (hBound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : Real) 1)
    (hMeas : AEMeasurable X μ)
    (hMean : ∫ ω, X ω ∂μ ≤ 0)
    (lam : Real) (hlam : 0 ≤ lam) :
    mgf X μ lam ≤ Real.exp (lam ^ (2 : Nat) / 2) := by
  let m : ℝ := ∫ ω, X ω ∂μ
  have hsub := hasSubgaussianMGF_of_mem_Icc hMeas hBound
  have hmgf :
      mgf (fun ω => X ω - m) μ lam ≤ Real.exp (lam ^ (2 : Nat) / 2) := by
    have h := hsub.mgf_le lam
    norm_num at h ⊢
    simpa only [m] using h
  have hexp : Real.exp (lam * m) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hlam hMean
  calc
    mgf X μ lam = mgf (fun ω => m + (X ω - m)) μ lam := by
      congr 1
      funext ω
      ring
    _ = Real.exp (lam * m) * mgf (fun ω => X ω - m) μ lam :=
      mgf_const_add (μ := μ) (X := fun ω => X ω - m) (t := lam) m
    _ ≤ 1 * Real.exp (lam ^ (2 : Nat) / 2) := by
      exact mul_le_mul hexp hmgf mgf_nonneg zero_le_one
    _ = Real.exp (lam ^ (2 : Nat) / 2) := one_mul _

/-- If X has E[X] = 0, Var(X) = 1, and |X| ≤ 1 a.s., then X ∈ {-1, 1} a.s.
    This characterizes Rademacher random variables: the only bounded, zero-mean,
    unit-variance distribution supported on [-1, 1] is the symmetric ±1 coin. -/
private lemma ae_rademacher_of_bound_mean_var
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hMeas : Measurable X)
    (hBound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-1 : ℝ) 1)
    (hMean : ∫ ω, X ω ∂μ = 0)
    (hVar : variance X μ = 1) :
    ∀ᵐ ω ∂μ, X ω = -1 ∨ X ω = 1 := by
  -- E[X²] = Var(X) + E[X]² = 1 + 0 = 1
  have hIntSq : ∫ ω, X ω ^ 2 ∂μ = 1 := by
    have hv := ProbabilityTheory.variance_of_integral_eq_zero hMeas.aemeasurable hMean
    rw [hVar] at hv; convert hv.symm using 1
  -- X² ≤ 1 a.e. (from |X| ≤ 1)
  have hSqBound : ∀ᵐ ω ∂μ, X ω ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hBound] with ω hω
    exact ⟨sq_nonneg _, by nlinarith [hω.1, hω.2]⟩
  -- 1 - X² ≥ 0 a.e. and integrable
  have hNonneg : 0 ≤ᵐ[μ] fun ω => 1 - X ω ^ 2 := by
    filter_upwards [hSqBound] with ω hω; simp only [Pi.zero_apply]; linarith [hω.2]
  have hInteg : Integrable (fun ω => 1 - X ω ^ 2) μ :=
    Integrable.of_mem_Icc 0 1 (measurable_const.sub (hMeas.pow_const 2)).aemeasurable
      (by filter_upwards [hSqBound] with ω hω
          exact ⟨by linarith [hω.2], by linarith [hω.1]⟩)
  -- ∫(1 - X²) = 1 - 1 = 0
  have hIntZero : ∫ ω, (1 - X ω ^ 2) ∂μ = 0 := by
    have hSqInteg : Integrable (fun ω => X ω ^ 2) μ :=
      Integrable.of_mem_Icc 0 1 (hMeas.pow_const 2).aemeasurable
        (by filter_upwards [hSqBound] with ω hω; exact hω)
    rw [integral_sub (integrable_const 1) hSqInteg, integral_const, smul_eq_mul, mul_one,
      hIntSq]
    simp [Measure.real, measure_univ]
  -- 1 - X² = 0 a.e. → X² = 1 a.e. → X = ±1 a.e.
  have hEqZero := (integral_eq_zero_iff_of_nonneg_ae hNonneg hInteg).mp hIntZero
  filter_upwards [hEqZero] with ω hω
  have hSq : X ω ^ 2 = 1 := by linarith [show (1 : ℝ) - X ω ^ 2 = 0 from hω]
  exact (sq_eq_one_iff.mp hSq).symm

/-- For Rademacher X (∈ {-1,1} a.s., E[X]=0), we have P(X=1) = P(X=-1).
    Used as a building block for the sum symmetry lemma below. -/
private lemma rademacher_prob_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hMeas : Measurable X)
    (hRad : ∀ᵐ ω ∂μ, X ω = -1 ∨ X ω = 1)
    (hMean : ∫ ω, X ω ∂μ = 0) :
    μ (X ⁻¹' {1}) = μ (X ⁻¹' {-1}) := by
  have hInteg : Integrable X μ := by
    exact (memLp_top_of_bound hMeas.aestronglyMeasurable 1
      (by filter_upwards [hRad] with ω hω; rcases hω with h | h <;> simp [h])).integrable le_top
  set A := X ⁻¹' {(1:ℝ)} with hA_def
  set B := X ⁻¹' {(-1:ℝ)} with hB_def
  have hmsA : MeasurableSet A := hMeas (measurableSet_singleton 1)
  have hmsB : MeasurableSet B := hMeas (measurableSet_singleton (-1))
  have hDisj : Disjoint A B := by
    rw [Set.disjoint_left]; intro ω ha hb
    simp [A, B, Set.mem_preimage, Set.mem_singleton_iff] at ha hb; linarith
  -- (A ∪ B)ᶜ has measure 0
  have hNull : μ (A ∪ B)ᶜ = 0 := by
    apply measure_mono_null _ (ae_iff.mp hRad)
    intro ω hω; simp only [Set.mem_compl_iff, Set.mem_union, A, B,
      Set.mem_preimage, Set.mem_singleton_iff] at hω
    push_neg at hω; exact fun h => h.elim hω.2 hω.1
  -- ∫ X dμ = ∫_{A∪B} X dμ + 0
  have hNullInt : ∫ ω in (A ∪ B)ᶜ, X ω ∂μ = 0 := by
    have : μ.restrict (A ∪ B)ᶜ = 0 := Measure.restrict_eq_zero.mpr hNull
    show ∫ ω, X ω ∂(μ.restrict (A ∪ B)ᶜ) = 0; rw [this]; exact integral_zero_measure _
  have hDecomp : ∫ ω, X ω ∂μ = ∫ ω in A ∪ B, X ω ∂μ := by
    rw [← integral_add_compl (hmsA.union hmsB) hInteg]; linarith [hNullInt]
  -- ∫_{A∪B} = ∫_A + ∫_B
  have hSplit : ∫ ω in A ∪ B, X ω ∂μ =
      ∫ ω in A, X ω ∂μ + ∫ ω in B, X ω ∂μ :=
    setIntegral_union hDisj hmsB hInteg.integrableOn hInteg.integrableOn
  -- ∫_A X = μ(A).toReal
  have h1 : ∫ ω in A, X ω ∂μ = (μ A).toReal := by
    trans ∫ ω in A, (1 : ℝ) ∂μ
    · exact setIntegral_congr_fun hmsA (fun ω hω => Set.mem_singleton_iff.mp hω)
    · rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  -- ∫_B X = -(μ B).toReal
  have h_1 : ∫ ω in B, X ω ∂μ = -(μ B).toReal := by
    trans ∫ ω in B, (-1 : ℝ) ∂μ
    · exact setIntegral_congr_fun hmsB (fun ω hω => Set.mem_singleton_iff.mp hω)
    · rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring
  -- 0 = μ(A) - μ(B), so μ(A) = μ(B)
  have h_eq : (μ A).toReal = (μ B).toReal := by linarith [hMean, hDecomp, hSplit, h1, h_1]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp h_eq

/-- For i.i.d. Rademacher random variables (bounded, mean 0, variance 1),
    the sum has a symmetric distribution about 0:
    P(∑ X_i > 0) ≤ P(∑ X_i ≤ 0).
    Proof: use characteristic functions. Each charFun(μ.map(X_i)) is
    real-valued (from P(X_i=1)=P(X_i=-1)), so charFun of the sum
    (product of charFuns by independence) is real, hence
    μ.map(∑ X_i) = μ.map(-∑ X_i), giving the probability inequality. -/
private lemma rademacher_sum_prob_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hRad : ∀ i, ∀ᵐ ω ∂μ, X i ω = -1 ∨ X i ω = 1)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = 0) (S : Finset ℕ) :
    μ {ω | 0 < ∑ j ∈ S, X j ω} ≤ μ {ω | ∑ j ∈ S, X j ω ≤ 0} := by
  -- Measurability of sum and negated sum
  have h_meas_sum : Measurable (fun ω => ∑ j ∈ S, X j ω) :=
    Finset.measurable_sum _ (fun i _ => hMeas i)
  have h_meas_neg : Measurable (fun ω => -(∑ j ∈ S, X j ω)) := h_meas_sum.neg
  -- Key: the distribution of ∑_S X_j is symmetric about 0.
  -- charFun(μ.map(X_j)) is self-conjugate for each j (from P(X_j=1)=P(X_j=-1)).
  -- By independence, charFun(μ.map(∑_S X)) = ∏ charFun(μ.map(X_j)) is also self-conjugate.
  -- charFun(μ.map(-∑ X))(t) = conj(charFun(μ.map(∑ X))(t)) = charFun(μ.map(∑ X))(t).
  -- By ext_of_charFun: μ.map(∑ X) = μ.map(-∑ X).
  have h_sum_sym : μ.map (fun ω => ∑ j ∈ S, X j ω) =
      μ.map (fun ω => -(∑ j ∈ S, X j ω)) := by
    -- Step 1: Individual charFun symmetry: charFun(μ.map(X j))(-t) = charFun(μ.map(X j))(t)
    -- Uses integral decomposition on {X j = 1} ∪ {X j = -1} and P(X=1)=P(X=-1)
    have h_charfun_sym : ∀ j, ∀ t : ℝ,
        charFun (μ.map (X j)) (-t) = charFun (μ.map (X j)) t := by
      intro j t
      -- charFun(-t) = conj(charFun(t)), so need conj = id, i.e. Im = 0.
      rw [charFun_neg]
      -- conj z = z ↔ z.im = 0. Show Im(charFun(μ.map(X j)) t) = 0.
      rw [Complex.conj_eq_iff_im]
      -- Need: (charFun (μ.map (X j)) t).im = 0
      -- charFun = ∫ exp(itx) d(μ.map(X j)) = ∫_Ω exp(it·X j ω) dμ
      -- Im(∫ f) = ∫ Im(f) by imCLM.integral_comp_comm
      -- Im(exp(it·x)) = sin(t·x)
      -- For X j ∈ {-1,1} a.e.: sin(t·X j ω) = sin(t) · X j ω a.e.
      -- So ∫ sin(t·X j ω) dμ = sin(t) · ∫ X j ω dμ = sin(t) · 0 = 0
      -- After charFun_neg, goal: conj(charFun) = charFun
      -- Show Im(charFun) = 0, which implies conj = id (from conj_eq_iff_im above)
      rw [charFun_apply_real]
      -- Goal: (∫ x : ℝ, exp(↑t * ↑x * I) d(μ.map(X j))).im = 0
      haveI : IsProbabilityMeasure (μ.map (X j)) :=
        Measure.isProbabilityMeasure_map (hMeas j).aemeasurable
      have hint : Integrable (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)) (μ.map (X j)) := by
        refine Integrable.mono (integrable_const (1 : ℂ))
          (Continuous.aestronglyMeasurable (by fun_prop)) ?_
        filter_upwards with x
        simp only [norm_one]
        rw [show (↑t : ℂ) * (↑x : ℂ) * Complex.I = ↑(t * x) * Complex.I by push_cast; ring]
        exact le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x))
      -- Pull .im through ∫ via imCLM
      rw [← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hint]
      -- Goal: ∫ x, Im(exp(↑t * ↑x * I)) d(μ.map(X j)) = 0
      -- Simplify Im(exp(↑t * ↑x * I)) = sin(t * x)
      simp_rw [show ∀ x : ℝ, Complex.imCLM (Complex.exp (↑t * ↑x * Complex.I)) =
          Real.sin (t * x) from fun x => by
        rw [Complex.imCLM_apply,
            show (↑t : ℂ) * (↑x : ℂ) * Complex.I = ↑(t * x) * Complex.I by push_cast; ring]
        exact Complex.exp_ofReal_mul_I_im (t * x)]
      -- Goal: ∫ x : ℝ, sin(t * x) d(μ.map(X j)) = 0
      rw [integral_map (hMeas j).aemeasurable
        (show Measurable (fun x : ℝ => Real.sin (t * x)) by fun_prop).aestronglyMeasurable]
      -- Goal: ∫ ω, sin(t * X j ω) dμ = 0
      -- sin(t * X j ω) = sin(t) * X j ω a.e. (since X j ∈ {-1, 1} a.e.)
      have h_sin_eq : (fun ω => Real.sin (t * X j ω)) =ᵐ[μ]
          (fun ω => Real.sin t * X j ω) := by
        filter_upwards [hRad j] with ω hω
        rcases hω with h1 | h1 <;> simp [h1, Real.sin_neg, mul_comm]
      rw [integral_congr_ae h_sin_eq, integral_const_mul, hMean j, mul_zero]
    -- Step 2: Product formula by Finset induction (stated for pointwise sum)
    have h_prod : ∀ (T : Finset ℕ), charFun (μ.map (fun ω => ∑ j ∈ T, X j ω)) =
        ∏ j ∈ T, charFun (μ.map (X j)) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty, Finset.prod_empty]
        rw [Measure.map_const, IsProbabilityMeasure.measure_univ, one_smul]
        ext t; simp [charFun_dirac]
      | @insert a s' ha ih =>
        rw [show (fun ω => ∑ j ∈ insert a s', X j ω) =
            X a + (fun ω => ∑ j ∈ s', X j ω) from by
          ext ω; simp [Finset.sum_insert ha]]
        have h_ind : IndepFun (X a) (fun ω => ∑ j ∈ s', X j ω) μ := by
          convert (hIndep.indepFun_finset_sum_of_notMem hMeas ha).symm using 1
          exact funext (fun ω => (Finset.sum_apply ω s' X).symm)
        rw [IndepFun.charFun_map_add_eq_mul (hMeas a).aemeasurable
          (Finset.measurable_sum _ (fun i _ => hMeas i)).aemeasurable h_ind,
          ih, Finset.prod_insert ha]
    -- Step 3: ext_of_charFun
    apply Measure.ext_of_charFun; ext t
    -- charFun(μ.map(-∑ X))(t) = conj(charFun(μ.map(∑ X))(t))
    rw [show (fun ω => -(∑ j ∈ S, X j ω)) = ((-1 : ℝ) * ·) ∘ (fun ω => ∑ j ∈ S, X j ω) from by
      ext ω; simp only [Function.comp_apply]; ring]
    rw [← Measure.map_map (measurable_const_mul _) h_meas_sum]
    rw [charFun_map_mul, neg_one_mul, charFun_neg]
    -- Now goal: charFun(μ.map(fun ω => ∑ X))(t) = conj(charFun(μ.map(fun ω => ∑ X))(t))
    rw [congr_fun (h_prod S) t]
    rw [show (∏ j ∈ S, charFun (μ.map (X j))) t = ∏ j ∈ S, charFun (μ.map (X j)) t from
      Finset.prod_apply t S (fun j => charFun (μ.map (X j)))]
    rw [map_prod (starRingEnd ℂ)]
    congr 1; ext j
    rw [show starRingEnd ℂ (charFun (μ.map (X j)) t) = charFun (μ.map (X j)) (-t) from
      (charFun_neg t).symm]
    exact (h_charfun_sym j t).symm
  -- P(∑ > 0) = P(∑ < 0) from distribution symmetry
  have h_pos_eq_neg : μ {ω | 0 < ∑ j ∈ S, X j ω} = μ {ω | ∑ j ∈ S, X j ω < 0} := by
    have h1 : μ {ω | 0 < ∑ j ∈ S, X j ω} =
        (μ.map (fun ω => ∑ j ∈ S, X j ω)) (Set.Ioi 0) := by
      rw [Measure.map_apply h_meas_sum measurableSet_Ioi]; rfl
    have h2 : μ {ω | ∑ j ∈ S, X j ω < 0} =
        (μ.map (fun ω => -(∑ j ∈ S, X j ω))) (Set.Ioi 0) := by
      rw [Measure.map_apply h_meas_neg measurableSet_Ioi]
      congr 1; ext ω; simp
    rw [h1, h_sum_sym, h2]
  -- P(∑ > 0) = P(∑ < 0) ≤ P(∑ ≤ 0) since {< 0} ⊆ {≤ 0}
  calc μ {ω | 0 < ∑ j ∈ S, X j ω}
      = μ {ω | ∑ j ∈ S, X j ω < 0} := h_pos_eq_neg
    _ ≤ μ {ω | ∑ j ∈ S, X j ω ≤ 0} :=
        measure_mono (fun ω (h : ∑ j ∈ S, X j ω < 0) => le_of_lt h)

/-- CLT anti-concentration for the running maximum of i.i.d. bounded random
    variable partial sums.  Paper `lemma:clt`: for i.i.d. Xᵢ with mean 0,
    variance 1, and |Xᵢ| ≤ 1 a.s. (hence Rademacher), ∀ ε ∈ (0,1),
    ∃ θ > 0, ∃ n₀: for all n ≥ n₀,
      P[max_{k≤n} (X₁+⋯+Xₖ) > θ√n] ≥ ε.

    **Why the running maximum is essential.** By symmetry of Rademacher
    variables, P[Sₙ > t] ≤ 1/2 for any t ≥ 0, so the endpoint sum cannot
    give probabilities above 1/2.  The reflection principle for symmetric
    random walks gives P[max_{k≤n} Sₖ ≥ a] ≥ 2·P[Sₙ > a], and the CLT
    yields P[Sₙ > θ√n] → 1 − Φ(θ) as n→∞.  Combined:
      P[max Sₖ ≥ θ√n] → 2(1 − Φ(θ)) → 1 as θ → 0⁺.
    The paper's lower-bound proofs (§5 SD, §7 NSD) apply this lemma
    with ε close to 1, which requires the running-maximum formulation. -/
theorem lemma_clt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Real)
    (hBound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hIdent : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hMean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hVar : ∀ i, variance (X i) μ = 1)
    (ε : Real) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ θ : Real, 0 < θ ∧ ∃ n₀ : Nat, ∀ n, n₀ ≤ n →
      ENNReal.ofReal ε ≤ μ {ω | ∃ k ∈ Finset.range (n + 1),
        θ * Real.sqrt n ≤ ∑ i ∈ Finset.range k, X i ω} := by
  set G : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 1, inferInstance⟩
  let normalizedSum : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, X k ω
  have hNormalizedSumMeas : ∀ n, Measurable (normalizedSum n) := fun n =>
    measurable_const.mul
      (Finset.measurable_sum _ fun i _ => hMeas i)
  let Pn : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (normalizedSum n),
      Measure.isProbabilityMeasure_map
        (hNormalizedSumMeas n).aemeasurable⟩
  -- Derive E[X 0] = 0 and E[X 0²] = 1 in CLT's notation
  have h0 : μ[X 0] = 0 := hMean 0
  have h1 : μ[X 0 ^ 2] = 1 := by
    have hv := ProbabilityTheory.variance_of_integral_eq_zero (hMeas 0).aemeasurable (hMean 0)
    rw [hVar 0] at hv
    change ∫ x, (X 0 ^ 2) x ∂μ = 1
    simpa only [Pi.pow_apply] using hv.symm
  -- Derive IdentDistrib in the form CLT expects
  have hIdent0 : ∀ i, IdentDistrib (X i) (X 0) μ μ :=
    fun i => hIdent i 0
  -- Apply Mathlib's Central Limit Theorem: Sₙ/√n → N(0,1)
  have hGaussianId :
      HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (G : Measure ℝ) :=
    HasLaw.id
  have hCLTDistribution :=
    ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum
      (P := μ) (P' := (G : Measure ℝ))
      (X := X) (Y := id) hGaussianId h0 h1 hIndep hIdent0
  have hCLT : Filter.Tendsto Pn Filter.atTop (nhds G) := by
    have hGmap :
        (⟨(G : Measure ℝ).map id,
          Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
            ProbabilityMeasure ℝ) = G := by
      apply ProbabilityMeasure.toMeasure_injective
      exact Measure.map_id
    have ht := hCLTDistribution.tendsto
    rw [hGmap] at ht
    simpa only [Pn, normalizedSum] using ht
  -- === Step 1: Reflection principle for symmetric random walks ===
  -- Since |Xᵢ| ≤ 1 a.s. and E[Xᵢ²] = 1, we have |Xᵢ| = 1 a.s. (Rademacher).
  -- For iid Rademacher walks: P(max_{k≤n} Sₖ ≥ m) ≥ 2·P(Sₙ > m) for INTEGER m.
  -- Proof: P(max ≥ m) = 2·P(Sₙ > m) + P(Sₙ = m) ≥ 2·P(Sₙ > m)
  -- by the reflection bijection on paths at the first hitting time of m.
  -- NOTE: m must be a natural number. For non-integer a, the bound
  -- 2·P(Sₙ > a) ≤ P(max ≥ a) can fail when P(Sₙ = ⌈a⌉) > 0.
  have hReflection : ∀ (m : ℕ) (n : ℕ), 0 < m →
      2 * μ {ω | (m : ℝ) < ∑ i ∈ Finset.range n, X i ω} ≤
        μ {ω | ∃ k ∈ Finset.range (n + 1), (m : ℝ) ≤ ∑ i ∈ Finset.range k, X i ω} := by
    intro m n hm
    -- X_i ∈ {-1, 1} a.e. (from Rademacher lemma above)
    have hRad : ∀ i, ∀ᵐ ω ∂μ, X i ω = -1 ∨ X i ω = 1 :=
      fun i => ae_rademacher_of_bound_mean_var (hMeas i) (hBound i) (hMean i) (hVar i)
    set Sn := fun ω => ∑ i ∈ Finset.range n, X i ω
    set maxE := {ω | ∃ k ∈ Finset.range (n + 1),
        (m : ℝ) ≤ ∑ i ∈ Finset.range k, X i ω}
    set hiE := {ω | (m : ℝ) < Sn ω}
    -- {S_n > m} ⊆ {max ≥ m}: the endpoint is one of the partial sums
    have h_sub : hiE ⊆ maxE := fun ω (hω : (m : ℝ) < Sn ω) =>
      ⟨n, Finset.self_mem_range_succ n, le_of_lt hω⟩
    -- Measurability
    have h_meas_Sn : Measurable Sn :=
      Finset.measurable_sum _ (fun i _ => hMeas i)
    have h_meas_hi : MeasurableSet hiE := measurableSet_lt measurable_const h_meas_Sn
    have h_meas_max : MeasurableSet maxE := by
      simp only [maxE]
      rw [show {ω | ∃ k ∈ Finset.range (n + 1),
          (m : ℝ) ≤ ∑ i ∈ Finset.range k, X i ω} =
        ⋃ k ∈ Finset.range (n + 1), {ω | (m : ℝ) ≤ ∑ i ∈ Finset.range k, X i ω} from by
          ext ω; simp [Set.mem_iUnion]]
      exact MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet
        (fun k _ => measurableSet_le measurable_const
          (Finset.measurable_sum _ (fun i _ => hMeas i)))
    -- Decompose: μ(max ≥ m) = μ(S_n > m) + μ(max ≥ m, S_n ≤ m)
    have h_decomp : μ maxE = μ hiE + μ (maxE \ hiE) := by
      conv_lhs => rw [← measure_inter_add_diff maxE h_meas_hi]
      rw [Set.inter_eq_self_of_subset_right h_sub]
    -- Core reflection inequality: μ(S_n > m) ≤ μ(max ≥ m, S_n ≤ m)
    -- This uses:
    -- (a) Sum symmetry: P(∑_{S} X_i > 0) ≤ P(∑_{S} X_i ≤ 0) for any finset S
    --     (proved in rademacher_sum_prob_le above)
    -- (b) Hitting time decomposition: decompose {max ≥ m} by first hitting time τ
    --     of level m. On {τ=k}, S_k = m exactly (integer argument: S_{k-1} < m
    --     integer, S_k ≥ m, step ±1 forces S_k = m). Then S_n > m ↔ R_k > 0
    --     where R_k = ∑_{i≥k} X_i is the post-hitting sum.
    -- (c) Independence: {τ=k} depends on X_0,...,X_{k-1} while R_k depends on
    --     X_k,...,X_{n-1}. By iIndepFun: P(τ=k, R_k>0) = P(τ=k)·P(R_k>0).
    -- (d) Sum symmetry gives P(R_k>0) ≤ P(R_k≤0), hence
    --     P(τ=k, S_n>m) ≤ P(τ=k, S_n≤m). Summing over k yields the result.
    have h_reflect : μ hiE ≤ μ (maxE \ hiE) := by
      -- Define partial sums and remainder sums
      set S' := fun k ω => ∑ i ∈ Finset.range k, X i ω with hS_def
      set R := fun k ω => ∑ i ∈ Finset.Ico k n, X i ω with hR_def
      -- Key: S_n = S_k + R_k for k ≤ n
      have h_Sn_eq : ∀ k, k ≤ n → ∀ ω, Sn ω = S' k ω + R k ω := by
        intro k hk ω; simp only [Sn, hS_def, hR_def]
        rw [← Finset.sum_union (by simp [Finset.disjoint_left]; omega)]
        congr 1; ext x; simp [Finset.mem_range, Finset.mem_Ico]; omega
      -- Key: S_k and R_k are independent (disjoint index sets)
      have h_indep_sum : ∀ k, k ≤ n →
          IndepFun (fun ω => S' k ω) (fun ω => R k ω) μ := by
        intro k hk
        have hDisj : Disjoint (Finset.range k) (Finset.Ico k n) := by
          simp [Finset.disjoint_left]; omega
        have h := hIndep.indepFun_finset (Finset.range k) (Finset.Ico k n) hDisj hMeas
        have hφ : Measurable (fun (y : ↑(Finset.range k) → ℝ) => ∑ i, y i) := by measurability
        have hψ : Measurable (fun (z : ↑(Finset.Ico k n) → ℝ) => ∑ j, z j) := by measurability
        convert h.comp hφ hψ using 1 <;> ext ω <;> exact (Finset.sum_coe_sort _ _).symm
      -- Key: R_k has symmetric distribution
      have h_sym : ∀ k, μ {ω | 0 < R k ω} ≤ μ {ω | R k ω ≤ 0} :=
        fun k => rademacher_sum_prob_le hMeas hIndep hRad hMean (Finset.Ico k n)
      -- Sum of {-1,1} valued r.v.s is integer-valued a.e.
      have h_int : ∀ S : Finset ℕ, ∀ᵐ ω ∂μ, ∃ z : ℤ, ∑ i ∈ S, X i ω = ↑z := by
        intro S; induction S using Finset.induction with
        | empty => exact Filter.Eventually.of_forall (fun _ => ⟨0, by simp⟩)
        | @insert a s ha ih =>
          filter_upwards [ih, hRad a] with ω ⟨z, hz⟩ hx
          rw [Finset.sum_insert ha, hz]
          rcases hx with h | h <;> rw [h]
          · exact ⟨-1 + z, by push_cast; ring⟩
          · exact ⟨1 + z, by push_cast; ring⟩
      -- First hitting time events: G k = {S'_k ≥ m, ∀ j < k, S'_j < m}
      set G := fun k => {ω | (m : ℝ) ≤ S' k ω ∧ ∀ j, j < k → S' j ω < ↑m}
      -- Partition: maxE = ⋃ k ∈ range(n+1), G k
      have h_partition : maxE = ⋃ k ∈ Finset.range (n + 1), G k := by
        ext ω; simp only [maxE, G, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
        constructor
        · intro ⟨k, hk, hle⟩
          let S₀ := (Finset.range (n + 1)).filter (fun k => (m : ℝ) ≤ S' k ω)
          have hS_ne : S₀.Nonempty :=
            ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hle⟩⟩
          set k₀ := S₀.min' hS_ne
          have hk₀_mem := Finset.min'_mem S₀ hS_ne
          rw [Finset.mem_filter, Finset.mem_range] at hk₀_mem
          exact ⟨k₀, hk₀_mem.1, hk₀_mem.2, fun j hj => by
            by_contra h_not_lt; push_neg at h_not_lt
            exact absurd (Finset.min'_le S₀ j (Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (lt_trans hj hk₀_mem.1), h_not_lt⟩)) (not_le.mpr hj)⟩
        · intro ⟨k, hk, hle, _⟩; exact ⟨k, hk, hle⟩
      -- Pairwise disjoint
      have h_disj : Set.PairwiseDisjoint (↑(Finset.range (n + 1))) G := by
        intro i _ j _ hij
        rw [Function.onFun, Set.disjoint_iff]; intro ω hω
        simp only [G, Set.mem_inter_iff, Set.mem_setOf_eq] at hω
        obtain ⟨⟨hi_ge, hi_prev⟩, ⟨hj_ge, hj_prev⟩⟩ := hω
        rcases Nat.lt_or_ge i j with h | h
        · exact absurd hi_ge (not_le.mpr (hj_prev i h))
        · exact absurd hj_ge (not_le.mpr (hi_prev j (lt_of_le_of_ne h (Ne.symm hij))))
      -- Measurability of G k
      have h_meas_G : ∀ k, MeasurableSet (G k) := by
        intro k
        have : G k = {ω | (m : ℝ) ≤ S' k ω} ∩
            (⋂ (j : ℕ), ⋂ (_ : j < k), {ω : Ω | S' j ω < ↑m}) := by
          ext ω; simp only [G, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
        rw [this]
        exact MeasurableSet.inter
          (measurableSet_le measurable_const
            (Finset.measurable_sum _ (fun i _ => hMeas i)))
          (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
            measurableSet_lt (Finset.measurable_sum _ (fun i _ => hMeas i))
              measurable_const)))
      -- Measurability of {R k > 0} and {R k ≤ 0}
      have h_meas_R_pos : ∀ k, MeasurableSet {ω | 0 < R k ω} :=
        fun k => measurableSet_lt measurable_const
          (Finset.measurable_sum _ (fun i _ => hMeas i))
      have h_meas_R_neg : ∀ k, MeasurableSet {ω | R k ω ≤ 0} :=
        fun k => measurableSet_le (Finset.measurable_sum _ (fun i _ => hMeas i)) measurable_const
      -- Integer argument: on G k (k ≥ 1), S'_k = m a.e.
      have h_integer : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → S' k ω = ↑m := by
        intro k
        -- If k = 0: G 0 = ∅ since S' 0 = 0 < m
        by_cases hk0 : k = 0
        · subst hk0
          exact Filter.Eventually.of_forall (fun ω hω => by
            exfalso
            have h1 : (m : ℝ) ≤ S' 0 ω := hω.1
            simp only [hS_def, Finset.range_zero, Finset.sum_empty] at h1
            have h2 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
            linarith)
        -- For k ≥ 1: S'_k = S'_{k-1} + X_{k-1}
        filter_upwards [h_int (Finset.range (k - 1)), hRad (k - 1)] with ω ⟨z, hz⟩ hx
        intro hω
        obtain ⟨hge, hprev⟩ := hω
        -- S'_{k-1} < m (from the first-hitting condition)
        have hprev_k : S' (k - 1) ω < ↑m := hprev (k - 1) (Nat.sub_one_lt hk0)
        -- S'_k = S'_{k-1} + X_{k-1}
        have hstep : S' k ω = S' (k - 1) ω + X (k - 1) ω := by
          simp only [hS_def]
          have : k = (k - 1) + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hk0)).symm
          conv_lhs => rw [this]
          exact Finset.sum_range_succ _ _
        -- S'_{k-1} is integer-valued: S'_{k-1} = z
        have hS_prev : S' (k - 1) ω = ↑z := by
          simp only [hS_def] at hz ⊢; exact hz
        -- X_{k-1} must be 1 (if -1, S'_k < m contradicting S'_k ≥ m)
        rcases hx with h_neg | h_pos
        · -- X_{k-1} = -1: S'_k = z - 1, but z < m so z - 1 < m, contradiction
          exfalso; linarith [hstep, hS_prev, h_neg]
        · -- X_{k-1} = 1: S'_k = z + 1, integer argument gives z + 1 = m
          rw [hstep, hS_prev, h_pos]
          have h1 : (z : ℝ) < ↑m := by linarith [hS_prev]
          have h2 : (↑m : ℝ) ≤ ↑z + 1 := by linarith [hstep, hS_prev, h_pos]
          have h1i : z < (m : ℤ) := by exact_mod_cast h1
          have h2i : (m : ℤ) ≤ z + 1 := by exact_mod_cast h2
          have : z + 1 = (m : ℤ) := by omega
          exact_mod_cast this
      -- Key per-k inequality using tuple independence
      have h_key : ∀ k ∈ Finset.range (n + 1),
          μ (hiE ∩ G k) ≤ μ ((maxE \ hiE) ∩ G k) := by
        intro k hk
        have hk_le : k ≤ n := by rwa [Finset.mem_range, Nat.lt_succ_iff] at hk
        -- Tuple functions for independence
        set F_pre := fun (ω : Ω) (i : ↑(Finset.range k)) => X ↑i ω
        set F_post := fun (ω : Ω) (j : ↑(Finset.Ico k n)) => X ↑j ω
        have hDisj : Disjoint (Finset.range k) (Finset.Ico k n) := by
          simp [Finset.disjoint_left]; omega
        have h_tup := hIndep.indepFun_finset (Finset.range k) (Finset.Ico k n) hDisj hMeas
        -- {R k > 0} as preimage of F_post
        have hR_pos_eq : {ω | 0 < R k ω} =
            F_post ⁻¹' {f | 0 < ∑ j, f j} := by
          ext ω; simp only [Set.mem_preimage, Set.mem_setOf_eq, hR_def, F_post]
          have key := Finset.sum_coe_sort (Finset.Ico k n) (fun j => X j ω)
          constructor <;> intro h <;> linarith
        -- {R k ≤ 0} as preimage of F_post
        have hR_neg_eq : {ω | R k ω ≤ 0} =
            F_post ⁻¹' {f | ∑ j, f j ≤ 0} := by
          ext ω; simp only [Set.mem_preimage, Set.mem_setOf_eq, hR_def, F_post]
          have key := Finset.sum_coe_sort (Finset.Ico k n) (fun j => X j ω)
          constructor <;> intro h <;> linarith
        -- G k as preimage of F_pre
        -- Helper: partial sum conversion
        have h_psum : ∀ j, j ≤ k → ∀ ω,
            ∑ i ∈ Finset.range j, X i ω =
            ∑ i ∈ Finset.range k, if i < j then X i ω else 0 := by
          intro j hj ω
          rw [show Finset.range j = (Finset.range k).filter (fun (i : ℕ) => i < j) from by
            ext x; simp [Finset.mem_filter, Finset.mem_range]; omega]
          rw [Finset.sum_filter]
        have hG_eq : G k =
            F_pre ⁻¹' {f | (m : ℝ) ≤ ∑ i, f i ∧
              ∀ j, j < k → (∑ i : ↑(Finset.range k),
                if (↑i : ℕ) < j then f i else 0) < ↑m} := by
          ext ω; simp only [G, Set.mem_preimage, Set.mem_setOf_eq, F_pre, hS_def]
          have h_conv : ∀ j, j ≤ k →
              ∑ i ∈ Finset.range j, X i ω =
              ∑ i : ↑(Finset.range k), if (↑i : ℕ) < j then X ↑i ω else 0 := by
            intro j hj
            rw [h_psum j hj ω]
            exact (Finset.sum_coe_sort (Finset.range k)
              (fun i => if i < j then X i ω else 0)).symm
          constructor
          · intro ⟨hge, hprev⟩
            refine ⟨?_, fun j hj => ?_⟩
            · have := Finset.sum_coe_sort (Finset.range k) (fun i => X i ω); linarith
            · rw [← h_conv j (le_of_lt hj)]; exact hprev j hj
          · intro ⟨hge, hprev⟩
            refine ⟨?_, fun j hj => ?_⟩
            · have := Finset.sum_coe_sort (Finset.range k) (fun i => X i ω); linarith
            · rw [h_conv j (le_of_lt hj)]; exact hprev j hj
        -- Measurability of the preimage sets
        have hT_meas : MeasurableSet {f : ↑(Finset.range k) → ℝ | (m : ℝ) ≤ ∑ i, f i ∧
            ∀ j, j < k → (∑ i : ↑(Finset.range k),
              if (↑i : ℕ) < j then f i else 0) < ↑m} := by
          have : {f : ↑(Finset.range k) → ℝ | (m : ℝ) ≤ ∑ i, f i ∧
              ∀ j, j < k → (∑ i : ↑(Finset.range k),
                if (↑i : ℕ) < j then f i else 0) < ↑m} =
            {f | (m : ℝ) ≤ ∑ i, f i} ∩
              (⋂ (j : ℕ), ⋂ (_ : j < k),
                {f : ↑(Finset.range k) → ℝ |
                  (∑ i : ↑(Finset.range k), if (↑i : ℕ) < j then f i else 0) < ↑m}) := by
            ext f; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
          rw [this]
          exact MeasurableSet.inter
            (measurableSet_le measurable_const
              (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)))
            (MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
              measurableSet_lt (Finset.measurable_sum _ (fun i _ => by
                by_cases h : (↑i : ℕ) < j
                · simp only [if_pos h]; exact measurable_pi_apply i
                · simp only [if_neg h]; exact measurable_const))
              measurable_const)))
        have hU_pos_meas : MeasurableSet {f : ↑(Finset.Ico k n) → ℝ | 0 < ∑ j, f j} :=
          measurableSet_lt measurable_const
            (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
        have hU_neg_meas : MeasurableSet {f : ↑(Finset.Ico k n) → ℝ | ∑ j, f j ≤ 0} :=
          measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
            measurable_const
        -- Independence: μ(G k ∩ {R > 0}) = μ(G k) · μ({R > 0})
        have h_prod_pos : μ (G k ∩ {ω | 0 < R k ω}) = μ (G k) * μ {ω | 0 < R k ω} := by
          rw [hG_eq, hR_pos_eq]
          exact h_tup.measure_inter_preimage_eq_mul _ _ hT_meas hU_pos_meas
        -- Independence: μ(G k ∩ {R ≤ 0}) = μ(G k) · μ({R ≤ 0})
        have h_prod_neg : μ (G k ∩ {ω | R k ω ≤ 0}) = μ (G k) * μ {ω | R k ω ≤ 0} := by
          rw [hG_eq, hR_neg_eq]
          exact h_tup.measure_inter_preimage_eq_mul _ _ hT_meas hU_neg_meas
        -- A.e. on G k: S'_k = m, so Sn > m ↔ R k > 0
        have h_ae_sub1 : (hiE ∩ G k : Set Ω) ≤ᵐ[μ] ({ω | 0 < R k ω} ∩ G k : Set Ω) := by
          filter_upwards [h_integer k] with ω hint
          rintro ⟨hhi, hG⟩
          refine ⟨?_, hG⟩
          have h1 := h_Sn_eq k hk_le ω
          have h2 := hint hG
          have h3 : (↑m : ℝ) < Sn ω := hhi
          show 0 < R k ω
          linarith
        -- A.e. on G k: S'_k = m and R k ≤ 0 → Sn ≤ m and ω ∈ maxE
        have h_ae_sub2 : ({ω | R k ω ≤ 0} ∩ G k : Set Ω) ≤ᵐ[μ] ((maxE \ hiE) ∩ G k : Set Ω) := by
          filter_upwards [h_integer k] with ω hint
          rintro ⟨hR, hG⟩
          refine ⟨⟨?_, ?_⟩, hG⟩
          · exact h_partition ▸ Set.mem_biUnion
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)) hG
          · intro habs
            have h1 := h_Sn_eq k hk_le ω
            have h2 := hint hG
            have h3 : (m : ℝ) < Sn ω := habs
            have h4 : R k ω ≤ 0 := hR
            linarith
        -- Chain the inequalities
        calc μ (hiE ∩ G k)
            ≤ μ ({ω | 0 < R k ω} ∩ G k) := measure_mono_ae h_ae_sub1
          _ = μ (G k ∩ {ω | 0 < R k ω}) := by rw [Set.inter_comm]
          _ = μ (G k) * μ {ω | 0 < R k ω} := h_prod_pos
          _ ≤ μ (G k) * μ {ω | R k ω ≤ 0} := mul_le_mul_right (h_sym k) _
          _ = μ (G k ∩ {ω | R k ω ≤ 0}) := h_prod_neg.symm
          _ = μ ({ω | R k ω ≤ 0} ∩ G k) := by rw [Set.inter_comm]
          _ ≤ μ ((maxE \ hiE) ∩ G k) := measure_mono_ae h_ae_sub2
      -- Summation: sum the per-k inequalities
      have h_disj_hi : Set.PairwiseDisjoint (↑(Finset.range (n + 1)))
          (fun k => hiE ∩ G k) := by
        intro i hi j hj hij
        exact Disjoint.mono_left Set.inter_subset_right
          (Disjoint.mono_right Set.inter_subset_right (h_disj hi hj hij))
      have h_disj_lo : Set.PairwiseDisjoint (↑(Finset.range (n + 1)))
          (fun k => (maxE \ hiE) ∩ G k) := by
        intro i hi j hj hij
        exact Disjoint.mono_left Set.inter_subset_right
          (Disjoint.mono_right Set.inter_subset_right (h_disj hi hj hij))
      calc μ hiE
          = μ (hiE ∩ maxE) := by rw [Set.inter_eq_self_of_subset_left h_sub]
        _ = μ (hiE ∩ ⋃ k ∈ Finset.range (n + 1), G k) := by rw [h_partition]
        _ = μ (⋃ k ∈ Finset.range (n + 1), hiE ∩ G k) := by rw [Set.inter_iUnion₂]
        _ = ∑ k ∈ Finset.range (n + 1), μ (hiE ∩ G k) :=
            measure_biUnion_finset (fun i hi j hj hij => h_disj_hi hi hj hij)
              (fun k _ => h_meas_hi.inter (h_meas_G k))
        _ ≤ ∑ k ∈ Finset.range (n + 1), μ ((maxE \ hiE) ∩ G k) :=
            Finset.sum_le_sum (fun k hk => h_key k hk)
        _ = μ (⋃ k ∈ Finset.range (n + 1), (maxE \ hiE) ∩ G k) :=
            (measure_biUnion_finset (fun i hi j hj hij => h_disj_lo hi hj hij)
              (fun k _ => (h_meas_max.diff h_meas_hi).inter (h_meas_G k))).symm
        _ = μ ((maxE \ hiE) ∩ ⋃ k ∈ Finset.range (n + 1), G k) := by rw [Set.inter_iUnion₂]
        _ = μ ((maxE \ hiE) ∩ maxE) := by rw [h_partition]
        _ = μ (maxE \ hiE) := by
            rw [Set.inter_eq_self_of_subset_left Set.diff_subset]
    -- Chain: 2·μ(S_n > m) ≤ μ(S_n > m) + μ(max ≥ m \ S_n > m) = μ(max ≥ m)
    calc 2 * μ hiE = μ hiE + μ hiE := two_mul _
      _ ≤ μ hiE + μ (maxE \ hiE) := add_le_add (le_refl _) h_reflect
      _ = μ maxE := h_decomp.symm
  -- === Step 2: Choose θ so that 2·N(0,1)(θ,∞) > ε ===
  -- As θ → 0⁺, gaussianReal(0,1)(Ioi θ) → 1/2. So 2·(1/2) = 1 > ε.
  have hChoose : ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal (ε / 2) <
      (G : Measure ℝ) (Set.Ioi θ) := by
    set Gμ := (gaussianReal 0 1 : Measure ℝ)
    have hG_eq : (G : Measure ℝ) = Gμ := rfl
    haveI : NullSingletonClass Gμ := by
      dsimp [Gμ]
      exact nullSingletonClass_gaussianReal one_ne_zero
    have nR2 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 :=
      fun n => by have := n.cast_nonneg (α := ℝ); linarith
    have hSym : Gμ.map Neg.neg = Gμ := by rw [gaussianReal_map_neg, neg_zero]
    have hIio_eq : Gμ (Set.Iio 0) = Gμ (Set.Ioi 0) := by
      calc Gμ (Set.Iio 0) = Gμ.map Neg.neg (Set.Ioi 0) := by
            rw [Measure.map_apply measurable_neg measurableSet_Ioi]; congr 1; ext x; simp
        _ = Gμ (Set.Ioi 0) := by rw [hSym]
    have hIic_Iio : Gμ (Set.Iic 0) = Gμ (Set.Iio 0) := by
      rw [show Set.Iic (0:ℝ) = Set.Iio 0 ∪ {0} from Set.Iio_union_right.symm]
      rw [measure_union (Set.disjoint_left.mpr fun x hx h0 => by simp at hx h0; linarith)
        (measurableSet_singleton _)]
      rw [measure_singleton, add_zero]
    have hDecomp : Gμ (Set.Ioi 0) + Gμ (Set.Iic 0) = 1 := by
      have h_union : Set.Ioi (0:ℝ) ∪ Set.Iic 0 = Set.univ := by
        ext x; simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
        exact (le_or_gt x 0).elim Or.inr Or.inl
      calc Gμ (Set.Ioi 0) + Gμ (Set.Iic 0)
          = Gμ (Set.Ioi 0 ∪ Set.Iic 0) := (measure_union
            (Set.disjoint_left.mpr fun x (hx : 0 < x) (hx2 : x ≤ 0) =>
              absurd hx (not_lt.mpr hx2))
            measurableSet_Iic).symm
        _ = Gμ Set.univ := by rw [h_union]
        _ = 1 := measure_univ
    rw [hIic_Iio, hIio_eq, ← two_mul] at hDecomp
    have h2ne : (2 : ENNReal) ≠ 0 := by norm_num
    have h2top : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
    have hHalf : Gμ (Set.Ioi 0) = 1 / 2 := by
      have : Gμ (Set.Ioi 0) = 2⁻¹ :=
        (ENNReal.mul_right_inj h2ne h2top).mp
          (hDecomp.trans (ENNReal.mul_inv_cancel h2ne h2top).symm)
      simp [this]
    have hε2_lt : ENNReal.ofReal (ε / 2) < Gμ (Set.Ioi 0) := by
      rw [hHalf]; calc ENNReal.ofReal (ε / 2)
          < ENNReal.ofReal (1 / 2) :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr (by linarith)
        _ = 1 / 2 := by simp
    have hMono : Monotone (fun n : ℕ => Set.Ioi (1 / ((n : ℝ) + 2))) := by
      intro a b hab; apply Set.Ioi_subset_Ioi
      apply div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num) (nR2 a)
      linarith [show (a:ℝ) ≤ (b:ℝ) from Nat.cast_le.mpr hab]
    have hUnion : ⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 2)) = Set.Ioi 0 := by
      ext x; simp only [Set.mem_iUnion, Set.mem_Ioi]; constructor
      · rintro ⟨n, hn⟩; linarith [div_pos (show (0:ℝ) < 1 by norm_num) (nR2 n)]
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / x - 2)
        refine ⟨n, ?_⟩
        rw [div_lt_iff₀ (nR2 n)]
        nlinarith [(div_lt_iff₀ hx).mp (show 1 / x < (n:ℝ) + 2 by linarith)]
    have hTend : Filter.Tendsto (fun n : ℕ => Gμ (Set.Ioi (1 / ((n : ℝ) + 2))))
        Filter.atTop (nhds (Gμ (Set.Ioi 0))) := by
      have h := tendsto_measure_iUnion_atTop hMono (μ := Gμ); rwa [hUnion] at h
    obtain ⟨n, hn⟩ := (hTend.eventually (Ioi_mem_nhds hε2_lt)).exists
    exact ⟨1 / ((n : ℝ) + 2), div_pos (show (0:ℝ) < 1 by norm_num) (nR2 n), hG_eq ▸ hn⟩
  -- θ₁ is the internal Gaussian threshold; output θ = θ₁/2 for the running max
  obtain ⟨θ₁, hθ₁_pos, hθ₁_gauss⟩ := hChoose
  refine ⟨θ₁ / 2, by linarith, ?_⟩
  -- === Step 3: Portmanteau — CLT convergence gives liminf bound ===
  have hPort := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hCLT
    (isOpen_Ioi (a := θ₁))
  -- === Step 4: From liminf ≥ c > ε/2 to eventually ≥ ε/2 ===
  have hEventual : ∀ᶠ n in Filter.atTop,
      ENNReal.ofReal (ε / 2) ≤
        (Pn n : Measure ℝ) (Set.Ioi θ₁) := by
    have hlt : ENNReal.ofReal (ε / 2) <
        Filter.atTop.liminf (fun n =>
          (Pn n : Measure ℝ) (Set.Ioi θ₁)) :=
      lt_of_lt_of_le hθ₁_gauss hPort
    exact (Filter.eventually_lt_of_lt_liminf hlt).mono (fun n h => h.le)
  -- === Step 5: Extract n₀ and combine with reflection ===
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hEventual
  obtain ⟨n₀, hn₀_spec⟩ := hEventual
  -- Need n large enough for: (a) CLT bound, (b) ⌈θ₁/2·√n⌉ > 0, (c) ⌈θ₁/2·√n⌉ ≤ θ₁·√n
  -- For (b)+(c): need θ₁/2 · √n ≥ 1, i.e., n ≥ 4/θ₁²
  set n₁ := max (max n₀ 1) (Nat.ceil (4 / θ₁ ^ 2) + 1)
  exact ⟨n₁, fun n hn => by
    have hn₀ : n₀ ≤ n := le_trans (le_max_left n₀ 1) (le_trans (le_max_left _ _) hn)
    have hn_pos : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; omega)
    have hPortN := hn₀_spec n hn₀
    -- n is large enough that θ₁/2 · √n ≥ 1
    have hn_large : 1 ≤ θ₁ / 2 * Real.sqrt n := by
      have hnn : Nat.ceil (4 / θ₁ ^ 2) + 1 ≤ n :=
        le_trans (le_max_right _ _) hn
      have hfn : (4 / θ₁ ^ 2 : ℝ) < n := by
        calc 4 / θ₁ ^ 2 ≤ ↑⌈(4 / θ₁ ^ 2 : ℝ)⌉₊ := Nat.le_ceil _
          _ < ↑(⌈(4 / θ₁ ^ 2 : ℝ)⌉₊ + 1) := by push_cast; linarith
          _ ≤ (n : ℝ) := Nat.cast_le.mpr hnn
      rw [div_lt_iff₀ (pow_pos hθ₁_pos 2)] at hfn
      -- 4 < θ₁² · n = (θ₁ · √n)², so θ₁ · √n > 2, so θ₁/2 · √n > 1
      have h_sqrt_sq : Real.sqrt ↑n * Real.sqrt ↑n = ↑n :=
        Real.mul_self_sqrt (Nat.cast_nonneg n)
      have h_prod_sq : (θ₁ * Real.sqrt n) ^ 2 = θ₁ ^ 2 * n := by
        ring_nf; rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have h_prod_pos : 0 < θ₁ * Real.sqrt n := by positivity
      -- (θ₁ · √n)² > 4 and θ₁ · √n > 0 → θ₁ · √n > 2
      have h_gt2 : 2 < θ₁ * Real.sqrt n := by
        nlinarith [sq_nonneg (θ₁ * Real.sqrt n - 2)]
      linarith
    -- Define m = ⌈θ₁/2 · √n⌉ (integer level for reflection)
    set m := ⌈θ₁ / 2 * Real.sqrt n⌉₊ with hm_def
    have hm_pos : 0 < m := by
      rw [hm_def, Nat.pos_iff_ne_zero, ne_eq, Nat.ceil_eq_zero]
      linarith
    -- m ≥ θ₁/2 · √n (ceiling ≥ argument)
    have hm_ge : θ₁ / 2 * Real.sqrt n ≤ (m : ℝ) := Nat.le_ceil _
    -- m ≤ θ₁/2 · √n + 1 ≤ θ₁ · √n (for large n)
    have hm_le_ceil : (m : ℝ) ≤ θ₁ / 2 * Real.sqrt n + 1 :=
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ θ₁ / 2 * Real.sqrt n)).le
    have hm_le : (m : ℝ) ≤ θ₁ * Real.sqrt n := by nlinarith
    -- Convert CLT bound: P(S_n/√n > θ₁) = P(S_n > θ₁·√n)
    have hConv : (Pn n : Measure ℝ) (Set.Ioi θ₁) =
        μ {ω | θ₁ * Real.sqrt ↑n < ∑ i ∈ Finset.range n, X i ω} := by
      change (μ.map (normalizedSum n)) (Set.Ioi θ₁) = _
      rw [Measure.map_apply
        (hNormalizedSumMeas n) measurableSet_Ioi]
      congr 1; ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq,
        normalizedSum]
      have hsqrt_pos : (0 : ℝ) < sqrt ↑n := sqrt_pos.mpr (Nat.cast_pos.mpr hn_pos)
      exact ⟨fun h => by nlinarith [inv_pos.mpr hsqrt_pos, mul_inv_cancel₀ hsqrt_pos.ne'],
             fun h => by nlinarith [inv_pos.mpr hsqrt_pos, mul_inv_cancel₀ hsqrt_pos.ne']⟩
    -- {S_n > θ₁√n} ⊆ {S_n > m} since m ≤ θ₁√n
    have hSub1 : {ω | θ₁ * sqrt ↑n < ∑ i ∈ Finset.range n, X i ω} ⊆
        {ω | (m : ℝ) < ∑ i ∈ Finset.range n, X i ω} :=
      fun ω hω => lt_of_le_of_lt hm_le hω
    -- {∃ k, m ≤ S_k} ⊆ {∃ k, θ₁/2·√n ≤ S_k} since m ≥ θ₁/2·√n
    have hSub2 : {ω | ∃ k ∈ Finset.range (n + 1),
          (m : ℝ) ≤ ∑ i ∈ Finset.range k, X i ω} ⊆
        {ω | ∃ k ∈ Finset.range (n + 1),
          θ₁ / 2 * sqrt ↑n ≤ ∑ i ∈ Finset.range k, X i ω} :=
      fun ω ⟨k, hk, hle⟩ => ⟨k, hk, le_trans hm_ge hle⟩
    -- Chain: ε ≤ 2·P(S_n > θ₁√n) ≤ 2·P(S_n > m) ≤ P(max ≥ m) ≤ P(max ≥ θ₁/2·√n)
    calc ENNReal.ofReal ε = 2 * ENNReal.ofReal (ε / 2) := by
            rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 2)]
            congr 1; ring
      _ ≤ 2 * μ {ω | θ₁ * sqrt ↑n < ∑ i ∈ Finset.range n, X i ω} :=
            mul_le_mul_right (hConv ▸ hPortN) 2
      _ ≤ 2 * μ {ω | (m : ℝ) < ∑ i ∈ Finset.range n, X i ω} :=
            mul_le_mul_right (measure_mono hSub1) 2
      _ ≤ μ {ω | ∃ k ∈ Finset.range (n + 1),
              (m : ℝ) ≤ ∑ i ∈ Finset.range k, X i ω} :=
            hReflection m n hm_pos
      _ ≤ μ {ω | ∃ k ∈ Finset.range (n + 1), θ₁ / 2 * sqrt ↑n ≤
              ∑ i ∈ Finset.range k, X i ω} :=
            measure_mono hSub2⟩

/-!
Proof roadmap from paper Appendix `apx:couple-with-independent`:

1. Quantile coupling idea: for each step `i`, sample a shared `Uᵢ ~ Uniform[0,1)`,
   define `Ŷᵢ = 1[Uᵢ < qᵢ]`, `X̂ᵢ = 1[Uᵢ < pᵢ(past)]`.
   If `pᵢ(past) ≤ qᵢ` a.s., then `X̂ᵢ ≤ Ŷᵢ` pointwise.
2. Hence `∑ X̂ᵢ ≤ ∑ Ŷᵢ` pointwise, so tail events are monotone:
   `P[∑ X̂ᵢ ≥ k] ≤ P[∑ Ŷᵢ ≥ k]`.
3. Marginal laws match the original processes by construction, yielding
   stochastic domination for the original sums.

For Lean, we target the equivalent `ℕ`-threshold statement first and then reduce
real thresholds to `Nat.ceil` (done in `lemma_couple_with_independent` below).
-/
private lemma sum_bool_real_eq_nat_cast
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool) (ω : Ω) :
    (∑ i : Fin n, if Z i ω then (1 : ℝ) else 0) =
      ((∑ i : Fin n, if Z i ω then (1 : ℕ) else 0 : ℕ) : ℝ) := by
  simp

private lemma threshold_nat_real_iff
    {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (Z : Fin n → Ω → Bool) (ω : Ω) :
    ((k : ℝ) ≤ ∑ i : Fin n, if Z i ω then (1 : ℝ) else 0) ↔
      (k ≤ ∑ i : Fin n, if Z i ω then (1 : ℕ) else 0) := by
  rw [sum_bool_real_eq_nat_cast (Z := Z) ω]
  exact_mod_cast Iff.rfl

private lemma nat_tail_split
    {Ω : Type*} [MeasurableSpace Ω]
    (S L : Ω → ℕ) (j : ℕ) (hL : ∀ ω, L ω ≤ 1) :
    {ω | j + 1 ≤ S ω + L ω} =
      {ω | j + 1 ≤ S ω} ∪ ({ω | S ω = j} ∩ {ω | L ω = 1}) := by
  ext ω
  constructor
  · intro h
    by_cases hs : j + 1 ≤ S ω
    · exact Or.inl hs
    · have hSle : S ω ≤ j := Nat.le_of_lt_succ (lt_of_not_ge hs)
      have hLle : L ω ≤ 1 := hL ω
      have hSge : j ≤ S ω := by
        have : Nat.succ j ≤ Nat.succ (S ω) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (le_trans h (Nat.add_le_add_left hLle (S ω)))
        exact Nat.succ_le_succ_iff.mp this
      have hSj : S ω = j := Nat.le_antisymm hSle hSge
      have hLge : 1 ≤ L ω := by
        have h' : j + 1 ≤ S ω + L ω := h
        rw [hSj] at h'
        omega
      have hL1 : L ω = 1 := Nat.le_antisymm hLle hLge
      exact Or.inr ⟨hSj, hL1⟩
  · intro h
    rcases h with hs | ⟨hSj, hL1⟩
    · exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self j) hs)
        (Nat.le_add_right (S ω) (L ω))
    · have hSj' : S ω = j := by simpa using hSj
      have hL1' : L ω = 1 := by simpa using hL1
      simp [hSj', hL1']

private lemma tail_event_zero_univ
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool) :
    {ω | (0 : ℝ) ≤ ∑ i : Fin n, if Z i ω then (1 : ℝ) else 0} = Set.univ := by
  ext ω
  simp

private lemma tail_event_nat_threshold
    {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (Z : Fin n → Ω → Bool) :
    {ω | (k : ℝ) ≤ ∑ i : Fin n, if Z i ω then (1 : ℝ) else 0} =
      {ω | k ≤ ∑ i : Fin n, if Z i ω then (1 : ℕ) else 0} := by
  ext ω
  exact threshold_nat_real_iff (Z := Z) (k := k) ω

private lemma coupling_nat_k0
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Fin n → Ω → Bool) :
    μ {ω | (0 : ℝ) ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} ≤
      μ {ω | (0 : ℝ) ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} := by
  rw [tail_event_zero_univ (Z := X), tail_event_zero_univ (Z := Y)]

private lemma coupling_nat_n0
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Fin 0 → Ω → Bool) (k : ℕ) :
    μ {ω | (k : ℝ) ≤ ∑ i : Fin 0, if X i ω then (1 : ℝ) else 0} ≤
      μ {ω | (k : ℝ) ≤ ∑ i : Fin 0, if Y i ω then (1 : ℝ) else 0} := by
  simp

private lemma sum_succ_split_real
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin (n + 1) → Ω → Bool) (ω : Ω) :
    (∑ i : Fin (n + 1), if Z i ω then (1 : ℝ) else 0) =
      (∑ i : Fin n, if Z i.castSucc ω then (1 : ℝ) else 0) +
      (if Z (Fin.last n) ω then (1 : ℝ) else 0) := by
  simpa using
    (Fin.sum_univ_castSucc (f := fun i : Fin (n + 1) => if Z i ω then (1 : ℝ) else 0))

private lemma sum_succ_split_nat
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin (n + 1) → Ω → Bool) (ω : Ω) :
    (∑ i : Fin (n + 1), if Z i ω then (1 : ℕ) else 0) =
      (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) +
      (if Z (Fin.last n) ω then (1 : ℕ) else 0) := by
  simpa using
    (Fin.sum_univ_castSucc (f := fun i : Fin (n + 1) => if Z i ω then (1 : ℕ) else 0))

private lemma tail_event_succ_split
    {Ω : Type*} [MeasurableSpace Ω] {n j : ℕ}
    (Z : Fin (n + 1) → Ω → Bool) :
    {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin (n + 1), if Z i ω then (1 : ℝ) else 0} =
      {ω | j + 1 ≤ (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) +
          (if Z (Fin.last n) ω then (1 : ℕ) else 0)} := by
  ext ω
  constructor
  · intro h
    have hnat : j + 1 ≤ ∑ i : Fin (n + 1), if Z i ω then (1 : ℕ) else 0 :=
      (threshold_nat_real_iff (Z := Z) (k := j + 1) ω).1 h
    simpa [sum_succ_split_nat (Z := Z) ω] using hnat
  · intro h
    have hnat : j + 1 ≤ ∑ i : Fin (n + 1), if Z i ω then (1 : ℕ) else 0 := by
      simpa [sum_succ_split_nat (Z := Z) ω] using h
    exact (threshold_nat_real_iff (Z := Z) (k := j + 1) ω).2 hnat

private lemma tail_event_succ_union
    {Ω : Type*} [MeasurableSpace Ω] {n j : ℕ}
    (Z : Fin (n + 1) → Ω → Bool) :
    {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin (n + 1), if Z i ω then (1 : ℝ) else 0} =
      {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin n, if Z i.castSucc ω then (1 : ℝ) else 0} ∪
      ({ω | (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) = j} ∩
        {ω | Z (Fin.last n) ω = true}) := by
  have h1 :
      {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin (n + 1), if Z i ω then (1 : ℝ) else 0} =
      {ω | j + 1 ≤ (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) +
          (if Z (Fin.last n) ω then (1 : ℕ) else 0)} := tail_event_succ_split (Z := Z)
  have h2 :
      {ω | j + 1 ≤ (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) +
          (if Z (Fin.last n) ω then (1 : ℕ) else 0)} =
      {ω | j + 1 ≤ ∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0} ∪
      ({ω | (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) = j} ∩
        {ω | (if Z (Fin.last n) ω then (1 : ℕ) else 0) = 1}) := by
    have hL : ∀ ω, (if Z (Fin.last n) ω then (1 : ℕ) else 0) ≤ 1 := by
      intro ω
      split <;> omega
    exact nat_tail_split
      (S := fun ω => ∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0)
      (L := fun ω => if Z (Fin.last n) ω then (1 : ℕ) else 0)
      j hL
  rw [h1, h2]
  congr 1
  · ext ω
    exact (threshold_nat_real_iff (Z := fun i : Fin n => Z i.castSucc) (k := j + 1) ω).symm
  · ext ω
    simp

private lemma tail_event_succ_union_disjoint
    {Ω : Type*} [MeasurableSpace Ω] {n j : ℕ}
    (Z : Fin (n + 1) → Ω → Bool) :
    Disjoint
      {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin n, if Z i.castSucc ω then (1 : ℝ) else 0}
      ({ω | (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) = j} ∩
        {ω | Z (Fin.last n) ω = true}) := by
  rw [Set.disjoint_left]
  intro ω hA hB
  rcases hB with ⟨hEq, _⟩
  have hNatA : j + 1 ≤ ∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0 :=
    (threshold_nat_real_iff (Z := fun i : Fin n => Z i.castSucc) (k := j + 1) ω).1 hA
  have hEq' : (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) = j := by simpa using hEq
  omega

private lemma tail_event_succ_union_measure
    {Ω : Type*} [MeasurableSpace Ω] {n j : ℕ}
    (μ : Measure Ω)
    (Z : Fin (n + 1) → Ω → Bool)
    (hZ : ∀ i, Measurable (Z i)) :
    μ {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin (n + 1), if Z i ω then (1 : ℝ) else 0} =
      μ {ω | ((j + 1 : ℕ) : ℝ) ≤ ∑ i : Fin n, if Z i.castSucc ω then (1 : ℝ) else 0} +
      μ ({ω | (∑ i : Fin n, if Z i.castSucc ω then (1 : ℕ) else 0) = j} ∩
        {ω | Z (Fin.last n) ω = true}) := by
  rw [tail_event_succ_union (Z := Z)]
  refine measure_union (tail_event_succ_union_disjoint (Z := Z)) ?_
  refine MeasurableSet.inter ?_ ?_
  · refine (Finset.measurable_sum _ (fun i _ => ?_)) (measurableSet_singleton j)
    have hset : MeasurableSet {ω | Z i.castSucc ω = true} :=
      hZ i.castSucc (measurableSet_singleton true)
    have hEq :
        (fun ω => if Z i.castSucc ω then (1 : ℕ) else 0) =
          Set.indicator {ω | Z i.castSucc ω = true} (fun _ : Ω => (1 : ℕ)) := by
      funext ω
      by_cases hz : Z i.castSucc ω = true <;> simp [Set.indicator, hz]
    rw [hEq]
    exact Measurable.indicator measurable_const hset
  · exact hZ (Fin.last n) (measurableSet_singleton true)

private lemma last_bool_nat_le_one
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin (n + 1) → Ω → Bool) :
    ∀ ω, (if Z (Fin.last n) ω then (1 : ℕ) else 0) ≤ 1 := by
  intro ω
  split <;> omega

/-- The σ-algebra generated by the Bernoulli variables strictly before `i`. -/
def bernoulliPastSpace
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → Bool) (i : Fin n) : MeasurableSpace Ω :=
  ⨆ j ∈ Set.Iio i, MeasurableSpace.comap (X j) ⊤

/-- Integrated form of
`P[Xᵢ = 1 | X₀, ..., Xᵢ₋₁] ≤ P[Yᵢ = 1]`.
It avoids division by zero on null histories and is equivalent to the usual
conditional-probability statement. -/
def BernoulliConditionallyLE
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X Y : Fin n → Ω → Bool) : Prop :=
  ∀ (i : Fin n) (A : Set Ω), MeasurableSet[bernoulliPastSpace X i] A →
    μ.real (A ∩ {ω | X i ω = true}) ≤
      μ.real A * μ.real {ω | Y i ω = true}

/-- Integrated form of
`P[Xᵢ = 1 | X₀, ..., Xᵢ₋₁] ≥ P[Yᵢ = 1]`. -/
def BernoulliConditionallyGE
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X Y : Fin n → Ω → Bool) : Prop :=
  ∀ (i : Fin n) (A : Set Ω), MeasurableSet[bernoulliPastSpace X i] A →
    μ.real A * μ.real {ω | Y i ω = true} ≤
      μ.real (A ∩ {ω | X i ω = true})

private def boolPrefixCount
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool) (m : ℕ) (ω : Ω) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m),
    if Z i ω then 1 else 0

private lemma boolPrefixCount_succ
    {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (Z : Fin n → Ω → Bool) (hm : m < n) (ω : Ω) :
    boolPrefixCount Z (m + 1) ω =
      boolPrefixCount Z m ω + if Z ⟨m, hm⟩ ω then 1 else 0 := by
  let i : Fin n := ⟨m, hm⟩
  have hfilter :
      Finset.univ.filter (fun j : Fin n => j.val < m + 1) =
        insert i (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · right
        have hne : j.val ≠ m := by
          intro h
          apply hji
          exact Fin.ext h
        omega
    · rintro (rfl | hj)
      · simp [i]
      · omega
  rw [boolPrefixCount, boolPrefixCount, hfilter, Finset.sum_insert]
  · simp [i, add_comm]
  · simp [i]

private lemma measurable_boolPrefixCount
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool) (hZMeas : ∀ i, Measurable (Z i)) (m : ℕ) :
    Measurable (boolPrefixCount Z m) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_finite (fun b : Bool => if b then (1 : ℕ) else 0)).comp (hZMeas i)

private lemma measurable_boolPrefixCount_past
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool) (i : Fin n) :
    @Measurable Ω ℕ (bernoulliPastSpace Z i) ⊤ (boolPrefixCount Z i.val) := by
  apply Finset.measurable_sum
  intro j hj
  have hjlt : j < i := by
    exact_mod_cast
      (show (j : Nat) < (i : Nat) by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj)
  have hZj :
      @Measurable Ω Bool (MeasurableSpace.comap (Z j) ⊤) ⊤ (Z j) :=
    comap_measurable _
  have hle : MeasurableSpace.comap (Z j) ⊤ ≤ bernoulliPastSpace Z i :=
    le_iSup_of_le j (le_iSup_of_le hjlt le_rfl)
  exact (measurable_of_finite (fun b : Bool => if b then (1 : ℕ) else 0)).comp
    (hZj.mono hle le_rfl)

private lemma boolPrefixCount_all
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool) (ω : Ω) :
    boolPrefixCount Z n ω = ∑ i : Fin n, if Z i ω then 1 else 0 := by
  simp [boolPrefixCount]

private lemma prefix_tail_succ_union
    {Ω : Type*} [MeasurableSpace Ω] {n m j : ℕ}
    (Z : Fin n → Ω → Bool) (hm : m < n) :
    {ω | j + 1 ≤ boolPrefixCount Z (m + 1) ω} =
      {ω | j + 1 ≤ boolPrefixCount Z m ω} ∪
        ({ω | boolPrefixCount Z m ω = j} ∩ {ω | Z ⟨m, hm⟩ ω = true}) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
  rw [boolPrefixCount_succ Z hm ω]
  by_cases h : Z ⟨m, hm⟩ ω = true <;> simp [h] <;> omega

private lemma prefix_tail_eq_union
    {Ω : Type*} [MeasurableSpace Ω] {n m j : ℕ}
    (Z : Fin n → Ω → Bool) :
    {ω | j ≤ boolPrefixCount Z m ω} =
      {ω | j + 1 ≤ boolPrefixCount Z m ω} ∪
        {ω | boolPrefixCount Z m ω = j} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_union]
  omega

private lemma prefix_tail_eq_disjoint
    {Ω : Type*} [MeasurableSpace Ω] {n m j : ℕ}
    (Z : Fin n → Ω → Bool) :
    Disjoint {ω | j + 1 ≤ boolPrefixCount Z m ω}
      {ω | boolPrefixCount Z m ω = j} := by
  rw [Set.disjoint_left]
  intro ω hge heq
  simp only [Set.mem_setOf_eq] at hge heq
  omega

private lemma prefix_tail_succ_disjoint
    {Ω : Type*} [MeasurableSpace Ω] {n m j : ℕ}
    (Z : Fin n → Ω → Bool) (hm : m < n) :
    Disjoint {ω | j + 1 ≤ boolPrefixCount Z m ω}
      ({ω | boolPrefixCount Z m ω = j} ∩ {ω | Z ⟨m, hm⟩ ω = true}) := by
  rw [Set.disjoint_left]
  intro ω hge heq
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff] at hge heq
  omega

private lemma iIndepFun_indep_past_current
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (Y : Fin n → Ω → Bool)
    (hYMeas : ∀ i, Measurable (Y i)) (hYIndep : iIndepFun Y μ) (i : Fin n) :
    Indep (bernoulliPastSpace Y i) (MeasurableSpace.comap (Y i) ⊤) μ := by
  have h := indep_iSup_of_disjoint
    (m := fun j : Fin n => MeasurableSpace.comap (Y j) ⊤)
    (fun j => (hYMeas j).comap_le) hYIndep.iIndep
    (S := Set.Iio i) (T := {i}) (Set.disjoint_singleton_right.mpr (lt_irrefl i))
  simpa [bernoulliPastSpace] using h

private lemma independent_past_inter_current_real
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (Y : Fin n → Ω → Bool)
    (hYMeas : ∀ i, Measurable (Y i)) (hYIndep : iIndepFun Y μ)
    (i : Fin n) (A : Set Ω) (hA : MeasurableSet[bernoulliPastSpace Y i] A) :
    μ.real (A ∩ {ω | Y i ω = true}) =
      μ.real A * μ.real {ω | Y i ω = true} := by
  have hlast : MeasurableSet[MeasurableSpace.comap (Y i) ⊤] {ω | Y i ω = true} :=
    (comap_measurable (Y i)) (measurableSet_singleton true)
  have h := (Indep_iff _ _ μ).mp
    (iIndepFun_indep_past_current μ Y hYMeas hYIndep i)
    A {ω | Y i ω = true} hA hlast
  simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

private theorem coupling_nat_aux_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Fin n → Ω → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y μ)
    (hDom : BernoulliConditionallyLE μ X Y)
    (k : ℕ) :
    μ {ω | k ≤ ∑ i : Fin n, if X i ω then (1 : ℕ) else 0} ≤
      μ {ω | k ≤ ∑ i : Fin n, if Y i ω then (1 : ℕ) else 0} := by
  suffices hreal :
      μ.real {ω | k ≤ ∑ i : Fin n, if X i ω then (1 : ℕ) else 0} ≤
        μ.real {ω | k ≤ ∑ i : Fin n, if Y i ω then (1 : ℕ) else 0} by
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mp hreal
  have hprefix : ∀ m : ℕ, m ≤ n → ∀ r : ℕ,
      μ.real {ω | r ≤ boolPrefixCount X m ω} ≤
        μ.real {ω | r ≤ boolPrefixCount Y m ω} := by
    intro m hm
    induction m with
    | zero =>
        intro r
        cases r <;> simp [boolPrefixCount]
    | succ m ih =>
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        have ihm := ih (Nat.le_of_lt hm_lt)
        intro r
        cases r with
        | zero =>
            simp
        | succ j =>
            let i : Fin n := ⟨m, hm_lt⟩
            let AXhi : Set Ω := {ω | j + 1 ≤ boolPrefixCount X m ω}
            let AXeq : Set Ω := {ω | boolPrefixCount X m ω = j}
            let AYhi : Set Ω := {ω | j + 1 ≤ boolPrefixCount Y m ω}
            let AYeq : Set Ω := {ω | boolPrefixCount Y m ω = j}
            let LX : Set Ω := {ω | X i ω = true}
            let LY : Set Ω := {ω | Y i ω = true}
            have hXm := measurable_boolPrefixCount X hXMeas m
            have hYm := measurable_boolPrefixCount Y hYMeas m
            have hAXhi : MeasurableSet AXhi := hXm (measurableSet_Ici)
            have hAXeq : MeasurableSet AXeq := hXm (measurableSet_singleton j)
            have hAYhi : MeasurableSet AYhi := hYm (measurableSet_Ici)
            have hAYeq : MeasurableSet AYeq := hYm (measurableSet_singleton j)
            have hAXpast : MeasurableSet[bernoulliPastSpace X i] AXeq := by
              exact (measurable_boolPrefixCount_past X i) (measurableSet_singleton j)
            have hAYpast : MeasurableSet[bernoulliPastSpace Y i] AYeq := by
              exact (measurable_boolPrefixCount_past Y i) (measurableSet_singleton j)
            have hLX : MeasurableSet LX := hXMeas i (measurableSet_singleton true)
            have hLY : MeasurableSet LY := hYMeas i (measurableSet_singleton true)
            have hXsucc :
                μ.real {ω | j + 1 ≤ boolPrefixCount X (m + 1) ω} =
                  μ.real AXhi + μ.real (AXeq ∩ LX) := by
              rw [prefix_tail_succ_union X hm_lt]
              exact measureReal_union (prefix_tail_succ_disjoint X hm_lt)
                (hAXeq.inter hLX)
            have hYsucc :
                μ.real {ω | j + 1 ≤ boolPrefixCount Y (m + 1) ω} =
                  μ.real AYhi + μ.real (AYeq ∩ LY) := by
              rw [prefix_tail_succ_union Y hm_lt]
              exact measureReal_union (prefix_tail_succ_disjoint Y hm_lt)
                (hAYeq.inter hLY)
            have hXsplit :
                μ.real {ω | j ≤ boolPrefixCount X m ω} =
                  μ.real AXhi + μ.real AXeq := by
              rw [prefix_tail_eq_union X]
              exact measureReal_union (prefix_tail_eq_disjoint X) hAXeq
            have hYsplit :
                μ.real {ω | j ≤ boolPrefixCount Y m ω} =
                  μ.real AYhi + μ.real AYeq := by
              rw [prefix_tail_eq_union Y]
              exact measureReal_union (prefix_tail_eq_disjoint Y) hAYeq
            have hcond : μ.real (AXeq ∩ LX) ≤ μ.real AXeq * μ.real LY := by
              exact hDom i AXeq hAXpast
            have hind : μ.real (AYeq ∩ LY) = μ.real AYeq * μ.real LY := by
              exact independent_past_inter_current_real μ Y hYMeas hYIndep i AYeq hAYpast
            have hq0 : 0 ≤ μ.real LY := measureReal_nonneg
            have hq1 : μ.real LY ≤ 1 := measureReal_le_one
            have hhi : μ.real AXhi ≤ μ.real AYhi := ihm (j + 1)
            have hlo :
                μ.real {ω | j ≤ boolPrefixCount X m ω} ≤
                  μ.real {ω | j ≤ boolPrefixCount Y m ω} := ihm j
            calc
              μ.real {ω | j + 1 ≤ boolPrefixCount X (m + 1) ω}
                  = μ.real AXhi + μ.real (AXeq ∩ LX) := hXsucc
              _ ≤ μ.real AXhi + μ.real AXeq * μ.real LY := add_le_add_right hcond _
              _ = (1 - μ.real LY) * μ.real AXhi +
                    μ.real LY * μ.real {ω | j ≤ boolPrefixCount X m ω} := by
                    rw [hXsplit]
                    ring
              _ ≤ (1 - μ.real LY) * μ.real AYhi +
                    μ.real LY * μ.real {ω | j ≤ boolPrefixCount Y m ω} := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hq1))
                      (mul_le_mul_of_nonneg_left hlo hq0)
              _ = μ.real AYhi + μ.real AYeq * μ.real LY := by
                    rw [hYsplit]
                    ring
              _ = μ.real AYhi + μ.real (AYeq ∩ LY) := by rw [hind]
              _ = μ.real {ω | j + 1 ≤ boolPrefixCount Y (m + 1) ω} := hYsucc.symm
  simpa only [boolPrefixCount_all] using hprefix n le_rfl k

private theorem coupling_nat_aux_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Fin n → Ω → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y μ)
    (hDom : BernoulliConditionallyGE μ X Y)
    (k : ℕ) :
    μ {ω | k ≤ ∑ i : Fin n, if Y i ω then (1 : ℕ) else 0} ≤
      μ {ω | k ≤ ∑ i : Fin n, if X i ω then (1 : ℕ) else 0} := by
  suffices hreal :
      μ.real {ω | k ≤ ∑ i : Fin n, if Y i ω then (1 : ℕ) else 0} ≤
        μ.real {ω | k ≤ ∑ i : Fin n, if X i ω then (1 : ℕ) else 0} by
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mp hreal
  have hprefix : ∀ m : ℕ, m ≤ n → ∀ r : ℕ,
      μ.real {ω | r ≤ boolPrefixCount Y m ω} ≤
        μ.real {ω | r ≤ boolPrefixCount X m ω} := by
    intro m hm
    induction m with
    | zero =>
        intro r
        simp [boolPrefixCount]
    | succ m ih =>
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        have ihm := ih (Nat.le_of_lt hm_lt)
        intro r
        cases r with
        | zero =>
            simp
        | succ j =>
            let i : Fin n := ⟨m, hm_lt⟩
            let AXhi : Set Ω := {ω | j + 1 ≤ boolPrefixCount X m ω}
            let AXeq : Set Ω := {ω | boolPrefixCount X m ω = j}
            let AYhi : Set Ω := {ω | j + 1 ≤ boolPrefixCount Y m ω}
            let AYeq : Set Ω := {ω | boolPrefixCount Y m ω = j}
            let LX : Set Ω := {ω | X i ω = true}
            let LY : Set Ω := {ω | Y i ω = true}
            have hXm := measurable_boolPrefixCount X hXMeas m
            have hYm := measurable_boolPrefixCount Y hYMeas m
            have hAXhi : MeasurableSet AXhi := hXm measurableSet_Ici
            have hAXeq : MeasurableSet AXeq := hXm (measurableSet_singleton j)
            have hAYhi : MeasurableSet AYhi := hYm measurableSet_Ici
            have hAYeq : MeasurableSet AYeq := hYm (measurableSet_singleton j)
            have hAXpast : MeasurableSet[bernoulliPastSpace X i] AXeq :=
              (measurable_boolPrefixCount_past X i) (measurableSet_singleton j)
            have hAYpast : MeasurableSet[bernoulliPastSpace Y i] AYeq :=
              (measurable_boolPrefixCount_past Y i) (measurableSet_singleton j)
            have hLX : MeasurableSet LX := hXMeas i (measurableSet_singleton true)
            have hLY : MeasurableSet LY := hYMeas i (measurableSet_singleton true)
            have hXsucc :
                μ.real {ω | j + 1 ≤ boolPrefixCount X (m + 1) ω} =
                  μ.real AXhi + μ.real (AXeq ∩ LX) := by
              rw [prefix_tail_succ_union X hm_lt]
              exact measureReal_union (prefix_tail_succ_disjoint X hm_lt)
                (hAXeq.inter hLX)
            have hYsucc :
                μ.real {ω | j + 1 ≤ boolPrefixCount Y (m + 1) ω} =
                  μ.real AYhi + μ.real (AYeq ∩ LY) := by
              rw [prefix_tail_succ_union Y hm_lt]
              exact measureReal_union (prefix_tail_succ_disjoint Y hm_lt)
                (hAYeq.inter hLY)
            have hXsplit :
                μ.real {ω | j ≤ boolPrefixCount X m ω} =
                  μ.real AXhi + μ.real AXeq := by
              rw [prefix_tail_eq_union X]
              exact measureReal_union (prefix_tail_eq_disjoint X) hAXeq
            have hYsplit :
                μ.real {ω | j ≤ boolPrefixCount Y m ω} =
                  μ.real AYhi + μ.real AYeq := by
              rw [prefix_tail_eq_union Y]
              exact measureReal_union (prefix_tail_eq_disjoint Y) hAYeq
            have hcond : μ.real AXeq * μ.real LY ≤ μ.real (AXeq ∩ LX) :=
              hDom i AXeq hAXpast
            have hind : μ.real (AYeq ∩ LY) = μ.real AYeq * μ.real LY :=
              independent_past_inter_current_real μ Y hYMeas hYIndep i AYeq hAYpast
            have hq0 : 0 ≤ μ.real LY := measureReal_nonneg
            have hq1 : μ.real LY ≤ 1 := measureReal_le_one
            have hhi : μ.real AYhi ≤ μ.real AXhi := ihm (j + 1)
            have hlo :
                μ.real {ω | j ≤ boolPrefixCount Y m ω} ≤
                  μ.real {ω | j ≤ boolPrefixCount X m ω} := ihm j
            calc
              μ.real {ω | j + 1 ≤ boolPrefixCount Y (m + 1) ω}
                  = μ.real AYhi + μ.real (AYeq ∩ LY) := hYsucc
              _ = μ.real AYhi + μ.real AYeq * μ.real LY := by rw [hind]
              _ = (1 - μ.real LY) * μ.real AYhi +
                    μ.real LY * μ.real {ω | j ≤ boolPrefixCount Y m ω} := by
                    rw [hYsplit]
                    ring
              _ ≤ (1 - μ.real LY) * μ.real AXhi +
                    μ.real LY * μ.real {ω | j ≤ boolPrefixCount X m ω} := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hq1))
                      (mul_le_mul_of_nonneg_left hlo hq0)
              _ = μ.real AXhi + μ.real AXeq * μ.real LY := by
                    rw [hXsplit]
                    ring
              _ ≤ μ.real AXhi + μ.real (AXeq ∩ LX) := add_le_add_right hcond _
              _ = μ.real {ω | j + 1 ≤ boolPrefixCount X (m + 1) ω} := hXsucc.symm
  simpa only [boolPrefixCount_all] using hprefix n le_rfl k

/-- Cross-space integrated conditional lower bound.  This is the form used
when the adapted process and its independent Bernoulli comparison live on
different probability spaces. -/
def BernoulliConditionallyGECross
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {n : ℕ} (μ : Measure Ω) (ν : Measure Ω')
    (X : Fin n → Ω → Bool) (Y : Fin n → Ω' → Bool) : Prop :=
  ∀ (i : Fin n) (A : Set Ω),
    MeasurableSet[bernoulliPastSpace X i] A →
      μ.real A * ν.real {ω | Y i ω = true} ≤
        μ.real (A ∩ {ω | X i ω = true})

/-- Conditional lower Bernoulli bounds imply lower-tail domination even when
the independent comparison variables are defined on another space. -/
theorem bernoulli_sum_domination_lower_cross
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (X : Fin n → Ω → Bool)
    (Y : Fin n → Ω' → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y ν)
    (hDom : BernoulliConditionallyGECross μ ν X Y)
    (k : ℕ) :
    ν {ω | k ≤ ∑ i : Fin n,
        if Y i ω then (1 : ℕ) else 0} ≤
      μ {ω | k ≤ ∑ i : Fin n,
        if X i ω then (1 : ℕ) else 0} := by
  suffices hreal :
      ν.real {ω | k ≤ ∑ i : Fin n,
          if Y i ω then (1 : ℕ) else 0} ≤
        μ.real {ω | k ≤ ∑ i : Fin n,
          if X i ω then (1 : ℕ) else 0} by
    exact (ENNReal.toReal_le_toReal
      (measure_ne_top ν _) (measure_ne_top μ _)).mp hreal
  have hprefix : ∀ m : ℕ, m ≤ n → ∀ r : ℕ,
      ν.real {ω | r ≤ boolPrefixCount Y m ω} ≤
        μ.real {ω | r ≤ boolPrefixCount X m ω} := by
    intro m hm
    induction m with
    | zero =>
        intro r
        cases r <;> simp [boolPrefixCount]
    | succ m ih =>
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        have ihm := ih (Nat.le_of_lt hm_lt)
        intro r
        cases r with
        | zero =>
            simp
        | succ j =>
            let i : Fin n := ⟨m, hm_lt⟩
            let AXhi : Set Ω :=
              {ω | j + 1 ≤ boolPrefixCount X m ω}
            let AXeq : Set Ω :=
              {ω | boolPrefixCount X m ω = j}
            let AYhi : Set Ω' :=
              {ω | j + 1 ≤ boolPrefixCount Y m ω}
            let AYeq : Set Ω' :=
              {ω | boolPrefixCount Y m ω = j}
            let LX : Set Ω := {ω | X i ω = true}
            let LY : Set Ω' := {ω | Y i ω = true}
            have hXm := measurable_boolPrefixCount X hXMeas m
            have hYm := measurable_boolPrefixCount Y hYMeas m
            have hAXhi : MeasurableSet AXhi :=
              hXm measurableSet_Ici
            have hAXeq : MeasurableSet AXeq :=
              hXm (measurableSet_singleton j)
            have hAYhi : MeasurableSet AYhi :=
              hYm measurableSet_Ici
            have hAYeq : MeasurableSet AYeq :=
              hYm (measurableSet_singleton j)
            have hAXpast :
                MeasurableSet[bernoulliPastSpace X i] AXeq :=
              (measurable_boolPrefixCount_past X i)
                (measurableSet_singleton j)
            have hAYpast :
                MeasurableSet[bernoulliPastSpace Y i] AYeq :=
              (measurable_boolPrefixCount_past Y i)
                (measurableSet_singleton j)
            have hLX : MeasurableSet LX :=
              hXMeas i (measurableSet_singleton true)
            have hLY : MeasurableSet LY :=
              hYMeas i (measurableSet_singleton true)
            have hXsucc :
                μ.real {ω | j + 1 ≤
                    boolPrefixCount X (m + 1) ω} =
                  μ.real AXhi + μ.real (AXeq ∩ LX) := by
              rw [prefix_tail_succ_union X hm_lt]
              exact measureReal_union
                (prefix_tail_succ_disjoint X hm_lt)
                (hAXeq.inter hLX)
            have hYsucc :
                ν.real {ω | j + 1 ≤
                    boolPrefixCount Y (m + 1) ω} =
                  ν.real AYhi + ν.real (AYeq ∩ LY) := by
              rw [prefix_tail_succ_union Y hm_lt]
              exact measureReal_union
                (prefix_tail_succ_disjoint Y hm_lt)
                (hAYeq.inter hLY)
            have hXsplit :
                μ.real {ω | j ≤ boolPrefixCount X m ω} =
                  μ.real AXhi + μ.real AXeq := by
              rw [prefix_tail_eq_union X]
              exact measureReal_union
                (prefix_tail_eq_disjoint X) hAXeq
            have hYsplit :
                ν.real {ω | j ≤ boolPrefixCount Y m ω} =
                  ν.real AYhi + ν.real AYeq := by
              rw [prefix_tail_eq_union Y]
              exact measureReal_union
                (prefix_tail_eq_disjoint Y) hAYeq
            have hcond :
                μ.real AXeq * ν.real LY ≤
                  μ.real (AXeq ∩ LX) :=
              hDom i AXeq hAXpast
            have hind :
                ν.real (AYeq ∩ LY) =
                  ν.real AYeq * ν.real LY :=
              independent_past_inter_current_real
                ν Y hYMeas hYIndep i AYeq hAYpast
            have hq0 : 0 ≤ ν.real LY := measureReal_nonneg
            have hq1 : ν.real LY ≤ 1 := measureReal_le_one
            have hhi : ν.real AYhi ≤ μ.real AXhi :=
              ihm (j + 1)
            have hlo :
                ν.real {ω | j ≤ boolPrefixCount Y m ω} ≤
                  μ.real {ω | j ≤ boolPrefixCount X m ω} :=
              ihm j
            calc
              ν.real {ω | j + 1 ≤
                  boolPrefixCount Y (m + 1) ω}
                  = ν.real AYhi +
                      ν.real (AYeq ∩ LY) := hYsucc
              _ = ν.real AYhi +
                    ν.real AYeq * ν.real LY := by rw [hind]
              _ = (1 - ν.real LY) * ν.real AYhi +
                    ν.real LY *
                      ν.real {ω | j ≤
                        boolPrefixCount Y m ω} := by
                    rw [hYsplit]
                    ring
              _ ≤ (1 - ν.real LY) * μ.real AXhi +
                    ν.real LY *
                      μ.real {ω | j ≤
                        boolPrefixCount X m ω} := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left hhi
                        (sub_nonneg.mpr hq1))
                      (mul_le_mul_of_nonneg_left hlo hq0)
              _ = μ.real AXhi +
                    μ.real AXeq * ν.real LY := by
                    rw [hXsplit]
                    ring
              _ ≤ μ.real AXhi +
                    μ.real (AXeq ∩ LX) :=
                  add_le_add_right hcond _
              _ = μ.real {ω | j + 1 ≤
                    boolPrefixCount X (m + 1) ω} :=
                  hXsucc.symm
  simpa only [boolPrefixCount_all] using
    hprefix n le_rfl k

/-- First half of paper `lemma:couple-with-independent`: conditional upper
Bernoulli bounds imply stochastic domination by the independent sum. -/
theorem lemma_couple_with_independent_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat)
    (X Y : Fin n → Ω → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y μ)
    (hDom : BernoulliConditionallyLE μ X Y) :
    StochDom μ
      (fun ω => ∑ i : Fin n, if X i ω then (1 : Real) else 0)
      (fun ω => ∑ i : Fin n, if Y i ω then (1 : Real) else 0) := by
  intro t
  -- coupling_nat_aux handles ℕ-cast thresholds.
  -- Since each ∑ (if X i ω then 1 else 0) is ℕ-valued, we reduce to ⌈t⌉.
  -- Sums take ℕ values so the sets for threshold t and ⌈t⌉₊ coincide.
  suffices ∀ k : ℕ,
      μ {ω | (k : ℝ) ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} ≤
      μ {ω | (k : ℝ) ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} by
    have hXceil :
        {ω | t ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} =
          {ω | ((Nat.ceil t : ℕ) : ℝ) ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} := by
      ext ω
      constructor
      · intro hω
        let m : ℕ := ∑ i : Fin n, if X i ω then 1 else 0
        have hceil_nat : Nat.ceil t ≤ m := by
          apply (Nat.ceil_le).2
          simpa [m] using hω
        exact (show (((Nat.ceil t : ℕ) : ℝ) ≤ (m : ℝ)) by exact_mod_cast hceil_nat).trans
          (by simp [m])
      · intro hω
        exact (Nat.le_ceil t).trans hω
    have hYceil :
        {ω | t ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} =
          {ω | ((Nat.ceil t : ℕ) : ℝ) ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} := by
      ext ω
      constructor
      · intro hω
        let m : ℕ := ∑ i : Fin n, if Y i ω then 1 else 0
        have hceil_nat : Nat.ceil t ≤ m := by
          apply (Nat.ceil_le).2
          simpa [m] using hω
        exact (show (((Nat.ceil t : ℕ) : ℝ) ≤ (m : ℝ)) by exact_mod_cast hceil_nat).trans
          (by simp [m])
      · intro hω
        exact (Nat.le_ceil t).trans hω
    simpa [hXceil, hYceil] using this (Nat.ceil t)
  intro k
  simpa only [tail_event_nat_threshold] using
    coupling_nat_aux_le μ n X Y hXMeas hYMeas hYIndep hDom k

/-- Second half of paper `lemma:couple-with-independent`: conditional lower
Bernoulli bounds imply that the independent sum is stochastically dominated. -/
theorem lemma_couple_with_independent_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat)
    (X Y : Fin n → Ω → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y μ)
    (hDom : BernoulliConditionallyGE μ X Y) :
    StochDom μ
      (fun ω => ∑ i : Fin n, if Y i ω then (1 : Real) else 0)
      (fun ω => ∑ i : Fin n, if X i ω then (1 : Real) else 0) := by
  intro t
  suffices ∀ k : ℕ,
      μ {ω | (k : ℝ) ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} ≤
      μ {ω | (k : ℝ) ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} by
    have hYceil :
        {ω | t ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} =
          {ω | ((Nat.ceil t : ℕ) : ℝ) ≤ ∑ i : Fin n, if Y i ω then (1 : ℝ) else 0} := by
      ext ω
      constructor
      · intro hω
        let m : ℕ := ∑ i : Fin n, if Y i ω then 1 else 0
        have hceil_nat : Nat.ceil t ≤ m := by
          apply (Nat.ceil_le).2
          simpa [m] using hω
        exact (show (((Nat.ceil t : ℕ) : ℝ) ≤ (m : ℝ)) by exact_mod_cast hceil_nat).trans
          (by simp [m])
      · intro hω
        exact (Nat.le_ceil t).trans hω
    have hXceil :
        {ω | t ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} =
          {ω | ((Nat.ceil t : ℕ) : ℝ) ≤ ∑ i : Fin n, if X i ω then (1 : ℝ) else 0} := by
      ext ω
      constructor
      · intro hω
        let m : ℕ := ∑ i : Fin n, if X i ω then 1 else 0
        have hceil_nat : Nat.ceil t ≤ m := by
          apply (Nat.ceil_le).2
          simpa [m] using hω
        exact (show (((Nat.ceil t : ℕ) : ℝ) ≤ (m : ℝ)) by exact_mod_cast hceil_nat).trans
          (by simp [m])
      · intro hω
        exact (Nat.le_ceil t).trans hω
    simpa [hYceil, hXceil] using this (Nat.ceil t)
  intro k
  simpa only [tail_event_nat_threshold] using
    coupling_nat_aux_ge μ n X Y hXMeas hYMeas hYIndep hDom k

/-- Paper `lemma:couple-with-independent`, both directions and with no custom
axioms.  Each implication directly matches one numbered part of the paper. -/
theorem lemma_couple_with_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat)
    (X Y : Fin n → Ω → Bool)
    (hXMeas : ∀ i, Measurable (X i))
    (hYMeas : ∀ i, Measurable (Y i))
    (hYIndep : iIndepFun Y μ) :
    (BernoulliConditionallyLE μ X Y →
      StochDom μ
        (fun ω => ∑ i : Fin n, if X i ω then (1 : Real) else 0)
        (fun ω => ∑ i : Fin n, if Y i ω then (1 : Real) else 0)) ∧
    (BernoulliConditionallyGE μ X Y →
      StochDom μ
        (fun ω => ∑ i : Fin n, if Y i ω then (1 : Real) else 0)
        (fun ω => ∑ i : Fin n, if X i ω then (1 : Real) else 0)) := by
  exact ⟨lemma_couple_with_independent_upper μ n X Y hXMeas hYMeas hYIndep,
    lemma_couple_with_independent_lower μ n X Y hXMeas hYMeas hYIndep⟩

end LVConsensus
