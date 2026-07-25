import LVConsensus.NsdInteractionConcentration

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal

namespace LVConsensus

lemma three_poly_inv_succ_le
    (n k : ℕ) (hn : 2 ≤ n) :
    ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
          ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ ≤
      ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
  let x : ℝ≥0∞ := n + 1
  have hx0 : x ≠ 0 := by simp [x]
  have hxtop : x ≠ ⊤ := by simp [x]
  have hthree : (3 : ℝ≥0∞) ≤ x := by
    dsimp [x]
    exact_mod_cast (show 3 ≤ n + 1 by omega)
  have hxeq : x = (↑(n + 1) : ℝ≥0∞) := by
    simp [x]
  rw [← hxeq]
  calc
    (x ^ (k + 1))⁻¹ + (x ^ (k + 1))⁻¹ +
          (x ^ (k + 1))⁻¹ =
        3 * (x ^ (k + 1))⁻¹ := by ring
    _ ≤ x * (x ^ (k + 1))⁻¹ :=
      mul_le_mul_right' hthree _
    _ = x * x⁻¹ ^ (k + 1) := by
      rw [ENNReal.inv_pow]
    _ = x * (x⁻¹ ^ k * x⁻¹) := by
      rw [pow_succ]
    _ = x⁻¹ ^ k * (x * x⁻¹) := by
      ac_rfl
    _ = x⁻¹ ^ k := by
      rw [ENNReal.mul_inv_cancel hx0 hxtop, mul_one]
    _ = (x ^ k)⁻¹ := by
      rw [ENNReal.inv_pow]

lemma nsd_interaction_tail_poly
    (CT k n : ℕ) (hCT : 0 < CT)
    (hnCT : CT ≤ n) (hn : 2 ≤ n) :
    let CY : ℝ :=
      Real.sqrt (2 * (CT : ℝ) * (k + 3))
    let t : ℝ :=
      CY *
        Real.sqrt ((n : ℝ) * logScale n)
    ((CT * n : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(t ^ 2) / (2 * (CT * n : ℕ)))) ≤
      ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  dsimp only
  have hnpos : 0 < n := by omega
  have hlogpos : 0 < logScale n :=
    Real.log_pos (by
      exact_mod_cast (show 1 < n + 1 by omega))
  have hradicand :
      0 ≤ 2 * (CT : ℝ) * ((k : ℝ) + 3) := by
    positivity
  have hCYsq :
      (Real.sqrt
        (2 * (CT : ℝ) * ((k : ℝ) + 3))) ^ 2 =
          2 * (CT : ℝ) * ((k : ℝ) + 3) := by
    exact Real.sq_sqrt hradicand
  have hNsqrt :
      (Real.sqrt ((n : ℝ) * logScale n)) ^ 2 =
        (n : ℝ) * logScale n := by
    exact Real.sq_sqrt
      (mul_nonneg (Nat.cast_nonneg n) hlogpos.le)
  have hExp :
      Real.exp
          (-((Real.sqrt
              (2 * (CT : ℝ) * ((k : ℝ) + 3)) *
            Real.sqrt ((n : ℝ) * logScale n)) ^ 2) /
            (2 * ((CT * n : ℕ) : ℝ))) =
        1 / (((n : ℝ) + 1) ^ (k + 3)) := by
    rw [mul_pow, hCYsq, hNsqrt]
    have hCTreal : (0 : ℝ) < CT := by exact_mod_cast hCT
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have harg : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [show
        -(2 * (CT : ℝ) * ((k : ℝ) + 3) *
              ((n : ℝ) * logScale n)) /
            (2 * ((CT * n : ℕ) : ℝ)) =
          -((k : ℝ) + 3) *
            Real.log ((n : ℝ) + 1) by
      unfold logScale
      push_cast
      field_simp
      ]
    rw [show
        -((k : ℝ) + 3) *
            Real.log ((n : ℝ) + 1) =
          -((((k + 3 : ℕ) : ℝ) *
            Real.log ((n : ℝ) + 1))) by
              push_cast
              ring]
    rw [Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log harg]
    ring
  rw [hExp]
  rw [ENNReal.ofReal_div_of_pos
    (by positivity :
      (0 : ℝ) < ((n : ℝ) + 1) ^ (k + 3))]
  rw [ENNReal.ofReal_one, one_div]
  rw [ENNReal.ofReal_pow (by positivity :
    (0 : ℝ) ≤ (n : ℝ) + 1)]
  have hbase :
      ENNReal.ofReal ((n : ℝ) + 1) =
        (n + 1 : ℕ) := by
    rw [show (n : ℝ) + 1 =
        ((n + 1 : ℕ) : ℝ) by norm_num,
      ENNReal.ofReal_natCast]
  rw [hbase]
  let x : ℝ≥0∞ := n + 1
  have hxeq :
      x = (↑(n + 1) : ℝ≥0∞) := by
    simp [x]
  have hx0 : x ≠ 0 := by simp [x]
  have hxtop : x ≠ ⊤ := by simp [x]
  have hCTn :
      ((CT * n : ℕ) : ℝ≥0∞) ≤ x ^ 2 := by
    dsimp only [x]
    exact_mod_cast
      (calc
        CT * n ≤ n * n :=
          Nat.mul_le_mul_right n hnCT
        _ ≤ (n + 1) ^ 2 := by nlinarith)
  rw [← hxeq]
  change
    ((CT * n : ℕ) : ℝ≥0∞) *
        (x ^ (k + 3))⁻¹ ≤
      (x ^ (k + 1))⁻¹
  calc
    ((CT * n : ℕ) : ℝ≥0∞) *
          (x ^ (k + 3))⁻¹ ≤
        x ^ 2 * (x ^ (k + 3))⁻¹ :=
      mul_le_mul_right' hCTn _
    _ = x⁻¹ ^ (k + 1) := by
      rw [ENNReal.inv_pow]
      rw [show k + 3 = (k + 1) + 2 by omega]
      calc
        x ^ 2 * x⁻¹ ^ (k + 1 + 2) =
            x⁻¹ ^ (k + 1) *
              (x ^ 2 * (x ^ 2)⁻¹) := by
          rw [pow_add (x⁻¹) (k + 1) 2,
            show x⁻¹ ^ 2 = (x ^ 2)⁻¹ from
              ENNReal.inv_pow.symm]
          ac_rfl
        _ = x⁻¹ ^ (k + 1) := by
          rw [ENNReal.mul_inv_cancel
            (pow_ne_zero _ hx0)
            (ENNReal.pow_ne_top hxtop),
            mul_one]
    _ = (x ^ (k + 1))⁻¹ := by
      exact ENNReal.inv_pow.symm

/-- A concrete comparison between the logarithmic scales used for the
birth-count and interaction-score bounds. -/
lemma logSqScale_le_sqrtNLogN_nsd
    (n : ℕ) (hn : 2 ≤ n) :
    (1 / 8 : ℝ) * logSqScale n ≤
      Real.sqrt ((n : ℝ) * logScale n) := by
  simp only [logSqScale, logScale]
  set L := Real.log ((n : ℝ) + 1)
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    linarith
  have hL_pos : 0 < L :=
    Real.log_pos (by
      exact_mod_cast
        (show 1 < n + 1 by omega))
  have lhs_nn : 0 ≤ (1 / 8 : ℝ) * L ^ 2 := by
    positivity
  have rhs_nn : 0 ≤ (n : ℝ) * L := by
    positivity
  rw [Real.le_sqrt lhs_nn rhs_nn]
  have step1 :
      L ≤ ((n : ℝ) + 1) ^ ((1 : ℝ) / 3) /
        ((1 : ℝ) / 3) :=
    Real.log_le_rpow_div hn1_pos.le
      (by positivity : (0 : ℝ) < 1 / 3)
  have hL_le :
      L ≤ 3 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 3) := by
    convert step1 using 1 <;> ring
  have hL3 :
      L ^ 3 ≤
        (3 * ((n : ℝ) + 1) ^
          ((1 : ℝ) / 3)) ^ 3 :=
    pow_le_pow_left₀ hL_pos.le hL_le 3
  have hsimp :
      (3 * ((n : ℝ) + 1) ^
        ((1 : ℝ) / 3)) ^ 3 =
          27 * ((n : ℝ) + 1) := by
    rw [mul_pow]
    norm_num
    rw [← Real.rpow_natCast _ 3,
      ← Real.rpow_mul hn1_pos.le]
    norm_num
  have hn_ge2 : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hL3_bound : L ^ 3 ≤ 64 * (n : ℝ) := by
    nlinarith [hL3]
  nlinarith [hL_pos, hL3_bound]

/-- The NSD upper bound obtained from the unconditional chain domination,
the logarithmic birth-count tail, and the labeled-reaction concentration
bound. -/
lemma chain_domination_nsd_upper_bound_unconditional
    (params : LVParams) (k : ℕ)
    (hBias : params.alpha1 ≤ params.alpha0)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : NiceChain)
    (hDom : IsDominatingChain N.toBirthDeathChain
      (lvEventProfile .nonSelfDestructive params))
    [IsMarkovKernel
      (lvKernel .nonSelfDestructive params)] :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ a b : ℕ,
      n₀ ≤ a + b → 0 < b → b < a →
      C *
          Real.sqrt
            (((a + b : ℕ) : ℝ) *
              logScale (a + b)) ≤
        (a : ℝ) - (b : ℝ) →
      majorityConsensusProb .nonSelfDestructive
          params (a, b) ≥
        ENNReal.ofReal
          (1 -
            1 /
              (((a + b : ℕ) + 1 : ℝ) ^ k)) := by
  classical
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), LVReaction.idle)⟩
  obtain ⟨CT, nT, hCT, hExt⟩ :=
    nice_whp_extinction_linear_uniform_unconditional
      N (k + 1)
  obtain ⟨CB, nB, hCB, hBirth⟩ :=
    nice_whp_births_logsq_uniform_unconditional
      N (k + 1)
  let CY : ℝ :=
    Real.sqrt
      (2 * (CT : ℝ) * ((k : ℝ) + 3))
  refine
    ⟨16 * CB + CY, by
      have : 0 ≤ CY := Real.sqrt_nonneg _
      positivity,
      max 2 (max CT (max nT nB)), ?_⟩
  intro a b hn hb hab hgap
  let n := a + b
  let m := Nat.min a b
  let R : ℕ := CT * n
  let L : ℕ := CB * logSqScaleNat n
  let t : ℝ :=
    CY * Real.sqrt ((n : ℝ) * logScale n)
  let P :=
    lvLabeledPathMeasure
      .nonSelfDestructive params (a, b)
  let MC : Set (ℕ → LabeledPopState) :=
    {ζ |
      majorityConsensusEvent
        (a, b) (forgetLVLabels ζ)}
  let ET : Set (ℕ → LabeledPopState) :=
    {ζ |
      consensusTime (forgetLVLabels ζ) ≥
        (R : ℕ)}
  let EB : Set (ℕ → LabeledPopState) :=
    {ζ |
      L ≤ labeledBadCountBeforeConsensus ζ}
  let EY : Set (ℕ → LabeledPopState) :=
    {ζ |
      ∃ i ∈ Finset.range R,
        t ≤
          ((nsdInteractionSumUpTo ζ (i + 1) : ℤ) :
            ℝ)}
  haveI : IsProbabilityMeasure P := by
    dsimp only [P]
    unfold lvLabeledPathMeasure homogeneousPathMeasure
    infer_instance
  have hn2 : 2 ≤ n := by
    dsimp only [n]
    exact (le_max_left _ _).trans hn
  have hnCT : CT ≤ n := by
    dsimp only [n]
    exact
      (le_max_of_le_right
        (le_max_left _ _)).trans hn
  have hnT : nT ≤ n := by
    dsimp only [n]
    exact
      (le_max_of_le_right
        (le_max_of_le_right
          (le_max_left _ _))).trans hn
  have hnB : nB ≤ n := by
    dsimp only [n]
    exact
      (le_max_of_le_right
        (le_max_of_le_right
          (le_max_right _ _))).trans hn
  have hnpos : 0 < n := by
    omega
  have hRpos : 0 < R := by
    dsimp only [R]
    exact Nat.mul_pos hCT hnpos
  have hm : m ≤ n := by
    dsimp only [m, n]
    exact
      (Nat.min_le_left a b).trans
        (Nat.le_add_right a b)
  obtain ⟨hConsTail, hBadTail⟩ :=
    chain_domination_unconditional
      .nonSelfDestructive params
      hGamma0 hGamma1 (a, b)
      N.toBirthDeathChain m le_rfl hDom
      (niceChain_extinction_almost_sure N m)
  have hET :
      P ET ≤
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ := by
    have hG :
        MeasurableSet
          {ω : ℕ → PopState |
            (R : WithTop ℕ) ≤ consensusTime ω} :=
      measurableSet_consensusTailEvent R
    calc
      P ET =
          lvPathMeasure .nonSelfDestructive params (a, b)
            {ω |
              (R : WithTop ℕ) ≤
                consensusTime ω} := by
        rw [← lvLabeledPathMeasure_map_forget
          .nonSelfDestructive params (a, b)]
        rw [Measure.map_apply
          measurable_forgetLVLabels hG]
        rfl
      _ = consensusTail .nonSelfDestructive
          params (a, b) R := rfl
      _ ≤ extinctionTail N.toBirthDeathChain
          m R := hConsTail R
      _ ≤
          ((↑(n + 1) : ℝ≥0∞) ^
            (k + 1))⁻¹ := by
        simpa only [R, Nat.cast_add, Nat.cast_one] using
          hExt n hnT m hm
  have hEB :
      P EB ≤
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ := by
    calc
      P EB =
          labeledBadTail .nonSelfDestructive
            params (a, b) L := rfl
      _ ≤ birthTail N.toBirthDeathChain m L :=
        hBadTail L
      _ ≤
          ((↑(n + 1) : ℝ≥0∞) ^
            (k + 1))⁻¹ := by
        simpa only [L, Nat.cast_add, Nat.cast_one] using
          hBirth n hnB m hm
  have ht : 0 ≤ t := by
    dsimp only [t, CY]
    positivity
  have hEY :
      P EY ≤
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ := by
    calc
      P EY ≤
          (R : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp
                (-(t ^ 2) / (2 * R))) := by
        simpa only [P, EY] using
          lvLabeledPathMeasure_nsdInteractionMax_tail
            params hBias (a, b) R hRpos t ht
      _ ≤
          ((↑(n + 1) : ℝ≥0∞) ^
            (k + 1))⁻¹ := by
        simpa only [R, t, CY] using
          nsd_interaction_tail_poly
            CT k n hCT hnCT hn2
  have hlog1 : 1 ≤ logSqScale n := by
    have hlog :=
      (one_lt_logScale_chain n hn2).le
    unfold logSqScale
    nlinarith
  have hceil :
      (logSqScaleNat n : ℝ) ≤
        2 * logSqScale n := by
    calc
      (logSqScaleNat n : ℝ) ≤
          logSqScale n + 1 :=
        logSqScaleNat_cast_le_add_one_chain n
      _ ≤ 2 * logSqScale n := by
        linarith
  have hLsqrt :
      (L : ℝ) ≤
        (16 * CB : ℝ) *
          Real.sqrt
            ((n : ℝ) * logScale n) := by
    have hscale :=
      logSqScale_le_sqrtNLogN_nsd n hn2
    calc
      (L : ℝ) =
          (CB : ℝ) *
            (logSqScaleNat n : ℝ) := by
        simp only [L]
        norm_num
      _ ≤ (CB : ℝ) *
          (2 * logSqScale n) :=
        mul_le_mul_of_nonneg_left hceil
          (Nat.cast_nonneg CB)
      _ ≤
          (16 * CB : ℝ) *
            Real.sqrt
              ((n : ℝ) * logScale n) := by
        have hmul :=
          mul_le_mul_of_nonneg_left hscale
            (show (0 : ℝ) ≤ 16 * CB by positivity)
        nlinarith
  have hgapLT :
      (L : ℝ) + t ≤
        (a : ℝ) - (b : ℝ) := by
    calc
      (L : ℝ) + t ≤
          (16 * CB + CY) *
            Real.sqrt
              ((n : ℝ) * logScale n) := by
        dsimp only [t]
        nlinarith [hLsqrt]
      _ ≤ (a : ℝ) - (b : ℝ) := by
        simpa only [n] using hgap
  have hInitialAE :
      ∀ᵐ ζ ∂P, (ζ 0).1 = (a, b) := by
    rw [ae_iff]
    have hmarg :
        P.map
            (fun ζ : ℕ → LabeledPopState => ζ 0) =
          Measure.dirac ((a, b), .idle) := by
      dsimp only [P]
      simp only [lvLabeledPathMeasure]
      exact homogeneousPathMeasure_marginal_zero
        (lvLabeledKernel .nonSelfDestructive params)
        (Measure.dirac ((a, b), .idle))
    calc
      P {ζ | ¬(ζ 0).1 = (a, b)} =
          P ((fun ζ : ℕ → LabeledPopState => ζ 0) ⁻¹'
            {z | ¬z.1 = (a, b)}) := rfl
      _ =
          P.map
            (fun ζ : ℕ → LabeledPopState => ζ 0)
            {z | ¬z.1 = (a, b)} := by
        symm
        exact Measure.map_apply
          (measurable_pi_apply 0)
          (DiscreteMeasurableSpace.forall_measurableSet _)
      _ =
          Measure.dirac ((a, b), LVReaction.idle)
            {z | ¬z.1 = (a, b)} := by
        rw [hmarg]
      _ = 0 := by simp
  have hFailureAE :
      ∀ᵐ ζ ∂P,
        ζ ∈ MCᶜ → ζ ∈ ET ∪ EB ∪ EY := by
    filter_upwards [
      lvLabeledPathMeasure_valid_nonSelfDestructive_ae
        params hGamma0 hGamma1 (a, b),
      hInitialAE] with ζ hvalid hInitial
    intro hnotMC
    by_cases htime :
        consensusTime (forgetLVLabels ζ) ≥
          (R : ℕ)
    · exact Or.inl (Or.inl htime)
    · have hfinite :
          consensusTime (forgetLVLabels ζ) < ⊤ :=
        (lt_of_not_ge htime).trans
          (WithTop.coe_lt_top _)
      obtain ⟨τ, hτ⟩ :=
        WithTop.ne_top_iff_exists.mp
          (WithTop.lt_top_iff_ne_top.mp hfinite)
      have hτR : τ < R := by
        have hlt :
            consensusTime (forgetLVLabels ζ) <
              (R : WithTop ℕ) :=
          lt_of_not_ge htime
        rw [← hτ] at hlt
        exact WithTop.coe_lt_coe.mp hlt
      by_cases hbad :
          L ≤ labeledBadCountBeforeConsensus ζ
      · exact Or.inl (Or.inr hbad)
      · exact Or.inr
          (nsd_failure_implies_interaction_max
            a b ζ hab hInitial hvalid
            τ R L hτ.symm hτR
            (Nat.lt_of_not_ge hbad)
            t hgapLT hnotMC)
  have hFail :
      P MCᶜ ≤
        ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
    calc
      P MCᶜ ≤ P (ET ∪ EB ∪ EY) :=
        measure_mono_ae hFailureAE
      _ ≤ P (ET ∪ EB) + P EY :=
        measure_union_le (ET ∪ EB) EY
      _ ≤ P ET + P EB + P EY :=
        add_le_add
          (measure_union_le ET EB) (le_refl _)
      _ ≤
          ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
            ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
          ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ :=
        add_le_add (add_le_add hET hEB) hEY
      _ ≤ ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ :=
        three_poly_inv_succ_le n k hn2
  have hMCmeas : MeasurableSet MC := by
    exact
      (measurableSet_majorityConsensusEvent
        (a, b)).preimage measurable_forgetLVLabels
  have hMCcomp :
      P MC = 1 - P MCᶜ := by
    have hcompl :=
      measure_compl hMCmeas.compl
        (measure_ne_top P MCᶜ)
    simpa only [compl_compl, measure_univ] using
      hcompl
  have htarget :
      ENNReal.ofReal
          (1 -
            1 / (((n : ℕ) + 1 : ℝ) ^ k)) =
        1 -
          ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
    rw [ENNReal.ofReal_sub 1 (by positivity),
      ENNReal.ofReal_one]
    rw [ennreal_poly_inv_eq_ofReal_chain n k]
  have hMClaw :
      majorityConsensusProb
          .nonSelfDestructive params (a, b) =
        P MC := by
    have hG :
        MeasurableSet
          {ω : ℕ → PopState |
            majorityConsensusEvent (a, b) ω} :=
      measurableSet_majorityConsensusEvent (a, b)
    calc
      majorityConsensusProb
          .nonSelfDestructive params (a, b) =
          lvPathMeasure .nonSelfDestructive params
            (a, b)
            {ω |
              majorityConsensusEvent
                (a, b) ω} := rfl
      _ =
          (P.map forgetLVLabels)
            {ω |
              majorityConsensusEvent
                (a, b) ω} := by
        rw [lvLabeledPathMeasure_map_forget
          .nonSelfDestructive params (a, b)]
      _ = P MC := by
        rw [Measure.map_apply
          measurable_forgetLVLabels hG]
        rfl
  rw [hMClaw, htarget, hMCcomp]
  exact tsub_le_tsub_left hFail 1

end LVConsensus
