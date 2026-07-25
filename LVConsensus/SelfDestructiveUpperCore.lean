import LVConsensus.DominationCategoricalCoupling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal

namespace LVConsensus

lemma chain_domination_upper_bound_unconditional
    (params : LVParams) (k : Nat)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : NiceChain)
    (hDom : IsDominatingChain N.toBirthDeathChain
      (lvEventProfile .selfDestructive params))
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel .selfDestructive params)] :
    ∃ C : Real, 0 < C ∧ ∃ n₀ : Nat, ∀ a b : Nat,
      n₀ ≤ a + b → b < a →
      C * logSqScale (a + b) ≤ (a : Real) - (b : Real) →
        majorityConsensusProb .selfDestructive params (a, b) ≥
          ENNReal.ofReal
            (1 - 1 / (((a + b : Nat) + 1 : Real) ^ k)) := by
  classical
  letI : Nonempty LabeledPopState :=
    ⟨((0, 0), LVReaction.idle)⟩
  obtain ⟨CT, nT, hCT, hExt⟩ :=
    nice_whp_extinction_linear_uniform_unconditional N (k + 1)
  obtain ⟨CB, nB, hCB, hBirth⟩ :=
    nice_whp_births_logsq_uniform_unconditional N (k + 1)
  refine ⟨2 * CB, by positivity, max 2 (max nT nB), ?_⟩
  intro a b hn hab hgap
  let n := a + b
  let m := Nat.min a b
  let R := lvLabeledPathMeasure
    .selfDestructive params (a, b)
  let MC : Set (Nat → LabeledPopState) :=
    {ζ | majorityConsensusEvent (a, b) (forgetLVLabels ζ)}
  let ET : Set (Nat → LabeledPopState) :=
    {ζ | consensusTime (forgetLVLabels ζ) ≥ (CT * n : Nat)}
  let EB : Set (Nat → LabeledPopState) :=
    {ζ | CB * logSqScaleNat n ≤
      labeledBadCountBeforeConsensus ζ}
  haveI : IsProbabilityMeasure R := by
    dsimp [R]
    unfold lvLabeledPathMeasure homogeneousPathMeasure
    infer_instance
  have hn2 : 2 ≤ n := by
    dsimp [n]
    exact le_trans (le_max_left _ _) hn
  have hnT : nT ≤ n := by
    dsimp [n]
    exact le_trans
      (le_max_of_le_right (le_max_left _ _)) hn
  have hnB : nB ≤ n := by
    dsimp [n]
    exact le_trans
      (le_max_of_le_right (le_max_right _ _)) hn
  have hm : m ≤ n := by
    dsimp [m, n]
    exact (Nat.min_le_left a b).trans
      (Nat.le_add_right a b)
  obtain ⟨hConsTail, hBadTail⟩ :=
    chain_domination_unconditional .selfDestructive params
      hGamma0 hGamma1 (a, b) N.toBirthDeathChain m
      le_rfl hDom (niceChain_extinction_almost_sure N m)
  have hET :
      R ET ≤ ((↑(n + 1) : ENNReal) ^ (k + 1))⁻¹ := by
    have hG :
        MeasurableSet
          {ω : Nat → PopState |
            (CT * n : WithTop Nat) ≤ consensusTime ω} :=
      measurableSet_consensusTailEvent (CT * n)
    calc
      R ET =
          lvPathMeasure .selfDestructive params (a, b)
            {ω | (CT * n : WithTop Nat) ≤
              consensusTime ω} := by
        rw [← lvLabeledPathMeasure_map_forget
          .selfDestructive params (a, b)]
        rw [Measure.map_apply measurable_forgetLVLabels hG]
        rfl
      _ = consensusTail .selfDestructive params
          (a, b) (CT * n) := rfl
      _ ≤ extinctionTail N.toBirthDeathChain m
          (CT * n) := hConsTail (CT * n)
      _ ≤ ((↑(n + 1) : ENNReal) ^ (k + 1))⁻¹ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hExt n hnT m hm
  have hEB :
      R EB ≤ ((↑(n + 1) : ENNReal) ^ (k + 1))⁻¹ := by
    calc
      R EB =
          labeledBadTail .selfDestructive params (a, b)
            (CB * logSqScaleNat n) := rfl
      _ ≤ birthTail N.toBirthDeathChain m
          (CB * logSqScaleNat n) :=
        hBadTail (CB * logSqScaleNat n)
      _ ≤ ((↑(n + 1) : ENNReal) ^ (k + 1))⁻¹ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hBirth n hnB m hm
  have hlog1 : 1 ≤ logSqScale n := by
    have hlog := (one_lt_logScale_chain n hn2).le
    unfold logSqScale
    nlinarith
  have hceil :
      (logSqScaleNat n : Real) ≤
        2 * logSqScale n := by
    calc
      (logSqScaleNat n : Real) ≤
          logSqScale n + 1 :=
        logSqScaleNat_cast_le_add_one_chain n
      _ ≤ 2 * logSqScale n := by linarith
  have hBGapNat :
      CB * logSqScaleNat n ≤ a - b := by
    have hcast :
        ((CB * logSqScaleNat n : Nat) : Real) ≤
          (a : Real) - b := by
      calc
        ((CB * logSqScaleNat n : Nat) : Real) =
            (CB : Real) * logSqScaleNat n := by norm_num
        _ ≤ (CB : Real) * (2 * logSqScale n) :=
          mul_le_mul_of_nonneg_left hceil (by positivity)
        _ = (2 * CB : Real) * logSqScale n := by ring
        _ ≤ (a : Real) - b := by
          simpa only [n] using hgap
    rw [← Nat.cast_sub hab.le] at hcast
    exact_mod_cast hcast
  have hInitialAE :
      ∀ᵐ ζ ∂ R, (ζ 0).1 = (a, b) := by
    rw [ae_iff]
    have hmarg :
        R.map (fun ζ : Nat → LabeledPopState => ζ 0) =
          Measure.dirac ((a, b), .idle) := by
      dsimp [R]
      simp only [lvLabeledPathMeasure]
      exact homogeneousPathMeasure_marginal_zero
        (lvLabeledKernel .selfDestructive params)
        (Measure.dirac ((a, b), .idle))
    calc
      R {ζ | ¬(ζ 0).1 = (a, b)} =
          R ((fun ζ : Nat → LabeledPopState => ζ 0) ⁻¹'
            {z | ¬z.1 = (a, b)}) := rfl
      _ = R.map
          (fun ζ : Nat → LabeledPopState => ζ 0)
            {z | ¬z.1 = (a, b)} := by
        symm
        exact Measure.map_apply (measurable_pi_apply 0)
          (DiscreteMeasurableSpace.forall_measurableSet _)
      _ = Measure.dirac ((a, b), LVReaction.idle)
          {z | ¬z.1 = (a, b)} := by rw [hmarg]
      _ = 0 := by simp
  have hFailureAE :
      ∀ᵐ ζ ∂ R, ζ ∈ MCᶜ → ζ ∈ ET ∪ EB := by
    filter_upwards [
      lvLabeledPathMeasure_valid_selfDestructive_ae
        params hGamma0 hGamma1 (a, b),
      hInitialAE] with ζ hvalid hInitial
    intro hnotMC
    by_cases htime :
        consensusTime (forgetLVLabels ζ) ≥
          (CT * n : Nat)
    · exact Or.inl htime
    · have hfinite :
          consensusTime (forgetLVLabels ζ) < ⊤ :=
        (lt_of_not_ge htime).trans
          (WithTop.coe_lt_top _)
      obtain ⟨τ, hτ⟩ :=
        WithTop.ne_top_iff_exists.mp
          (WithTop.lt_top_iff_ne_top.mp hfinite)
      by_cases hbad :
          a - b ≤ labeledBadCountBeforeConsensus ζ
      · exact Or.inr (hBGapNat.trans hbad)
      · exfalso
        apply hnotMC
        exact labeled_gap_majority_argument
          a b ζ hab hInitial hvalid τ hτ.symm
            (Nat.lt_of_not_ge hbad)
  have hFail :
      R MCᶜ ≤ ((↑(n + 1) : ENNReal) ^ k)⁻¹ := by
    calc
      R MCᶜ ≤ R (ET ∪ EB) :=
        measure_mono_ae hFailureAE
      _ ≤ R ET + R EB := measure_union_le ET EB
      _ ≤ ((↑(n + 1) : ENNReal) ^ (k + 1))⁻¹ +
          ((↑(n + 1) : ENNReal) ^ (k + 1))⁻¹ :=
        add_le_add hET hEB
      _ ≤ ((↑(n + 1) : ENNReal) ^ k)⁻¹ :=
        twice_poly_inv_succ_le_chain n k (by omega)
  have hMCmeas : MeasurableSet MC := by
    exact
      (measurableSet_majorityConsensusEvent (a, b)).preimage
        measurable_forgetLVLabels
  have hMCcomp :
      R MC = 1 - R MCᶜ := by
    have h := measure_compl hMCmeas.compl
      (measure_ne_top R MCᶜ)
    simpa only [compl_compl, measure_univ] using h
  have htarget :
      ENNReal.ofReal
          (1 - 1 / (((n : Nat) + 1 : Real) ^ k)) =
        1 - ((↑(n + 1) : ENNReal) ^ k)⁻¹ := by
    rw [ENNReal.ofReal_sub 1 (by positivity),
      ENNReal.ofReal_one]
    rw [ennreal_poly_inv_eq_ofReal_chain n k]
  have hMClaw :
      majorityConsensusProb .selfDestructive
          params (a, b) = R MC := by
    have hG :
        MeasurableSet
          {ω : Nat → PopState |
            majorityConsensusEvent (a, b) ω} :=
      measurableSet_majorityConsensusEvent (a, b)
    calc
      majorityConsensusProb .selfDestructive
          params (a, b) =
          lvPathMeasure .selfDestructive params (a, b)
            {ω | majorityConsensusEvent (a, b) ω} := rfl
      _ = (R.map forgetLVLabels)
          {ω | majorityConsensusEvent (a, b) ω} := by
        rw [lvLabeledPathMeasure_map_forget
          .selfDestructive params (a, b)]
      _ = R MC := by
        rw [Measure.map_apply measurable_forgetLVLabels hG]
        rfl
  rw [hMClaw, htarget, hMCcomp]
  exact tsub_le_tsub_left hFail 1

end LVConsensus
