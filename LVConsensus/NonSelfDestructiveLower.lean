import LVConsensus.Preliminaries
import LVConsensus.SwapInvariance
import LVConsensus.MarkovLib
import LVConsensus.NsdGapProof

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LVConsensus

/-! ## Measurability helpers -/

/-- The majority-consensus event is measurable at any initial state. -/
private lemma measurableSet_majorityConsensusEvent_general (s0 : PopState) :
    MeasurableSet {ω : ℕ → PopState | majorityConsensusEvent s0 ω} := by
  suffices h : {ω : ℕ → PopState | majorityConsensusEvent s0 ω} =
      ⋃ t : ℕ, {ω | consensusTime ω = ↑t} ∩
        ((fun ω : ℕ → PopState => ω t) ⁻¹'
          {s : PopState |
            (species0Majority s0 ∧ s.1 > 0 ∧ s.2 = 0) ∨
              (¬species0Majority s0 ∧ s.2 > 0 ∧ s.1 = 0)}) by
    rw [h]
    exact MeasurableSet.iUnion fun t =>
      (measurableSet_consensusTime_eq_coe t).inter
        ((measurable_pi_apply t) (DiscreteMeasurableSpace.forall_measurableSet _))
  ext ω
  simp only [Set.mem_setOf, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    unfold majorityConsensusEvent at h
    cases hct : consensusTime ω with
    | top => simp [hct] at h
    | coe t => exact ⟨t, rfl, by simp [hct] at h; exact h⟩
  · intro ⟨t, ht, hpred⟩
    unfold majorityConsensusEvent
    cases hct : consensusTime ω with
    | top => exact absurd (ht ▸ hct) WithTop.coe_ne_top
    | coe t' =>
      have : t' = t := WithTop.coe_eq_coe.mp (hct.symm.trans ht)
      subst this; exact hpred

/-- The "gap reaches 0 with both alive at step ≤ b" event is measurable. -/
private lemma measurableSet_diagonal_reach (b : ℕ) :
    MeasurableSet {ω : ℕ → PopState |
      ∃ k ∈ Finset.range (b + 1), (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} := by
  -- Rewrite as finite union of preimage sets (PopState is discrete, so all sets measurable)
  have : {ω : ℕ → PopState |
      ∃ k ∈ Finset.range (b + 1), (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} =
    ⋃ k ∈ Finset.range (b + 1),
      ((fun ω : ℕ → PopState => ω k) ⁻¹'
        {s : PopState | s.1 = s.2 ∧ 0 < s.1}) := by
    ext ω; constructor
    · rintro ⟨k, hk, hpred⟩; exact Set.mem_biUnion hk hpred
    · intro h; simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf] at h
      obtain ⟨k, hk, hpred⟩ := h; exact ⟨k, hk, hpred⟩
  rw [this]
  exact MeasurableSet.biUnion (Finset.range (b + 1)).countable_toSet
    (fun k _ =>
      (measurable_pi_apply k) (DiscreteMeasurableSpace.forall_measurableSet _))

/-! ## NSD gap symmetry: P(gap+1) = P(gap-1) under neutral parameters -/

/-- Under neutral NSD (α₀=α₁, β=δ, γ=0), the kernel assigns equal weight to
    gap-increasing and gap-decreasing transitions. -/
private lemma nsd_gap_kernel_symmetric
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (lvKernel .nonSelfDestructive params (a, b))
      {s : PopState | gap s = gap (a, b) + 1} =
    (lvKernel .nonSelfDestructive params (a, b))
      {s : PopState | gap s = gap (a, b) - 1} := by
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · -- φ = 0: kernel = dirac(a,b), both sides are 0
    rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    have h1 : gap (a, b) ≠ gap (a, b) + 1 := by unfold gap; omega
    have h2 : gap (a, b) ≠ gap (a, b) - 1 := by unfold gap; omega
    simp [Measure.dirac_apply, h1, h2]
  · -- φ ≠ 0: unfold and compute
    rw [lvKernel_nsd_apply params a b hφ]
    simp only [Measure.smul_apply, Measure.add_apply]
    -- Evaluate each Dirac on {gap = gap(a,b) + 1}
    have hg_b0_p : gap (a + 1, b) = gap (a, b) + 1 := by simp [gap]; omega
    have hg_b1_p : gap (a, b + 1) ≠ gap (a, b) + 1 := by simp [gap]; omega
    have hg_d0_p : gap (a - 1, b) ≠ gap (a, b) + 1 := by simp [gap]; omega
    have hg_d1_p : gap (a, b - 1) = gap (a, b) + 1 := by simp [gap]; omega
    -- Evaluate each Dirac on {gap = gap(a,b) - 1}
    have hg_b0_m : gap (a + 1, b) ≠ gap (a, b) - 1 := by simp [gap]; omega
    have hg_b1_m : gap (a, b + 1) = gap (a, b) - 1 := by simp [gap]; omega
    have hg_d0_m : gap (a - 1, b) = gap (a, b) - 1 := by simp [gap]; omega
    have hg_d1_m : gap (a, b - 1) ≠ gap (a, b) - 1 := by simp [gap]; omega
    -- Compute Dirac measures
    have hms_p : MeasurableSet {s : PopState | gap s = gap (a, b) + 1} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    have hms_m : MeasurableSet {s : PopState | gap s = gap (a, b) - 1} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    -- Dirac evaluations for gap+1
    have hd_b0_p : Measure.dirac (a + 1, b) {s : PopState | gap s = gap (a, b) + 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_b0_p])
    have hd_b1_p : Measure.dirac (a, b + 1) {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_b1_p]
    have hd_d0_p : Measure.dirac (a - 1, b) {s : PopState | gap s = gap (a, b) + 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_d0_p]
    have hd_d1_p : Measure.dirac (a, b - 1) {s : PopState | gap s = gap (a, b) + 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_d1_p])
    -- Dirac evaluations for gap-1
    have hd_b0_m : Measure.dirac (a + 1, b) {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_b0_m]
    have hd_b1_m : Measure.dirac (a, b + 1) {s : PopState | gap s = gap (a, b) - 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_b1_m])
    have hd_d0_m : Measure.dirac (a - 1, b) {s : PopState | gap s = gap (a, b) - 1} = 1 :=
      Measure.dirac_apply_of_mem (by simp [hg_d0_m])
    have hd_d1_m : Measure.dirac (a, b - 1) {s : PopState | gap s = gap (a, b) - 1} = 0 := by
      rw [Measure.dirac_apply]; simp [hg_d1_m]
    -- Substitute β = δ, α₀ = α₁, γ₀ = γ₁ = 0
    rw [hBetaDelta, hNeutral, hGamma0, hGamma1]
    -- Now simplify: both sides equal invφ * (δ*a + δ*b + α₁*a*b)
    simp only [hd_b0_p, hd_b1_p, hd_d0_p, hd_d1_p, hd_b0_m, hd_b1_m, hd_d0_m, hd_d1_m,
      smul_eq_mul, mul_one, mul_zero]
    ring

/-! ## CLT + Markov property for the gap process -/

/-- Core CLT + Markov bound: under neutral NSD, the gap process reaches the positive
    diagonal within b steps with probability ≥ 1-ε, when gap₀ ≤ θ√b.

    **Proof outline** (the three key ingredients are marked with their status):
    1. **Gap kernel symmetry** (PROVED: `nsd_gap_kernel_symmetric`):
       P(gap+1 | state) = P(gap-1 | state) = 1/2 at all interior states.
    2. **Markov property** (PROVED: `homogeneousPathMeasure_markov_bound`):
       Gap changes X_i are i.i.d. Rademacher, because P(X_i=+1 | F_{i-1}) = 1/2
       regardless of the state, and the tower property gives independence.
    3. **CLT anti-concentration** (PROVED: `lemma_clt`):
       For i.i.d. Rademacher X_i, ∃ θ>0, ∀ b≥n₀, P(max_{k≤b} Σ X_i ≥ θ√b) ≥ 1-ε.
    4. By symmetry of Rademacher: P(min_{k≤b} Σ X_i ≤ -θ√b) ≥ 1-ε.
    5. If gap₀ ≤ θ√b: gap reaches ≤ 0, so by **integer IVT** (gap changes by ±1),
       gap passes through 0. Total pop ≥ a > 0 ensures a positive diagonal. -/
private lemma nsd_gap_clt_markov_bound
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (ε : Real) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ θ : Real, 0 < θ ∧ ∃ n₀ : Nat,
      ∀ a b : Nat, n₀ ≤ b → 0 < b → b ≤ a →
        (a : Real) - b ≤ θ * Real.sqrt b →
          ENNReal.ofReal (1 - ε) ≤
            (lvPathMeasure LVVariant.nonSelfDestructive params (a, b))
              {ω | ∃ k ∈ Finset.range (b + 1),
                (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} :=
  nsd_gap_clt_markov_bound_unconditional params hNeutral hInter
    hBetaDelta hGamma0 hGamma1 ε hε0 hε1

/-! ## Bookkeeping: convert from θ√b to φ√(a+b) -/

/-- If gap₀ ≤ φ√n with φ = θ/2 and n = a+b ≥ n₁, then b ≥ n/4 and gap₀ ≤ θ√b.
    This converts the φ√(a+b) condition to the θ√b condition needed by the CLT. -/
private lemma nsd_gap_reaches_diagonal
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (ε : Real) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ φ : Real, 0 < φ ∧ ∃ n₁ : Nat,
      ∀ a b : Nat, n₁ ≤ a + b → 0 < b → b ≤ a →
        (a : Real) - b ≤ φ * Real.sqrt (a + b) →
          ENNReal.ofReal (1 - ε) ≤
            (lvPathMeasure LVVariant.nonSelfDestructive params (a, b))
              {ω | ∃ k ∈ Finset.range (b + 1),
                (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} := by
  obtain ⟨θ, hθ, n₀, hCLT⟩ := nsd_gap_clt_markov_bound params
    hNeutral hInter hBetaDelta hGamma0 hGamma1 ε hε0 hε1
  -- Set φ = θ/2; need n₁ large enough that b ≥ n₀ and gap₀ ≤ θ√b
  refine ⟨θ / 2, by linarith, max (4 * n₀) (Nat.ceil (θ ^ 2) + 1), ?_⟩
  intro a b hn hb hab hgap
  -- Key: from gap₀ ≤ (θ/2)√n and n large, deduce b ≥ n/4, hence b ≥ n₀ and gap₀ ≤ θ√b
  have hn₁ : (4 * n₀ : ℕ) ≤ a + b := le_trans (le_max_left _ _) hn
  have hθsq : (Nat.ceil (θ ^ 2) + 1 : ℕ) ≤ a + b := le_trans (le_max_right _ _) hn
  -- gap₀ ≤ θ√b: from gap₀ ≤ (θ/2)√(a+b) and b ≥ (a+b)/4
  have hb_quarter : (a + b : ℝ) ≤ 4 * b := by
    -- From gap₀ ≤ (θ/2)√n and n ≥ θ²+1: φ√n ≤ n/2, so 2b ≥ n - n/2 = n/2
    have hnn : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring
    have hab' : (a : ℝ) ≤ (b : ℝ) + (θ / 2) * Real.sqrt (a + b) := by linarith
    -- n ≥ θ²+1 > θ², so √n > θ, so (θ/2)√n < n/2
    have hn_pos : (0 : ℝ) < (a + b : ℝ) := by positivity
    have hsqrt_pos : 0 < Real.sqrt (a + b : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn_pos)
    have hsqrt_bound : θ < Real.sqrt (a + b : ℝ) := by
      rw [show (a + b : ℝ) = ((a + b : ℕ) : ℝ) from by push_cast; ring]
      rw [← Real.sqrt_sq (le_of_lt hθ)]
      apply Real.sqrt_lt_sqrt (sq_nonneg θ)
      have : (Nat.ceil (θ ^ 2) : ℝ) < (a + b : ℕ) := by
        exact_mod_cast (by omega : Nat.ceil (θ ^ 2) < a + b)
      linarith [Nat.le_ceil (θ ^ 2)]
    -- (θ/2)√n < √n · √n / 2 = n/2
    have : (θ / 2) * Real.sqrt (a + b : ℝ) < (a + b : ℝ) / 2 := by
      have h1 := mul_lt_mul_of_pos_right hsqrt_bound hsqrt_pos
      have h2 : Real.sqrt (↑a + ↑b) * Real.sqrt (↑a + ↑b) = ↑a + ↑b :=
        Real.mul_self_sqrt (by exact_mod_cast le_of_lt hn_pos)
      linarith
    linarith
  -- b ≥ n₀ from a + b ≥ 4n₀ and (a+b) ≤ 4b
  have hb_large : n₀ ≤ b := by
    have : (n₀ : ℝ) ≤ b := by linarith [show (4 * n₀ : ℝ) ≤ a + b from by exact_mod_cast hn₁]
    exact_mod_cast this
  have hgap_θ : (a : Real) - b ≤ θ * Real.sqrt b := by
    calc (a : ℝ) - b ≤ (θ / 2) * Real.sqrt (a + b) := hgap
      _ ≤ (θ / 2) * Real.sqrt (4 * b) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact Real.sqrt_le_sqrt (by exact_mod_cast hb_quarter)
      _ = (θ / 2) * (2 * Real.sqrt b) := by
          congr 1
          rw [show (4 : ℝ) * b = (2 : ℝ) ^ 2 * b from by ring,
              Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2^2),
              Real.sqrt_sq (by linarith : (0:ℝ) ≤ 2)]
      _ = θ * Real.sqrt b := by ring
  exact hCLT a b hb_large hb hab hgap_θ

/-- Once the chain reaches diagonal (m,m) with m > 0, by the Markov property
    and swap invariance (lemma_identical_gap_fail), P(MC | diagonal) ≤ 1/2.
    Therefore P(MC ∩ diagonal_reached) ≤ 1/2. -/
private lemma nsd_mc_cap_diagonal_le_half
    (params : LVParams)
    (_hNeutral : params.alpha0 = params.alpha1)
    (_hGamma0 : params.gamma0 = 0)
    (_hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : Nat) (_hb : 0 < b) (_hab : b ≤ a) :
    (lvPathMeasure LVVariant.nonSelfDestructive params (a, b))
      ({ω | majorityConsensusEvent (a, b) ω} ∩
        {ω | ∃ k ∈ Finset.range (b + 1),
          (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}) ≤
      ENNReal.ofReal (1 / 2) := by
  calc (lvPathMeasure LVVariant.nonSelfDestructive params (a, b))
        ({ω | majorityConsensusEvent (a, b) ω} ∩
          {ω | ∃ k ∈ Finset.range (b + 1), (ω k).1 = (ω k).2 ∧ 0 < (ω k).1})
      ≤ (lvPathMeasure LVVariant.nonSelfDestructive params (a, b))
          ({ω | majorityConsensusEvent (a, b) ω} ∩
            {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}) :=
        measure_mono (Set.inter_subset_inter_right _ fun ω ⟨k, hk, h⟩ => ⟨k, h⟩)
    _ ≤ ENNReal.ofReal (1 / 2) :=
        mc_cap_any_diagonal_le_half _ params (a, b) (a, b) _hNeutral
          (by rw [_hGamma0, _hGamma1])
          (fun t => nsd_path_no_revival_species0 params (a, b) t)
          (fun t => nsd_path_no_revival_species1 params (a, b) t)

/-- Section 7 lower bound for non-self-destructive competition (paper line 808–809).
    For any ε > 0, there exists φ > 0 such that if Δ₀ ≤ φ√n,
    then ρ(S) ≤ 1/2 + ε for all sufficiently large n.

    Proof: P(MC) = P(MC ∩ diag) + P(MC \ diag) ≤ 1/2 + P(diagᶜ) ≤ 1/2 + ε. -/
theorem thm_non_self_destructive_lower
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hBetaDelta : params.beta = params.delta)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    ∀ ε : Real, 0 < ε →
      ∃ φ : Real, 0 < φ ∧ ∃ n₀ : Nat,
        ∀ a b : Nat, n₀ ≤ a + b → 0 < b → b ≤ a →
          (a : Real) - b ≤ φ * Real.sqrt (a + b) →
            majorityConsensusProb LVVariant.nonSelfDestructive params (a, b) ≤
              ENNReal.ofReal (1 / 2 + ε) := by
  intro ε hε
  by_cases hε1 : ε < 1
  · -- Main case: 0 < ε < 1
    obtain ⟨φ, hφ, n₁, hgap⟩ := nsd_gap_reaches_diagonal params
      hNeutral hInter hBetaDelta hGamma0 hGamma1 ε hε hε1
    exact ⟨φ, hφ, n₁, fun a b hn hb hab hΔ => by
      set μ := lvPathMeasure LVVariant.nonSelfDestructive params (a, b) with hμ_def
      haveI : IsProbabilityMeasure μ := by
        rw [hμ_def]; unfold lvPathMeasure homogeneousPathMeasure; infer_instance
      set mcE := {ω : ℕ → PopState | majorityConsensusEvent (a, b) ω}
      set diagE := {ω : ℕ → PopState |
        ∃ k ∈ Finset.range (b + 1), (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}
      have hmc_meas : MeasurableSet mcE :=
        measurableSet_majorityConsensusEvent_general (a, b)
      have hdiag_meas : MeasurableSet diagE := measurableSet_diagonal_reach b
      -- Step 1: P(diag) ≥ 1 - ε
      have h_diag : ENNReal.ofReal (1 - ε) ≤ μ diagE := hgap a b hn hb hab hΔ
      -- Step 2: P(MC ∩ diag) ≤ 1/2
      have h_mc_diag : μ (mcE ∩ diagE) ≤ ENNReal.ofReal (1 / 2) :=
        nsd_mc_cap_diagonal_le_half params hNeutral hGamma0 hGamma1 a b hb hab
      -- Step 3: P(MC) = P(MC ∩ diag) + P(MC \ diag)
      have h_split : μ mcE = μ (mcE ∩ diagE) + μ (mcE \ diagE) :=
        (measure_inter_add_diff mcE hdiag_meas).symm
      -- Step 4: P(MC \ diag) ≤ P(diagᶜ)
      have h_diff_le : μ (mcE \ diagE) ≤ μ diagEᶜ :=
        measure_mono fun x ⟨_, hx2⟩ => hx2
      -- Step 5: P(diagᶜ) ≤ ε (using μ diagEᶜ = 1 - μ diagE and h_diag)
      have h_compl : μ diagEᶜ ≤ ENNReal.ofReal ε := by
        have h_eq : μ diagEᶜ = 1 - μ diagE := by
          have := measure_compl hdiag_meas (measure_ne_top μ diagE)
          rwa [measure_univ] at this
        have h_simp : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - ε) = ENNReal.ofReal ε := by
          have h_add : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
            rw [← ENNReal.ofReal_add (by linarith) hε.le]
            simp only [sub_add_cancel, ENNReal.ofReal_one]
          rw [← h_add, ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
        calc μ diagEᶜ = 1 - μ diagE := h_eq
          _ ≤ 1 - ENNReal.ofReal (1 - ε) := tsub_le_tsub_left h_diag 1
          _ = ENNReal.ofReal ε := h_simp
      -- Step 6: Combine
      calc μ mcE
          = μ (mcE ∩ diagE) + μ (mcE \ diagE) := h_split
        _ ≤ μ (mcE ∩ diagE) + μ diagEᶜ := add_le_add le_rfl h_diff_le
        _ ≤ ENNReal.ofReal (1 / 2) + ENNReal.ofReal ε :=
            add_le_add h_mc_diag h_compl
        _ = ENNReal.ofReal (1 / 2 + ε) := by
            rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2) hε.le]⟩
  · -- Trivial case: ε ≥ 1, so 1/2 + ε ≥ 3/2 ≥ 1
    push_neg at hε1
    exact ⟨1, one_pos, 0, fun a b _ _ _ _ => by
      haveI : IsProbabilityMeasure
          (lvPathMeasure LVVariant.nonSelfDestructive params (a, b)) := by
        unfold lvPathMeasure homogeneousPathMeasure; infer_instance
      calc majorityConsensusProb LVVariant.nonSelfDestructive params (a, b)
          ≤ 1 := (measure_mono (Set.subset_univ _)).trans measure_univ.le
        _ ≤ ENNReal.ofReal (1 / 2 + ε) := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (by linarith)⟩

end LVConsensus
