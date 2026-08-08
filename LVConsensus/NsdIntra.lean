import LVConsensus.Definitions
import LVConsensus.LineageDynamics
import LVConsensus.MarkovLib
import LVConsensus.NsdConsensus
import LVConsensus.SwapInvariance
import LVConsensus.SelfDestructiveLower

set_option autoImplicit false

namespace LVConsensus

open MeasureTheory ProbabilityTheory

-- =========================================================================
-- Lineage symmetry framework (Paper §6, Lemmas 6.3–6.4)
-- =========================================================================
-- We track lineages: individual i ∈ Fin n has L_t(i) descendants at time t.
-- Under neutral NSD (α₀=α₁=α, γ₀=γ₁=2α), each individual's birth and
-- death+competition rates depend only on its lineage count L(i) and the
-- total population N, NOT on which species it belongs to. This is the core
-- of the permutation equivariance (Lemma 6.3).

-- ---- Per-individual rate decomposition (core of Lemma 6.3) ----

/-- Under neutral NSD, the total death+competition rate for species 0,
    `δ·a' + α₁·a'·b' + γ₀·a'·(a'-1)/2`, factors as `(δ + α₀·(n-1)) · a'`
    where n = a'+b'. This shows the per-individual death+competition rate
    `δ + α₀·(n-1)` is independent of the species split (a',b'). -/
lemma nsd_neutral_sp0_death_rate (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0) (a' b' : ℕ) :
    params.delta * (a' : ℝ) + params.alpha1 * a' * b' +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2) =
    (params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) * a' := by
  rw [hNeutral.symm, hEq0]; ring

/-- Under neutral NSD, the total death+competition rate for species 1,
    `δ·b' + α₀·a'·b' + γ₁·b'·(b'-1)/2`, factors as `(δ + α₀·(n-1)) · b'`.
    Combined with `nsd_neutral_sp0_death_rate`, this shows both species
    have the SAME per-individual death+competition rate `δ + α₀·(n-1)`. -/
lemma nsd_neutral_sp1_death_rate (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq1 : params.gamma1 = 2 * params.alpha1) (a' b' : ℕ) :
    params.delta * (b' : ℝ) + params.alpha0 * a' * b' +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2) =
    (params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) * b' := by
  rw [hEq1, hNeutral]; ring

/-- Paper `lem:nsd-intra:symmetry` (Lemma 6.3): Equivariance under lineage
    permutations. The transition kernel on lineage states commutes with
    all permutations π ∈ S_n, because the per-individual rates (birth rate β,
    death+competition rate δ+α₀(N-1)) depend only on L(i) and N = Σ L(j),
    not on which species individual i belongs to.

    Formally: Pr[L_{t+1} = L' | L_t = L] = Pr[L_{t+1} = π·L' | L_t = π·L].
    The algebraic content is captured by `nsd_neutral_sp0_death_rate` and
    `nsd_neutral_sp1_death_rate`: both species have the same per-individual
    rates, so the lineage kernel treats all individuals identically. -/
theorem lem_nsd_intra_rate_factorization
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (n : Nat) (a' b' : ℕ) (_hn : a' + b' = n) :
    -- Per-individual birth rate: β (same for both species)
    params.beta = params.beta ∧
    -- Per-individual death+competition rate: δ + α₀·(n-1) for species 0
    params.delta * (a' : ℝ) + params.alpha1 * a' * b' +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2) =
    (params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) * a' ∧
    -- Per-individual death+competition rate: δ + α₀·(n-1) for species 1
    params.delta * (b' : ℝ) + params.alpha0 * a' * b' +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2) =
    (params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) * b' :=
  ⟨rfl, nsd_neutral_sp0_death_rate params hNeutral hEq0 a' b',
   nsd_neutral_sp1_death_rate params hNeutral hEq1 a' b'⟩

/-- The consensus probability function h(a,b) = a/(a+b). -/
private noncomputable def h_ratio : PopState → ℝ :=
  fun s => (s.1 : ℝ) / ((s.1 : ℝ) + (s.2 : ℝ))

private noncomputable def h_ratio_swap : PopState → ℝ :=
  fun s => h_ratio s.swap

private lemma h_ratio_def (a b : ℕ) : h_ratio (a, b) = (a : ℝ) / ((a : ℝ) + (b : ℝ)) := rfl

private lemma h_ratio_bound (s : PopState) : 0 ≤ h_ratio s ∧ h_ratio s ≤ 1 := by
  have h1 : (0 : ℝ) ≤ s.1 := Nat.cast_nonneg s.1
  have h2 : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg s.2
  constructor
  · exact div_nonneg h1 (by linarith)
  · by_cases hn : (s.1 : ℝ) + (s.2 : ℝ) = 0
    · simp [h_ratio, hn]
    · have hpos : 0 < (s.1 : ℝ) + (s.2 : ℝ) :=
        lt_of_le_of_ne (by linarith) (Ne.symm hn)
      exact (div_le_one hpos).mpr (by linarith)

private lemma h_ratio_bnd1 (a' : ℕ) (ha' : 0 < a') : h_ratio (a', 0) = 1 := by
  simp [h_ratio, Nat.cast_pos.mpr ha' |>.ne']

private lemma h_ratio_bnd0 (b' : ℕ) : h_ratio (0, b') = 0 := by
  simp [h_ratio]

/-- Under NSD with β=δ=0 and positive competition, consensus is reached almost surely
    from any initial state (a,b) with a,b > 0. Derived from
    `nsd_kernelIter_concentrated_on_absorbing`: after N = a+b−1 steps the chain
    concentrates on {(1,0),(0,1)}, both of which are consensus states. -/
lemma nsd_consensus_almost_sure
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (a b : Nat)
    (hposA : 0 < a) (hposB : 0 < b)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b) {ω | consensusReachedEvent ω} = 1 := by
  set P := lvPathMeasure .nonSelfDestructive params (a, b) with hP_def
  haveI : IsProbabilityMeasure P := by
    rw [hP_def]; unfold lvPathMeasure homogeneousPathMeasure; infer_instance
  let N := a + b - 1
  -- The absorbing set {(1,0),(0,1)} at time N
  set absorb := (fun ω : ℕ → PopState => ω N) ⁻¹' ({(1, 0), (0, 1)} : Set PopState)
  -- P[ω(N) ∉ {(1,0),(0,1)}] = 0
  have hNullConc : P absorbᶜ = 0 := by
    change lvPathMeasure .nonSelfDestructive params (a, b) _ = 0
    unfold lvPathMeasure
    rw [show absorbᶜ = (fun ω => ω N) ⁻¹' ({(1, 0), (0, 1)} : Set PopState)ᶜ from rfl,
      ← Measure.map_apply (measurable_pi_apply N) (by measurability),
      homogeneousPathMeasure_dirac_marginal]
    convert nsd_kernelIter_concentrated_on_absorbing params hBeta hDelta
      hGamma0 hGamma1 hAlphaSum a b hposA hposB using 2
  -- absorb is measurable
  have hAbsorbMeas : MeasurableSet absorb :=
    (measurable_pi_apply N) (by measurability)
  -- P[absorb] = 1
  have hAbsorbOne : P absorb = 1 := by
    have h := measure_add_measure_compl hAbsorbMeas (μ := P)
    rw [hNullConc, add_zero, measure_univ] at h; exact h
  -- absorb ⊆ {ω | consensusReachedEvent ω}
  have hSubset : absorb ⊆ {ω | consensusReachedEvent ω} := by
    intro ω (hω : ω N ∈ ({(1, 0), (0, 1)} : Set PopState))
    change consensusReachedEvent ω
    unfold consensusReachedEvent
    have hrc : reachedConsensus (ω N) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      unfold reachedConsensus
      rcases hω with h | h <;> rw [h] <;> simp
    exact lt_of_le_of_lt (consensusTime_le_of_reached' ω N hrc) (WithTop.coe_lt_top N)
  -- Conclude P[consensusReachedEvent] = 1
  apply le_antisymm
  · calc P {ω | consensusReachedEvent ω} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · calc 1 = P absorb := hAbsorbOne.symm
      _ ≤ P {ω | consensusReachedEvent ω} := measure_mono hSubset

/-- Paper `thm:nsd-intra` (neutral Moran model in NSD), Part 2.
Paper Part 1: If α > 0 or δ > 0, Pr[majority | consensus] = a/(a+b).
Paper Part 2: If α > 0, consensus is reached a.s. and ρ(S) = a/(a+b).
We formalize Part 2. The condition `γ₀ = 2α₀` (not `γ₀ = α₀`) reflects our
convention that γ counts unordered intra-species pairs. -/
theorem thm_nsd_intra
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    majorityConsensusProb LVVariant.nonSelfDestructive params (a, b) =
      ENNReal.ofReal ((a : Real) / (a + b)) := by
  have hGamma0 : 0 < params.gamma0 := by rw [hEq0]; linarith
  have hGamma1 : 0 < params.gamma1 := by rw [hEq1, ← hNeutral]; linarith
  rcases Nat.eq_or_lt_of_le hba with rfl | hba_strict
  · -- b = a: by swap invariance + kernel concentration, P[MCE] = 1/2
    have hval : (b : ℝ) / ((b : ℝ) + b) = 1 / 2 := by
      field_simp; ring
    rw [hval]
    have hAlphaSum : 0 < params.alpha0 + params.alpha1 := by
      linarith [hNeutral.symm ▸ hAlpha]
    have hGammaEq : params.gamma0 = params.gamma1 := by rw [hEq0, hEq1, hNeutral]
    -- Setup
    let N := b + b - 1
    set P := lvPathMeasure .nonSelfDestructive params (b, b) with hP_def
    haveI : IsProbabilityMeasure P := by
      rw [hP_def]; unfold lvPathMeasure homogeneousPathMeasure; infer_instance
    set A := {ω : ℕ → PopState | majorityConsensusEvent (b, b) ω}
    -- P[MCE] ≤ 1/2
    have hle := lemma_identical_gap_fail .nonSelfDestructive params hNeutral hGammaEq b
    -- P[MCE] = P[swap(MCE)] by path-measure swap-invariance
    set C := {ω : ℕ → PopState | majorityConsensusEvent (b, b) (swapTraj ω)}
    have hswap_meas : Measurable swapTraj := by
      rw [measurable_pi_iff]; intro n
      exact (measurable_of_countable PopState.swap).comp (measurable_pi_apply n)
    have hA_meas : MeasurableSet A := measurableSet_majorityConsensusEvent_diag b
    have hC_eq : C = swapTraj ⁻¹' A := Set.ext fun ω => Iff.rfl
    have hC_meas : MeasurableSet C := hC_eq ▸ hA_meas.preimage hswap_meas
    have h_inv : P.map swapTraj = P := lvPathMeasure_swap_invariant
      .nonSelfDestructive params hNeutral hGammaEq b
    have hA_eq_C : P A = P C := by
      rw [hC_eq, ← Measure.map_apply hswap_meas hA_meas, h_inv]
    -- A and C are disjoint
    have h_disj : Disjoint A C := disjoint_majorityConsensus_swap_diag b
    -- Null sets for no-revival and concentration
    have hNull0 : ∀ s, P {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} = 0 :=
      fun s => nsd_path_no_revival_species0 params (b, b) s
    have hNull1 : ∀ s, P {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} = 0 :=
      fun s => nsd_path_no_revival_species1 params (b, b) s
    have hNullConc : P {ω | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} = 0 := by
      change lvPathMeasure .nonSelfDestructive params (b, b) _ = 0
      unfold lvPathMeasure
      rw [show {ω : ℕ → PopState | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} =
          (fun ω => ω N) ⁻¹' ({(1, 0), (0, 1)} : Set PopState)ᶜ from rfl,
        ← Measure.map_apply (measurable_pi_apply N) (by measurability),
        homogeneousPathMeasure_dirac_marginal]
      convert nsd_kernelIter_concentrated_on_absorbing params hBeta hDelta
        hGamma0 hGamma1 hAlphaSum b b hposB hposB using 2
    -- P[(A ∪ C)ᶜ] = 0: on nice paths, MCE or swap(MCE) holds
    have hAC_null : P (A ∪ C)ᶜ = 0 := by
      apply measure_mono_null (show (A ∪ C)ᶜ ⊆
          {ω | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} ∪
          (⋃ s, {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0}) ∪
          (⋃ s, {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0}) from by
        intro ω hω
        simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hω
        by_cases hC' : ω N ∈ ({(1, 0), (0, 1)} : Set PopState)
        · by_cases hNR0 : ∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0
          · by_cases hNR1 : ∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0
            · exfalso
              have hMCE_iff := mce_iff_omega_N_diag b ω N hC' hNR0 hNR1
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC'
              rcases hC' with h | h
              · -- ω(N) = (1,0): MCE holds directly under the diagonal tie-break
                exact hω.1 (hMCE_iff.mpr h)
              · -- ω(N) = (0,1): swap(MCE) holds
                apply hω.2
                have hle' := consensusTime_le_of_reached' ω N
                  (by rw [h]; simp [reachedConsensus])
                obtain ⟨t, hct, htN⟩ := WithTop.le_coe_iff.mp hle'
                have ht2 : 0 < (ω t).2 := by
                  by_contra hp; push_neg at hp
                  have := propagate_zero_snd ω t N htN
                    (fun s hs1 hs2 => hNR1 s hs2) (Nat.eq_zero_of_le_zero hp)
                  rw [h] at this; simp at this
                have ht1 : (ω t).1 = 0 := by
                  have hcons := reachedConsensus_at_consensusTime' ω t hct
                  rcases hcons with hc | hc
                  · exact hc
                  · exfalso; omega
                change majorityConsensusEvent (b, b) (swapTraj ω)
                simp only [majorityConsensusEvent, consensusTime_swapTraj,
                  swapTraj_apply, PopState.swap_fst, PopState.swap_snd, hct]
                exact Or.inl ⟨species0Majority_diag' b, ht2, ht1⟩
            · push_neg at hNR1; obtain ⟨s, _, h1, h2⟩ := hNR1
              exact Or.inr (Set.mem_iUnion.mpr ⟨s, h1, h2⟩)
          · push_neg at hNR0; obtain ⟨s, _, h1, h2⟩ := hNR0
            exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s, h1, h2⟩))
        · exact Or.inl (Or.inl hC'))
      exact measure_union_null (measure_union_null hNullConc (measure_iUnion_null hNull0))
        (measure_iUnion_null hNull1)
    -- P[A ∪ C] = 1
    have hAC_one : P (A ∪ C) = 1 := by
      have hAC_meas : MeasurableSet (A ∪ C) := hA_meas.union hC_meas
      have h1 := measure_add_measure_compl hAC_meas (μ := P)
      rw [hAC_null, add_zero, measure_univ] at h1; exact h1
    -- P[A] + P[C] = 1
    have hsum : P A + P C = 1 := by
      rw [← measure_union h_disj hC_meas]; exact hAC_one
    -- 2 * P[A] = 1
    have htwice : P A + P A = 1 := hA_eq_C ▸ hsum
    -- P[A] = 1/2 by le_antisymm
    apply le_antisymm hle
    -- ≥ 1/2: from 2 * P A = 1
    have hPA : P A = (2 : ENNReal)⁻¹ := by
      have : P A + P A = 1 := htwice
      have hfin : P A ≠ ⊤ := measure_ne_top _ _
      rwa [← two_mul, ← ENNReal.eq_div_iff (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤), one_div] at this
    rw [show ENNReal.ofReal (1 / (2 : ℝ)) = (2 : ENNReal)⁻¹ from by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
      simp only [ENNReal.ofReal_ofNat]]
    exact hPA.ge
  · rw [← h_ratio_def]
    have hAlphaSum : 0 < params.alpha0 + params.alpha1 := by
      linarith [hNeutral.symm ▸ hAlpha]
    apply consensus_eq_harmonic_nsd params h_ratio a b hposA hposB hba_strict
      hBeta hDelta hGamma0 hGamma1 hAlphaSum h_ratio_bound
    · -- Harmonicity: weighted sum = φ * h for neutral NSD
      intro a' b' ha' hb'
      simp only [h_ratio]
      simp only [Nat.cast_sub (show 1 ≤ a' from ha'), Nat.cast_sub (show 1 ≤ b' from hb'),
        Nat.cast_add, Nat.cast_one]
      have hα : params.alpha1 = params.alpha0 := hNeutral.symm
      have hγ1 : params.gamma1 = 2 * params.alpha0 := by rw [hEq1, hNeutral]
      simp only [hα, hEq0, hγ1]
      simp only [lvTotalPropensity, hα, hEq0, hγ1, hBeta, hDelta]
      have ha1 : (1 : ℝ) ≤ (a' : ℝ) := Nat.one_le_cast.mpr ha'
      have hb1 : (1 : ℝ) ≤ (b' : ℝ) := Nat.one_le_cast.mpr hb'
      have : (a' : ℝ) + b' ≠ 0 := by linarith
      have : (a' : ℝ) + b' - 1 ≠ 0 := by linarith
      have : (a' : ℝ) - 1 + b' ≠ 0 := by linarith
      have : (a' : ℝ) + (b' - 1) ≠ 0 := by linarith
      have : (a' : ℝ) + 1 + b' ≠ 0 := by linarith
      have : (a' : ℝ) + (b' + 1) ≠ 0 := by linarith
      field_simp
      ring
    · exact h_ratio_bnd1
    · intro b'; exact h_ratio_bnd0 b'

/-- Paper `thm:nsd-intra`, Part 1 (conditional majority consensus probability).
    Under the hypotheses of Part 2, consensus is reached a.s. and the conditional
    probability Pr[majority consensus | consensus] equals a/(a+b).
    Since consensus is certain (probability 1), the conditional and unconditional
    probabilities coincide.

    The statement is: Pr[MCE] = (a/(a+b)) · Pr[consensus reached], which is
    equivalent to Pr[MCE | consensus] = a/(a+b) when Pr[consensus] > 0. -/
theorem thm_nsd_intra_part1
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    -- (1) Consensus is reached with positive probability
    0 < lvPathMeasure .nonSelfDestructive params (a, b) {ω | consensusReachedEvent ω} ∧
    -- (2) Pr[MCE] = (a/(a+b)) · Pr[consensus reached]
    majorityConsensusProb .nonSelfDestructive params (a, b) =
      ENNReal.ofReal ((a : ℝ) / ((a : ℝ) + (b : ℝ))) *
        lvPathMeasure .nonSelfDestructive params (a, b) {ω | consensusReachedEvent ω} := by
  have hGamma0 : 0 < params.gamma0 := by rw [hEq0]; linarith
  have hGamma1 : 0 < params.gamma1 := by rw [hEq1, ← hNeutral]; linarith
  have hAlphaSum : 0 < params.alpha0 + params.alpha1 := by
    linarith [hNeutral.symm ▸ hAlpha]
  have hcons := nsd_consensus_almost_sure params hBeta hDelta hGamma0 hGamma1
    hAlphaSum a b hposA hposB
  constructor
  · rw [hcons]; exact one_pos
  · rw [hcons, mul_one]
    exact thm_nsd_intra params hAlpha hNeutral hEq0 hEq1 hBeta hDelta a b hposA hposB hba

-- =========================================================================
-- Generalized versions without β=δ=0 restriction
-- =========================================================================

/-- Harmonicity of h_ratio for neutral NSD with arbitrary β,δ≥0.
    At interior states (a',b') with a',b' > 0:
    ∑ transition_rate(s') · h(s') = φ(a',b') · h(a',b')
    where φ is the total propensity. The identity h(a,b) = a/(a+b) satisfies
    this because both sides equal a'·(β + δ + α₀·(a'+b'-1)). -/
lemma nsd_harmonic_h_ratio_general
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a' b' : ℕ) (ha' : 0 < a') (hb' : 0 < b') :
    params.beta * a' * h_ratio (a' + 1, b') + params.beta * b' * h_ratio (a', b' + 1) +
    (params.delta * a' + params.alpha1 * a' * b' +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2)) * h_ratio (a' - 1, b') +
    (params.delta * b' + params.alpha0 * a' * b' +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2)) * h_ratio (a', b' - 1) =
    lvTotalPropensity params (a', b') * h_ratio (a', b') := by
  simp only [h_ratio]
  simp only [Nat.cast_sub (show 1 ≤ a' from ha'), Nat.cast_sub (show 1 ≤ b' from hb'),
    Nat.cast_add, Nat.cast_one]
  have hα : params.alpha1 = params.alpha0 := hNeutral.symm
  have hγ1 : params.gamma1 = 2 * params.alpha0 := by rw [hEq1, hNeutral]
  simp only [hα, hEq0, hγ1]
  simp only [lvTotalPropensity, hα, hEq0, hγ1]
  have ha1 : (1 : ℝ) ≤ (a' : ℝ) := Nat.one_le_cast.mpr ha'
  have hb1 : (1 : ℝ) ≤ (b' : ℝ) := Nat.one_le_cast.mpr hb'
  have : (a' : ℝ) + b' ≠ 0 := by linarith
  have : (a' : ℝ) + b' - 1 ≠ 0 := by linarith
  have : (a' : ℝ) - 1 + b' ≠ 0 := by linarith
  have : (a' : ℝ) + (b' - 1) ≠ 0 := by linarith
  have : (a' : ℝ) + 1 + b' ≠ 0 := by linarith
  have : (a' : ℝ) + (b' + 1) ≠ 0 := by linarith
  field_simp
  ring

/-- Paper `lem:nsd-intra:lineages` (Lemma 6.4): Permutation invariance of
    lineage distributions. For all t, L, and π:
      Pr[L_t = L] = Pr[L_t = π·L].
    Proof: by induction on t. Base case: L_0 = (1,...,1) is invariant.
    Inductive step: equivariance (Lemma 6.3) + law of total probability.

    The consequence at the PopState level: h(a,b) = a/(a+b) is harmonic
    for the LV kernel, because the per-individual martingale
    M_t(i) = L_t(i)/N_t satisfies E[M_{t+1}(i) | L_t] = M_t(i)
    (from equal birth and death rates). Summing over species 0 individuals:
    E[a_{t+1}/N_{t+1} | (a_t,b_t)] = a_t/N_t, which is harmonicity. -/
theorem lem_nsd_intra_harmonic
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a' b' : ℕ) (ha' : 0 < a') (hb' : 0 < b') :
    -- Consequence: h(a',b') = a'/(a'+b') is harmonic for the LV kernel.
    -- This IS the algebraic expression of lineage permutation invariance.
    params.beta * a' * h_ratio (a' + 1, b') +
    params.beta * b' * h_ratio (a', b' + 1) +
    (params.delta * a' + params.alpha1 * a' * b' +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2)) *
      h_ratio (a' - 1, b') +
    (params.delta * b' + params.alpha0 * a' * b' +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2)) *
      h_ratio (a', b' - 1) =
    lvTotalPropensity params (a', b') * h_ratio (a', b') :=
  nsd_harmonic_h_ratio_general params hNeutral hEq0 hEq1 a' b' ha' hb'

/-- Under NSD with neutral parameters and α>0, consensus is reached almost surely
    from any initial state (a,b) with a,b > 0, for arbitrary β,δ ≥ 0.
    The proof maps the pre-consensus total population to the shifted birth-death
    chain and uses eventual negative drift to show that its survival probabilities
    have infimum zero. -/
lemma nsd_consensus_almost_sure_general
    (params : LVParams)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (a b : Nat)
    (hposA : 0 < a) (hposB : 0 < b)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b) {ω | consensusReachedEvent ω} = 1 := by
  exact nsd_consensus_almost_sure_via_shift params hGamma0 hGamma1 hAlphaSum
    a b hposA hposB hAlpha hNeutral hEq0 hEq1

private lemma h_ratio_nsd_superharmonic
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (s : PopState)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    ∫ x, h_ratio x ∂(lvKernel .nonSelfDestructive params) s ≤ h_ratio s := by
  have hInt : Integrable h_ratio ((lvKernel .nonSelfDestructive params) s) := by
    haveI : IsProbabilityMeasure ((lvKernel .nonSelfDestructive params) s) := by
      infer_instance
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h_ratio).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(h_ratio_bound x).1],
      (h_ratio_bound x).2⟩
  rcases s with ⟨a, b⟩
  by_cases ha0 : a = 0
  · have hdead :
        (lvKernel .nonSelfDestructive params (a, b))
          {x : PopState | x.1 ≠ 0} = 0 :=
      nsd_kernel_species0_dead_absorbing params (a, b) ha0
    have hae : ∀ᵐ x ∂(lvKernel .nonSelfDestructive params (a, b)), x.1 = 0 := by
      rw [ae_iff]
      simpa only [Set.compl_setOf] using hdead
    have hz : ∫ x, h_ratio x ∂(lvKernel .nonSelfDestructive params (a, b)) = 0 := by
      calc
        ∫ x, h_ratio x ∂(lvKernel .nonSelfDestructive params (a, b))
            = ∫ _x, (0 : ℝ) ∂(lvKernel .nonSelfDestructive params (a, b)) := by
              apply integral_congr_ae
              filter_upwards [hae] with x hx
              simp [h_ratio, hx]
        _ = 0 := by simp
    rw [hz]
    simp [h_ratio, ha0]
  · by_cases hb0 : b = 0
    · haveI : IsProbabilityMeasure
          ((lvKernel .nonSelfDestructive params) (a, b)) := by
        infer_instance
      calc
        ∫ x, h_ratio x ∂(lvKernel .nonSelfDestructive params (a, b))
            ≤ ∫ _x, (1 : ℝ) ∂(lvKernel .nonSelfDestructive params (a, b)) := by
              apply integral_mono_ae hInt (integrable_const (1 : ℝ))
              filter_upwards with x
              exact (h_ratio_bound x).2
        _ = 1 := by simp
        _ = h_ratio (a, b) := by
          simpa [hb0] using (h_ratio_bnd1 a (Nat.pos_of_ne_zero ha0)).symm
    · have ha : 0 < a := Nat.pos_of_ne_zero ha0
      have hb : 0 < b := Nat.pos_of_ne_zero hb0
      by_cases hφ : lvTotalPropensity params (a, b) = 0
      · rw [lvKernel_apply_zero_propensity .nonSelfDestructive params (a, b) hφ]
        rw [integral_dirac' h_ratio (a, b)
          (measurable_of_countable h_ratio).stronglyMeasurable]
      · exact le_of_eq (lvKernel_nsd_harmonic_integral params h_ratio a b ha hb hφ
          (nsd_harmonic_h_ratio_general params hNeutral hEq0 hEq1 a b ha hb))

private lemma h_ratio_nsd_ennreal_superharmonic
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (s : PopState)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    ∫⁻ x, ENNReal.ofReal (h_ratio x)
        ∂(lvKernel .nonSelfDestructive params) s ≤
      ENNReal.ofReal (h_ratio s) := by
  have hInt : Integrable h_ratio ((lvKernel .nonSelfDestructive params) s) := by
    haveI : IsProbabilityMeasure ((lvKernel .nonSelfDestructive params) s) := by
      infer_instance
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h_ratio).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(h_ratio_bound x).1],
      (h_ratio_bound x).2⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun x => (h_ratio_bound x).1)]
  exact ENNReal.ofReal_le_ofReal
    (h_ratio_nsd_superharmonic params hNeutral hEq0 hEq1 s)

private lemma h_ratio_swap_nsd_ennreal_superharmonic
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (s : PopState)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    ∫⁻ x, ENNReal.ofReal (h_ratio_swap x)
        ∂(lvKernel .nonSelfDestructive params) s ≤
      ENNReal.ofReal (h_ratio_swap s) := by
  have hGamma : params.gamma0 = params.gamma1 := by
    rw [hEq0, hEq1, hNeutral]
  have hswap := lvKernel_swap_equivariant .nonSelfDestructive params
    hNeutral hGamma s
  have hm : Measurable PopState.swap := measurable_of_countable _
  have hf : Measurable (fun x : PopState => ENNReal.ofReal (h_ratio x)) :=
    (measurable_of_countable _)
  calc
    ∫⁻ x, ENNReal.ofReal (h_ratio_swap x)
        ∂(lvKernel .nonSelfDestructive params) s =
      ∫⁻ x, ENNReal.ofReal (h_ratio x)
        ∂Measure.map PopState.swap
          ((lvKernel .nonSelfDestructive params) s) := by
            rw [MeasureTheory.lintegral_map hf hm]
            rfl
    _ = ∫⁻ x, ENNReal.ofReal (h_ratio x)
        ∂(lvKernel .nonSelfDestructive params) s.swap := by rw [hswap]
    _ ≤ ENNReal.ofReal (h_ratio s.swap) :=
      h_ratio_nsd_ennreal_superharmonic params hNeutral hEq0 hEq1 s.swap
    _ = ENNReal.ofReal (h_ratio_swap s) := rfl

private lemma lvPath_event_le_of_hits_nsd
    (params : LVParams)
    (f : PopState → ENNReal)
    (A : Set PopState)
    (E : Set (ℕ → PopState))
    (s : PopState)
    (hSub : E ⊆ ⋃ N : ℕ, pathHitsBy A N)
    (hA : ∀ x ∈ A, 1 ≤ f x)
    (hSuper : ∀ x,
      ∫⁻ y, f y ∂(lvKernel .nonSelfDestructive params) x ≤ f x)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s E ≤ f s := by
  let P := lvPathMeasure .nonSelfDestructive params s
  have hMono : Monotone (pathHitsBy A) := by
    intro m n hmn ω hω
    rcases hω with ⟨t, htm, htA⟩
    exact ⟨t, htm.trans hmn, htA⟩
  have hEach : ∀ N, P (pathHitsBy A N) ≤ f s := by
    intro N
    exact homogeneousPathMeasure_hitBy_le
      (lvKernel .nonSelfDestructive params) f A hA hSuper s N
  calc
    lvPathMeasure .nonSelfDestructive params s E
        ≤ P (⋃ N : ℕ, pathHitsBy A N) := measure_mono hSub
    _ = ⨆ N : ℕ, P (pathHitsBy A N) := hMono.measure_iUnion
    _ ≤ f s := iSup_le hEach

private lemma nsd_species0_win_le_ratio
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (hba : b < a)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | majorityConsensusEvent (a, b) ω} ≤
      ENNReal.ofReal (h_ratio (a, b)) := by
  let A : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  have hMaj : species0Majority (a, b) := by
    exact Nat.le_of_lt hba
  have hSub :
      {ω : ℕ → PopState | majorityConsensusEvent (a, b) ω} ⊆
        ⋃ N : ℕ, pathHitsBy A N := by
    intro ω hω
    unfold majorityConsensusEvent at hω
    cases hct : consensusTime ω with
    | top => simp [hct] at hω
    | coe t =>
        have ht : 0 < (ω t).1 ∧ (ω t).2 = 0 := by
          simpa [hct, hMaj] using hω
        exact Set.mem_iUnion.mpr ⟨t, ⟨t, le_rfl, ht⟩⟩
  apply lvPath_event_le_of_hits_nsd params
    (fun s => ENNReal.ofReal (h_ratio s)) A
    {ω | majorityConsensusEvent (a, b) ω} (a, b) hSub
  · intro ⟨a', b'⟩ hs
    simp only [A, Set.mem_setOf_eq] at hs
    rw [show h_ratio (a', b') = 1 by
      simpa [hs.2] using h_ratio_bnd1 a' hs.1]
    simp
  · intro x
    exact h_ratio_nsd_ennreal_superharmonic params hNeutral hEq0 hEq1 x

private lemma nsd_species1_win_le_ratio
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (hba : b < a)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | majorityConsensusEvent (b, a) ω} ≤
      ENNReal.ofReal (h_ratio_swap (a, b)) := by
  let A : Set PopState := {s | 0 < s.2 ∧ s.1 = 0}
  have hNotMaj : ¬ species0Majority (b, a) := by
    exact Nat.not_le_of_gt hba
  have hSub :
      {ω : ℕ → PopState | majorityConsensusEvent (b, a) ω} ⊆
        ⋃ N : ℕ, pathHitsBy A N := by
    intro ω hω
    unfold majorityConsensusEvent at hω
    cases hct : consensusTime ω with
    | top => simp [hct] at hω
    | coe t =>
        have ht : 0 < (ω t).2 ∧ (ω t).1 = 0 := by
          simpa [hct, hNotMaj] using hω
        exact Set.mem_iUnion.mpr ⟨t, ⟨t, le_rfl, ht⟩⟩
  apply lvPath_event_le_of_hits_nsd params
    (fun s => ENNReal.ofReal (h_ratio_swap s)) A
    {ω | majorityConsensusEvent (b, a) ω} (a, b) hSub
  · intro ⟨a', b'⟩ hs
    simp only [A, Set.mem_setOf_eq] at hs
    rw [show h_ratio_swap (a', b') = 1 by
      simpa [h_ratio_swap, PopState.swap, hs.2] using h_ratio_bnd1 b' hs.1]
    simp
  · intro x
    exact h_ratio_swap_nsd_ennreal_superharmonic params hNeutral hEq0 hEq1 x

private lemma nsd_kernel_interior_draw_zero
    (params : LVParams) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (lvKernel .nonSelfDestructive params (a, b)) {(0, 0)} = 0 := by
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · rw [lvKernel_apply_zero_propensity .nonSelfDestructive params (a, b) hφ]
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    have hne : (a, b) ≠ (0, 0) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact (Nat.ne_of_gt ha) h.1
    simp [hne]
  · rw [lvKernel_nsd_apply params a b hφ]
    simp [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      ha.ne', hb.ne']

private lemma nsd_path_interior_to_draw_step_null
    (params : LVParams) (s0 : PopState) (t : ℕ)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s0
      {ω | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)} = 0 := by
  let K := lvKernel LVVariant.nonSelfDestructive params
  let g : PopState → ENNReal := fun x =>
    if 0 < x.1 ∧ 0 < x.2 then 1 else 0
  let φ : PopState → ENNReal := fun y => if y = (0, 0) then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas :
      MeasurableSet
        {ω : ℕ → PopState |
          0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)} := by
    measurability
  rw [← lintegral_indicator_one hmeas]
  have hInd : ∀ ω : ℕ → PopState,
      Set.indicator
          {ω' : ℕ → PopState |
            0 < (ω' t).1 ∧ 0 < (ω' t).2 ∧ ω' (t + 1) = (0, 0)}
          (1 : (ℕ → PopState) → ENNReal) ω =
        g (ω t) * φ (ω (t + 1)) := by
    intro ω
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp_all
  simp_rw [hInd]
  unfold lvPathMeasure
  rw [homogeneousPathMeasure_joint_lintegral K s0 t g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {(0, 0)} := by
    intro x
    have hφind :
        φ = Set.indicator ({(0, 0)} : Set PopState) 1 := by
      ext y
      simp only [φ, Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
    rw [hφind]
    exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]
  have hzero : ∀ x : PopState, g x * K x {(0, 0)} = 0 := by
    intro x
    rcases x with ⟨a, b⟩
    by_cases hx : 0 < a ∧ 0 < b
    · have hK0 : K (a, b) {(0, 0)} = 0 :=
        nsd_kernel_interior_draw_zero params a b hx.1 hx.2
      simp [g, hx, hK0]
    · simp [g, hx]
  simp_rw [hzero, lintegral_zero]

private lemma nsd_draw_at_consensus_null
    (params : LVParams) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | match consensusTime ω with
        | ⊤ => False
        | (t : Nat) => ω t = (0, 0)} = 0 := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  let Z : Set (ℕ → PopState) :=
    {ω | match consensusTime ω with
      | ⊤ => False
      | (t : Nat) => ω t = (0, 0)}
  have hZ_subset :
      Z ⊆ {ω : ℕ → PopState | ω 0 = (0, 0)} ∪
        ⋃ t : ℕ,
          {ω : ℕ → PopState |
            0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)} := by
    intro ω hω
    by_cases hct0 : consensusTime ω = (0 : WithTop Nat)
    · left
      simpa [Z, hct0] using hω
    · cases hct : consensusTime ω with
      | top =>
          simp [Z, hct] at hω
      | coe t =>
          cases t with
          | zero =>
              exfalso
              exact hct0 hct
          | succ t =>
              right
              refine Set.mem_iUnion.mpr ⟨t, ?_⟩
              change (match consensusTime ω with
                | ⊤ => False
                | (u : Nat) => ω u = (0, 0)) at hω
              rw [hct] at hω
              have hω00 : ω (t + 1) = (0, 0) := by
                simpa only [← WithTop.coe_one, ← WithTop.coe_add] using hω
              have hfirst := (consensusTime_eq_coe_iff ω (t + 1)).mp hct
              have hnot : ¬ reachedConsensus (ω t) :=
                hfirst.2 t (Nat.lt_succ_self t)
              have hfst : 0 < (ω t).1 := by
                exact Nat.pos_of_ne_zero fun h0 => hnot (Or.inl h0)
              have hsnd : 0 < (ω t).2 := by
                exact Nat.pos_of_ne_zero fun h0 => hnot (Or.inr h0)
              exact ⟨hfst, hsnd, hω00⟩
  have hZ0_null : P {ω : ℕ → PopState | ω 0 = (0, 0)} = 0 := by
    unfold P lvPathMeasure
    rw [show ({ω : ℕ → PopState | ω 0 = (0, 0)} : Set (ℕ → PopState)) =
        (fun ω : ℕ → PopState => ω 0) ⁻¹' ({(0, 0)} : Set PopState) from rfl]
    rw [← Measure.map_apply (measurable_pi_apply 0) (by measurability)]
    rw [homogeneousPathMeasure_dirac_marginal, kernelIter_zero, Kernel.id_apply]
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    have hne : (a, b) ≠ (0, 0) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact (Nat.ne_of_gt ha) h.1
    simp [hne]
  have hU_null :
      P (⋃ t : ℕ,
        {ω : ℕ → PopState |
          0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)}) = 0 := by
    apply measure_iUnion_null
    intro t
    exact nsd_path_interior_to_draw_step_null params (a, b) t
  apply measure_mono_null hZ_subset
  exact measure_union_null hZ0_null hU_null

private lemma nsd_species_win_partition
    (params : LVParams) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hConsensus : lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | consensusReachedEvent ω} = 1)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | majorityConsensusEvent (a, b) ω} +
      lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | majorityConsensusEvent (b, a) ω} = 1 := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  let A : Set (ℕ → PopState) := {ω | majorityConsensusEvent (a, b) ω}
  let C : Set (ℕ → PopState) := {ω | majorityConsensusEvent (b, a) ω}
  let Z : Set (ℕ → PopState) :=
    {ω | match consensusTime ω with
      | ⊤ => False
      | (t : Nat) => ω t = (0, 0)}
  have hMaj : species0Majority (a, b) := by
    exact Nat.le_of_lt hba
  have hNotMaj : ¬ species0Majority (b, a) := by
    exact Nat.not_le_of_gt hba
  have hA_meas : MeasurableSet A := by
    exact measurableSet_majorityConsensusEvent (a, b)
  have hC_meas : MeasurableSet C := by
    exact measurableSet_majorityConsensusEvent (b, a)
  have hDisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro ω hA hC
    change majorityConsensusEvent (a, b) ω at hA
    change majorityConsensusEvent (b, a) ω at hC
    unfold majorityConsensusEvent at hA hC
    cases hct : consensusTime ω with
    | top => simp [hct] at hA
    | coe t =>
        simp [hct, hMaj, hNotMaj] at hA hC
        omega
  have hCons_set :
      {ω : ℕ → PopState | consensusReachedEvent ω} =
        ⋃ t : ℕ, {ω : ℕ → PopState | consensusTime ω = ↑t} := by
    ext ω
    constructor
    · intro hω
      rcases WithTop.ne_top_iff_exists.mp
          (WithTop.lt_top_iff_ne_top.mp hω) with ⟨t, ht⟩
      exact Set.mem_iUnion.mpr ⟨t, ht.symm⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨t, ht⟩
      show consensusTime ω < ⊤
      rw [ht]
      exact WithTop.coe_lt_top t
  have hNoCons_null :
      P {ω : ℕ → PopState | ¬ consensusReachedEvent ω} = 0 := by
    have hCons_meas :
        MeasurableSet {ω : ℕ → PopState | consensusReachedEvent ω} := by
      rw [hCons_set]
      exact MeasurableSet.iUnion fun t => measurableSet_consensusTime_eq_coe t
    have hCons_ne_top :
        P {ω : ℕ → PopState | consensusReachedEvent ω} ≠ ⊤ := by
      rw [show P {ω : ℕ → PopState | consensusReachedEvent ω} = 1 by
        simpa [P] using hConsensus]
      simp
    have hcomp := measure_compl hCons_meas hCons_ne_top
    rw [show P {ω : ℕ → PopState | consensusReachedEvent ω} = 1 by
      simpa [P] using hConsensus, measure_univ] at hcomp
    simpa [Set.compl_setOf] using hcomp
  have hZ_null : P Z = 0 := by
    simpa [P, Z] using nsd_draw_at_consensus_null params a b ha hb
  have hAC_comp_subset :
      (A ∪ C)ᶜ ⊆
        {ω : ℕ → PopState | ¬ consensusReachedEvent ω} ∪ Z := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hω
    cases hct : consensusTime ω with
    | top =>
        left
        simp [consensusReachedEvent, hct]
    | coe t =>
        right
        have hcons : reachedConsensus (ω t) :=
          reachedConsensus_at_consensusTime' ω t hct
        have hnotA : ¬ ((ω t).1 > 0 ∧ (ω t).2 = 0) := by
          intro hAt
          apply hω.1
          unfold A majorityConsensusEvent
          simp [hct, hMaj, hAt]
        have hnotC : ¬ ((ω t).2 > 0 ∧ (ω t).1 = 0) := by
          intro hCt
          apply hω.2
          unfold C majorityConsensusEvent
          simp [hct, hNotMaj, hCt]
        have hfst0 : (ω t).1 = 0 := by
          rcases hcons with h0 | h0
          · exact h0
          · by_contra hne
            exact hnotA ⟨Nat.pos_of_ne_zero hne, h0⟩
        have hsnd0 : (ω t).2 = 0 := by
          rcases hcons with h0 | h0
          · by_contra hne
            exact hnotC ⟨Nat.pos_of_ne_zero hne, h0⟩
          · exact h0
        show ω ∈ Z
        simp only [Z, Set.mem_setOf_eq, hct]
        exact Prod.ext hfst0 hsnd0
  have hAC_null : P (A ∪ C)ᶜ = 0 := by
    apply measure_mono_null hAC_comp_subset
    exact measure_union_null hNoCons_null hZ_null
  have hAC_one : P (A ∪ C) = 1 := by
    have hAC_meas : MeasurableSet (A ∪ C) := hA_meas.union hC_meas
    have h := measure_add_measure_compl hAC_meas (μ := P)
    rw [hAC_null, add_zero, measure_univ] at h
    exact h
  change P A + P C = 1
  rw [← measure_union hDisj hC_meas]
  exact hAC_one

private lemma nsd_majority_consensus_eq_ratio_direct
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hConsensus : lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | consensusReachedEvent ω} = 1)
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    majorityConsensusProb .nonSelfDestructive params (a, b) =
      ENNReal.ofReal (h_ratio (a, b)) := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  let A : Set (ℕ → PopState) := {ω | majorityConsensusEvent (a, b) ω}
  let C : Set (ℕ → PopState) := {ω | majorityConsensusEvent (b, a) ω}
  have hA :
      P A ≤ ENNReal.ofReal (h_ratio (a, b)) := by
    simpa [P, A] using
      nsd_species0_win_le_ratio params hNeutral hEq0 hEq1 a b hba
  have hC :
      P C ≤ ENNReal.ofReal (h_ratio_swap (a, b)) := by
    simpa [P, C] using
      nsd_species1_win_le_ratio params hNeutral hEq0 hEq1 a b hba
  have hSum : P A + P C = 1 := by
    simpa [P, A, C] using
      nsd_species_win_partition params a b ha hb hba hConsensus
  have hRatioSum :
      ENNReal.ofReal (h_ratio (a, b)) +
          ENNReal.ofReal (h_ratio_swap (a, b)) = 1 := by
    rw [← ENNReal.ofReal_add (h_ratio_bound (a, b)).1
      (by exact (h_ratio_bound (a, b).swap).1)]
    have hden : (a : ℝ) + b ≠ 0 := by
      positivity
    have hreal : h_ratio (a, b) + h_ratio_swap (a, b) = 1 := by
      simp only [h_ratio, h_ratio_swap, PopState.swap, Prod.fst, Prod.snd]
      field_simp
      ring
    rw [hreal, ENNReal.ofReal_one]
  change P A = ENNReal.ofReal (h_ratio (a, b))
  apply le_antisymm hA
  have hRatioSub :
      (1 : ENNReal) - ENNReal.ofReal (h_ratio_swap (a, b)) =
        ENNReal.ofReal (h_ratio (a, b)) := by
    rw [← hRatioSum, ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top]
  have hPathSub : (1 : ENNReal) - P C = P A := by
    rw [← hSum, ENNReal.add_sub_cancel_right (measure_ne_top P C)]
  calc
    ENNReal.ofReal (h_ratio (a, b)) =
        1 - ENNReal.ofReal (h_ratio_swap (a, b)) := hRatioSub.symm
    _ ≤ 1 - P C := tsub_le_tsub_left hC 1
    _ = P A := hPathSub

private lemma absorb_interior_le_path_no_consensus
    (params : LVParams) (a b N : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    (kernelIter (lvKernelAbsorb .nonSelfDestructive params) N) (a, b)
      {s : PopState | 0 < s.1 ∧ 0 < s.2} ≤
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | ∀ t ≤ N, 0 < (ω t).1 ∧ 0 < (ω t).2} := by
  let K := lvKernel .nonSelfDestructive params
  let Ka := lvKernelAbsorb .nonSelfDestructive params
  let I : Set PopState := {s : PopState | 0 < s.1 ∧ 0 < s.2}
  let P : Measure (ℕ → PopState) := lvPathMeasure .nonSelfDestructive params (a, b)
  let E : Set (ℕ → PopState) := {ω | 0 < (ω N).1 ∧ 0 < (ω N).2}
  let F : Set (ℕ → PopState) := {ω | ∀ t ≤ N, 0 < (ω t).1 ∧ 0 < (ω t).2}
  have _ : 0 < a := ha
  have _ : 0 < b := hb
  have hI_meas : MeasurableSet I := by
    dsimp [I]
    measurability
  have hI_subset_fst : I ⊆ {s' : PopState | s'.1 ≠ 0} := by
    intro s hs
    exact Nat.ne_of_gt hs.1
  have hI_subset_snd : I ⊆ {s' : PopState | s'.2 ≠ 0} := by
    intro s hs
    exact Nat.ne_of_gt hs.2
  have hK_boundary :
      ∀ m s, (s.1 = 0 ∨ s.2 = 0) → (kernelIter K m) s I = 0 := by
    intro m s hs
    rcases hs with hs | hs
    · have hdead : (kernelIter (lvKernel .nonSelfDestructive params) m) s
        {s' : PopState | s'.1 ≠ 0} = 0 :=
        nsd_kernelIter_species0_dead_absorbing params s hs m
      apply le_antisymm
      · calc
          (kernelIter K m) s I ≤ (kernelIter K m) s {s' : PopState | s'.1 ≠ 0} :=
            measure_mono hI_subset_fst
          _ = 0 := by simpa [K] using hdead
      · exact zero_le
    · have hdead : (kernelIter (lvKernel .nonSelfDestructive params) m) s
        {s' : PopState | s'.2 ≠ 0} = 0 :=
        nsd_kernelIter_species1_dead_absorbing params s hs m
      apply le_antisymm
      · calc
          (kernelIter K m) s I ≤ (kernelIter K m) s {s' : PopState | s'.2 ≠ 0} :=
            measure_mono hI_subset_snd
          _ = 0 := by simpa [K] using hdead
      · exact zero_le
  have hDom : ∀ m s, (kernelIter Ka m) s I ≤ (kernelIter K m) s I := by
    intro m
    induction m with
    | zero =>
        intro s
        simp [kernelIter_zero, Kernel.id_apply]
    | succ m ih =>
        intro s
        rw [kernelIter_succ_right, kernelIter_succ_right]
        rw [Kernel.comp_apply' _ _ _ hI_meas, Kernel.comp_apply' _ _ _ hI_meas]
        have hle1 :
            ∫⁻ y, (kernelIter Ka m) y I ∂(Ka s) ≤
              ∫⁻ y, (kernelIter K m) y I ∂(Ka s) := by
          exact lintegral_mono (fun y => ih y)
        by_cases hs1 : s.1 = 0
        · have hKa_cons : Ka s = Measure.dirac s := by
            simpa [Ka] using
              lvKernelAbsorb_consensus .nonSelfDestructive params s (Or.inl hs1)
          have hmid0 : ∫⁻ y, (kernelIter K m) y I ∂(Ka s) = 0 := by
            rw [hKa_cons, lintegral_dirac]
            exact hK_boundary m s (Or.inl hs1)
          calc
            ∫⁻ y, (kernelIter Ka m) y I ∂(Ka s)
                ≤ ∫⁻ y, (kernelIter K m) y I ∂(Ka s) := hle1
            _ = 0 := hmid0
            _ ≤ ∫⁻ y, (kernelIter K m) y I ∂(K s) := zero_le
        · by_cases hs2 : s.2 = 0
          · have hKa_cons : Ka s = Measure.dirac s := by
              simpa [Ka] using
                lvKernelAbsorb_consensus .nonSelfDestructive params s (Or.inr hs2)
            have hmid0 : ∫⁻ y, (kernelIter K m) y I ∂(Ka s) = 0 := by
              rw [hKa_cons, lintegral_dirac]
              exact hK_boundary m s (Or.inr hs2)
            calc
              ∫⁻ y, (kernelIter Ka m) y I ∂(Ka s)
                  ≤ ∫⁻ y, (kernelIter K m) y I ∂(Ka s) := hle1
              _ = 0 := hmid0
              _ ≤ ∫⁻ y, (kernelIter K m) y I ∂(K s) := zero_le
          · have hs1' : 0 < s.1 := Nat.pos_of_ne_zero hs1
            have hs2' : 0 < s.2 := Nat.pos_of_ne_zero hs2
            have hKa_eq : Ka s = K s := by
              simpa [Ka, K] using
                lvKernelAbsorb_interior .nonSelfDestructive params s hs1' hs2'
            calc
              ∫⁻ y, (kernelIter Ka m) y I ∂(Ka s)
                  ≤ ∫⁻ y, (kernelIter K m) y I ∂(Ka s) := hle1
              _ = ∫⁻ y, (kernelIter K m) y I ∂(K s) := by rw [hKa_eq]
  have hMarg :
      (kernelIter K N) (a, b) I = P E := by
    dsimp [P, E, I]
    unfold lvPathMeasure
    rw [show ({ω : ℕ → PopState | 0 < (ω N).1 ∧ 0 < (ω N).2} : Set (ℕ → PopState)) =
        (fun ω : ℕ → PopState => ω N) ⁻¹' ({s : PopState | 0 < s.1 ∧ 0 < s.2} : Set PopState)
        from rfl]
    rw [← Measure.map_apply (measurable_pi_apply N) (by measurability)]
    rw [homogeneousPathMeasure_dirac_marginal
      (K := lvKernel .nonSelfDestructive params) (s₀ := (a, b)) (n := N)]
  have hDiff_sub :
      E ∩ Fᶜ ⊆
        (⋃ t ≤ N, {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω N).1 ≠ 0}) ∪
        (⋃ t ≤ N, {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω N).2 ≠ 0}) := by
    intro ω hω
    have hEN : 0 < (ω N).1 ∧ 0 < (ω N).2 := by simpa [E] using hω.1
    have hNotF : ¬ ∀ t ≤ N, 0 < (ω t).1 ∧ 0 < (ω t).2 := by
      simpa [F] using hω.2
    have hExists : ∃ t, t ≤ N ∧ ¬ (0 < (ω t).1 ∧ 0 < (ω t).2) := by
      simpa [not_forall, _root_.not_imp] using hNotF
    rcases hExists with ⟨t, htN, hIntFail⟩
    have hZero : (ω t).1 = 0 ∨ (ω t).2 = 0 := by
      by_cases h1 : (ω t).1 = 0
      · exact Or.inl h1
      · by_cases h2 : (ω t).2 = 0
        · exact Or.inr h2
        · exfalso
          exact hIntFail ⟨Nat.pos_of_ne_zero h1, Nat.pos_of_ne_zero h2⟩
    rcases hZero with h1 | h2
    · left
      exact Set.mem_iUnion₂.mpr ⟨t, htN, ⟨h1, Nat.ne_of_gt hEN.1⟩⟩
    · right
      exact Set.mem_iUnion₂.mpr ⟨t, htN, ⟨h2, Nat.ne_of_gt hEN.2⟩⟩
  have hU0_null :
      P (⋃ t ≤ N, {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω N).1 ≠ 0}) = 0 := by
    refine measure_iUnion_null ?_
    intro t
    refine measure_iUnion_null ?_
    intro htN
    have hdead :
        lvPathMeasure .nonSelfDestructive params (a, b)
          {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + (N - t))).1 ≠ 0} = 0 :=
      nsd_path_species0_dead_forward params (a, b) t (N - t)
    have hset :
        ({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω N).1 ≠ 0} : Set (ℕ → PopState)) =
          {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + (N - t))).1 ≠ 0} := by
      ext ω
      simp [Nat.add_sub_of_le htN]
    simpa [P, hset] using hdead
  have hU1_null :
      P (⋃ t ≤ N, {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω N).2 ≠ 0}) = 0 := by
    refine measure_iUnion_null ?_
    intro t
    refine measure_iUnion_null ?_
    intro htN
    have hdead :
        lvPathMeasure .nonSelfDestructive params (a, b)
          {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + (N - t))).2 ≠ 0} = 0 :=
      nsd_path_species1_dead_forward params (a, b) t (N - t)
    have hset :
        ({ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω N).2 ≠ 0} : Set (ℕ → PopState)) =
          {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + (N - t))).2 ≠ 0} := by
      ext ω
      simp [Nat.add_sub_of_le htN]
    simpa [P, hset] using hdead
  have hDiff_null : P (E ∩ Fᶜ) = 0 := by
    apply measure_mono_null hDiff_sub
    exact measure_union_null hU0_null hU1_null
  have hE_le_F : P E ≤ P F := by
    calc
      P E ≤ P (F ∪ (E ∩ Fᶜ)) := by
        apply measure_mono
        intro ω hω
        by_cases hFω : ω ∈ F
        · exact Or.inl hFω
        · exact Or.inr (by exact ⟨hω, hFω⟩)
      _ ≤ P F + P (E ∩ Fᶜ) := measure_union_le _ _
      _ = P F := by rw [hDiff_null, add_zero]
  calc
    (kernelIter (lvKernelAbsorb .nonSelfDestructive params) N) (a, b)
        {s : PopState | 0 < s.1 ∧ 0 < s.2}
        ≤ (kernelIter K N) (a, b) I := by
          simpa [Ka, I] using hDom N (a, b)
    _ = P E := hMarg
    _ ≤ P F := hE_le_F
    _ = lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | ∀ t ≤ N, 0 < (ω t).1 ∧ 0 < (ω t).2} := by
          rfl

private lemma absorb_interior_small_of_consensus
    (params : LVParams) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hConsensus : lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | consensusReachedEvent ω} = 1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    ∀ e : ENNReal, 0 < e → ∃ N : ℕ,
      (kernelIter (lvKernelAbsorb .nonSelfDestructive params) N) (a, b)
        {s : PopState | 0 < s.1 ∧ 0 < s.2} ≤ e := by
  intro e he
  by_cases hOneLe : (1 : ENNReal) ≤ e
  · refine ⟨0, le_trans ?_ hOneLe⟩
    haveI : IsProbabilityMeasure
        ((kernelIter (lvKernelAbsorb .nonSelfDestructive params) 0) (a, b)) :=
      (kernelIter_isMarkov (K := lvKernelAbsorb .nonSelfDestructive params) 0)
        |>.isProbabilityMeasure (a, b)
    calc
      (kernelIter (lvKernelAbsorb .nonSelfDestructive params) 0) (a, b)
          {s : PopState | 0 < s.1 ∧ 0 < s.2}
          ≤ (kernelIter (lvKernelAbsorb .nonSelfDestructive params) 0) (a, b) Set.univ :=
            measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · let P : Measure (ℕ → PopState) := lvPathMeasure .nonSelfDestructive params (a, b)
    haveI : IsProbabilityMeasure P := by
      dsimp [P, lvPathMeasure, homogeneousPathMeasure]
      infer_instance
    let A : ℕ → Set (ℕ → PopState) := fun N => {ω | consensusTime ω ≤ N}
    have hA_mono : Monotone A := by
      intro m n hmn ω hω
      dsimp [A] at hω ⊢
      exact le_trans hω (by exact_mod_cast hmn)
    have hA_union :
        (⋃ N : ℕ, A N) = {ω : ℕ → PopState | consensusReachedEvent ω} := by
      ext ω
      constructor
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨N, hN⟩
        exact lt_of_le_of_lt hN (WithTop.coe_lt_top N)
      · intro hω
        change consensusReachedEvent ω at hω
        rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hω) with ⟨t, ht⟩
        refine Set.mem_iUnion.mpr ⟨t, ?_⟩
        dsimp [A]
        exact le_of_eq ht.symm
    have hSup : (⨆ N : ℕ, P (A N)) = 1 := by
      calc
        (⨆ N : ℕ, P (A N)) = P (⋃ N : ℕ, A N) := by
          symm
          exact hA_mono.measure_iUnion (μ := P)
        _ = 1 := by simpa [P, hA_union] using hConsensus
    have hSubLt : (1 : ENNReal) - e < ⨆ N : ℕ, P (A N) := by
      rw [hSup]
      exact ENNReal.sub_lt_self (by simp) one_ne_zero (ne_of_gt he)
    rcases lt_iSup_iff.mp hSubLt with ⟨N, hN⟩
    have hA_meas : ∀ N, MeasurableSet (A N) := by
      intro N
      have hA_eq :
          A N = ⋃ t ≤ N, {ω : ℕ → PopState | consensusTime ω = ↑t} := by
        ext ω
        constructor
        · intro hω
          have hlt : consensusTime ω < ⊤ := lt_of_le_of_lt hω (WithTop.coe_lt_top N)
          rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hlt) with ⟨t, ht⟩
          refine Set.mem_iUnion₂.mpr ⟨t, ?_, ?_⟩
          · exact WithTop.coe_le_coe.mp (by simpa [A, ht] using hω)
          · exact ht.symm
        · intro hω
          rcases Set.mem_iUnion₂.mp hω with ⟨t, htN, htEq⟩
          dsimp [A]
          calc
            consensusTime ω = (t : WithTop ℕ) := htEq
            _ ≤ N := by exact_mod_cast htN
      rw [hA_eq]
      exact MeasurableSet.iUnion fun t =>
        MeasurableSet.iUnion fun _ => measurableSet_consensusTime_eq_coe t
    have hA_le_one : ∀ N, P (A N) ≤ 1 := by
      intro N
      calc
        P (A N) ≤ P Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hStay_subset :
        ∀ N : ℕ,
          {ω : ℕ → PopState | ∀ t ≤ N, 0 < (ω t).1 ∧ 0 < (ω t).2} ⊆
            {ω : ℕ → PopState | N < consensusTime ω} := by
      intro N ω hω
      by_contra hnot
      have hle : consensusTime ω ≤ N := le_of_not_gt hnot
      rcases (hittingAfter_le_iff.mp hle) with ⟨j, hjIcc, hjCons⟩
      have hjPos : 0 < (ω j).1 ∧ 0 < (ω j).2 := hω j hjIcc.2
      have hjReached : reachedConsensus (ω j) := by
        simpa [popCoord] using hjCons
      rcases hjReached with hj0 | hj0
      · exact (Nat.lt_irrefl 0) (by simpa [hj0] using hjPos.1)
      · exact (Nat.lt_irrefl 0) (by simpa [hj0] using hjPos.2)
    have hGt_eq_compl : ∀ N : ℕ,
        ({ω : ℕ → PopState | N < consensusTime ω} : Set (ℕ → PopState)) = (A N)ᶜ := by
      intro N
      ext ω
      simp [A, not_le]
    have hTail_le : P {ω : ℕ → PopState | N < consensusTime ω} ≤ e := by
      have hANeTop : P (A N) ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hA_le_one N)
      have hOneLt : (1 : ENNReal) < e + P (A N) := by
        exact ENNReal.lt_add_of_sub_lt_left (Or.inl (by simp)) hN
      have hCompLt : (1 : ENNReal) - P (A N) < e := by
        exact (ENNReal.sub_lt_iff_lt_right hANeTop (hA_le_one N)).2
          (by simpa [add_comm] using hOneLt)
      rw [hGt_eq_compl N, measure_compl (hA_meas N) hANeTop, measure_univ]
      exact le_of_lt hCompLt
    refine ⟨N, ?_⟩
    calc
      (kernelIter (lvKernelAbsorb .nonSelfDestructive params) N) (a, b)
          {s : PopState | 0 < s.1 ∧ 0 < s.2}
          ≤ P {ω : ℕ → PopState | ∀ t ≤ N, 0 < (ω t).1 ∧ 0 < (ω t).2} :=
            by simpa [P] using absorb_interior_le_path_no_consensus params a b N ha hb
      _ ≤ P {ω : ℕ → PopState | N < consensusTime ω} :=
        measure_mono (hStay_subset N)
      _ ≤ e := hTail_le

private lemma absorb_majority_iSup_ge_h_of_consensus
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1)
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    (hIterAll : ∀ N, ∫ x, h x ∂(kernelIter
        (lvKernelAbsorb .nonSelfDestructive params) N) (a, b) = h (a, b))
    (hConsensus : lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | consensusReachedEvent ω} = 1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    ENNReal.ofReal (h (a, b)) ≤
      (⨆ N : ℕ, (kernelIter (lvKernelAbsorb .nonSelfDestructive params) N) (a, b)
        {s : PopState | 0 < s.1 ∧ s.2 = 0}) := by
  set Ka := lvKernelAbsorb .nonSelfDestructive params
  set μ : ℕ → Measure PopState := fun N => (kernelIter Ka N) (a, b)
  set Splus : Set PopState := {s : PopState | 0 < s.1 ∧ s.2 = 0}
  set I : Set PopState := {s : PopState | 0 < s.1 ∧ 0 < s.2}
  have hμ_prob : ∀ N, IsProbabilityMeasure (μ N) := by
    intro N
    dsimp [μ, Ka]
    exact (kernelIter_isMarkov (K := lvKernelAbsorb .nonSelfDestructive params) N)
      |>.isProbabilityMeasure (a, b)
  have hSplus_meas : MeasurableSet Splus := by
    dsimp [Splus]
    measurability
  have hI_meas : MeasurableSet I := by
    dsimp [I]
    measurability
  have hInt : ∀ N, Integrable h (μ N) := by
    intro N
    haveI : IsProbabilityMeasure (μ N) := hμ_prob N
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h).aestronglyMeasurable
    filter_upwards with s
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(hBound s).1], (hBound s).2⟩
  have hSplus_val : ∀ s ∈ Splus, h s = 1 := by
    intro s hs
    rcases s with ⟨a', b'⟩
    simp only [Splus, Set.mem_setOf_eq] at hs
    simpa [hs.2] using hBnd1 a' hs.1
  have hI_subset_comp : I ⊆ Splusᶜ := by
    intro s hsI hsS
    exact (Nat.ne_of_gt hsI.2) hsS.2
  have hStep : ∀ N, ENNReal.ofReal (h (a, b)) ≤ (μ N) Splus + (μ N) I := by
    intro N
    let g : PopState → ℝ := Set.indicator I (fun _ => (1 : ℝ))
    have hDecomp : ∫ x, h x ∂(μ N) =
        ∫ x in Splus, h x ∂(μ N) + ∫ x in Splusᶜ, h x ∂(μ N) := by
      symm
      exact integral_add_compl hSplus_meas (hInt N)
    have hSplusInt : ∫ x in Splus, h x ∂(μ N) = ((μ N) Splus).toReal := by
      trans ∫ x in Splus, (1 : ℝ) ∂(μ N)
      · exact setIntegral_congr_fun hSplus_meas (fun x hx => hSplus_val x hx)
      · rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    have hInt_h_restrict : Integrable h ((μ N).restrict Splusᶜ) := by
      haveI : IsFiniteMeasure ((μ N).restrict Splusᶜ) := by infer_instance
      apply Integrable.mono (integrable_const (1 : ℝ))
        (measurable_of_countable h).aestronglyMeasurable
      filter_upwards with s
      simp only [Real.norm_eq_abs, norm_one]
      exact abs_le.mpr ⟨by linarith [(hBound s).1], (hBound s).2⟩
    have hInt_g_restrict : Integrable g ((μ N).restrict Splusᶜ) := by
      haveI : IsFiniteMeasure ((μ N).restrict Splusᶜ) := by infer_instance
      apply Integrable.mono (integrable_const (1 : ℝ))
        (measurable_of_countable g).aestronglyMeasurable
      filter_upwards with s
      by_cases hsI : s ∈ I
      · simp [g, hsI]
      · simp [g, hsI]
    have hpoint : ∀ x ∈ Splusᶜ, h x ≤ g x := by
      intro x hxcomp
      rcases x with ⟨a', b'⟩
      by_cases hsI : 0 < a' ∧ 0 < b'
      · have hg : g (a', b') = 1 := by simp [g, I, hsI]
        have hh : h (a', b') ≤ 1 := (hBound (a', b')).2
        linarith
      · have hxcomp' : ¬ (0 < a' ∧ b' = 0) := by
          simpa [Splus, Set.mem_setOf_eq] using hxcomp
        have ha0 : a' = 0 := by
          by_contra ha0
          have ha' : 0 < a' := Nat.pos_of_ne_zero ha0
          have hnb : ¬ 0 < b' := by
            intro hb'
            exact hsI ⟨ha', hb'⟩
          have hb0 : b' = 0 := Nat.eq_zero_of_not_pos hnb
          exact hxcomp' ⟨ha', hb0⟩
        have hh0 : h (a', b') = 0 := by
          simpa [ha0] using hBnd0 b'
        have hg0 : g (a', b') = 0 := by
          simp [g, I, ha0]
        rw [hh0, hg0]
    have hAE : (fun x => h x) ≤ᵐ[(μ N).restrict Splusᶜ] g := by
      exact ae_restrict_of_forall_mem hSplus_meas.compl (fun x hx => hpoint x hx)
    have hComp_le_g :
        ∫ x in Splusᶜ, h x ∂(μ N) ≤ ∫ x in Splusᶜ, g x ∂(μ N) := by
      simpa using integral_mono_ae hInt_h_restrict hInt_g_restrict hAE
    have hG_eval : ∫ x in Splusᶜ, g x ∂(μ N) = ((μ N) I).toReal := by
      rw [show g = Set.indicator I (fun _ => (1 : ℝ)) from rfl]
      rw [MeasureTheory.integral_indicator hI_meas]
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      rw [Measure.restrict_apply hI_meas]
      rw [Set.inter_eq_left.mpr hI_subset_comp]
    have hComp_leI : ∫ x in Splusᶜ, h x ∂(μ N) ≤ ((μ N) I).toReal := by
      exact hComp_le_g.trans_eq hG_eval
    have hReal_le : h (a, b) ≤ ((μ N) Splus).toReal + ((μ N) I).toReal := by
      rw [← hIterAll N, hDecomp, hSplusInt]
      linarith
    have hμS_ne_top : (μ N) Splus ≠ ⊤ := by
      haveI : IsProbabilityMeasure (μ N) := hμ_prob N
      exact measure_ne_top _ _
    have hμI_ne_top : (μ N) I ≠ ⊤ := by
      haveI : IsProbabilityMeasure (μ N) := hμ_prob N
      exact measure_ne_top _ _
    calc
      ENNReal.ofReal (h (a, b))
          ≤ ENNReal.ofReal (((μ N) Splus).toReal + ((μ N) I).toReal) :=
            ENNReal.ofReal_le_ofReal hReal_le
      _ = ENNReal.ofReal (((μ N) Splus).toReal) + ENNReal.ofReal (((μ N) I).toReal) := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
      _ = (μ N) Splus + (μ N) I := by
            rw [ENNReal.ofReal_toReal hμS_ne_top, ENNReal.ofReal_toReal hμI_ne_top]
  have hInterior_small :
      ∀ e : ENNReal, 0 < e → ∃ N : ℕ, (μ N) I ≤ e := by
    intro e he
    simpa [μ, Ka, I] using
      absorb_interior_small_of_consensus params a b ha hb hConsensus e he
  set B : ENNReal := ⨆ N : ℕ, (μ N) Splus
  have hBnd : ENNReal.ofReal (h (a, b)) ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hB_ne_top
    rcases hInterior_small (ε : ENNReal) (by exact_mod_cast hε) with ⟨N, hNI⟩
    calc
      ENNReal.ofReal (h (a, b))
          ≤ (μ N) Splus + (μ N) I := hStep N
      _ ≤ B + ε := add_le_add (le_iSup (fun n => (μ n) Splus) N) hNI
  simpa [B, μ, Ka, Splus] using hBnd

private lemma absorb_majority_iSup_eq_h
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1)
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    (hIterAll : ∀ N, ∫ x, h x ∂(kernelIter
        (lvKernelAbsorb .nonSelfDestructive params) N) (a, b) = h (a, b))
    (hConsensus : lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | consensusReachedEvent ω} = 1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    (⨆ N : ℕ, (kernelIter (lvKernelAbsorb .nonSelfDestructive params) N) (a, b)
      {s : PopState | 0 < s.1 ∧ s.2 = 0}) = ENNReal.ofReal (h (a, b)) := by
  set Ka := lvKernelAbsorb .nonSelfDestructive params
  set μ : ℕ → Measure PopState := fun N => (kernelIter Ka N) (a, b)
  set Splus : Set PopState := {s : PopState | 0 < s.1 ∧ s.2 = 0}
  have hμ_prob : ∀ N, IsProbabilityMeasure (μ N) := by
    intro N
    dsimp [μ, Ka]
    exact (kernelIter_isMarkov (K := lvKernelAbsorb .nonSelfDestructive params) N)
      |>.isProbabilityMeasure (a, b)
  have hSplus_meas : MeasurableSet Splus := by
    dsimp [Splus]
    measurability
  have hInt : ∀ N, Integrable h (μ N) := by
    intro N
    haveI : IsProbabilityMeasure (μ N) := hμ_prob N
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h).aestronglyMeasurable
    filter_upwards with s
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(hBound s).1], (hBound s).2⟩
  have hSplus_val : ∀ s ∈ Splus, h s = 1 := by
    intro s hs
    rcases s with ⟨a', b'⟩
    simp only [Splus, Set.mem_setOf_eq] at hs
    simpa [hs.2] using hBnd1 a' hs.1
  have hSup_le : (⨆ N : ℕ, (μ N) Splus) ≤ ENNReal.ofReal (h (a, b)) := by
    refine iSup_le ?_
    intro N
    have hDecomp : ∫ x, h x ∂(μ N) =
        ∫ x in Splus, h x ∂(μ N) + ∫ x in Splusᶜ, h x ∂(μ N) := by
      symm
      exact integral_add_compl hSplus_meas (hInt N)
    have hSplusInt : ∫ x in Splus, h x ∂(μ N) = ((μ N) Splus).toReal := by
      trans ∫ x in Splus, (1 : ℝ) ∂(μ N)
      · exact setIntegral_congr_fun hSplus_meas (fun x hx => hSplus_val x hx)
      · rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    have hComp_nonneg : 0 ≤ ∫ x in Splusᶜ, h x ∂(μ N) := by
      exact integral_nonneg (fun s => (hBound s).1)
    have hToReal_le : ((μ N) Splus).toReal ≤ h (a, b) := by
      rw [← hIterAll N, hDecomp, hSplusInt]
      linarith
    have hμN_ne_top : (μ N) Splus ≠ ⊤ := by
      haveI : IsProbabilityMeasure (μ N) := hμ_prob N
      exact measure_ne_top _ _
    calc
      (μ N) Splus = ENNReal.ofReal (((μ N) Splus).toReal) := by
        rw [ENNReal.ofReal_toReal hμN_ne_top]
      _ ≤ ENNReal.ofReal (h (a, b)) := ENNReal.ofReal_le_ofReal hToReal_le
  have hSup_ge : ENNReal.ofReal (h (a, b)) ≤ (⨆ N : ℕ, (μ N) Splus) := by
    simpa [μ, Ka, Splus] using
      absorb_majority_iSup_ge_h_of_consensus params h a b ha hb hba
        hBound hBnd1 hBnd0 hIterAll hConsensus
  exact le_antisymm hSup_le hSup_ge

/-- Paper `thm:nsd-intra` Part 2, generalized to arbitrary β,δ ≥ 0.
    For a neutral NSD LV chain with α=γ>0 and initial state (a,b) with a≥b>0:
    ρ(S) = a/(a+b).
    Compared to `thm_nsd_intra`, this removes the β=δ=0 restriction. -/
theorem thm_nsd_intra_general
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    majorityConsensusProb LVVariant.nonSelfDestructive params (a, b) =
      ENNReal.ofReal ((a : Real) / (a + b)) := by
  have hGamma0 : 0 < params.gamma0 := by rw [hEq0]; linarith
  have hGamma1 : 0 < params.gamma1 := by rw [hEq1, ← hNeutral]; linarith
  have hAlphaSum : 0 < params.alpha0 + params.alpha1 := by
    linarith [hNeutral.symm ▸ hAlpha]
  have hConsensus := nsd_consensus_almost_sure_general params
    hGamma0 hGamma1 hAlphaSum a b hposA hposB hAlpha hNeutral hEq0 hEq1
  rcases Nat.eq_or_lt_of_le hba with hab | hba_strict
  · rw [hab] at hConsensus ⊢
    rw [show ENNReal.ofReal ((a : Real) / (a + a)) = ENNReal.ofReal (1 / (2 : Real)) by
      have : (a : ℝ) / ((a : ℝ) + a) = 1 / (2 : ℝ) := by
        field_simp
        ring
      rw [this]]
    have hGammaEq : params.gamma0 = params.gamma1 := by
      rw [hEq0, hEq1, hNeutral]
    have hle_half :
        majorityConsensusProb LVVariant.nonSelfDestructive params (a, a) ≤
          ENNReal.ofReal (1 / (2 : Real)) :=
      lemma_identical_gap_fail .nonSelfDestructive params hNeutral hGammaEq a
    -- Diagonal case: swap invariance + consensus a.s. should give the reverse
    -- inequality, yielding equality at 1/2.
    apply le_antisymm hle_half
    set P := lvPathMeasure .nonSelfDestructive params (a, a) with hP_def
    haveI : IsProbabilityMeasure P := by
      rw [hP_def]
      unfold lvPathMeasure homogeneousPathMeasure
      infer_instance
    set A := {ω : ℕ → PopState | majorityConsensusEvent (a, a) ω}
    set C := {ω : ℕ → PopState | majorityConsensusEvent (a, a) (swapTraj ω)}
    have hswap_meas : Measurable swapTraj := by
      rw [measurable_pi_iff]
      intro n
      exact (measurable_of_countable PopState.swap).comp (measurable_pi_apply n)
    have hA_meas : MeasurableSet A := measurableSet_majorityConsensusEvent_diag a
    have hC_eq : C = swapTraj ⁻¹' A := Set.ext fun ω => Iff.rfl
    have hC_meas : MeasurableSet C := hC_eq ▸ hA_meas.preimage hswap_meas
    have h_inv : P.map swapTraj = P := by
      simpa [P] using
        (lvPathMeasure_swap_invariant .nonSelfDestructive params hNeutral hGammaEq a)
    have hA_eq_C : P A = P C := by
      rw [hC_eq, ← Measure.map_apply hswap_meas hA_meas, h_inv]
    have h_disj : Disjoint A C := disjoint_majorityConsensus_swap_diag a
    have h_step_to00_zero :
        ∀ t : ℕ, P {ω | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)} = 0 := by
      intro t
      let K := lvKernel LVVariant.nonSelfDestructive params
      let g : PopState → ENNReal := fun x => if 0 < x.1 ∧ 0 < x.2 then 1 else 0
      let φ : PopState → ENNReal := fun y => if y = (0, 0) then 1 else 0
      have hgm : Measurable g := by measurability
      have hφm : Measurable φ := by measurability
      have hmeas :
          MeasurableSet {ω' : ℕ → PopState | 0 < (ω' t).1 ∧ 0 < (ω' t).2 ∧ ω' (t + 1) = (0, 0)} := by
        measurability
      rw [hP_def]
      unfold lvPathMeasure
      have hconv :
          (homogeneousPathMeasure (Measure.dirac (a, a)) K)
            {ω | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)} =
            ∫⁻ ω', g (ω' t) * φ (ω' (t + 1)) ∂(homogeneousPathMeasure (Measure.dirac (a, a)) K) := by
        rw [← lintegral_indicator_one hmeas]
        congr 1
        ext ω'
        simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
        split_ifs <;> simp_all
      rw [hconv, homogeneousPathMeasure_joint_lintegral K (a, a) t g φ hgm hφm]
      have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {(0, 0)} := by
        intro x
        have : φ = Set.indicator ({(0, 0)} : Set PopState) 1 := by
          ext y
          simp only [φ, Set.indicator, Set.mem_singleton_iff, Pi.one_apply]
        rw [this]
        exact lintegral_indicator_one (by measurability)
      simp_rw [hinner]
      have hzero :
          ∀ x : PopState, g x * K x {(0, 0)} = 0 := by
        intro x
        rcases x with ⟨x0, x1⟩
        by_cases hx : 0 < x0 ∧ 0 < x1
        · have hK00 : K (x0, x1) {(0, 0)} = 0 := by
            by_cases hφ0 : lvTotalPropensity params (x0, x1) = 0
            · rw [show K (x0, x1) = Measure.dirac (x0, x1) by
                  simpa [K] using
                    (lvKernel_apply_zero_propensity .nonSelfDestructive params (x0, x1) hφ0)]
              rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
              have hne : (x0, x1) ≠ (0, 0) := by
                intro h
                simp only [Prod.mk.injEq] at h
                exact (Nat.ne_of_gt hx.1) h.1
              simp [hne]
            · rw [show K (x0, x1) = (lvKernel .nonSelfDestructive params) (x0, x1) by rfl]
              rw [lvKernel_nsd_apply params x0 x1 hφ0]
              simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply]
              simp [hx.1.ne', hx.2.ne']
          simp [g, hx, hK00]
        · simp [g, hx]
      simp_rw [hzero]
      exact lintegral_zero
    let Z : Set (ℕ → PopState) := {ω | match consensusTime ω with
      | ⊤ => False
      | (t : Nat) => ω t = (0, 0)}
    have hZ_subset :
        Z ⊆ {ω : ℕ → PopState | ω 0 = (0, 0)} ∪
          ⋃ t : ℕ, {ω : ℕ → PopState | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)} := by
      intro ω hω
      by_cases hct0 : consensusTime ω = (0 : WithTop Nat)
      · left
        simpa [Z, hct0] using hω
      · cases hct : consensusTime ω with
        | top =>
            simp [Z, hct] at hω
        | coe t =>
            cases t with
            | zero =>
                exfalso
                exact hct0 hct
            | succ t =>
                right
                refine Set.mem_iUnion.mpr ⟨t, ?_⟩
                change (match consensusTime ω with
                  | ⊤ => False
                  | (u : Nat) => ω u = (0, 0)) at hω
                rw [hct] at hω
                have hω00 : ω (t + 1) = (0, 0) := by
                  simpa only [← WithTop.coe_one, ← WithTop.coe_add] using hω
                have hfirst := (consensusTime_eq_coe_iff ω (t + 1)).mp hct
                have hnot_cons_t : ¬ reachedConsensus (ω t) := hfirst.2 t (Nat.lt_succ_self t)
                have hfst_pos : 0 < (ω t).1 := by
                  have hfst_ne : (ω t).1 ≠ 0 := by
                    intro h0
                    exact hnot_cons_t (Or.inl h0)
                  exact Nat.pos_of_ne_zero hfst_ne
                have hsnd_pos : 0 < (ω t).2 := by
                  have hsnd_ne : (ω t).2 ≠ 0 := by
                    intro h0
                    exact hnot_cons_t (Or.inr h0)
                  exact Nat.pos_of_ne_zero hsnd_ne
                exact ⟨hfst_pos, hsnd_pos, hω00⟩
    have hZ0_null : P {ω : ℕ → PopState | ω 0 = (0, 0)} = 0 := by
      rw [hP_def]
      unfold lvPathMeasure
      rw [show ({ω : ℕ → PopState | ω 0 = (0, 0)} : Set (ℕ → PopState)) =
          (fun ω : ℕ → PopState => ω 0) ⁻¹' ({(0, 0)} : Set PopState) from rfl]
      rw [← Measure.map_apply (measurable_pi_apply 0) (by measurability)]
      rw [homogeneousPathMeasure_dirac_marginal
        (K := lvKernel .nonSelfDestructive params) (s₀ := (a, a)) (n := 0)]
      rw [kernelIter_zero, Kernel.id_apply]
      rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
      have hne : (a, a) ≠ (0, 0) := by
        intro h
        simp only [Prod.mk.injEq] at h
        exact (Nat.ne_of_gt hposA) h.1
      simp [hne]
    have hZ_null : P Z = 0 := by
      apply measure_mono_null hZ_subset
      have hU_null :
          P (⋃ t : ℕ, {ω : ℕ → PopState | 0 < (ω t).1 ∧ 0 < (ω t).2 ∧ ω (t + 1) = (0, 0)}) = 0 :=
        measure_iUnion_null h_step_to00_zero
      exact measure_union_null hZ0_null hU_null
    have hCons_set :
        {ω : ℕ → PopState | consensusReachedEvent ω} =
          ⋃ t : ℕ, {ω : ℕ → PopState | consensusTime ω = ↑t} := by
      ext ω
      constructor
      · intro hω
        rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hω) with ⟨t, ht⟩
        exact Set.mem_iUnion.mpr ⟨t, ht.symm⟩
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨t, ht⟩
        show consensusTime ω < ⊤
        rw [ht]
        exact WithTop.coe_lt_top t
    have hNoCons_null : P {ω : ℕ → PopState | ¬ consensusReachedEvent ω} = 0 := by
      have hCons_meas : MeasurableSet {ω : ℕ → PopState | consensusReachedEvent ω} := by
        rw [hCons_set]
        exact MeasurableSet.iUnion fun t => measurableSet_consensusTime_eq_coe t
      have hCons_ne_top : P {ω : ℕ → PopState | consensusReachedEvent ω} ≠ ⊤ := by
        rw [hConsensus]
        simp
      have hcomp := measure_compl hCons_meas hCons_ne_top
      rw [hConsensus, measure_univ] at hcomp
      simpa [Set.compl_setOf] using hcomp
    have hAC_comp_subset :
        (A ∪ C)ᶜ ⊆ {ω : ℕ → PopState | ¬ consensusReachedEvent ω} ∪ Z := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hω
      cases hct : consensusTime ω with
      | top =>
          left
          simp [consensusReachedEvent, hct]
      | coe t =>
          right
          have hcons : reachedConsensus (ω t) := reachedConsensus_at_consensusTime' ω t hct
          have hnotA : ¬ ((ω t).1 > 0 ∧ (ω t).2 = 0) := by
            intro hAt
            exact hω.1 ((majorityConsensusEvent_diag_iff a ω).2 (by simpa [hct] using hAt))
          have hnotC : ¬ ((ω t).2 > 0 ∧ (ω t).1 = 0) := by
            intro hCt
            exact hω.2 ((majorityConsensusEvent_swapTraj_diag a ω).2 (by simpa [hct] using hCt))
          have hfst0 : (ω t).1 = 0 := by
            rcases hcons with h0 | h0
            · exact h0
            · by_contra hne
              have hpos : 0 < (ω t).1 := Nat.pos_of_ne_zero hne
              exact hnotA ⟨hpos, h0⟩
          have hsnd0 : (ω t).2 = 0 := by
            rcases hcons with h0 | h0
            · by_contra hne
              have hpos : 0 < (ω t).2 := Nat.pos_of_ne_zero hne
              exact hnotC ⟨hpos, h0⟩
            · exact h0
          show ω ∈ Z
          simp only [Z, Set.mem_setOf_eq, hct]
          exact Prod.ext hfst0 hsnd0
    have hAC_null : P (A ∪ C)ᶜ = 0 := by
      apply measure_mono_null hAC_comp_subset
      exact measure_union_null hNoCons_null hZ_null
    have hAC_one : P (A ∪ C) = 1 := by
      have hAC_meas : MeasurableSet (A ∪ C) := hA_meas.union hC_meas
      have h1 := measure_add_measure_compl hAC_meas (μ := P)
      rw [hAC_null, add_zero, measure_univ] at h1
      exact h1
    have hsum : P A + P C = 1 := by
      rw [← measure_union h_disj hC_meas]
      exact hAC_one
    have htwice : P A + P A = 1 := hA_eq_C ▸ hsum
    have hPA : P A = (2 : ENNReal)⁻¹ := by
      have : P A + P A = 1 := htwice
      have hfin : P A ≠ ⊤ := measure_ne_top _ _
      rwa [← two_mul, ← ENNReal.eq_div_iff (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤), one_div] at this
    rw [show ENNReal.ofReal (1 / (2 : ℝ)) = (2 : ENNReal)⁻¹ from by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [ENNReal.ofReal_ofNat]]
    change (2 : ENNReal)⁻¹ ≤ P A
    exact hPA.ge
  · rw [← h_ratio_def]
    exact nsd_majority_consensus_eq_ratio_direct params hNeutral hEq0 hEq1
      a b hposA hposB hba_strict hConsensus

end LVConsensus
