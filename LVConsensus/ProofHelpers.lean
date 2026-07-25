/-
  ProofHelpers.lean
  Reusable helper lemmas for the paper-facing probability proofs.

  Sections:
    § 1  Harmonic sum bounds  →  bd_expected_births_logarithmic_unconditional
    § 2  Algebraic probability lower bound  →  lemma_log_individual_events (SelfDestructiveLower)
    § 3  Kernel individual-event bounds  →  same
    § 4  Discrete descending IVT  →  same
    § 5  Stochastic domination via coupling  →  paper chain-domination lemma
-/

import LVConsensus.Definitions
import LVConsensus.Helpers
import LVConsensus.MarkovLib
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

/-! -----------------------------------------------------------------------
    § 1  Harmonic sum bounds
    ----------------------------------------------------------------------- -/

/-- The harmonic sum as a real equals ∑_{k<n} 1/(k+1).
    Bridge from Mathlib's ℚ-valued `harmonic` to ℝ sums used in MarkovLib. -/
lemma harmonic_cast_eq_sum_real (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
  have heq : (harmonic n : ℝ) = ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)⁻¹ := by
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq]
  congr 1; ext k; push_cast; ring

/-- The real harmonic sum ∑_{k<n} 1/(k+1) ≤ Real.log n + 1.
    Used in the unconditional expected-births proof:
    E[B_R] ≤ C · H_n ≤ C · (log n + 1). -/
lemma harmonic_sum_real_le_log_add_one (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) ≤ Real.log n + 1 := by
  have h := harmonic_le_one_add_log n  -- (harmonic n : ℝ) ≤ 1 + Real.log n
  rw [← harmonic_cast_eq_sum_real]; linarith

/-- Alias with i+1 denominator form. -/
lemma harmonic_sum_one_to_n_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) ≤ Real.log n + 1 :=
  harmonic_sum_real_le_log_add_one n

/-- For p(m) ≤ C/m, the sum ∑_{i<n} p(n-i) ≤ C·(log n + 1).
    Paper: "E[B_R] ≤ C · H_n" in proof of lemma:nice-expected-births. -/
lemma nice_birth_prob_harmonic_sum (C : ℝ) (hC : 0 < C) (n : ℕ) (hn : 0 < n)
    (p : ℕ → ℝ) (hp : ∀ m, 0 < m → p m ≤ C / m) :
    ∑ i ∈ Finset.range n, p (n - i) ≤ C * (Real.log n + 1) := by
  -- Step 1: p(n-i) ≤ C/(n-i:ℕ) for each i < n; collect the sum
  have hle : ∑ i ∈ Finset.range n, p (n - i) ≤
      ∑ i ∈ Finset.range n, C / ((n - i : ℕ) : ℝ) :=
    Finset.sum_le_sum fun i hi =>
      hp (n - i) (Nat.sub_pos_of_lt (Finset.mem_range.mp hi))
  -- Step 2: factor out C; reindex ∑_{i<n} 1/(n-i) = ∑_{k<n} 1/(k+1)
  have hreindex : ∑ i ∈ Finset.range n, (1 : ℝ) / ((n - i : ℕ) : ℝ) =
      ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun k => (1 : ℝ) / ((k : ℝ) + 1)) n]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < n := Finset.mem_range.mp hi
    congr 1
    -- (n-1-i:ℕ)+1 = n-i as ℕ for i < n, so their casts are equal
    norm_cast; omega
  calc ∑ i ∈ Finset.range n, p (n - i)
      ≤ ∑ i ∈ Finset.range n, C / ((n - i : ℕ) : ℝ) := hle
    _ = C * ∑ i ∈ Finset.range n, (1 : ℝ) / ((n - i : ℕ) : ℝ) := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
    _ = C * ∑ k ∈ Finset.range n, (1 : ℝ) / ((k : ℝ) + 1) := by rw [hreindex]
    _ ≤ C * (Real.log n + 1) :=
          mul_le_mul_of_nonneg_left (harmonic_sum_real_le_log_add_one n) hC.le

/-! -----------------------------------------------------------------------
    § 2  Non-competitive event probability lower bound (algebra)
    Paper ref: § 5, proof of lemma:log-individual-events, line 730
    ----------------------------------------------------------------------- -/

/-- Algebraic core: θ/(αk+2θ) ≤ θ(a+k)/(θ(a+k)+αak) for a ≥ k > 0, α ≥ 0, θ > 0.
    Cross-multiplied: 0 ≤ θ·α·k² + θ²·(a+k). -/
lemma noncompetitive_prob_lb (a k α θ : ℝ)
    (hk : 0 < k) (ha : k ≤ a) (hα : 0 ≤ α) (hθ : 0 < θ) :
    θ / (α * k + 2 * θ) ≤ θ * (a + k) / (θ * (a + k) + α * a * k) := by
  have ha_pos : 0 < a := by linarith
  have hak : 0 < a + k := by linarith
  have hdenom1 : 0 < α * k + 2 * θ := by nlinarith
  have hdenom2 : 0 < θ * (a + k) + α * a * k := by
    have := mul_pos hθ hak
    nlinarith [mul_nonneg (mul_nonneg hα ha_pos.le) hk.le]
  rw [div_le_div_iff₀ hdenom1 hdenom2]
  nlinarith [mul_nonneg (mul_nonneg hθ.le hα) (mul_nonneg hk.le hk.le),
             mul_nonneg (mul_nonneg hθ.le hθ.le) hak.le,
             mul_nonneg hα (mul_nonneg hk.le (sub_nonneg.mpr ha))]

/-- Nat version for LV parameters. -/
lemma noncompetitive_prob_lb_nat (params : LVParams) (a b : ℕ)
    (hab : b ≤ a) (hb : 0 < b)
    (hTheta : 0 < params.beta + params.delta) :
    (params.beta + params.delta) /
        ((params.alpha0 + params.alpha1) * b + 2 * (params.beta + params.delta)) ≤
      (params.beta + params.delta) * (a + b) /
        ((params.beta + params.delta) * (a + b) +
          (params.alpha0 + params.alpha1) * a * b) := by
  apply noncompetitive_prob_lb
  · exact_mod_cast hb
  · exact_mod_cast hab
  · have := params.alpha0_nonneg; have := params.alpha1_nonneg; linarith
  · exact hTheta

/-! -----------------------------------------------------------------------
    § 3  LV kernel individual-event probability bounds
    ----------------------------------------------------------------------- -/

/-- For SD with γ₀=γ₁=0, P(individual event at (a,b)) = θ(a+b)/φ.
    Since competitive events go to (a-1,b-1), not counted here. -/
lemma lvKernel_sd_indiv_event_measure (params : LVParams) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0) :
    let θ := params.beta + params.delta
    let φ := lvTotalPropensity params (a, b)
    (lvKernel .selfDestructive params (a, b))
        {s | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
             (s.1 = a - 1 ∧ s.2 = b ∧ s ≠ (a - 1, b - 1)) ∨
             (s.1 = a ∧ s.2 = b - 1 ∧ s ≠ (a - 1, b - 1))} =
      ENNReal.ofReal (θ * (a + b) / φ) := by
  -- Case split on whether the propensity is zero
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · -- φ = 0 ⟹ kernel = dirac(a,b); (a,b) ∉ S, so LHS = 0. RHS = θ*(a+b)/0 = 0. ✓
    rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    simp only [hφ, div_zero, ENNReal.ofReal_zero, Measure.dirac_apply]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
      all_goals (first | exact absurd h1 (by omega) | exact absurd h2 (by omega))
    · rfl
  · -- φ ≠ 0: unfold the SD kernel and compute
    set S := {s : PopState | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
               (s.1 = a - 1 ∧ s.2 = b ∧ s ≠ (a - 1, b - 1)) ∨
               (s.1 = a ∧ s.2 = b - 1 ∧ s ≠ (a - 1, b - 1))}
    -- Membership facts for Dirac evaluations
    have hS_b0 : (a + 1, b) ∈ S := Or.inl ⟨rfl, rfl⟩
    have hS_b1 : (a, b + 1) ∈ S := Or.inr (Or.inl ⟨rfl, rfl⟩)
    have hS_d0 : (a - 1, b) ∈ S := Or.inr (Or.inr (Or.inl ⟨rfl, rfl,
      fun heq => by have := Prod.ext_iff.mp heq; simp at this; omega⟩))
    have hS_d1 : (a, b - 1) ∈ S := Or.inr (Or.inr (Or.inr ⟨rfl, rfl,
      fun heq => by have := Prod.ext_iff.mp heq; simp at this; omega⟩))
    have hS_comp : (a - 1, b - 1) ∉ S := by
      simp only [S, Set.mem_setOf_eq]
      push_neg
      exact ⟨by omega, by omega, fun _ => by omega, fun _ => by omega⟩
    -- Propensity is positive (since p,q ≥ 0 and hφ ≠ 0)
    have hφ_pos : 0 < lvTotalPropensity params (a, b) :=
      lt_of_le_of_ne (lvTotalPropensity_nonneg params (a, b)) (Ne.symm hφ)
    -- (lvTotalPropensity_nonneg from MarkovLib)
    have hinvφ : (0 : ℝ) ≤ 1 / lvTotalPropensity params (a, b) :=
      div_nonneg zero_le_one hφ_pos.le
    -- Weight nonnegativity
    have h1 : (0:ℝ) ≤ params.beta * a := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have h2 : (0:ℝ) ≤ params.beta * b := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have h3 : (0:ℝ) ≤ params.delta * a := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have h4 : (0:ℝ) ≤ params.delta * b := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    -- φ expressed with γ=0
    have hφ_eq : lvTotalPropensity params (a, b) =
        params.beta * (a:ℝ) + params.beta * (b:ℝ) + params.delta * (a:ℝ) +
        params.delta * (b:ℝ) + params.alpha0 * (a:ℝ) * (b:ℝ) +
        params.alpha1 * (a:ℝ) * (b:ℝ) := by
      unfold lvTotalPropensity; rw [hGamma0, hGamma1]; push_cast; ring
    -- Compute the kernel measure on S: competitive Dirac ∉ S, so contribute 0
    have hcomp_zero : Measure.dirac (a - 1, b - 1) S = 0 := by
      simp [Measure.dirac_apply, Set.indicator_apply, hS_comp]
    rw [lvKernel_sd_apply params a b hφ, hGamma0, hGamma1]
    simp only [zero_mul, ENNReal.ofReal_zero, zero_smul, add_zero, Measure.smul_apply,
               Measure.add_apply, smul_eq_mul, Measure.dirac_apply_of_mem hS_b0,
               Measure.dirac_apply_of_mem hS_b1, Measure.dirac_apply_of_mem hS_d0,
               Measure.dirac_apply_of_mem hS_d1, mul_one, hcomp_zero, mul_zero]
    -- Combine: ofReal(1/φ) * (ofReal(β*a) + ofReal(β*b) + ofReal(δ*a) + ofReal(δ*b))
    --        = ofReal((β+δ)*(a+b)/φ)
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3,
        ← ENNReal.ofReal_add (by linarith) h4, ← ENNReal.ofReal_mul hinvφ]
    congr 1
    push_cast
    field_simp [hφ_pos.ne']
    linarith [hφ_eq]

/-- For SD with γ=0 and a ≥ b ≥ 1, P(individual event) ≥ θ/(αb+2θ). -/
lemma lvKernel_sd_indiv_event_prob_lb (params : LVParams) (a b : ℕ)
    (hab : b ≤ a) (hb : 0 < b)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    (hTheta : 0 < params.beta + params.delta) :
    ENNReal.ofReal ((params.beta + params.delta) /
        ((params.alpha0 + params.alpha1) * b + 2 * (params.beta + params.delta))) ≤
      (lvKernel .selfDestructive params (a, b))
        {s | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
             (s.1 = a - 1 ∧ s.2 = b ∧ s ≠ (a - 1, b - 1)) ∨
             (s.1 = a ∧ s.2 = b - 1 ∧ s ≠ (a - 1, b - 1))} := by
  have ha : 0 < a := Nat.lt_of_lt_of_le hb hab
  rw [lvKernel_sd_indiv_event_measure params a b ha hb hGamma0 hGamma1]
  apply ENNReal.ofReal_le_ofReal
  have hφ_val : lvTotalPropensity params (a, b) =
      (params.beta + params.delta) * ((a:ℝ) + b) + (params.alpha0 + params.alpha1) * a * b := by
    simp only [lvTotalPropensity, hGamma0, hGamma1]; push_cast; ring
  rw [hφ_val]; push_cast
  exact noncompetitive_prob_lb_nat params a b hab hb hTheta

/-- For NSD with γ=0 and a,b ≥ 1, ALL transitions are individual events
    (competitive α₀,α₁ land on (a,b-1),(a-1,b)), so P(ind. event) = 1. -/
lemma lvKernel_nsd_indiv_event_prob_lb (params : LVParams) (a b : ℕ)
    (hab : b ≤ a) (hb : 0 < b)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    (hTheta : 0 < params.beta + params.delta) :
    ENNReal.ofReal ((params.beta + params.delta) /
        ((params.alpha0 + params.alpha1) * b + 2 * (params.beta + params.delta))) ≤
      (lvKernel .nonSelfDestructive params (a, b))
        {s | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
             (s.1 = a - 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b - 1)} := by
  have h1 : (lvKernel .nonSelfDestructive params (a, b))
        {s | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
             (s.1 = a - 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b - 1)} = 1 := by
    -- φ > 0 from hTheta and b > 0
    have ha : 0 < a := Nat.lt_of_lt_of_le hb hab
    have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hb' : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
    have hφ_pos : 0 < lvTotalPropensity params (a, b) := by
      simp only [lvTotalPropensity]
      have ha_r : (0:ℝ) ≤ a := Nat.cast_nonneg _
      have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
      have hb_r : (0:ℝ) < b := Nat.cast_pos.mpr hb
      have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
      have hbeta_b : 0 < (params.beta + params.delta) * (b:ℝ) := mul_pos hTheta hb_r
      have hg0 : (0:ℝ) ≤ params.gamma0 * ((a:ℝ) * ((a:ℝ) - 1) / 2) :=
        mul_nonneg params.gamma0_nonneg (div_nonneg (mul_nonneg ha_r (by linarith)) (by norm_num))
      have hg1 : (0:ℝ) ≤ params.gamma1 * ((b:ℝ) * ((b:ℝ) - 1) / 2) :=
        mul_nonneg params.gamma1_nonneg (div_nonneg (mul_nonneg hb_r.le (by linarith)) (by norm_num))
      nlinarith [mul_nonneg params.beta_nonneg ha_r, mul_nonneg params.delta_nonneg ha_r,
                 mul_nonneg (add_nonneg params.alpha0_nonneg params.alpha1_nonneg) ha_r, hg0, hg1]
    have hφ_ne : lvTotalPropensity params (a, b) ≠ 0 := hφ_pos.ne'
    set S := {s : PopState | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
             (s.1 = a - 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b - 1)} with hS_def
    -- Compute K(S) directly: all NSD targets (with γ=0) are in S
    rw [lvKernel_nsd_apply params a b hφ_ne, hGamma0, hGamma1]
    simp only [zero_mul, ENNReal.ofReal_zero, zero_smul, add_zero, Measure.smul_apply,
               Measure.add_apply, smul_eq_mul, Measure.dirac_apply_of_mem
                 (show (a + 1, b) ∈ S from Or.inl ⟨rfl, rfl⟩),
               Measure.dirac_apply_of_mem
                 (show (a, b + 1) ∈ S from Or.inr (Or.inl ⟨rfl, rfl⟩)),
               Measure.dirac_apply_of_mem
                 (show (a - 1, b) ∈ S from Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
               Measure.dirac_apply_of_mem
                 (show (a, b - 1) ∈ S from Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))]
    simp only [mul_one]
    -- Sum: ofReal(1/φ) * (ofReal(β*a) + ofReal(β*b) + ofReal(δ*a) + ofReal(δ*b)
    --                     + ofReal(α₀*a*b) + ofReal(α₁*a*b)) = 1
    -- Collect: these sum to ofReal(φ) when γ=0
    have h1 : (0:ℝ) ≤ params.beta * a := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have h2 : (0:ℝ) ≤ params.beta * b := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have h3 : (0:ℝ) ≤ params.delta * a := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have h4 : (0:ℝ) ≤ params.delta * b := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have h5 : (0:ℝ) ≤ params.alpha0 * a * b :=
      mul_nonneg (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have h6 : (0:ℝ) ≤ params.alpha1 * a * b :=
      mul_nonneg (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hinvφ : (0:ℝ) ≤ 1 / lvTotalPropensity params (a, b) :=
      div_nonneg zero_le_one hφ_pos.le
    -- Show sum equals φ (with γ=0), then cancel
    have hsum : params.beta * (a:ℝ) + params.beta * (b:ℝ) + params.delta * (a:ℝ) +
        params.delta * (b:ℝ) + params.alpha0 * (a:ℝ) * (b:ℝ) + params.alpha1 * (a:ℝ) * (b:ℝ) =
        lvTotalPropensity params (a, b) := by
      simp only [lvTotalPropensity]; rw [hGamma0, hGamma1]
      push_cast; ring
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3,
        ← ENNReal.ofReal_add (by linarith) h4, ← ENNReal.ofReal_add (by linarith) h5,
        ← ENNReal.ofReal_add (by linarith) h6, hsum,
        ← ENNReal.ofReal_mul hinvφ, one_div_mul_cancel hφ_ne, ENNReal.ofReal_one]
  rw [h1, ENNReal.ofReal_le_one]
  have hb' : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hdenom : 0 < (params.alpha0 + params.alpha1) * (b : ℝ) +
      2 * (params.beta + params.delta) := by
    have := params.alpha0_nonneg; have := params.alpha1_nonneg; nlinarith
  rw [div_le_one hdenom]
  have := params.alpha0_nonneg; have := params.alpha1_nonneg
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ params.alpha0 + params.alpha1 by linarith)
               (le_of_lt hb')]

/-- For any LV variant with γ=0, P(individual event at (a,b) with a≥b≥1) ≥ θ/(αb+2θ).
    Core inequality for proof of lemma:log-individual-events. -/
lemma lvKernel_indiv_event_prob_lb (v : LVVariant) (params : LVParams) (a b : ℕ)
    (hab : b ≤ a) (hb : 0 < b)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    (hTheta : 0 < params.beta + params.delta) :
    ENNReal.ofReal ((params.beta + params.delta) /
        ((params.alpha0 + params.alpha1) * b + 2 * (params.beta + params.delta))) ≤
      (lvKernel v params (a, b))
        {s | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
             (s.1 = a - 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b - 1)} := by
  cases v with
  | selfDestructive =>
    -- The target set {s | ... (a-1,b) ∨ (a,b-1)} equals the set with s≠(a-1,b-1) conditions,
    -- since (a-1,b)≠(a-1,b-1) and (a,b-1)≠(a-1,b-1) for all a,b.
    have ha : 0 < a := Nat.lt_of_lt_of_le hb hab
    have hset_eq : {s : PopState | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
              (s.1 = a - 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b - 1)} =
        {s : PopState | (s.1 = a + 1 ∧ s.2 = b) ∨ (s.1 = a ∧ s.2 = b + 1) ∨
              (s.1 = a - 1 ∧ s.2 = b ∧ s ≠ (a - 1, b - 1)) ∨
              (s.1 = a ∧ s.2 = b - 1 ∧ s ≠ (a - 1, b - 1))} := by
      ext s; simp only [Set.mem_setOf_eq]
      constructor
      · rintro (h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, by intro heq; have := Prod.ext_iff.mp heq; omega⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, by intro heq; have := Prod.ext_iff.mp heq; omega⟩))
      · rintro (h | h | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
    rw [hset_eq]
    exact lvKernel_sd_indiv_event_prob_lb params a b hab hb hGamma0 hGamma1 hTheta
  | nonSelfDestructive =>
    exact lvKernel_nsd_indiv_event_prob_lb params a b hab hb hGamma0 hGamma1 hTheta

/-! -----------------------------------------------------------------------
    § 4  Discrete descending IVT and min-count path analysis
    Paper: "the sequence (M_t) has to visit every state m, m-1, ..., 1"
    ----------------------------------------------------------------------- -/

/-- Discrete descending IVT: f starts at m, ends at 0, steps down ≤ 1 at a time,
    so f hits every value k ≤ m.
    Key structural fact for proof of lemma:log-individual-events. -/
lemma discrete_descending_ivt (f : ℕ → ℕ) (T m : ℕ)
    (hstart : f 0 = m)
    (hend : f T = 0)
    (hstep : ∀ t, t < T → f (t + 1) + 1 ≥ f t) :
    ∀ k ≤ m, ∃ t ≤ T, f t = k := by
  intro k hkm
  suffices h : ∀ j ≤ m, ∃ t ≤ T, f t = m - j by
    obtain ⟨t, ht, heq⟩ := h (m - k) (by omega)
    exact ⟨t, ht, by omega⟩
  intro j hjm
  induction j with
  | zero => exact ⟨0, Nat.zero_le T, by simp [hstart]⟩
  | succ j ih =>
    have hj : j ≤ m := by omega
    obtain ⟨t₁, ht₁T, ht₁eq⟩ := ih hj
    have ht₁T_lt : t₁ < T := by
      rcases Nat.lt_or_eq_of_le ht₁T with h | h
      · exact h
      · subst h; rw [hend] at ht₁eq; omega
    -- Find the minimum t ∈ [t₁+1, T] where f(t) < m - j.
    let S := (Finset.Ico (t₁ + 1) (T + 1)).filter (fun n => f n < m - j)
    have hS_ne : S.Nonempty := by
      exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩⟩
    obtain ⟨t₂, ht₂_mem, ht₂_min⟩ := S.exists_min_image id hS_ne
    rw [Finset.mem_filter, Finset.mem_Ico] at ht₂_mem
    obtain ⟨⟨ht₂_lb, ht₂_ub⟩, ht₂_small⟩ := ht₂_mem
    simp only [Function.id_def] at ht₂_min
    -- t₂ - 1 ∉ S by minimality, so f(t₂-1) ≥ m - j.
    have ht₂_prev : f (t₂ - 1) ≥ m - j := by
      by_contra h
      push_neg at h
      rcases Nat.lt_or_eq_of_le (show t₁ + 1 ≤ t₂ from by omega) with hlt | heqt
      · -- t₂ > t₁ + 1: t₂ - 1 ≥ t₁ + 1, contradicting minimality of t₂
        have hmem : t₂ - 1 ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, h⟩
        have := ht₂_min (t₂ - 1) hmem
        omega
      · -- t₂ = t₁ + 1, so t₂ - 1 = t₁, but f(t₁) = m - j ≮ m - j
        have : t₂ - 1 = t₁ := by omega
        rw [this, ht₁eq] at h; omega
    -- f(t₂) ≥ m - j - 1 by the step bound.
    have ht₂_lb2 : f t₂ ≥ m - j - 1 := by
      have hstep' := hstep (t₂ - 1) (by omega)
      rw [show t₂ - 1 + 1 = t₂ from by omega] at hstep'
      omega
    exact ⟨t₂, by omega, by omega⟩

/-- For LV with γ=0, one step cannot decrease the min species count by more than 1. -/
lemma lvKernel_min_count_step_lb (v : LVVariant) (params : LVParams) (a b : ℕ)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0) :
    (lvKernel v params (a, b)) {s | Nat.min a b ≤ Nat.min s.1 s.2 + 1} = 1 := by
  set T := {s : PopState | Nat.min a b ≤ Nat.min s.1 s.2 + 1} with hT_def
  -- All Dirac targets satisfy the min-count bound; compute K(T) = 1 directly
  have hT_mem : (a+1, b) ∈ T ∧ (a, b+1) ∈ T ∧ (a-1, b) ∈ T ∧ (a, b-1) ∈ T ∧
      (a-1, b-1) ∈ T ∧ (a, b) ∈ T := by
    simp only [hT_def, Set.mem_setOf_eq]; constructor
    · simp only [Nat.min_def]; split_ifs <;> omega
    constructor
    · simp only [Nat.min_def]; split_ifs <;> omega
    constructor
    · simp only [Nat.min_def]; split_ifs <;> omega
    constructor
    · simp only [Nat.min_def]; split_ifs <;> omega
    constructor
    · simp only [Nat.min_def]; split_ifs <;> omega
    · simp only [Nat.min_def]; split_ifs <;> omega
  obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6⟩ := hT_mem
  by_cases hφ : lvTotalPropensity params (a, b) = 0
  · -- φ = 0: kernel = dirac at (a,b) ∈ T
    rw [lvKernel_apply_zero_propensity _ _ _ hφ]
    exact Measure.dirac_apply_of_mem ht6
  · -- φ ≠ 0: compute K(T) = (1/φ) * φ = 1 by applying dirac targets to T
    have hφ_nonneg : 0 ≤ lvTotalPropensity params (a, b) := by
      simp only [lvTotalPropensity, hGamma0, hGamma1, zero_mul, add_zero]
      push_cast
      nlinarith [mul_nonneg params.beta_nonneg (Nat.cast_nonneg (α := ℝ) a),
                 mul_nonneg params.delta_nonneg (Nat.cast_nonneg (α := ℝ) a),
                 mul_nonneg params.beta_nonneg (Nat.cast_nonneg (α := ℝ) b),
                 mul_nonneg params.delta_nonneg (Nat.cast_nonneg (α := ℝ) b),
                 mul_nonneg (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg (α := ℝ) a))
                   (Nat.cast_nonneg (α := ℝ) b),
                 mul_nonneg (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg (α := ℝ) a))
                   (Nat.cast_nonneg (α := ℝ) b)]
    have h1 : (0:ℝ) ≤ params.beta * a := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have h2 : (0:ℝ) ≤ params.beta * b := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have h3 : (0:ℝ) ≤ params.delta * a := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have h4 : (0:ℝ) ≤ params.delta * b := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have h5 : (0:ℝ) ≤ params.alpha0 * a * b :=
      mul_nonneg (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have h6 : (0:ℝ) ≤ params.alpha1 * a * b :=
      mul_nonneg (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hinvφ : (0:ℝ) ≤ 1 / lvTotalPropensity params (a, b) :=
      div_nonneg zero_le_one hφ_nonneg
    have hsum : params.beta * (a:ℝ) + params.beta * (b:ℝ) + params.delta * (a:ℝ) +
        params.delta * (b:ℝ) + params.alpha0 * (a:ℝ) * (b:ℝ) + params.alpha1 * (a:ℝ) * (b:ℝ) =
        lvTotalPropensity params (a, b) := by
      simp only [lvTotalPropensity]; rw [hGamma0, hGamma1]; push_cast; ring
    cases v with
    | selfDestructive =>
      rw [lvKernel_sd_apply params a b hφ, hGamma0, hGamma1]
      simp only [zero_mul, ENNReal.ofReal_zero, zero_smul, add_zero, Measure.smul_apply,
                 Measure.add_apply, smul_eq_mul, Measure.dirac_apply_of_mem ht1,
                 Measure.dirac_apply_of_mem ht2, Measure.dirac_apply_of_mem ht3,
                 Measure.dirac_apply_of_mem ht4, Measure.dirac_apply_of_mem ht5, mul_one]
      -- Combine the 6 ofReal terms into one, then cancel 1/φ * φ = 1
      rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3,
          ← ENNReal.ofReal_add (by linarith) h4, ← ENNReal.ofReal_add (by linarith) h5,
          ← ENNReal.ofReal_add (by linarith) h6, ← ENNReal.ofReal_mul hinvφ, hsum,
          one_div_mul_cancel hφ, ENNReal.ofReal_one]
    | nonSelfDestructive =>
      rw [lvKernel_nsd_apply params a b hφ, hGamma0, hGamma1]
      simp only [zero_mul, ENNReal.ofReal_zero, zero_smul, add_zero, Measure.smul_apply,
                 Measure.add_apply, smul_eq_mul, Measure.dirac_apply_of_mem ht1,
                 Measure.dirac_apply_of_mem ht2, Measure.dirac_apply_of_mem ht3,
                 Measure.dirac_apply_of_mem ht4, mul_one]
      rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3,
          ← ENNReal.ofReal_add (by linarith) h4, ← ENNReal.ofReal_add (by linarith) h5,
          ← ENNReal.ofReal_add (by linarith) h6, ← ENNReal.ofReal_mul hinvφ, hsum,
          one_div_mul_cancel hφ, ENNReal.ofReal_one]

/-- A.e. version of min-count step bound via the Markov property. -/
lemma lvPath_min_count_step_lb_ae (v : LVVariant) (params : LVParams)
    (s0 : PopState) (t : ℕ)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    [IsMarkovKernel (lvKernel v params)] :
    ∀ᵐ ω ∂(lvPathMeasure v params s0),
      Nat.min (ω t).1 (ω t).2 ≤ Nat.min (ω (t + 1)).1 (ω (t + 1)).2 + 1 := by
  -- For each s : PopState, K(s)(Ts sᶜ) = 0
  have hKbad : ∀ s : PopState,
      (lvKernel v params s) {s' | ¬(Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1)} = 0 := by
    intro s
    have h1 := lvKernel_min_count_step_lb v params s.1 s.2 hGamma0 hGamma1
    simp only [Prod.mk.eta] at h1
    have hSmeas : MeasurableSet {s' : PopState | Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1} :=
      (Set.to_countable _).measurableSet
    -- {s' | ¬P s'} = {s' | P s'}ᶜ definitionally; use measure_compl
    change (lvKernel v params s) {s' | Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1}ᶜ = 0
    rw [measure_compl hSmeas (by rw [h1]; exact ENNReal.one_ne_top), h1, measure_univ, tsub_self]
  -- bad event decomposes over source state s
  have hBadUnion : {ω : ℕ → PopState |
        ¬(Nat.min (ω t).1 (ω t).2 ≤ Nat.min (ω (t + 1)).1 (ω (t + 1)).2 + 1)} =
      ⋃ (s : PopState), {ω | ω t = s} ∩
        {ω | ¬(Nat.min s.1 s.2 ≤ Nat.min (ω (t + 1)).1 (ω (t + 1)).2 + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨ω t, rfl, h⟩, fun ⟨_, hs, h⟩ => hs ▸ h⟩
  rw [ae_iff, hBadUnion]
  apply measure_iUnion_null_iff.mpr
  intro s
  -- P({ω | ω t = s} ∩ bad_s) = ∫⁻ ω, 1_{ω t=s} * 1_{ω(t+1)∉Ts} dP = 0
  have hsmeas : MeasurableSet {s' : PopState | Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1} :=
    (Set.to_countable _).measurableSet
  have hBadMeas : MeasurableSet
      ({ω : ℕ → PopState | ω t = s} ∩
        {ω | ¬(Nat.min s.1 s.2 ≤ Nat.min (ω (t + 1)).1 (ω (t + 1)).2 + 1)}) := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton s).preimage (measurable_pi_apply t)
    · exact hsmeas.compl.preimage (measurable_pi_apply (t + 1))
  rw [← lintegral_indicator_one hBadMeas]
  -- Rewrite indicator of intersection as product of indicators
  have hInd : ∀ ω : ℕ → PopState,
      ({ω' | ω' t = s} ∩
          {ω' | ¬(Nat.min s.1 s.2 ≤ Nat.min (ω' (t + 1)).1 (ω' (t + 1)).2 + 1)}).indicator
        (1 : (ℕ → PopState) → ℝ≥0∞) ω =
      Set.indicator {s} (1 : PopState → ℝ≥0∞) (ω t) *
        Set.indicator {s' | ¬(Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1)}
          (1 : PopState → ℝ≥0∞) (ω (t + 1)) := by
    intro ω
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_cases hs : ω t = s <;>
      by_cases hb : ¬(Nat.min s.1 s.2 ≤ Nat.min (ω (t+1)).1 (ω (t+1)).2 + 1) <;>
      simp [hs, hb, mul_one, mul_zero, zero_mul]
  simp_rw [hInd]
  -- Unfold lvPathMeasure then apply joint lintegral (Markov property)
  simp only [lvPathMeasure]
  rw [homogeneousPathMeasure_joint_lintegral (lvKernel v params) s0 t
      (Set.indicator {s} 1)
      (Set.indicator {s' | ¬(Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1)} 1)
      (measurable_of_countable _) (measurable_of_countable _)]
  -- RHS: ∫⁻ x, 1_{x=s} * K(x)(bad_s) d(K^t s0)(x) = K(s)(bad_s) * (K^t s0)({s}) = 0
  have hcompl_meas : MeasurableSet {s' : PopState | ¬(Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1)} :=
    hsmeas.compl
  simp_rw [lintegral_indicator_one hcompl_meas]
  -- simplify: 1_{x=s} * K(x)(bad_s) = 0 since K(s)(bad_s) = 0
  have hzero : ∀ x : PopState, Set.indicator {s} (1 : PopState → ℝ≥0∞) x *
      (lvKernel v params x) {s' | ¬(Nat.min s.1 s.2 ≤ Nat.min s'.1 s'.2 + 1)} = 0 := by
    intro x
    by_cases hx : x = s
    · rw [hx, Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl),
          Pi.one_apply, one_mul, hKbad]
    · simp [Set.indicator_apply, Set.mem_singleton_iff, hx]
  simp_rw [hzero, lintegral_zero]

/-- On a.e. path (given consensus is a.s. reached), the min species count visits every
    level from b₀ down to 0 before the consensus time.
    Paper: "the minimum M_t must visit every m, m-1, ..., 1 before T(S)".
    Proof: apply discrete_descending_ivt pathwise using lvPath_min_count_step_lb_ae,
    restricted to paths where consensus is reached (the a.e. case under hConsensus_ae). -/
lemma lvPath_min_count_visits_each_level (v : LVVariant) (params : LVParams)
    (a₀ b₀ : ℕ) (h_start : b₀ ≤ a₀) (hb₀ : 0 < b₀)
    (hGamma0 : params.gamma0 = 0) (hGamma1 : params.gamma1 = 0)
    [IsMarkovKernel (lvKernel v params)]
    (hConsensus_ae : ∀ᵐ ω ∂(lvPathMeasure v params (a₀, b₀)), consensusTime ω < ⊤)
    (k : ℕ) (hk1 : 0 < k) (hk2 : k ≤ b₀) :
    ∀ᵐ ω ∂(lvPathMeasure v params (a₀, b₀)),
      ∃ t : ℕ, (consensusTime ω = ⊤ ∨ (t : ℕ∞) ≤ consensusTime ω) ∧
        Nat.min (ω t).1 (ω t).2 = k := by
  -- Step 1: a.e. step bound for ALL t simultaneously (countable intersection)
  have hstep_all : ∀ᵐ ω ∂(lvPathMeasure v params (a₀, b₀)), ∀ t,
      Nat.min (ω t).1 (ω t).2 ≤ Nat.min (ω (t + 1)).1 (ω (t + 1)).2 + 1 := by
    rw [ae_all_iff]
    exact fun t => lvPath_min_count_step_lb_ae v params (a₀, b₀) t hGamma0 hGamma1
  -- Step 2: a.e. initial state is (a₀, b₀)
  have hinitial : ∀ᵐ ω ∂(lvPathMeasure v params (a₀, b₀)), ω 0 = (a₀, b₀) := by
    have hmarg : (lvPathMeasure v params (a₀, b₀)).map (fun ω ↦ ω 0) =
        Measure.dirac (a₀, b₀) := by
      simp only [lvPathMeasure]
      exact homogeneousPathMeasure_marginal_zero (lvKernel v params) (Measure.dirac (a₀, b₀))
    rw [ae_iff]
    have hne : lvPathMeasure v params (a₀, b₀) {ω | ω 0 ≠ (a₀, b₀)} = 0 := by
      have heq : lvPathMeasure v params (a₀, b₀) {ω | ω 0 ≠ (a₀, b₀)} =
          (Measure.dirac (a₀, b₀)) {x : PopState | x ≠ (a₀, b₀)} := by
        calc lvPathMeasure v params (a₀, b₀) {ω | ω 0 ≠ (a₀, b₀)}
            = (lvPathMeasure v params (a₀, b₀)) ((fun ω : ℕ → PopState ↦ ω 0) ⁻¹'
                {x | x ≠ (a₀, b₀)}) := by rfl
          _ = (lvPathMeasure v params (a₀, b₀)).map (fun ω ↦ ω 0) {x | x ≠ (a₀, b₀)} := by
                rw [Measure.map_apply (measurable_pi_apply 0) (by measurability)]
          _ = _ := by rw [hmarg]
      rw [heq]; simp
    simpa using hne
  -- Step 3: combine all a.e. sets and apply discrete_descending_ivt
  filter_upwards [hstep_all, hConsensus_ae, hinitial] with ω hstep hcons h0
  -- Extract T : ℕ with consensusTime ω = ↑T
  rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp hcons) with ⟨T, hT⟩
  -- Compute min at time 0 = b₀
  have hstart : Nat.min (ω 0).1 (ω 0).2 = b₀ := by
    rw [h0]; exact Nat.min_eq_right h_start
  -- Compute min at time T = 0 (reachedConsensus)
  have hend : Nat.min (ω T).1 (ω T).2 = 0 := by
    have hrc : reachedConsensus (ω T) := reachedConsensus_at_consensusTime' ω T hT.symm
    rcases hrc with h1 | h2
    · simp [h1]
    · simp [h2]
  -- Apply discrete IVT to get the level k visited at some t ≤ T
  obtain ⟨t, htT, htk⟩ := discrete_descending_ivt (fun s => Nat.min (ω s).1 (ω s).2)
      T b₀ hstart hend (fun s hs => hstep s) k hk2
  -- The time t satisfies t ≤ T = consensusTime ω, so second disjunct holds
  exact ⟨t, Or.inr (hT ▸ (by exact_mod_cast htT : (t : ℕ∞) ≤ ↑T)), htk⟩

/-! -----------------------------------------------------------------------
    § 5  Stochastic domination via coupling
    Paper: chain domination proof extracts StochDominates from pseudo-coupling.
    ----------------------------------------------------------------------- -/

/-- Coupling lemma: X ≤ Y pointwise on joint space implies P(X ≥ t) ≤ P(Y ≥ t).
    Used to extract stochastic domination from the pseudo-coupling construction.
    Paper: the chain domination proof uses "P(min Ŝₜ > 0) ≤ P(N̂ₜ > 0)". -/
lemma stochDom_of_coupling
    {Ω Ω' Ω'' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (μ : Measure Ω) (ν : Measure Ω') (κ : Measure Ω'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (πX : Ω'' → Ω) (πY : Ω'' → Ω')
    (hπX_meas : Measurable πX) (hπY_meas : Measurable πY)
    (X : Ω → ℕ) (Y : Ω' → ℕ)
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hX_marg : κ.map πX = μ)
    (hY_marg : κ.map πY = ν)
    (hXY : ∀ ω'', X (πX ω'') ≤ Y (πY ω'')) :
    ∀ t : ℕ, μ {ω | t ≤ X ω} ≤ ν {ω' | t ≤ Y ω'} := by
  intro t
  have hmX : MeasurableSet {ω : Ω | t ≤ X ω} := hX_meas measurableSet_Ici
  have hmY : MeasurableSet {ω' : Ω' | t ≤ Y ω'} := hY_meas measurableSet_Ici
  rw [← hX_marg, ← hY_marg,
      Measure.map_apply hπX_meas hmX, Measure.map_apply hπY_meas hmY]
  apply measure_mono
  intro ω'' h
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at h ⊢
  exact le_trans h (hXY ω'')

/-- A.e. version: coupling with a.e. X ≤ Y still gives P(X ≥ t) ≤ P(Y ≥ t). -/
lemma stochDom_of_coupling_ae
    {Ω Ω' Ω'' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (μ : Measure Ω) (ν : Measure Ω') (κ : Measure Ω'')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (πX : Ω'' → Ω) (πY : Ω'' → Ω')
    (hπX_meas : Measurable πX) (hπY_meas : Measurable πY)
    (X : Ω → ℕ) (Y : Ω' → ℕ)
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hX_marg : κ.map πX = μ)
    (hY_marg : κ.map πY = ν)
    (hXY : ∀ᵐ ω'' ∂κ, X (πX ω'') ≤ Y (πY ω'')) :
    ∀ t : ℕ, μ {ω | t ≤ X ω} ≤ ν {ω' | t ≤ Y ω'} := by
  intro t
  have hmX : MeasurableSet {ω : Ω | t ≤ X ω} := hX_meas measurableSet_Ici
  have hmY : MeasurableSet {ω' : Ω' | t ≤ Y ω'} := hY_meas measurableSet_Ici
  rw [← hX_marg, ← hY_marg,
      Measure.map_apply hπX_meas hmX, Measure.map_apply hπY_meas hmY]
  apply measure_mono_ae
  filter_upwards [hXY] with ω'' hle
  intro h; exact le_trans h hle

/-- Unfolding lemma: consensusTail = path measure on {ω | consensusTime ω ≥ t}. -/
lemma consensusTail_def (v : LVVariant) (params : LVParams)
    (s0 : PopState) (t : ℕ)
    [IsMarkovKernel (lvKernel v params)] :
    consensusTail v params s0 t =
      lvPathMeasure v params s0 {ω | consensusTime ω ≥ t} :=
  rfl

/-! -----------------------------------------------------------------------
    Summary

  Main helpers:
  - harmonic_cast_eq_sum_real
  - harmonic_sum_real_le_log_add_one    ← for the unconditional expected-births theorem
  - harmonic_sum_one_to_n_le
  - noncompetitive_prob_lb              ← algebraic core of lemma_log_individual_events
  - noncompetitive_prob_lb_nat
  - discrete_descending_ivt             ← combinatorial heart of same
  - stochDom_of_coupling                ← for the paper chain-domination lemma
  - stochDom_of_coupling_ae
  - consensusTail_def
  - nice_birth_prob_harmonic_sum
  - lvKernel_min_count_step_lb
  - lvPath_min_count_step_lb_ae
  - lvPath_min_count_visits_each_level (requires hConsensus_ae hypothesis)
  - lvKernel_sd_indiv_event_measure, lvKernel_sd_indiv_event_prob_lb
  - lvKernel_nsd_indiv_event_prob_lb    (h1 body)
  - lvKernel_indiv_event_prob_lb        (SD case)
  ----------------------------------------------------------------------- -/

end LVConsensus
