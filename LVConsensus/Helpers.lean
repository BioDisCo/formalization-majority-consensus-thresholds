import Mathlib

set_option autoImplicit false

namespace LVConsensus.Helpers

/-! ## Real arithmetic helpers for the domination proof -/

/-- For naturals a, b ≥ 1: a + b ≤ 2 * a * b. -/
lemma add_le_two_mul_of_one_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a : ℝ) + (b : ℝ) ≤ 2 * (a : ℝ) * (b : ℝ) := by
  have ha' : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb' : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  nlinarith [mul_le_mul_of_nonneg_left hb' (by linarith : (0:ℝ) ≤ a - 1)]

/-- Nat.min is zero iff one argument is zero. -/
lemma nat_min_eq_zero {a b : ℕ} : Nat.min a b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [Nat.min_def]; split_ifs <;> omega

/-- Nat.min a b > 0 implies a ≥ 1 and b ≥ 1. -/
lemma nat_min_pos {a b : ℕ} (h : 0 < Nat.min a b) : 1 ≤ a ∧ 1 ≤ b := by
  simp [Nat.min_def] at h; split_ifs at h <;> omega

/-- For the D1 proof: key cross-multiplication inequality.
    (δa + βb)(αb + θ) ≤ θ(αab + θ(a+b)) when a ≥ b ≥ 0, θ = β+δ, α,β,δ ≥ 0. -/
lemma d1_cross_mul {α β δ θ : ℝ} {a b : ℝ}
    (hθ : θ = β + δ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) :
    (δ * a + β * b) * (α * b + θ) ≤ θ * (α * a * b + θ * (a + b)) := by
  subst hθ
  nlinarith [sq_nonneg (a - b), sq_nonneg β, sq_nonneg δ,
             mul_nonneg hα (mul_nonneg hβ (mul_nonneg hb (sub_nonneg.mpr hab))),
             mul_nonneg hβ (mul_nonneg hδ ha),
             mul_nonneg hβ (mul_nonneg hδ hb)]

/-- Symmetric version of D1 for the case a ≤ b. -/
lemma d1_cross_mul_sym {α β δ θ : ℝ} {a b : ℝ}
    (hθ : θ = β + δ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hα : 0 ≤ α)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    (δ * a + β * b) * (α * a + θ) ≤ θ * (α * a * b + θ * (a + b)) := by
  subst hθ
  nlinarith [sq_nonneg (b - a), sq_nonneg β, sq_nonneg δ,
             mul_nonneg hα (mul_nonneg hδ (mul_nonneg ha (sub_nonneg.mpr hab))),
             mul_nonneg hβ (mul_nonneg hδ ha),
             mul_nonneg hβ (mul_nonneg hδ hb)]

/-- For the D2 proof: θ*(a+b) ≤ 2*θ*a*b when a, b ≥ 1 and θ ≥ 0. -/
lemma d2_ineq {θ : ℝ} {a b : ℝ}
    (hθ : 0 ≤ θ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    θ * (a + b) ≤ 2 * θ * a * b := by
  have : a + b ≤ 2 * a * b := by
    nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ a - 1)]
  nlinarith [mul_nonneg hθ (by linarith : 0 ≤ 2 * a * b - (a + b))]

/-- p(n) + q(n) ≤ 1 helper: θ*(α+2θ) + αmin*(αn+θ) ≤ (αn+θ)*(α+2θ) for n ≥ 1. -/
lemma pq_cross_mul {α αmin θ : ℝ} {n : ℝ}
    (hα : 0 < α) (hαmin_le : αmin ≤ α) (hθ : 0 ≤ θ) (hn : 1 ≤ n) (_hαmin : 0 ≤ αmin) :
    θ * (α + 2 * θ) + αmin * (α * n + θ) ≤ (α * n + θ) * (α + 2 * θ) := by
  have h1 : 0 ≤ α * (n - 1) := mul_nonneg (le_of_lt hα) (by linarith)
  nlinarith [mul_nonneg h1 (by linarith : 0 ≤ α + 2 * θ)]

end LVConsensus.Helpers
