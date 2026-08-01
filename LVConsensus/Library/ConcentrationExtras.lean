import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Concentration library extras

General concentration results proved in the course of this project but not
used by a paper-facing result. This file is imported by `LVConsensus.lean`, so
its results are compiled by `lake build` and scanned by `check_sorry.sh`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace LVConsensus

/-- Hoeffding inequality for sums of independent bounded random variables:
    P[|Σ Xᵢ - E[Σ Xᵢ]| ≥ t] ≤ 2·exp(-t²/(2n)) when each Xᵢ ∈ [-1, 1].

    Proof: By `hasSubgaussianMGF_of_mem_Icc`, each Xᵢ - E[Xᵢ] is sub-Gaussian
    with parameter ((‖1-(-1)‖₊/2)²) = 1. The centered variables are independent
    (from `iIndepFun.comp`). By Mathlib's `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`,
    P[Σ(Xᵢ-E[Xᵢ]) ≥ t] ≤ exp(-t²/(2n)). A union bound gives the two-sided
    version with factor 2. -/
theorem lemma_hoeffding_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : Nat) (X : Fin n → Ω → Real)
    (hBound : ∀ i ω, X i ω ∈ Set.Icc (-1 : Real) 1)
    (hMeas : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (t : Real) (ht : 0 ≤ t) :
    μ {ω | t ≤ |(∑ i : Fin n, X i ω) - (∫ x, (∑ i : Fin n, X i x) ∂μ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ (2 : Nat)) / (2 * n))) := by
  set Y : Fin n → Ω → ℝ := fun i ω => X i ω - ∫ x, X i x ∂μ with hY_def
  have hX_int : ∀ i, Integrable (X i) μ := fun i =>
    Integrable.of_mem_Icc (-1) 1 (hMeas i).aemeasurable (ae_of_all _ fun ω => hBound i ω)
  have hY_meas : ∀ i, Measurable (Y i) := fun i => (hMeas i).sub measurable_const
  have hY_indep : iIndepFun Y μ :=
    hIndep.comp (fun i => fun x => x - ∫ ω, X i ω ∂μ) (fun _ => measurable_sub_const _)
  have hY_subG : ∀ i, HasSubgaussianMGF (Y i) ((‖(1:ℝ) - (-1)‖₊ / 2) ^ 2) μ := fun i =>
    hasSubgaussianMGF_of_mem_Icc (hMeas i).aemeasurable
      (ae_of_all _ fun ω => hBound i ω)
  have hparam : (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2 = 1 := by norm_num
  have hSY : ∀ ω, ∑ i : Fin n, Y i ω =
      (∑ i : Fin n, X i ω) - ∫ x, (∑ i : Fin n, X i x) ∂μ := by
    intro ω
    simp only [Y, Finset.sum_sub_distrib]
    congr 1
    rw [integral_finset_sum _ (fun i _ => hX_int i)]
  have h_upper : μ.real {ω | t ≤ ∑ i : Fin n, Y i ω} ≤
      exp (-(t ^ (2 : Nat)) / (2 * n)) := by
    have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY_indep
      (c := fun _ => (‖(1:ℝ) - (-1)‖₊ / 2) ^ 2)
      (s := Finset.univ)
      (fun i _ => hY_subG i) ht
    simp only [hparam, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at this
    convert this using 2 <;> norm_num
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
  have hset : {ω | t ≤ |(∑ i : Fin n, X i ω) - ∫ x, (∑ i : Fin n, X i x) ∂μ|} ⊆
      {ω | t ≤ ∑ i : Fin n, Y i ω} ∪ {ω | t ≤ ∑ i : Fin n, (-(Y i ω))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [← hSY ω] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib]
    by_cases h : (0 : ℝ) ≤ ∑ i : Fin n, Y i ω
    · left; rwa [abs_of_nonneg h] at hω
    · right; push_neg at h; rwa [abs_of_neg h] at hω
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
        rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
        ring_nf

end LVConsensus
