import LVConsensus.Definitions
import LVConsensus.SwapInvariance
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
/-!
# Markov Chain Library

Foundational lemmas for birth-death chains and LV kernels:
- Kernel unfolding (bdKernel, lvKernel applied at specific states)
- One-step transition probabilities
- Drift computations for birth-death chains
- Harmonic function framework
- Path-space marginal property
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

/-! ## Birth-death kernel computation -/

/-- `bdKernel N n` unfolds to the explicit weighted Dirac sum. -/
lemma bdKernel_apply (N : BirthDeathChain) (n : ℕ) :
    (bdKernel N) n =
      ENNReal.ofReal (N.p n) • Measure.dirac (n + 1)
        + ENNReal.ofReal (N.q n) • Measure.dirac (n - 1)
        + ENNReal.ofReal (holdProb N n) • Measure.dirac n := by
  simp [bdKernel, Kernel.ofFunOfCountable]

/-- `bdKernel` at state 0 is `Dirac 0` (absorbing). -/
lemma bdKernel_zero (N : BirthDeathChain) :
    (bdKernel N) 0 = Measure.dirac 0 := by
  rw [bdKernel_apply]
  have hp := N.absorb_zero.1
  have hq := N.absorb_zero.2
  simp only [hp, hq, holdProb, sub_zero]
  simp [ENNReal.ofReal_zero, zero_smul, zero_add, one_smul]

/-- Singleton probability for `bdKernel`. -/
lemma bdKernel_apply_singleton (N : BirthDeathChain) (n m : ℕ) :
    (bdKernel N n) {m} =
      (if m = n + 1 then ENNReal.ofReal (N.p n) else 0)
        + (if m = n - 1 then ENNReal.ofReal (N.q n) else 0)
        + (if m = n then ENNReal.ofReal (holdProb N n) else 0) := by
  rw [bdKernel_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  simp only [mul_ite, mul_one, mul_zero, eq_comm]

/-! ## LV kernel unfolding -/

/-- When total propensity is 0, the LV kernel is Dirac at the current state. -/
lemma lvKernel_apply_zero_propensity (v : LVVariant) (params : LVParams) (s : PopState)
    (hφ : lvTotalPropensity params s = 0) :
    (lvKernel v params) s = Measure.dirac s := by
  simp [lvKernel, Kernel.ofFunOfCountable, hφ]

/-- The NSD kernel at (a,b) with φ ≠ 0 is the explicit 8-term sum. -/
lemma lvKernel_nsd_apply (params : LVParams) (a b : ℕ)
    (hφ : lvTotalPropensity params (a, b) ≠ 0) :
    (lvKernel .nonSelfDestructive params) (a, b) =
      ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) •
        (ENNReal.ofReal (params.beta * a) • Measure.dirac (a + 1, b)
          + ENNReal.ofReal (params.beta * b) • Measure.dirac (a, b + 1)
          + ENNReal.ofReal (params.delta * a) • Measure.dirac (a - 1, b)
          + ENNReal.ofReal (params.delta * b) • Measure.dirac (a, b - 1)
          + ENNReal.ofReal (params.alpha0 * a * b) • Measure.dirac (a, b - 1)
          + ENNReal.ofReal (params.alpha1 * a * b) • Measure.dirac (a - 1, b)
          + ENNReal.ofReal (params.gamma0 * (a * (a - 1) / 2)) • Measure.dirac (a - 1, b)
          + ENNReal.ofReal (params.gamma1 * (b * (b - 1) / 2)) •
              Measure.dirac (a, b - 1)) := by
  simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, hφ, dite_false]

/-- The SD kernel at (a,b) with φ ≠ 0 is the explicit 8-term sum.
    Note: both Inter0 and Inter1 map to (a-1, b-1) in SD. -/
lemma lvKernel_sd_apply (params : LVParams) (a b : ℕ)
    (hφ : lvTotalPropensity params (a, b) ≠ 0) :
    (lvKernel .selfDestructive params) (a, b) =
      ENNReal.ofReal (1 / lvTotalPropensity params (a, b)) •
        (ENNReal.ofReal (params.beta * a) • Measure.dirac (a + 1, b)
          + ENNReal.ofReal (params.beta * b) • Measure.dirac (a, b + 1)
          + ENNReal.ofReal (params.delta * a) • Measure.dirac (a - 1, b)
          + ENNReal.ofReal (params.delta * b) • Measure.dirac (a, b - 1)
          + ENNReal.ofReal (params.alpha0 * a * b) • Measure.dirac (a - 1, b - 1)
          + ENNReal.ofReal (params.alpha1 * a * b) • Measure.dirac (a - 1, b - 1)
          + ENNReal.ofReal (params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) •
              Measure.dirac (a - 2, b)
          + ENNReal.ofReal (params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) •
              Measure.dirac (a, b - 2)) := by
  simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, hφ, dite_false]

/-- Total propensity is positive whenever either population is positive and δ > 0.
    This ensures the kernel is well-defined (not stuck at the current state). -/
lemma lvTotalPropensity_pos (params : LVParams) (k b : ℕ)
    (hDelta : 0 < params.delta) (hk : 0 < k) :
    0 < lvTotalPropensity params (k, b) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  -- Lower bound: lvTotalPropensity ≥ delta * k > 0
  -- All other terms are nonneg (beta, alpha, gamma all nonneg)
  have hLow : params.delta * k ≤ lvTotalPropensity params (k, b) := by
    have heq : lvTotalPropensity params (k, b) =
        params.beta * k + params.beta * b + params.delta * k + params.delta * b +
          (params.alpha0 + params.alpha1) * k * b +
            params.gamma0 * (k * (k - 1) / 2) + params.gamma1 * (b * (b - 1) / 2) := by
      unfold lvTotalPropensity; simp [Prod.fst, Prod.snd]
    rw [heq]
    have hβ := LVParams.beta_nonneg params
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast Nat.zero_le b
    have hk1 : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
    have hα0 := LVParams.alpha0_nonneg params
    have hα1 := LVParams.alpha1_nonneg params
    have hγ0 := LVParams.gamma0_nonneg params
    have hγ1 := LVParams.gamma1_nonneg params
    have hδ' := LVParams.delta_nonneg params
    have hterm1 : 0 ≤ params.beta * k := mul_nonneg hβ hk'.le
    have hterm2 : 0 ≤ params.beta * b := mul_nonneg hβ hb'
    have hterm4 : 0 ≤ params.delta * b := mul_nonneg hδ' hb'
    have hterm5 : 0 ≤ (params.alpha0 + params.alpha1) * k * b :=
      mul_nonneg (mul_nonneg (by linarith) hk'.le) hb'
    have hterm6 : 0 ≤ params.gamma0 * (k * (k - 1) / 2) := by
      apply mul_nonneg hγ0; apply div_nonneg _ (by norm_num)
      nlinarith
    have hterm7 : 0 ≤ params.gamma1 * (b * (b - 1) / 2) := by
      apply mul_nonneg hγ1; apply div_nonneg _ (by norm_num)
      rcases Nat.eq_zero_or_pos b with rfl | hb_pos
      · simp
      · have : (1:ℝ) ≤ b := Nat.one_le_cast.mpr hb_pos; nlinarith
    linarith
  linarith [mul_pos hDelta hk']

/-- Total propensity is always nonneg (all rates and populations are nonneg). -/
lemma lvTotalPropensity_nonneg (params : LVParams) (s : PopState) :
    0 ≤ lvTotalPropensity params s := by
  have ha : (0:ℝ) ≤ s.1 := Nat.cast_nonneg _
  have hb : (0:ℝ) ≤ s.2 := Nat.cast_nonneg _
  have hγ0 : (0:ℝ) ≤ params.gamma0 * ((s.1:ℝ) * ((s.1:ℝ) - 1) / 2) := by
    apply mul_nonneg params.gamma0_nonneg
    apply div_nonneg _ (by norm_num)
    rcases Nat.eq_zero_or_pos s.1 with h0 | hpos
    · simp [h0]
    · exact mul_nonneg ha (by linarith [show (1:ℝ) ≤ s.1 from by exact_mod_cast hpos])
  have hγ1 : (0:ℝ) ≤ params.gamma1 * ((s.2:ℝ) * ((s.2:ℝ) - 1) / 2) := by
    apply mul_nonneg params.gamma1_nonneg
    apply div_nonneg _ (by norm_num)
    rcases Nat.eq_zero_or_pos s.2 with h0 | hpos
    · simp [h0]
    · exact mul_nonneg hb (by linarith [show (1:ℝ) ≤ s.2 from by exact_mod_cast hpos])
  simp only [lvTotalPropensity]
  nlinarith [mul_nonneg params.beta_nonneg ha, mul_nonneg params.beta_nonneg hb,
             mul_nonneg params.delta_nonneg ha, mul_nonneg params.delta_nonneg hb,
             mul_nonneg (mul_nonneg params.alpha0_nonneg ha) hb,
             mul_nonneg (mul_nonneg params.alpha1_nonneg ha) hb, hγ0, hγ1]

/-- The death-0 event contributes `δ*k/φ(k,b)` to `K(k,b){(k-1,b)}` as a lower bound.
    Both SD and NSD variants always include the `δk • dirac(k-1,b)` term. -/
lemma lvKernel_death0_singleton_lower (v : LVVariant) (params : LVParams) (k b : ℕ)
    (hk : 0 < k) (hDelta : 0 < params.delta) :
    ENNReal.ofReal (params.delta * k) * ENNReal.ofReal (1 / lvTotalPropensity params (k, b)) ≤
      lvKernel v params (k, b) {(k - 1, b)} := by
  have hφ_pos := lvTotalPropensity_pos params k b hDelta hk
  have hφ_ne : lvTotalPropensity params (k, b) ≠ 0 := hφ_pos.ne'
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  -- Both NSD and SD include `(1/φ) • δk • dirac(k-1,b)`.
  -- This contributes δk/φ to the singleton measure at (k-1,b).
  have hDiracEq :
      (ENNReal.ofReal (1 / lvTotalPropensity params (k, b)) •
        (ENNReal.ofReal (params.delta * k) • Measure.dirac (k - 1, b))) {(k - 1, b)} =
      ENNReal.ofReal (params.delta * k) * ENNReal.ofReal (1 / lvTotalPropensity params (k, b)) := by
    simp [Measure.smul_apply, smul_eq_mul, mul_comm]
  rw [← hDiracEq]
  cases v with
  | nonSelfDestructive =>
    rw [lvKernel_nsd_apply params k b hφ_ne]
    -- Show: (1/φ) • (δk • dirac(k-1,b)) {·} ≤ (1/φ) • (big sum) {·}
    simp only [Measure.smul_apply, smul_eq_mul]
    apply mul_le_mul_left'
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    -- t₃ ≤ (t₁+t₂)+t₃+t₄+t₅+t₆+t₇+t₈ (left-associative sums)
    -- Pattern: le_add_left h : a ≤ b → a ≤ c + b; le_add_right h : a ≤ b → a ≤ b + c
    apply le_add_right; apply le_add_right; apply le_add_right
    apply le_add_right; apply le_add_right; apply le_add_left; rfl
  | selfDestructive =>
    rw [lvKernel_sd_apply params k b hφ_ne]
    simp only [Measure.smul_apply, smul_eq_mul]
    apply mul_le_mul_left'
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    apply le_add_right; apply le_add_right; apply le_add_right
    apply le_add_right; apply le_add_right; apply le_add_left; rfl

/-- The one-step kernel `K(k,b)` assigns positive probability to the individual death
    of species 0, i.e., `K(k,b){(k-1,b)} > 0`, whenever `k > 0` and `δ > 0`.
    This holds for both SD and NSD variants. -/
lemma lvKernel_death0_pos (v : LVVariant) (params : LVParams) (k b : ℕ)
    (hk : 0 < k) (hDelta : 0 < params.delta) :
    0 < lvKernel v params (k, b) {(k - 1, b)} := by
  have hφ_pos := lvTotalPropensity_pos params k b hDelta hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc (0 : ℝ≥0∞)
      < ENNReal.ofReal (params.delta * k) * ENNReal.ofReal (1 / lvTotalPropensity params (k, b)) := by
          have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal (params.delta * k) :=
            ENNReal.ofReal_pos.mpr (mul_pos hDelta hk')
          have h2 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / lvTotalPropensity params (k, b)) :=
            ENNReal.ofReal_pos.mpr (div_pos one_pos hφ_pos)
          exact ENNReal.mul_pos h1.ne' h2.ne'
    _ ≤ lvKernel v params (k, b) {(k - 1, b)} :=
          lvKernel_death0_singleton_lower v params k b hk hDelta

/-! ## NSD kernel with neutral parameters: transition weights

For NSD with α₀ = α₁ = α and γ₀ = γ₁ = 2α, the weight to state (a-1, b)
(from Death0 + Inter1 + Intra0) equals a * (δ + α * (a + b - 1)). -/

section NsdNeutral

variable (params : LVParams) (a b : ℕ)

/-- Total propensity for NSD neutral model simplifies to n * (β + δ + α * (n-1))
    where α = α₀ = α₁ (half-rate) and n = a + b. -/
lemma lvTotalPropensity_nsd_neutral
    (hα : params.alpha0 = params.alpha1)
    (hγ0 : params.gamma0 = 2 * params.alpha0)
    (hγ1 : params.gamma1 = 2 * params.alpha1) :
    lvTotalPropensity params (a, b) =
      (a + b) * (params.beta + params.delta +
        params.alpha0 * ((a : ℝ) + b - 1)) := by
  have h1 : params.alpha1 = params.alpha0 := hα.symm
  have h2 : params.gamma0 = 2 * params.alpha0 := hγ0
  have h3 : params.gamma1 = 2 * params.alpha0 := by rw [hγ1, hα]
  simp only [lvTotalPropensity, h1, h2, h3]
  ring

/-- The total propensity is positive when β + δ + α * (n-1) > 0 and n > 0. -/
lemma lvTotalPropensity_nsd_neutral_pos
    (hα : params.alpha0 = params.alpha1)
    (hγ0 : params.gamma0 = 2 * params.alpha0)
    (hγ1 : params.gamma1 = 2 * params.alpha1)
    (ha : 0 < a) (hb : 0 < b)
    (hαpos : 0 < params.alpha0 ∨ 0 < params.beta + params.delta) :
    lvTotalPropensity params (a, b) ≠ 0 := by
  rw [lvTotalPropensity_nsd_neutral params a b hα hγ0 hγ1]
  have ha' : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb' : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  have hn : (0 : ℝ) < (a : ℝ) + b := by linarith
  apply mul_ne_zero
  · exact ne_of_gt hn
  · cases hαpos with
    | inl h =>
      have : 0 < params.alpha0 * ((a : ℝ) + b - 1) :=
        mul_pos h (by linarith)
      linarith [params.beta_nonneg, params.delta_nonneg]
    | inr h =>
      have : (0 : ℝ) ≤ params.alpha0 * ((a : ℝ) + b - 1) :=
        mul_nonneg params.alpha0_nonneg (by linarith)
      linarith

end NsdNeutral

/-! ## Birth-death kernel integrals -/

/-- Any function is integrable against `ENNReal.ofReal c • Measure.dirac n`. -/
lemma integrable_ofReal_smul_dirac {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (c : ℝ) (n : α) :
    Integrable f (ENNReal.ofReal c • Measure.dirac n) :=
  (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Integral against `bdKernel` decomposes into three weighted terms. -/
lemma bdKernel_integral (N : BirthDeathChain) (n : ℕ) (f : ℕ → ℝ) :
    ∫ x, f x ∂(bdKernel N n) =
      N.p n * f (n + 1) + N.q n * f (n - 1) + holdProb N n * f n := by
  rw [bdKernel_apply]
  have hp := N.p_nonneg n
  have hq := N.q_nonneg n
  have hh : 0 ≤ holdProb N n := by simp [holdProb]; linarith [N.pq_le_one n]
  rw [integral_add_measure (hμ := (integrable_ofReal_smul_dirac f _ _).add_measure
      (integrable_ofReal_smul_dirac f _ _)) (hν := integrable_ofReal_smul_dirac f _ _),
    integral_add_measure (hμ := integrable_ofReal_smul_dirac f _ _)
      (hν := integrable_ofReal_smul_dirac f _ _),
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, integral_dirac,
    smul_eq_mul, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hh]

/-! ## Iterated kernel power and constant-expectation lemma -/

/-- Iterated kernel power: `kernelIter K 0 = id`, `kernelIter K (n+1) = K ∘ₖ K^n`. -/
noncomputable def kernelIter {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) : ℕ → Kernel α α
  | 0 => Kernel.id
  | n + 1 => K ∘ₖ (kernelIter K n)

@[simp]
lemma kernelIter_zero {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) : kernelIter K 0 = Kernel.id := rfl

@[simp]
lemma kernelIter_succ {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) (n : ℕ) :
    kernelIter K (n + 1) = K ∘ₖ kernelIter K n := rfl

lemma kernelIter_isMarkov {α : Type*} [MeasurableSpace α]
    {K : Kernel α α} [IsMarkovKernel K] : ∀ (n : ℕ),
    IsMarkovKernel (kernelIter K n)
  | 0 => by rw [kernelIter_zero]; infer_instance
  | n + 1 => by
    rw [kernelIter_succ]
    have := kernelIter_isMarkov (K := K) (n := n)
    infer_instance

/-- Right decomposition: `K^(n+1) = K^n ∘ₖ K`. -/
lemma kernelIter_succ_right
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    kernelIter K (n + 1) = kernelIter K n ∘ₖ K := by
  induction n with
  | zero =>
    simp [kernelIter_zero, kernelIter_succ, Kernel.id_comp, Kernel.comp_id]
  | succ n ih =>
    conv_lhs => rw [kernelIter_succ, ih]
    rw [← Kernel.comp_assoc, kernelIter_succ]

/-- Chapman–Kolmogorov: `K^(a+b) = K^b ∘ₖ K^a`. -/
lemma kernelIter_add
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (a b : ℕ) :
    kernelIter K (a + b) = kernelIter K b ∘ₖ kernelIter K a := by
  induction b with
  | zero => simp [kernelIter_zero, Kernel.id_comp]
  | succ b ih =>
    rw [Nat.add_succ, kernelIter_succ, ih, ← Kernel.comp_assoc, ← kernelIter_succ]

/-- Chapman–Kolmogorov for lintegrals:
    `∫⁻ f d(K^{a+b})(s₀) = ∫⁻ (∫⁻ f d(K^b)(j)) d(K^a)(s₀)`. -/
lemma kernelIter_lintegral_add
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K] (a b : ℕ)
    (s₀ : α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(kernelIter K (a + b)) s₀ =
      ∫⁻ j, (∫⁻ x, f x ∂(kernelIter K b) j) ∂(kernelIter K a) s₀ := by
  rw [kernelIter_add, Kernel.comp_apply]
  exact Measure.lintegral_bind
    (Kernel.measurable _).aemeasurable hf.aemeasurable

/-- Chapman–Kolmogorov for set measures:
    `K^{a+b}(s₀)(S) = ∫⁻ K^b(j)(S) d(K^a)(s₀)(j)`. -/
lemma kernelIter_measure_add
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K] (a b : ℕ)
    (s₀ : α) (S : Set α) (hS : MeasurableSet S) :
    (kernelIter K (a + b)) s₀ S =
      ∫⁻ j, (kernelIter K b) j S ∂(kernelIter K a) s₀ := by
  rw [kernelIter_add, Kernel.comp_apply]
  exact Measure.bind_apply hS (Kernel.measurable _).aemeasurable

/-- Constant expectation for harmonic functions: if `∫ h ∂K(x) = h(x)` for all `x`,
    then `∫ h ∂K^n(s₀) = h(s₀)` for all `n`. -/
lemma kernelIter_harmonic_integral
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (h : α → ℝ) (s₀ : α)
    (hHarm : ∀ s, ∫ x, h x ∂K s = h s)
    (hInt : ∀ (n : ℕ), Integrable h ((kernelIter K n) s₀)) :
    ∀ (n : ℕ), ∫ x, h x ∂(kernelIter K n) s₀ = h s₀ := by
  intro n
  induction n with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    exact integral_dirac' h s₀ (measurable_of_countable h).stronglyMeasurable
  | succ n ih =>
    rw [kernelIter_succ]
    have : IsMarkovKernel (kernelIter K n) := kernelIter_isMarkov n
    rw [Kernel.integral_comp (hInt (n + 1))]
    conv_lhs => arg 2; ext x; rw [hHarm x]
    exact ih

/-- Concentration propagation: if K^n(s₀) concentrates on S and K maps S into S',
    then K^(n+1)(s₀) concentrates on S'. -/
lemma kernelIter_concentrated_step
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s₀ : α) (n : ℕ) (S S' : Set α) (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (hConc : (kernelIter K n) s₀ Sᶜ = 0)
    (hStep : ∀ x ∈ S, K x S'ᶜ = 0) :
    (kernelIter K (n + 1)) s₀ S'ᶜ = 0 := by
  rw [kernelIter_succ, Kernel.comp_apply' _ _ _ hS'.compl]
  have h1 : ∫⁻ x in S, (K x) S'ᶜ ∂(kernelIter K n) s₀ = 0 := by
    apply le_antisymm _ zero_le
    calc ∫⁻ x in S, (K x) S'ᶜ ∂(kernelIter K n) s₀
        ≤ ∫⁻ _ in S, 0 ∂(kernelIter K n) s₀ := by
          apply lintegral_mono_ae
          exact ae_restrict_of_forall_mem hS (fun x hx => le_of_eq (hStep x hx))
      _ = 0 := by simp
  rw [← lintegral_add_compl _ hS, h1, setLIntegral_measure_zero _ _ hConc]; simp

/-- If μ concentrates on {p₁, p₂} and h(p₁)=1, h(p₂)=0, then ∫ h dμ = μ({p₁}).toReal. -/
lemma integral_eq_measure_of_concentrated
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (h : α → ℝ) (p₁ p₂ : α) (hp : p₁ ≠ p₂)
    (hConc : μ {s | s ≠ p₁ ∧ s ≠ p₂} = 0)
    (h1 : h p₁ = 1) (h0 : h p₂ = 0) :
    ∫ x, h x ∂μ = (μ {p₁}).toReal := by
  have hae : h =ᵐ[μ] Set.indicator {p₁} (fun _ => (1 : ℝ)) := by
    rw [Filter.EventuallyEq, ae_iff]
    apply le_antisymm _ zero_le
    calc μ {x | h x ≠ Set.indicator {p₁} (fun _ => (1:ℝ)) x}
        ≤ μ {s | s ≠ p₁ ∧ s ≠ p₂} := by
          apply measure_mono; intro x hx
          simp only [Set.mem_setOf_eq, ne_eq] at hx ⊢
          constructor
          · intro heq; subst heq
            exact hx (by rw [Set.indicator_of_mem (Set.mem_singleton _)]; exact h1)
          · intro heq; subst heq
            exact hx (by rw [Set.indicator_of_notMem (Set.notMem_singleton_iff.mpr (Ne.symm hp))]; exact h0)
      _ = 0 := hConc
  rw [integral_congr_ae hae, MeasureTheory.integral_indicator (measurableSet_singleton _)]
  simp [MeasureTheory.integral_const]

/-! ## Path-space marginal property

For a homogeneous Markov chain with kernel K and initial measure μ₀,
the time-n marginal of the path measure equals K^n applied to μ₀.
This is the key infrastructure connecting path-space reasoning to
iterated kernel computations. -/

private lemma homogeneousHistoryKernel_comp_eq
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ)
    (μ : Measure (∀ i : Finset.Iic n, α)) [SFinite μ] :
    (homogeneousHistoryKernel K n) ∘ₘ μ =
      K ∘ₘ (μ.map (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) := by
  unfold homogeneousHistoryKernel
  rw [← Measure.comp_assoc]
  congr 1
  exact Measure.deterministic_comp_eq_map (by fun_prop)

private lemma eval_frestrictLe' {α : Type*} (n : ℕ) :
    (fun (h : ∀ i : Finset.Iic n, α) => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ∘
      (frestrictLe n : (ℕ → α) → _) = (fun (ω : ℕ → α) => ω n) := by
  ext ω; simp [frestrictLe_apply]

/-- The time-0 marginal of a homogeneous path measure equals the initial measure. -/
lemma homogeneousPathMeasure_marginal_zero
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀] :
    (homogeneousPathMeasure μ₀ K).map (fun ω ↦ ω 0) = μ₀ := by
  let X : ℕ → Type _ := fun _ => α
  let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  have hκ : ∀ t, IsMarkovKernel (κ t) := fun t => homogeneousHistoryKernel_isMarkov K t
  change (trajMeasure (X := X) (κ := κ) μ₀).map (fun ω ↦ ω 0) = μ₀
  letI := hκ
  rw [trajMeasure, Measure.map_comp _ _ (by fun_prop)]
  have h1 : (fun ω : ∀ n, X n => ω 0) =
    (fun h : ∀ i : Finset.Iic 0, X ↑i => h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe 0 := by
    ext ω; simp [frestrictLe_apply]
  rw [h1, Kernel.map_comp_right _ (by fun_prop) (by fun_prop),
      traj_map_frestrictLe, partialTraj_self,
      Kernel.id_map (by fun_prop),
      Measure.deterministic_comp_eq_map (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
  have hEval :
      (fun h : ∀ i : Finset.Iic 0, X ↑i =>
        h ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
          (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X ↑i)).symm = id := by
    funext x
    rfl
  rw [hEval, Measure.map_id]

/-- The time-(n+1) marginal of a homogeneous path measure factors through K. -/
lemma homogeneousPathMeasure_marginal_succ
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (n : ℕ) :
    (homogeneousPathMeasure μ₀ K).map (fun ω ↦ ω (n + 1)) =
      K ∘ₘ ((homogeneousPathMeasure μ₀ K).map (fun ω ↦ ω n)) := by
  let X : ℕ → Type _ := fun _ => α
  let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  have hκ : ∀ t, IsMarkovKernel (κ t) := fun t => homogeneousHistoryKernel_isMarkov K t
  change (trajMeasure (X := X) (κ := κ) μ₀).map (fun ω ↦ ω (n + 1)) =
    K ∘ₘ ((trajMeasure (X := X) (κ := κ) μ₀).map (fun ω ↦ ω n))
  letI := hκ
  set P := trajMeasure (X := X) (κ := κ) μ₀
  have hmarg := map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (κ := κ) (μ₀ := μ₀) (a := n)
  have hsnd : ((P.map (frestrictLe n)) ⊗ₘ (κ n)).snd =
    (P.map (fun x => (frestrictLe n x, x (n + 1)))).snd := by rw [hmarg]
  rw [Measure.snd_compProd] at hsnd
  rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at hsnd
  simp only [Function.comp_def] at hsnd
  change P.map (fun ω => ω (n + 1)) = K ∘ₘ (P.map (fun ω => ω n))
  rw [← hsnd]
  change (homogeneousHistoryKernel K n) ∘ₘ (P.map (frestrictLe n)) =
    K ∘ₘ (P.map (fun ω => ω n))
  rw [homogeneousHistoryKernel_comp_eq K n,
      Measure.map_map (by fun_prop) (by fun_prop), eval_frestrictLe' n]

/-- The time-n marginal of a homogeneous path measure equals K^n applied to the initial measure. -/
lemma homogeneousPathMeasure_marginal
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (n : ℕ) :
    (homogeneousPathMeasure μ₀ K).map (fun ω ↦ ω n) = (kernelIter K n) ∘ₘ μ₀ := by
  induction n with
  | zero =>
    rw [homogeneousPathMeasure_marginal_zero, kernelIter_zero, Measure.id_comp]
  | succ n ih =>
    rw [homogeneousPathMeasure_marginal_succ K μ₀ n, ih,
        Measure.comp_assoc, kernelIter_succ]

/-- For Dirac initial measure: time-n marginal is K^n(s₀). -/
lemma homogeneousPathMeasure_dirac_marginal
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s₀ : α) (n : ℕ) :
    (homogeneousPathMeasure (Measure.dirac s₀) K).map (fun ω ↦ ω n) = (kernelIter K n) s₀ := by
  rw [homogeneousPathMeasure_marginal K (Measure.dirac s₀) n]
  exact Measure.dirac_bind (Kernel.measurable _) s₀

/-! ### Joint integral at consecutive times -/

private def lastElem (n : ℕ) (α : Type*) :
    (∀ i : Finset.Iic n, α) → α :=
  fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

private lemma lastElem_frestrictLe {α : Type*}
    (n : ℕ) (ω : ℕ → α) :
    lastElem n α (frestrictLe n ω) = ω n := by
  simp [lastElem, frestrictLe_apply]

private lemma lastElem_measurable (n : ℕ)
    {α : Type*} [MeasurableSpace α] :
    Measurable (lastElem n α) :=
  measurable_pi_apply _

private lemma histKernel_eq_K_lastElem
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ)
    (h : ∀ i : Finset.Iic n, α) :
    homogeneousHistoryKernel K n h =
      K (lastElem n α h) := by
  unfold homogeneousHistoryKernel lastElem
  rw [Kernel.comp_apply,
      Kernel.deterministic_apply (by fun_prop)]
  exact Measure.dirac_bind (Kernel.measurable K) _

-- -----------------------------------------------------------------------
-- Markov shift property: helpers
-- -----------------------------------------------------------------------

/-- Project path coordinates from Iic (k+n) to Iic n by shifting. -/
private def projKn {α : Type*} (k n : ℕ) (h : ∀ i : Finset.Iic (k + n), α) :
    ∀ i : Finset.Iic n, α :=
  fun i => h ⟨k + i.val, Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp i.2; omega)⟩

private lemma measurable_projKn {α : Type*} [MeasurableSpace α] (k n : ℕ) :
    Measurable (projKn (α := α) k n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Reindex the singleton interval Ioc(k+n)(k+n+1) → Ioc n (n+1). -/
private def singletonReindex {α : Type*} (k n : ℕ)
    (y : ∀ i : Finset.Ioc (k + n) (k + n + 1), α) : ∀ i : Finset.Ioc n (n + 1), α :=
  fun _ => y ⟨k + n + 1, Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩⟩

private lemma measurable_singletonReindex {α : Type*} [MeasurableSpace α] (k n : ℕ) :
    Measurable (singletonReindex (α := α) k n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- projKn k (n+1) ∘ IicProdIoc(k+n)(k+n+1) = IicProdIoc n (n+1) ∘ Prod.map (projKn k n) (singletonReindex k n) -/
private lemma projKn_comp_IicProdIoc {α : Type*} (k n : ℕ) :
    (projKn (α := α) k (n + 1)) ∘
      (show (∀ i : Finset.Iic (k + n), α) × (∀ i : Finset.Ioc (k + n) (k + n + 1), α) →
        ∀ i : Finset.Iic (k + (n + 1)), α from
        (IicProdIoc (X := fun _ => α) (k + n) (k + n + 1) ·)) =
    (IicProdIoc (X := fun _ => α) n (n + 1)) ∘ Prod.map (projKn k n) (singletonReindex k n) := by
  funext ⟨x, y⟩ ⟨i, hi⟩
  simp only [Function.comp, Prod.map, projKn, singletonReindex, IicProdIoc,
    Finset.mem_Ioc, Finset.mem_Iic]
  by_cases h1 : k + i ≤ k + n
  · have h2 : i ≤ n := by omega
    simp [h1, h2]
  · have h2 : ¬ (i ≤ n) := by omega
    have h3 : i = n + 1 := by have := Finset.mem_Iic.mp hi; omega
    subst h3
    simp only [dif_neg (show ¬ k + (n + 1) ≤ k + n by omega),
               dif_neg (show ¬ n + 1 ≤ n by omega), singletonReindex]
    exact congrArg y (Subtype.ext rfl)

/-- singletonReindex k n ∘ MeasurableEquiv.piSingleton (k+n) = MeasurableEquiv.piSingleton n -/
private lemma singletonReindex_comp_piSingleton {α : Type*} [MeasurableSpace α] (k n : ℕ) :
    (singletonReindex (α := α) k n) ∘
      (MeasurableEquiv.piSingleton (X := fun _ => α) (k + n) : α → _) =
    (MeasurableEquiv.piSingleton (X := fun _ => α) n : α → _) := by
  funext a _
  simp [Function.comp, singletonReindex, MeasurableEquiv.piSingleton]

/-- homogeneousHistoryKernel K (k+n) h = homogeneousHistoryKernel K n (projKn k n h) -/
private lemma hHK_projKn_eq {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (k n : ℕ) (h : ∀ i : Finset.Iic (k + n), α) :
    homogeneousHistoryKernel K (k + n) h =
    homogeneousHistoryKernel K n (projKn k n h) := by
  rw [histKernel_eq_K_lastElem, histKernel_eq_K_lastElem]
  simp [lastElem, projKn]

/-- Key shift lemma: the partial trajectory from k shifted by k equals the fresh partial
    trajectory from 0. Proved by induction on n. -/
private lemma partialTraj_shift_eq'
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (k : ℕ) (p : ∀ i : Finset.Iic k, α) (n : ℕ) :
    let X : ℕ → Type _ := fun _ => α
    let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
      fun t => homogeneousHistoryKernel K t
    let q₀ : ∀ _ : Finset.Iic 0, X 0 := fun _ => p ⟨k, Finset.mem_Iic.mpr le_rfl⟩
    (partialTraj (X := X) κ k (k + n) p).map (projKn k n) =
    partialTraj (X := X) κ 0 n q₀ := by
  intro X κ q₀
  induction n with
  | zero =>
    simp only [Nat.add_zero]
    rw [partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_projKn k 0),
        partialTraj_self, Kernel.id_apply]
    congr 1
    funext ⟨i, hi⟩
    simp [projKn, Nat.le_zero.mp (Finset.mem_Iic.mp hi), q₀]
  | succ n ih =>
    -- Normalize k + (n + 1) to k + n + 1 (definitionally equal in Lean 4)
    show (partialTraj (X := X) κ k (k + n + 1) p).map (projKn k (n + 1)) =
        partialTraj (X := X) κ 0 (n + 1) q₀
    rw [partialTraj_succ_of_le (Nat.le_add_right k n)]
    -- Unpack kernel map and comp applied to p
    rw [Kernel.map_apply _ measurable_IicProdIoc, Kernel.comp_apply]
    have hProdMeas : Measurable
        (Prod.map (projKn (α := α) k n) (singletonReindex (α := α) k n)) :=
      Measurable.prodMap (measurable_projKn k n) (measurable_singletonReindex k n)
    have hIicMeas : Measurable
        (IicProdIoc (X := fun _ => α) n (n + 1)) :=
      measurable_IicProdIoc
    -- The compose: (Kernel.id ×ₖ ...) ∘ₘ ν = ν ⊗ₘ (κ (k+n)).map (piSingleton (k+n))
    -- Now apply projKn k (n+1) via map_map: swap map_map order then use hfcomp
    rw [Measure.map_map (measurable_projKn k (n + 1)) measurable_IicProdIoc,
        projKn_comp_IicProdIoc k n,
        ← Measure.map_map hIicMeas hProdMeas]
    -- Prove the compProd transformation (the key step)
    -- Goal: ((⊗ₘ part).map (Prod.map ...)).map (IicProdIoc n (n+1)) = partialTraj κ 0 (n+1) q₀
    -- First establish the inner compProd factoring
    rw [← Measure.compProd_eq_comp_prod]
    suffices hcompProd :
        ((partialTraj (X := X) κ k (k + n) p) ⊗ₘ
          (κ (k + n)).map (MeasurableEquiv.piSingleton (X := fun _ => α) (k + n))).map
          (Prod.map (projKn k n) (singletonReindex k n)) =
        (partialTraj (X := X) κ 0 n q₀) ⊗ₘ
          (κ n).map (MeasurableEquiv.piSingleton (X := fun _ => α) n) by
      rw [hcompProd, Measure.compProd_eq_comp_prod,
          ← Kernel.comp_apply,
          ← Kernel.map_apply _ hIicMeas]
      exact congrArg
        (fun L : Kernel (∀ i : Finset.Iic 0, X i)
            (∀ i : Finset.Iic (n + 1), X i) => L q₀)
        (partialTraj_succ_of_le (X := X) (κ := κ) (Nat.zero_le n)).symm
    -- Prove the compProd map factoring via lintegral
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (Measurable.prodMap (measurable_projKn k n) (measurable_singletonReindex k n)) hs,
        Measure.compProd_apply (hs.preimage (Measurable.prodMap (measurable_projKn k n) (measurable_singletonReindex k n))),
        Measure.compProd_apply hs, ← ih,
        MeasureTheory.lintegral_map (Kernel.measurable_kernel_prodMk_left hs)
          (measurable_projKn k n)]
    congr 1; ext h
    rw [show Prod.mk h ⁻¹' (Prod.map (projKn k n) (singletonReindex k n) ⁻¹' s) =
              (fun b => (projKn k n h, singletonReindex k n b)) ⁻¹' s from rfl,
        Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ => α) (k + n)).measurable _
          (hs.preimage (Measurable.prodMk measurable_const (measurable_singletonReindex k n))),
        Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ => α) n).measurable _
          (hs.preimage measurable_prodMk_left),
        hHK_projKn_eq K k n h]
    congr 1; ext a
    simp only [Set.mem_preimage]
    constructor <;> intro ha <;>
      rwa [← Function.comp_apply (f := singletonReindex k n)
                (g := ⇑(MeasurableEquiv.piSingleton (X := fun _ => α) (k + n))),
           congrFun (singletonReindex_comp_piSingleton k n) a] at *

/-- Markov property for homogeneous chains: shifting the trajectory by k steps gives the same
    distribution as a fresh chain started at the state at time k. -/
lemma traj_map_pathShift_eq_homogeneousPathMeasure
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (k : ℕ) (p : ∀ i : Finset.Iic k, α) :
    let X : ℕ → Type _ := fun _ => α
    let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
      fun t => homogeneousHistoryKernel K t
    (traj (X := X) κ k p).map (pathShift k) =
    homogeneousPathMeasure (Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K := by
  intro X κ
  let q₀ : ∀ _ : Finset.Iic 0, X 0 := fun _ => p ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  -- Show both are projective limits of the same family
  have hRHS : (homogeneousPathMeasure (Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K) =
      (traj (X := X) κ 0) ∘ₘ
        ((Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map
          (MeasurableEquiv.piUnique _).symm) := by
    simp only [homogeneousPathMeasure, trajMeasure, X, κ]
  have hshift_meas : Measurable (pathShift (α := α) k) :=
    measurable_pi_lambda _ fun n => measurable_pi_apply _
  -- Use projective limit uniqueness
  have hshift : IsProjectiveLimit ((traj (X := X) κ k p).map (pathShift k))
      (inducedFamily (fun n => partialTraj (X := X) κ 0 n q₀)) := by
    rw [isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ q₀)]
    intro n
    rw [inducedFamily_Iic,
        Measure.map_map (measurable_frestrictLe n) hshift_meas,
        show frestrictLe n ∘ pathShift k = projKn k n ∘ frestrictLe (k + n) from by
          funext ω ⟨i, hi⟩
          simp [frestrictLe_apply, pathShift, projKn],
        ← Measure.map_map (measurable_projKn k n) (measurable_frestrictLe (k + n))]
    have htraj : (traj (X := X) κ k p).map (frestrictLe (k + n)) =
        (partialTraj (X := X) κ k (k + n)) p := by
      rw [← Kernel.map_apply _ (measurable_frestrictLe (k + n)),
          traj_map_frestrictLe (X := X)]
    rw [htraj]
    exact partialTraj_shift_eq' K k p n
  have hRHSlim : IsProjectiveLimit (homogeneousPathMeasure
        (Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K)
      (inducedFamily (fun n => partialTraj (X := X) κ 0 n q₀)) := by
    have heq : homogeneousPathMeasure (Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K =
        (traj (X := X) κ 0) q₀ := by
      simp only [homogeneousPathMeasure, trajMeasure, κ, q₀]
      rw [Measure.map_dirac' (MeasurableEquiv.piUnique _ |>.symm.measurable)]
      exact Measure.dirac_bind (Kernel.measurable _) _
    rw [heq, traj_apply (X := X)]
    exact isProjectiveLimit_trajFun (X := X) (κ := κ) 0 q₀
  exact hshift.unique hRHSlim

/-- Exact Markov-shift formula on a countable state space.  The probability
    of a future event after time `k` is the time-`k` marginal average of the
    same event for a fresh chain. -/
lemma homogeneousPathMeasure_shift_apply
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s₀ : α) (k : ℕ) (C : Set (ℕ → α)) (hC : MeasurableSet C) :
    homogeneousPathMeasure (Measure.dirac s₀) K ((pathShift k) ⁻¹' C) =
      ∫⁻ x, homogeneousPathMeasure (Measure.dirac x) K C
        ∂(kernelIter K k) s₀ := by
  let X : ℕ → Type _ := fun _ => α
  let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]
    infer_instance
  let u₀ : ∀ i : Finset.Iic 0, X i := fun _ => s₀
  set P := homogeneousPathMeasure (Measure.dirac s₀) K with hP_def
  have hPeq : P = traj κ 0 u₀ := by
    have hdef : P = (traj κ 0) ∘ₘ
        (Measure.dirac s₀).map
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm := rfl
    rw [hdef, Measure.map_dirac' (MeasurableEquiv.measurable _),
        show (traj κ 0) ∘ₘ Measure.dirac
            ((MeasurableEquiv.piUnique
              (fun _ : Finset.Iic 0 => α)).symm s₀) =
          (Measure.dirac _).bind (traj κ 0) from rfl,
        Measure.dirac_bind (Kernel.measurable _)]
    congr 1
  set μ := P.map (frestrictLe k) with hμ_def
  have hμ_eq : μ = partialTraj κ 0 k u₀ := by
    rw [hμ_def, hPeq]
    have hm :
        (traj κ 0 u₀).map (frestrictLe k) =
          ((traj κ 0).map (frestrictLe k)) u₀ :=
      (Kernel.map_apply (traj κ 0) (measurable_frestrictLe k) u₀).symm
    rw [hm, traj_map_frestrictLe (κ := κ) 0 k]
  have hCP : μ ⊗ₘ (traj κ k) =
      P.map (fun x => (frestrictLe k x, x)) := by
    rw [hμ_eq, hPeq, partialTraj_compProd_traj (Nat.zero_le k) u₀]
  have hshift_meas : Measurable (pathShift k : (ℕ → α) → ℕ → α) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  have hPair_meas :
      Measurable (fun x : ℕ → α => (frestrictLe k x, x)) :=
    Measurable.prod (measurable_frestrictLe k) measurable_id
  let F : (∀ i : Finset.Iic k, α) × (ℕ → α) → ENNReal :=
    fun p => (pathShift k ⁻¹' C).indicator (fun _ => (1 : ENNReal)) p.2
  have hFmeas : Measurable F := by
    exact (Measurable.indicator measurable_const
      (hC.preimage hshift_meas)).comp measurable_snd
  have hLHS :
      P (pathShift k ⁻¹' C) =
        ∫⁻ p, ∫⁻ y,
          (pathShift k ⁻¹' C).indicator (fun _ => (1 : ENNReal)) y
            ∂traj κ k p ∂μ := by
    rw [← lintegral_indicator_one (hC.preimage hshift_meas)]
    rw [show
        ∫⁻ ω, (pathShift k ⁻¹' C).indicator
            (1 : (ℕ → α) → ENNReal) ω ∂P =
          ∫⁻ p, F p ∂(P.map (fun x => (frestrictLe k x, x))) from
        (lintegral_map hFmeas hPair_meas).symm]
    rw [← hCP, Measure.lintegral_compProd hFmeas]
  rw [hLHS, hμ_def]
  have hInnerMeas :
      Measurable (fun p : ∀ i : Finset.Iic k, α =>
        ∫⁻ y, (pathShift k ⁻¹' C).indicator
          (fun _ => (1 : ENNReal)) y ∂traj κ k p) :=
    Measurable.lintegral_kernel_prod_right' hFmeas
  rw [MeasureTheory.lintegral_map hInnerMeas (measurable_frestrictLe k)]
  have hInner :
      ∀ ω : ℕ → α,
        ∫⁻ y, (pathShift k ⁻¹' C).indicator
            (fun _ => (1 : ENNReal)) y
              ∂traj κ k (frestrictLe k ω) =
          homogeneousPathMeasure (Measure.dirac (ω k)) K C := by
    intro ω
    calc
      ∫⁻ y, (pathShift k ⁻¹' C).indicator
          (fun _ => (1 : ENNReal)) y
            ∂traj κ k (frestrictLe k ω)
          = (traj κ k (frestrictLe k ω)) (pathShift k ⁻¹' C) := by
              rw [show
                  ∫⁻ y, (pathShift k ⁻¹' C).indicator
                      (fun _ => (1 : ENNReal)) y
                        ∂traj κ k (frestrictLe k ω) =
                    ∫⁻ y, (pathShift k ⁻¹' C).indicator
                      (1 : ((n : ℕ) → X n) → ENNReal) y
                        ∂traj κ k (frestrictLe k ω) from rfl,
                lintegral_indicator_one (hC.preimage hshift_meas)]
      _ = ((traj κ k (frestrictLe k ω)).map (pathShift k)) C := by
              rw [Measure.map_apply hshift_meas hC]
      _ = homogeneousPathMeasure
          (Measure.dirac
            ((frestrictLe k ω) ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K C := by
              rw [traj_map_pathShift_eq_homogeneousPathMeasure K k
                (frestrictLe k ω)]
      _ = homogeneousPathMeasure (Measure.dirac (ω k)) K C := by
              simp [frestrictLe_apply]
  simp_rw [hInner]
  have hFreshMeas :
      Measurable (fun x : α =>
        homogeneousPathMeasure (Measure.dirac x) K C) :=
    measurable_of_countable _
  calc
    ∫⁻ ω, homogeneousPathMeasure (Measure.dirac (ω k)) K C ∂P =
        ∫⁻ x, homogeneousPathMeasure (Measure.dirac x) K C
          ∂(P.map (fun ω => ω k)) := by
            exact (MeasureTheory.lintegral_map hFreshMeas
              (measurable_pi_apply k)).symm
    _ = ∫⁻ x, homogeneousPathMeasure (Measure.dirac x) K C
          ∂(kernelIter K k) s₀ := by
            rw [hP_def, homogeneousPathMeasure_dirac_marginal]

/-- Joint integral at consecutive times:
    ∫ g(ω(n))·φ(ω(n+1)) dP
      = ∫ g(x)·(∫ φ(y) dK(x)(y)) dK^n(s₀)(x). -/
lemma homogeneousPathMeasure_joint_lintegral
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s₀ : α) (n : ℕ)
    (g : α → ℝ≥0∞) (φ : α → ℝ≥0∞)
    (hg : Measurable g) (hφ : Measurable φ) :
    ∫⁻ ω, g (ω n) * φ (ω (n + 1))
      ∂homogeneousPathMeasure (Measure.dirac s₀) K =
    ∫⁻ x, g x * ∫⁻ y, φ y ∂K x
      ∂(kernelIter K n) s₀ := by
  set P := homogeneousPathMeasure (Measure.dirac s₀) K
  set κ : (t : ℕ) →
      Kernel (∀ i : Finset.Iic t, α) (α) :=
    fun t => homogeneousHistoryKernel K t
  have hG : Measurable
      (fun u : α => g u * ∫⁻ y, φ y ∂K u) :=
    hg.mul (hφ.lintegral_kernel)
  set μ := P.map (frestrictLe n)
  have hPair : Measurable (fun ω : ℕ → α =>
      (frestrictLe n ω, ω (n + 1))) :=
    Measurable.prod (measurable_frestrictLe n)
      (measurable_pi_apply _)
  have hF : Measurable (fun p :
      (∀ i : Finset.Iic n, α) × α =>
      g (lastElem n α p.1) * φ p.2) :=
    (hg.comp ((lastElem_measurable n).comp
      measurable_fst)).mul
        (hφ.comp measurable_snd)
  have hCP : μ ⊗ₘ κ n = P.map (fun ω =>
      (frestrictLe n ω, ω (n + 1))) := by
    show P.map (frestrictLe n) ⊗ₘ κ n = _
    rw [show P = trajMeasure (X := fun _ => α)
      (κ := κ) (Measure.dirac s₀) from rfl]
    exact
      map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  haveI : IsProbabilityMeasure P := by
    simp only [P, homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [show μ = P.map (frestrictLe n) from rfl,
        Measure.map_apply (measurable_frestrictLe n)
          MeasurableSet.univ,
        Set.preimage_univ, measure_univ]
  calc ∫⁻ ω, g (ω n) * φ (ω (n + 1)) ∂P
    _ = ∫⁻ p, g (lastElem n α p.1) * φ p.2
          ∂(P.map (fun ω =>
            (frestrictLe n ω, ω (n + 1)))) :=
        (lintegral_map hF hPair).symm
    _ = ∫⁻ p, g (lastElem n α p.1) * φ p.2
          ∂(μ ⊗ₘ κ n) := by rw [hCP]
    _ = ∫⁻ h, ∫⁻ x, g (lastElem n α h) * φ x
          ∂(κ n h) ∂μ :=
        Measure.lintegral_compProd hF
    _ = ∫⁻ h, g (lastElem n α h) *
          ∫⁻ x, φ x ∂K (lastElem n α h) ∂μ := by
        congr 1; ext h
        rw [histKernel_eq_K_lastElem K n h,
            lintegral_const_mul _ hφ]
    _ = ∫⁻ u, g u * ∫⁻ x, φ x ∂K u
          ∂(μ.map (lastElem n α)) :=
        (lintegral_map hG
          (lastElem_measurable n)).symm
    _ = ∫⁻ x, g x * ∫⁻ y, φ y ∂K x
          ∂(kernelIter K n) s₀ := by
        congr 1
        rw [show μ = P.map (frestrictLe n) from rfl,
            Measure.map_map (lastElem_measurable n)
              (measurable_frestrictLe n),
            show (lastElem n α) ∘
              (frestrictLe (π := fun _ => α) n) =
              (fun ω => ω n)
              from funext (lastElem_frestrictLe n),
            homogeneousPathMeasure_dirac_marginal
              K s₀ n]

/-! ## Finite hitting bound for superharmonic functions -/

/-- Paths that visit `A` by time `N`. -/
def pathHitsBy {α : Type*} (A : Set α) (N : ℕ) : Set (ℕ → α) :=
  {ω | ∃ t, t ≤ N ∧ ω t ∈ A}

lemma measurableSet_pathHitsBy
    {α : Type*} [MeasurableSpace α]
    (A : Set α) (hA : MeasurableSet A) (N : ℕ) :
    MeasurableSet (pathHitsBy A N) := by
  have heq : pathHitsBy A N =
      ⋃ t : Fin (N + 1), (fun ω : ℕ → α => ω t.val) ⁻¹' A := by
    ext ω
    simp only [pathHitsBy, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, hmem⟩
      exact ⟨⟨t, by omega⟩, hmem⟩
    · rintro ⟨t, hmem⟩
      exact ⟨t.val, by omega, hmem⟩
  rw [heq]
  exact MeasurableSet.iUnion fun t => hA.preimage (measurable_pi_apply t.val)

lemma homogeneousPathMeasure_initial_ne_null
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (s : α) :
    homogeneousPathMeasure (Measure.dirac s) K {ω | ω 0 ≠ s} = 0 := by
  rw [show {ω : ℕ → α | ω 0 ≠ s} =
      (fun ω : ℕ → α => ω 0) ⁻¹' ({s} : Set α)ᶜ by ext; simp]
  rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton s).compl,
    homogeneousPathMeasure_dirac_marginal, kernelIter_zero, Kernel.id_apply]
  simp

/-- `kernelIter K 1 = K`, for an arbitrary state space. -/
lemma kernelIter_one_generic
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] :
    kernelIter K 1 = K := by
  ext x S hS
  rw [show (1 : ℕ) = 0 + 1 from rfl, kernelIter_succ, kernelIter_zero,
    Kernel.comp_apply, Kernel.id_apply]
  rw [Measure.dirac_bind (Kernel.measurable _) x]

/-- A nonnegative superharmonic function bounds the probability of hitting a
    set on which its value is at least one.  This is the finite-time
    optional-stopping inequality used by the consensus arguments. -/
lemma homogeneousPathMeasure_hitBy_le
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (f : α → ENNReal) (A : Set α)
    (hA : ∀ x ∈ A, 1 ≤ f x)
    (hSuper : ∀ x, ∫⁻ y, f y ∂K x ≤ f x)
    (s : α) (N : ℕ) :
    homogeneousPathMeasure (Measure.dirac s) K (pathHitsBy A N) ≤ f s := by
  induction N generalizing s with
  | zero =>
      letI : IsProbabilityMeasure
          (homogeneousPathMeasure (Measure.dirac s) K) := by
        simp only [homogeneousPathMeasure]
        infer_instance
      by_cases hs : s ∈ A
      · exact prob_le_one.trans (hA s hs)
      · have hsub : pathHitsBy A 0 ⊆ {ω : ℕ → α | ω 0 ≠ s} := by
          rintro ω ⟨t, ht, hmem⟩
          simp only [Set.mem_setOf_eq] at *
          have ht0 : t = 0 := by omega
          subst t
          exact fun heq => hs (heq ▸ hmem)
        calc
          homogeneousPathMeasure (Measure.dirac s) K (pathHitsBy A 0)
              ≤ homogeneousPathMeasure (Measure.dirac s) K {ω | ω 0 ≠ s} :=
                measure_mono hsub
          _ = 0 := homogeneousPathMeasure_initial_ne_null K s
          _ ≤ f s := bot_le
  | succ n ih =>
      letI : IsProbabilityMeasure
          (homogeneousPathMeasure (Measure.dirac s) K) := by
        simp only [homogeneousPathMeasure]
        infer_instance
      by_cases hs : s ∈ A
      · exact prob_le_one.trans (hA s hs)
      · let P := homogeneousPathMeasure (Measure.dirac s) K
        let B : α → Set (ℕ → α) := fun x => {ω | ω 1 = x}
        have hInit : P {ω | ω 0 ≠ s} = 0 :=
          homogeneousPathMeasure_initial_ne_null K s
        have hsub : pathHitsBy A (n + 1) ⊆
            {ω | ω 0 ≠ s} ∪
              ⋃ x, B x ∩ (pathShift 1) ⁻¹' pathHitsBy A n := by
          intro ω hω
          by_cases h0 : ω 0 = s
          · right
            obtain ⟨t, ht, hmem⟩ := hω
            have htpos : 0 < t := by
              by_contra hnpos
              have : t = 0 := by omega
              subst t
              exact hs (h0 ▸ hmem)
            refine Set.mem_iUnion.mpr ⟨ω 1, rfl, ?_⟩
            exact ⟨t - 1, by omega, by
              simpa only [pathShift, show 1 + (t - 1) = t by omega] using hmem⟩
          · left
            exact h0
        calc
          P (pathHitsBy A (n + 1))
              ≤ P ({ω | ω 0 ≠ s} ∪
                  ⋃ x, B x ∩ (pathShift 1) ⁻¹' pathHitsBy A n) :=
                measure_mono hsub
          _ ≤ P {ω | ω 0 ≠ s} +
                P (⋃ x, B x ∩ (pathShift 1) ⁻¹' pathHitsBy A n) :=
                measure_union_le _ _
          _ = P (⋃ x, B x ∩ (pathShift 1) ⁻¹' pathHitsBy A n) := by
                rw [hInit, zero_add]
          _ ≤ ∑' x, P (B x ∩ (pathShift 1) ⁻¹' pathHitsBy A n) :=
                measure_iUnion_le _
          _ ≤ ∑' x, f x * P (B x) := by
                apply ENNReal.tsum_le_tsum
                intro x
                exact homogeneousPathMeasure_markov_bound K s 1 (f x)
                  (B x) (pathHitsBy A n)
                  (by measurability)
                  (measurableSet_pathHitsBy A (Set.to_countable A).measurableSet n)
                  (by
                    intro ω ω' heq hω
                    show ω' 1 = x
                    rw [← heq 1 le_rfl]
                    exact hω)
                  (by
                    intro ω hω
                    have hx : ω 1 = x := hω
                    simpa [hx] using ih x)
          _ = ∫⁻ x, f x ∂K s := by
                rw [lintegral_countable']
                apply tsum_congr
                intro x
                congr 1
                change homogeneousPathMeasure (Measure.dirac s) K
                    {ω : ℕ → α | ω 1 = x} = K s {x}
                rw [show {ω : ℕ → α | ω 1 = x} =
                    (fun ω : ℕ → α => ω 1) ⁻¹' {x} by ext; simp,
                  ← Measure.map_apply (measurable_pi_apply 1)
                    (measurableSet_singleton x),
                  homogeneousPathMeasure_dirac_marginal,
                  kernelIter_one_generic]
          _ ≤ f s := hSuper s

/-! ## Birth-death chain: drift at a state -/

/-- Nat.cast is integrable against a smul-Dirac measure. -/
private lemma integrable_natCast_smul_dirac (c : ENNReal) (n : ℕ) (hc : c ≠ ⊤) :
    Integrable (fun x : ℕ => (x : ℝ)) (c • Measure.dirac n) :=
  (integrable_dirac (f := fun x : ℕ => (x : ℝ)) enorm_lt_top).smul_measure hc

/-- Bochner integral of the identity against `bdKernel N n` for `n > 0`:
    `∫ x ∂(bdKernel N n) = n + p(n) - q(n)`. -/
lemma bd_kernel_integral_id (N : BirthDeathChain) (n : ℕ) (hn : 0 < n) :
    ∫ x, (x : ℝ) ∂(bdKernel N n) = (n : ℝ) + N.p n - N.q n := by
  simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
    ProbabilityTheory.Kernel.coe_mk, holdProb]
  have hint : ∀ (r : ℝ) (m : ℕ),
      Integrable (fun x : ℕ => (x : ℝ)) (ENNReal.ofReal r • Measure.dirac m) :=
    fun r m => integrable_natCast_smul_dirac _ m ENNReal.ofReal_ne_top
  rw [integral_add_measure ((hint _ (n + 1)).add_measure (hint _ (n - 1))) (hint _ n),
      integral_add_measure (hint _ (n + 1)) (hint _ (n - 1))]
  simp only [integral_smul_measure, integral_dirac]
  have hp := N.p_nonneg n
  have hq := N.q_nonneg n
  have hpq := N.pq_le_one n
  rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq,
      ENNReal.toReal_ofReal (by linarith)]
  rcases n with _ | n
  · omega
  · simp only [smul_eq_mul, Nat.succ_sub_one]; push_cast; ring

/-- Bochner integral of the identity against `bdKernel N 0` is 0 (absorbing). -/
lemma bd_kernel_integral_id_zero (N : BirthDeathChain) :
    ∫ x, (x : ℝ) ∂(bdKernel N 0) = 0 := by
  have ⟨hp, hq⟩ := N.absorb_zero
  simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
    ProbabilityTheory.Kernel.coe_mk, holdProb, hp, hq,
    ENNReal.ofReal_zero, zero_smul, zero_add, sub_zero, ENNReal.ofReal_one, one_smul]
  rw [integral_dirac]; simp

/-- Combined: integral of identity for all `n` (including absorbing state 0). -/
lemma bd_kernel_integral_id_all (N : BirthDeathChain) (n : ℕ) :
    ∫ x, (x : ℝ) ∂(bdKernel N n) = (n : ℝ) + N.p n - N.q n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bd_kernel_integral_id_zero, N.absorb_zero.1, N.absorb_zero.2]
  · exact bd_kernel_integral_id N n hn

/-! ## Absorption infrastructure for birth-death chains -/

/-- Lower bound on lintegral from singleton contribution:
    `∫⁻ f dμ ≥ f(a) · μ({a})`. -/
lemma lintegral_ge_singleton_mul
    (f : ℕ → ℝ≥0∞) (a : ℕ) (μ : Measure ℕ) :
    f a * μ {a} ≤ ∫⁻ x, f x ∂μ := by
  have h1 : f a * μ {a} = ∫⁻ x in {a}, f x ∂μ := by
    rw [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac]
    exact mul_comm _ _
  rw [h1]
  exact setLIntegral_le_lintegral _ _

/-- General version: for any measurable space with singleton classes. -/
lemma lintegral_ge_singleton_mul_general
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → ℝ≥0∞) (a : α) (μ : Measure α) :
    f a * μ {a} ≤ ∫⁻ x, f x ∂μ := by
  have h1 : f a * μ {a} = ∫⁻ x in {a}, f x ∂μ := by
    rw [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac]
    exact mul_comm _ _
  rw [h1]
  exact setLIntegral_le_lintegral _ _

/-- Iterated BD kernel at absorbing state 0 is `Dirac 0`. -/
lemma kernelIter_bdKernel_zero (N : BirthDeathChain) (n : ℕ)
    [IsMarkovKernel (bdKernel N)] :
    (kernelIter (bdKernel N) n) 0 = Measure.dirac 0 := by
  induction n with
  | zero => simp [kernelIter_zero, ProbabilityTheory.Kernel.id_apply]
  | succ n ih =>
    simp only [kernelIter_succ]
    rw [ProbabilityTheory.Kernel.comp_apply, ih]
    simp only [Measure.dirac_bind (ProbabilityTheory.Kernel.measurable _)]
    exact bdKernel_zero N

/-- Singleton mass for the down transition: `K(m)({m-1}) = q(m)` for `m > 0`. -/
lemma bdKernel_down_singleton (N : BirthDeathChain) (m : ℕ) (hm : 0 < m) :
    bdKernel N m {m - 1} = ENNReal.ofReal (N.q m) := by
  rw [bdKernel_apply_singleton]
  have h1 : ¬ (m - 1 = m + 1) := by omega
  have h2 : ¬ (m - 1 = m) := by omega
  simp [h1, h2]

/-- A finite product of positive ENNReal values is positive (Fin-indexed). -/
lemma ENNReal.fin_prod_pos {n : ℕ} {f : Fin n → ℝ≥0∞} (h : ∀ i, 0 < f i) :
    0 < ∏ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    exact ENNReal.mul_pos (ih (fun i => h i.castSucc)).ne' (h (Fin.last n)).ne'

/-- A finite product of positive ENNReal values is positive (Finset-indexed). -/
lemma ENNReal.finset_prod_pos {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → ℝ≥0∞}
    (h : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i := by
  revert h
  induction s using Finset.induction with
  | empty => intros; simp
  | @insert a s' hmem ih =>
    intro h
    rw [Finset.prod_insert hmem]
    apply ENNReal.mul_pos
    · exact (h _ (Finset.mem_insert_self _ _)).ne'
    · exact (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))).ne'

/-- **General path lower bound** (library lemma).
    Given a Markov kernel `K` on a countable measurable space and an explicit
    finite path given as a sequence `path : Fin (n + 1) → α`, the probability
    of reaching `path (Fin.last n)` from `path 0` in exactly `n` steps is at least
    the product of the consecutive one-step transition probabilities. -/
lemma kernelIter_path_lower
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : ProbabilityTheory.Kernel α α) [IsMarkovKernel K]
    (n : ℕ) (path : Fin (n + 1) → α) :
    (∏ i : Fin n, K (path i.castSucc) {path i.succ}) ≤
      (kernelIter K n) (path 0) {path (Fin.last n)} := by
  induction n with
  | zero =>
    simp [kernelIter_zero, Kernel.id_apply, Measure.dirac_apply', Fin.last]
  | succ n ih =>
    -- Split product: (∏ Fin(n+1)) = K(path 0){path 1} · (∏ i : Fin n, K(path(i+1)){path(i+2)})
    rw [Fin.prod_univ_succ]
    -- Tail path: path ∘ Fin.succ goes from path 1 to path (n+1)
    have ih' : (∏ i : Fin n, K ((path ∘ Fin.succ) i.castSucc) {(path ∘ Fin.succ) i.succ}) ≤
        (kernelIter K n) (path 1) {path (Fin.last (n + 1))} := by
      have := ih (path ∘ Fin.succ)
      simp only [Function.comp, Fin.castSucc_succ, Fin.succ_last] at this
      exact this
    -- K^(n+1)(path 0){path(n+1)} = ∫⁻ j, K^n(j){path(n+1)} d(K(path 0))
    -- using RIGHT decomposition K^(n+1) = K^n ∘ₖ K
    rw [kernelIter_succ_right, Kernel.comp_apply,
        Measure.bind_apply (measurableSet_singleton _) (Kernel.measurable _).aemeasurable]
    -- Bound: K(path 0){path 1} · (K^n)(path 1){path(n+1)} ≤ ∫⁻ j, K^n(j){...} d(K(path 0))
    have hkey : (kernelIter K n) (path (Fin.succ 0)) {path (Fin.last (n + 1))} *
            K (path 0) {path (Fin.succ 0)} ≤
        ∫⁻ j, (kernelIter K n) j {path (Fin.last (n + 1))} ∂K (path 0) :=
      lintegral_ge_singleton_mul_general
        (fun j => (kernelIter K n) j {path (Fin.last (n + 1))})
        (path (Fin.succ 0)) (K (path 0))
    calc K (path (Fin.castSucc 0)) {path (Fin.succ 0)} *
            ∏ i : Fin n, K (path (Fin.succ i).castSucc) {path (Fin.succ i).succ}
        ≤ K (path (Fin.castSucc 0)) {path (Fin.succ 0)} *
            (kernelIter K n) (path (Fin.succ 0)) {path (Fin.last (n + 1))} := by
          apply mul_le_mul_of_nonneg_left
          · convert ih' using 2 <;>
              first | rfl | simp [Fin.succ, Fin.castSucc]
          · exact zero_le
      _ ≤ ∫⁻ j, (kernelIter K n) j {path (Fin.last (n + 1))} ∂K (path 0) := by
          have heq : path (Fin.castSucc (0 : Fin (n+1))) = path 0 := by congr 1
          calc K (path (Fin.castSucc 0)) {path (Fin.succ 0)} *
                  (kernelIter K n) (path (Fin.succ 0)) {path (Fin.last (n + 1))}
              = (kernelIter K n) (path (Fin.succ 0)) {path (Fin.last (n + 1))} *
                  K (path 0) {path (Fin.succ 0)} := by
                rw [heq, mul_comm]
            _ ≤ _ := hkey

/-- `kernelIter K 1 = K`. -/
lemma kernelIter_one (K : Kernel ℕ ℕ) [IsMarkovKernel K] :
    kernelIter K 1 = K := by
  ext j s hs
  rw [show (1 : ℕ) = 0 + 1 from rfl, kernelIter_succ, kernelIter_zero]
  rw [Kernel.comp_apply, Kernel.id_apply]
  rw [Measure.dirac_bind (Kernel.measurable _) j]

/-- CK for lintegrals in the form needed for induction:
    `∫⁻ f d(K^{t+1})(n₀) = ∫⁻ (∫⁻ f dK(j)) d(K^t(n₀))`. -/
lemma kernelIter_succ_lintegral
    (K : Kernel ℕ ℕ) [IsMarkovKernel K]
    (t : ℕ) (n₀ : ℕ) (f : ℕ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂(kernelIter K (t + 1)) n₀ =
    ∫⁻ j, (∫⁻ x, f x ∂K j) ∂(kernelIter K t) n₀ := by
  rw [kernelIter_lintegral_add K t 1 n₀ f hf]
  congr 1; ext j; rw [kernelIter_one]

/-- One-step identity bound: `∫⁻ n d(K(j)) ≤ j + 1`.
    The expected position after one step is at most j + 1. -/
lemma bd_lintegral_id_bound_step (N : BirthDeathChain) (j : ℕ) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(bdKernel N j) ≤ (j : ℝ≥0∞) + 1 := by
  rw [bdKernel_apply, lintegral_add_measure, lintegral_add_measure,
      lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac, lintegral_dirac, lintegral_dirac]
  have hp := N.p_nonneg j; have hq := N.q_nonneg j; have hpq := N.pq_le_one j
  calc ENNReal.ofReal (N.p j) * ↑(j + 1) +
          ENNReal.ofReal (N.q j) * ↑(j - 1) +
          ENNReal.ofReal (holdProb N j) * ↑j
      ≤ ENNReal.ofReal (N.p j) * ↑(j + 1) +
          ENNReal.ofReal (N.q j) * ↑(j + 1) +
          ENNReal.ofReal (holdProb N j) * ↑(j + 1) := by
        gcongr
        · exact_mod_cast (by omega : (j - 1 : ℕ) ≤ j + 1)
        · exact_mod_cast (by omega : j ≤ j + 1)
    _ = (ENNReal.ofReal (N.p j) + ENNReal.ofReal (N.q j) +
          ENNReal.ofReal (holdProb N j)) * ↑(j + 1) := by ring
    _ = 1 * ↑(j + 1) := by
        congr 1
        rw [← ENNReal.ofReal_add hp hq,
            ← ENNReal.ofReal_add (by linarith) (by unfold holdProb; linarith),
            show N.p j + N.q j + holdProb N j = 1 from by unfold holdProb; ring]
        exact ENNReal.ofReal_one
    _ = ↑(j + 1 : ℕ) := one_mul _
    _ = (↑j : ℝ≥0∞) + 1 := by push_cast; ring

/-- Inductive bound: `∫⁻ n d(K^t)(n₀) ≤ n₀ + t`.
    The expected position after t steps grows at most linearly. -/
lemma bd_lintegral_id_bound
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ ≤ ↑n₀ + ↑t := by
  induction t with
  | zero =>
    simp [kernelIter_zero, Kernel.id_apply, lintegral_dirac]
  | succ t ih =>
    rw [kernelIter_succ_lintegral _ _ _ _ (measurable_of_countable _)]
    calc ∫⁻ j, (∫⁻ n, (n : ℝ≥0∞) ∂(bdKernel N j)) ∂(kernelIter (bdKernel N) t) n₀
        ≤ ∫⁻ j, ((j : ℝ≥0∞) + 1) ∂(kernelIter (bdKernel N) t) n₀ :=
          lintegral_mono (fun j => bd_lintegral_id_bound_step N j)
      _ = ∫⁻ j, (j : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ +
          ∫⁻ _, 1 ∂(kernelIter (bdKernel N) t) n₀ :=
          lintegral_add_left (measurable_of_countable _) _
      _ = ∫⁻ j, (j : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ + 1 := by
          have : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
            (kernelIter_isMarkov t).isProbabilityMeasure n₀
          rw [lintegral_one, measure_univ]
      _ ≤ (↑n₀ + ↑t) + 1 := by gcongr
      _ = ↑n₀ + ↑(t + 1) := by push_cast; ring

/-- bdKernel at state 0 equals Dirac at 0 (absorbing state). -/
lemma bdKernel_zero_eq_dirac (N : BirthDeathChain) :
    bdKernel N 0 = Measure.dirac 0 := by
  ext s hs
  have ⟨hp, hq⟩ := N.absorb_zero
  rw [bdKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  simp [hp, hq, holdProb, Measure.dirac_apply' _ hs]

/-- Lintegral w.r.t. bdKernel at 0 reduces to evaluation at 0. -/
lemma bdKernel_zero_lintegral (N : BirthDeathChain) (f : ℕ → ℝ≥0∞) :
    ∫⁻ y, f y ∂(bdKernel N 0) = f 0 := by
  rw [bdKernel_zero_eq_dirac, lintegral_dirac]

/-- Path measure marginal: P(ω(t) ∈ S) = K^t(n₀)(S). -/
lemma bdPathMeasure_coord_eq
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) (S : Set ℕ) (hS : MeasurableSet S) :
    bdPathMeasure N n₀ {ω | ω t ∈ S} = (kernelIter (bdKernel N) t) n₀ S := by
  unfold bdPathMeasure
  rw [show {ω : ℕ → ℕ | ω t ∈ S} = (fun ω => ω t) ⁻¹' S from rfl,
      ← Measure.map_apply (measurable_pi_apply t) hS,
      homogeneousPathMeasure_dirac_marginal]

/-- Under the BD path measure, P(ω(t)=0 ∧ ω(t+1)≠0) = 0.
    This expresses that 0 is absorbing at the path level. -/
lemma bdPathMeasure_absorbing_step
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    bdPathMeasure N n₀ {ω | ω t = 0 ∧ ω (t + 1) ≠ 0} = 0 := by
  unfold bdPathMeasure
  set P := homogeneousPathMeasure (Measure.dirac n₀) (bdKernel N)
  suffices h : ∫⁻ ω, (Set.indicator {(0 : ℕ)} 1 (ω t)) *
               (Set.indicator {(0 : ℕ)}ᶜ 1 (ω (t + 1))) ∂P = 0 by
    apply le_antisymm _ zero_le
    calc P {ω | ω t = 0 ∧ ω (t + 1) ≠ 0}
        ≤ ∫⁻ ω, (Set.indicator {(0 : ℕ)} 1 (ω t)) *
               (Set.indicator {(0 : ℕ)}ᶜ 1 (ω (t + 1))) ∂P := by
          rw [← lintegral_indicator_one (by measurability :
            MeasurableSet {ω : ℕ → ℕ | ω t = 0 ∧ ω (t + 1) ≠ 0})]
          apply lintegral_mono; intro ω
          simp only [Set.indicator, Set.mem_setOf_eq, Set.mem_singleton_iff,
                     Set.mem_compl_iff, Pi.one_apply]
          split <;> simp_all
      _ = 0 := h
  rw [homogeneousPathMeasure_joint_lintegral _ n₀ t _ _
      (measurable_of_countable _) (measurable_of_countable _)]
  have : ∀ x : ℕ, Set.indicator {(0 : ℕ)} 1 x *
      ∫⁻ y, Set.indicator {(0 : ℕ)}ᶜ 1 y ∂(bdKernel N x) = 0 := by
    intro x
    by_cases hx : x = 0
    · subst hx; rw [bdKernel_zero_lintegral]
      simp [Set.indicator, Set.mem_compl_iff]
    · simp [Set.indicator, hx]
  simp_rw [this, lintegral_zero]

/-- If ω(t) = 0, then the extinction time is ≤ t. -/
lemma ext_time_le_of_zero (ω : ℕ → ℕ) (t : ℕ) (h0 : ω t = 0) :
    extinctionTime ω ≤ t :=
  hittingAfter_le_iff.mpr ⟨t, ⟨Nat.zero_le _, le_refl _⟩, by simp [natCoord, h0]⟩

/-- If the extinction time is ≤ t, there exists a hitting time j ≤ t. -/
lemma ext_time_hit_exists (ω : ℕ → ℕ) (t : ℕ) (hτ : extinctionTime ω ≤ t) :
    ∃ j, j ≤ t ∧ ω j = 0 := by
  obtain ⟨j, ⟨_, hjt⟩, hj⟩ := hittingAfter_le_iff.mp hτ
  exact ⟨j, hjt, by simpa [natCoord] using hj⟩

/-- If the extinction time is > t, then ω(t) ≠ 0. -/
lemma ext_time_gt_imp_nonzero (ω : ℕ → ℕ) (t : ℕ)
    (hτ : (t : WithTop ℕ) < extinctionTime ω) : ω t ≠ 0 := by
  intro h0; exact absurd (ext_time_le_of_zero ω t h0) (not_le.mpr hτ)

/-! ## Integrability and drift telescoping -/

/-- The identity function is integrable w.r.t. K^t(n₀) (from finite lintegral). -/
lemma bd_integrable_id
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    Integrable (fun x : ℕ => (x : ℝ)) ((kernelIter (bdKernel N) t) n₀) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ (x : ℕ), (‖(x : ℝ)‖₊ : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀
      = ∫⁻ (x : ℕ), (x : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ := by
        congr 1; ext x; rw [Real.nnnorm_natCast, ENNReal.coe_natCast]
    _ ≤ ↑n₀ + ↑t := bd_lintegral_id_bound N n₀ t
    _ < ⊤ := by simp

/-- Any ℝ-valued function bounded by 1 is integrable on a probability measure. -/
lemma integrable_of_bounded_on_prob {f : ℕ → ℝ} (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ∂μ
      ≤ ∫⁻ _, 1 ∂μ := by
        apply lintegral_mono; intro x; simp; exact_mod_cast hb x
    _ = 1 := by rw [lintegral_one, measure_univ]
    _ < ⊤ := ENNReal.one_lt_top

/-- The drift function p - q is integrable on any probability measure over ℕ. -/
lemma bd_integrable_drift (N : BirthDeathChain) (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Integrable (fun x : ℕ => N.p x - N.q x) μ := by
  apply integrable_of_bounded_on_prob μ (measurable_of_countable _)
  intro x; rw [abs_le]
  exact ⟨by linarith [N.p_nonneg x, N.q_nonneg x, N.pq_le_one x],
         by linarith [N.p_nonneg x, N.q_nonneg x, N.pq_le_one x]⟩

/-- One-step drift telescope: E[X_{t+1}] = E[X_t] + ∫ (p-q) d(K^t)(n₀). -/
lemma bd_drift_telescope
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) (t + 1)) n₀ =
    ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) t) n₀ +
    ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) t) n₀ := by
  rw [kernelIter_succ]
  have hint : Integrable (fun x : ℕ => (x : ℝ))
      ((bdKernel N ∘ₖ kernelIter (bdKernel N) t) n₀) := by
    rw [← kernelIter_succ]; exact bd_integrable_id N n₀ (t + 1)
  rw [Kernel.integral_comp hint]
  simp_rw [bd_kernel_integral_id_all]
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    (kernelIter_isMarkov t).isProbabilityMeasure n₀
  rw [show (fun x : ℕ => (x : ℝ) + N.p x - N.q x) =
      (fun x : ℕ => (x : ℝ) + (N.p x - N.q x)) from by ext x; ring]
  rw [integral_add (bd_integrable_id N n₀ t) (bd_integrable_drift N _)]

/-- Full drift telescoping: E[X_T] = n₀ + Σ_{t<T} ∫ (p-q) d(K^t)(n₀). -/
lemma bd_telescope_sum
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (T : ℕ) :
    ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) T) n₀ =
    ↑n₀ + ∑ t ∈ Finset.range T,
      ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) t) n₀ := by
  induction T with
  | zero => simp [kernelIter_zero, Kernel.id_apply, integral_dirac]
  | succ T ih => rw [bd_drift_telescope, ih, Finset.sum_range_succ]; ring

/-! ## Markov inequality and survival bounds -/

/-- E[X_t] ≥ 0 since X_t takes values in ℕ. -/
lemma bd_expected_nonneg
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    0 ≤ ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) t) n₀ :=
  integral_nonneg fun x => Nat.cast_nonneg x

/-- Absorption probability is non-decreasing in time. -/
lemma bd_absorption_mono
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    (kernelIter (bdKernel N) t) n₀ {0} ≤
    (kernelIter (bdKernel N) (t + 1)) n₀ {0} := by
  rw [kernelIter_succ]
  have hmeas : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  calc (kernelIter (bdKernel N) t n₀) {0}
      = ∫⁻ j, ({0} : Set ℕ).indicator 1 j ∂(kernelIter (bdKernel N) t) n₀ := by
        rw [lintegral_indicator_one hmeas]
    _ ≤ ∫⁻ j, (bdKernel N j) {0} ∂(kernelIter (bdKernel N) t) n₀ := by
        apply lintegral_mono; intro j
        simp only [Set.indicator_apply, Pi.one_apply]
        split_ifs with hj
        · simp only [Set.mem_singleton_iff] at hj; subst hj
          rw [bdKernel_zero_eq_dirac N, Measure.dirac_apply' 0 hmeas]; simp
        · exact zero_le
    _ = (Kernel.comp (bdKernel N) (kernelIter (bdKernel N) t)) n₀ {0} := by
        rw [Kernel.comp_apply' _ _ _ hmeas]

/-- P(X_t ≥ 1) ≤ E[X_t] (Markov inequality, Bochner integral version). -/
lemma bd_survival_le_expected
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    ((kernelIter (bdKernel N) t) n₀ {0}ᶜ).toReal ≤
    ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) t) n₀ := by
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    (kernelIter_isMarkov t).isProbabilityMeasure n₀
  calc ((kernelIter (bdKernel N) t n₀) {0}ᶜ).toReal
      ≤ (∫⁻ x, (x : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀).toReal := by
        apply ENNReal.toReal_mono
        · exact ne_top_of_le_ne_top (by simp) (bd_lintegral_id_bound N n₀ t)
        · calc (kernelIter (bdKernel N) t n₀) {0}ᶜ
              = ∫⁻ x, ({0}ᶜ : Set ℕ).indicator 1 x ∂(kernelIter (bdKernel N) t) n₀ := by
                rw [lintegral_indicator_one (MeasurableSet.compl (measurableSet_singleton 0))]
            _ ≤ ∫⁻ x, (x : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ := by
                apply lintegral_mono; intro x
                simp only [Set.indicator_apply, Pi.one_apply]
                split_ifs with hx
                · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx
                · exact zero_le
    _ = ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) t) n₀ := by
        rw [integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun x => Nat.cast_nonneg x)
          (measurable_of_countable _).aestronglyMeasurable]
        congr 1; congr 1; ext x; simp [ENNReal.ofReal_natCast]

/-- When drift ≤ 0 globally (p(n) ≤ q(n) for all n ≥ 1), E[X_t] ≤ n₀. -/
lemma bd_expected_nonincreasing
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (hDrift : ∀ n, 0 < n → N.p n ≤ N.q n) (T : ℕ) :
    ∫ x, (x : ℝ) ∂(kernelIter (bdKernel N) T) n₀ ≤ ↑n₀ := by
  -- Prove by induction using drift telescope
  induction T with
  | zero => simp [kernelIter_zero, Kernel.id_apply, integral_dirac]
  | succ T ih =>
    rw [bd_drift_telescope]
    have hdrift_int : ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) T) n₀ ≤ 0 := by
      apply integral_nonpos_of_ae; apply ae_of_all; intro x
      show N.p x - N.q x ≤ 0
      by_cases hx : x = 0
      · subst hx; simp [N.absorb_zero.1, N.absorb_zero.2]
      · linarith [hDrift x (Nat.pos_of_ne_zero hx)]
    linarith

/-- For a NiceChain, the drift is bounded above: p(n) - q(n) ≤ C/n - D. -/
lemma nice_drift_upper (N : NiceChain) (n : ℕ) (hn : 0 < n) :
    N.toBirthDeathChain.p n - N.toBirthDeathChain.q n ≤
      N.C / (n : ℝ) - N.D := by
  have hp := N.p_le n hn
  have hq := N.q_ge n hn
  linarith

/-- For large enough `n` in a NiceChain, the drift is at most `-D/2`. -/
lemma nice_drift_neg (N : NiceChain) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      N.toBirthDeathChain.p n - N.toBirthDeathChain.q n ≤ -N.D / 2 := by
  -- Choose n₀ such that C/n₀ ≤ D/2
  use Nat.ceil (2 * N.C / N.D) + 1
  intro n hn hn_pos
  have hD := N.D_pos
  have hC := N.C_pos
  have := nice_drift_upper N n hn_pos
  have hn_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have : N.C / (n : ℝ) ≤ N.D / 2 := by
    rw [div_le_div_iff₀ hn_real (by positivity)]
    have h1 : (Nat.ceil (2 * N.C / N.D) : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have h2 : 2 * N.C / N.D ≤ Nat.ceil (2 * N.C / N.D) := Nat.le_ceil _
    have h3 : 2 * N.C / N.D ≤ (n : ℝ) - 1 := by linarith
    have h4 : 2 * N.C ≤ N.D * ((n : ℝ) - 1) := by
      have := (div_le_iff₀ (show (0:ℝ) < N.D by positivity)).mp h3
      linarith
    linarith
  linarith

/-! ## Tail sum formula and drift-based bounds -/

/-- For ℕ-valued functions, the Lebesgue integral equals the sum of tail probabilities:
    ∫⁻ f dμ = Σ_{k=0}^∞ μ{ω | k < f ω}.
    This is the discrete version of the layer cake formula. -/
lemma lintegral_nat_eq_tsum_meas_gt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℕ) (hf : Measurable f) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {ω | k < f ω} := by
  have key : ∀ ω, (f ω : ℝ≥0∞) = ∑' k : ℕ, {ω' | k < f ω'}.indicator (fun _ => 1) ω := by
    intro ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [tsum_eq_sum (s := Finset.range (f ω))]
    · simp only [Finset.sum_ite]
      rw [Finset.filter_true_of_mem, Finset.filter_false_of_mem]
      · simp
      · intro k hk; simp only [Finset.mem_range] at hk; omega
      · intro k hk; exact Finset.mem_range.mp hk
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      simp [show ¬ (k < f ω) by omega]
  conv_lhs => arg 2; ext ω; rw [key ω]
  rw [lintegral_tsum]
  · congr 1; ext k
    have hmeas : MeasurableSet {ω | k < f ω} := hf measurableSet_Ioi
    calc ∫⁻ a, {ω' | k < f ω'}.indicator (fun _ => 1) a ∂μ
        = ∫⁻ _ in {ω | k < f ω}, 1 ∂μ := lintegral_indicator hmeas _
      _ = μ {ω | k < f ω} := by simp [MeasureTheory.lintegral_const]
  · intro k
    exact (Measurable.indicator measurable_const (hf measurableSet_Ioi)).aemeasurable

/-- When drift ≤ -ε for all states ≥ 1, the drift integral at time t is
    bounded by -ε times the survival probability. -/
lemma bd_drift_integral_le_neg_eps
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (ε : ℝ)
    (hDrift : ∀ n, 0 < n → N.p n - N.q n ≤ -ε)
    (n₀ : ℕ) (t : ℕ) :
    ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) t) n₀ ≤
    -ε * (((kernelIter (bdKernel N) t) n₀) {j | 0 < j}).toReal := by
  set μ := (kernelIter (bdKernel N) t) n₀ with hμ_def
  haveI : IsMarkovKernel (kernelIter (bdKernel N) t) := kernelIter_isMarkov t
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  have hpw : ∀ j : ℕ, N.p j - N.q j ≤ -ε * Set.indicator {j | 0 < j} (fun _ => (1 : ℝ)) j := by
    intro j
    by_cases hj : 0 < j
    · simp only [Set.indicator_of_mem (show j ∈ {j | 0 < j} from hj), mul_one]
      linarith [hDrift j hj]
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [Set.indicator_of_notMem (show (0 : ℕ) ∉ ({j | 0 < j} : Set ℕ) by simp), mul_zero]
      linarith [N.absorb_zero.1, N.absorb_zero.2]
  have hint2 : Integrable (fun j : ℕ => -ε * Set.indicator {j | 0 < j} (fun _ => (1 : ℝ)) j) μ := by
    apply Integrable.const_mul
    exact (integrable_const 1).indicator ((Set.to_countable _).measurableSet)
  calc ∫ j, (N.p j - N.q j) ∂μ
      ≤ ∫ j, -ε * Set.indicator {j | 0 < j} (fun _ => (1 : ℝ)) j ∂μ :=
        integral_mono (bd_integrable_drift N μ) hint2 hpw
    _ = -ε * ∫ j, Set.indicator {j | 0 < j} (fun _ => (1 : ℝ)) j ∂μ :=
        integral_const_mul _ _
    _ = -ε * (μ {j | 0 < j}).toReal := by
        congr 1
        rw [integral_indicator ((Set.to_countable _).measurableSet)]
        simp [MeasureTheory.integral_const, smul_eq_mul]
        rfl

/-- Telescoped drift bound: for finite T, Σ_{t<T} P(X_t ≥ 1) ≤ n₀/ε
    when drift ≤ -ε for all states ≥ 1. Uses the identity
    0 ≤ E[X_T] = n₀ + Σ drift ≤ n₀ - ε · Σ P(X_t ≥ 1). -/
lemma bd_survival_sum_le_init
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (ε : ℝ) (hε : 0 < ε)
    (hDrift : ∀ n, 0 < n → N.p n - N.q n ≤ -ε)
    (n₀ : ℕ) (T : ℕ) :
    ∑ t ∈ Finset.range T, (((kernelIter (bdKernel N) t) n₀) {j | 0 < j}).toReal ≤ n₀ / ε := by
  have htel := bd_telescope_sum N n₀ T
  have hnonneg := bd_expected_nonneg N n₀ T
  have hdrift_sum : ∑ t ∈ Finset.range T,
      ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) t) n₀ ≤
      -ε * ∑ t ∈ Finset.range T, (((kernelIter (bdKernel N) t) n₀) {j | 0 < j}).toReal := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun t _ => bd_drift_integral_le_neg_eps N ε hDrift n₀ t)
  have h2 : ε * ∑ t ∈ Finset.range T,
      (((kernelIter (bdKernel N) t) n₀) {j | 0 < j}).toReal ≤ n₀ := by linarith
  rwa [le_div_iff₀ hε, mul_comm]

/-! ## Indicator telescoping for birth-death chains -/

/-- One-step kernel integral for the survival indicator 1_{·≥1}:
    ∫ 1_{·>0} d(bdK j) = 1_{j>0} - q(j)·1_{j=1}. -/
lemma bd_kernel_integral_survival (N : BirthDeathChain) (j : ℕ) :
    ∫ x, (if (0 : ℕ) < x then (1 : ℝ) else 0) ∂(bdKernel N j) =
    (if 0 < j then 1 else 0) - N.q j * (if j = 1 then 1 else 0) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [bdKernel_zero N, integral_dirac]; simp
  · simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
      ProbabilityTheory.Kernel.coe_mk, holdProb]
    have hint : ∀ (r : ℝ) (m : ℕ),
        Integrable (fun x : ℕ => if 0 < x then (1:ℝ) else 0)
          (ENNReal.ofReal r • Measure.dirac m) :=
      fun r m => integrable_ofReal_smul_dirac _ r m
    rw [integral_add_measure ((hint _ _).add_measure (hint _ _)) (hint _ _),
        integral_add_measure (hint _ _) (hint _ _)]
    simp only [integral_smul_measure, integral_dirac]
    have hp := N.p_nonneg j; have hq := N.q_nonneg j; have hpq := N.pq_le_one j
    rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq,
        ENNReal.toReal_ofReal (by linarith)]
    rcases j with _ | j; · omega
    rcases j with _ | j
    · simp; ring
    · have h1 : 0 < j.succ := Nat.succ_pos _
      simp [h1, show 0 < j + 2 by omega]

/-- Integrability of the survival indicator on probability measures. -/
lemma bd_integrable_survival (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Integrable (fun x : ℕ => if (0 : ℕ) < x then (1 : ℝ) else 0) μ := by
  have : (fun x : ℕ => if (0 : ℕ) < x then (1 : ℝ) else 0) =
      Set.indicator {x : ℕ | 0 < x} (fun _ => (1 : ℝ)) := by
    ext x; simp [Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]; exact (integrable_const 1).indicator ((Set.to_countable _).measurableSet)

/-- One-step survival indicator telescope:
    P(X_{t+1} ≥ 1) = P(X_t ≥ 1) - ∫ q(x)·1_{x=1} dμ_t. -/
lemma bd_survival_one_step
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    ∫ x, (if (0:ℕ) < x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) (t + 1)) n₀ =
    ∫ x, (if (0:ℕ) < x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) t) n₀ -
    ∫ x, (N.q x * if x = 1 then 1 else 0) ∂(kernelIter (bdKernel N) t) n₀ := by
  rw [kernelIter_succ]
  haveI : IsMarkovKernel (kernelIter (bdKernel N) t) := kernelIter_isMarkov t
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    (kernelIter_isMarkov t).isProbabilityMeasure n₀
  have hint_comp : Integrable (fun x : ℕ => if (0:ℕ) < x then (1:ℝ) else 0)
      ((bdKernel N ∘ₖ kernelIter (bdKernel N) t) n₀) := by
    rw [← kernelIter_succ]
    haveI : IsMarkovKernel (kernelIter (bdKernel N) (t+1)) := kernelIter_isMarkov (t+1)
    exact bd_integrable_survival _
  rw [Kernel.integral_comp hint_comp]
  simp_rw [bd_kernel_integral_survival]
  have hint2 : Integrable (fun x : ℕ => N.q x * if x = 1 then (1:ℝ) else 0)
      ((kernelIter (bdKernel N) t) n₀) := by
    have : (fun x : ℕ => N.q x * if x = 1 then (1:ℝ) else 0) =
        fun x => if x = 1 then N.q 1 else 0 := by ext x; by_cases hx : x = 1 <;> simp [hx]
    rw [this, show (fun x : ℕ => if x = 1 then N.q 1 else (0:ℝ)) =
        Set.indicator {1} (fun _ => N.q 1) from by ext x; simp [Set.indicator_apply]]
    exact (integrable_const _).indicator (measurableSet_singleton _)
  rw [integral_sub (bd_integrable_survival _) hint2]

/-- Full survival indicator telescope:
    P(X_T ≥ 1) = 1_{n₀>0} - Σ_{t<T} ∫ q(x)·1_{x=1} dμ_t. -/
lemma bd_survival_telescope_full
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (T : ℕ) :
    ∫ x, (if (0:ℕ) < x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) T) n₀ =
    (if 0 < n₀ then 1 else 0) -
    ∑ t ∈ Finset.range T, ∫ x, (N.q x * if x = 1 then 1 else 0) ∂(kernelIter (bdKernel N) t) n₀ := by
  induction T with
  | zero => simp [kernelIter_zero, Kernel.id_apply, integral_dirac]
  | succ T ih => rw [bd_survival_one_step, ih, Finset.sum_range_succ]; ring

/-- Integral of q(x)·1_{x=1} = q(1)·μ({1}). -/
lemma integral_q_singleton (N : BirthDeathChain) (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    ∫ x, (N.q x * if x = 1 then (1:ℝ) else 0) ∂μ = N.q 1 * (μ {1}).toReal := by
  have : (fun x : ℕ => N.q x * if x = 1 then (1:ℝ) else 0) =
      fun x => if x = 1 then N.q 1 else 0 := by ext x; by_cases hx : x = 1 <;> simp [hx]
  rw [this, show (fun x : ℕ => if x = 1 then N.q 1 else (0:ℝ)) =
      Set.indicator {1} (fun _ => N.q 1) from by ext x; simp [Set.indicator_apply]]
  rw [integral_indicator (measurableSet_singleton _)]
  simp [MeasureTheory.integral_const, smul_eq_mul]; ring

/-- Bound on total expected time at state 1: Σ_{t<T} P(X_t=1) ≤ 1/δ. -/
lemma bd_sum_singleton_one_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (n₀ : ℕ) (hn₀ : 0 < n₀) (T : ℕ) :
    ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {1}).toReal ≤ 1 / δ := by
  have htel := bd_survival_telescope_full N n₀ T
  haveI : ∀ t, IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    fun t => (kernelIter_isMarkov t).isProbabilityMeasure n₀
  have hsurv_nn : 0 ≤ ∫ x, (if (0:ℕ) < x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) T) n₀ :=
    integral_nonneg (fun x => by by_cases h : 0 < x <;> simp [h])
  have hq1_sum : ∑ t ∈ Finset.range T,
      ∫ x, (N.q x * if x = 1 then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) t) n₀ =
      N.q 1 * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {1}).toReal := by
    rw [Finset.mul_sum]; congr 1; ext t; exact integral_q_singleton N _
  rw [htel, if_pos hn₀] at hsurv_nn; rw [hq1_sum] at hsurv_nn
  have hq1 : δ ≤ N.q 1 := hDeath 1 Nat.one_pos
  have hsum_nn : 0 ≤ ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {1}).toReal :=
    Finset.sum_nonneg (fun t _ => ENNReal.toReal_nonneg)
  rw [le_div_iff₀ hδ, mul_comm]
  calc δ * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {1}).toReal
      ≤ N.q 1 * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {1}).toReal :=
        mul_le_mul_of_nonneg_right hq1 hsum_nn
    _ ≤ 1 := by linarith

/-- One-step kernel integral for the indicator 1_{·≥k} (k ≥ 1):
    ∫ 1_{·≥k} d(bdK j) = 1_{j≥k} + p(k-1)·1_{j=k-1,j≥1} - q(k)·1_{j=k}. -/
lemma bd_kernel_integral_ge_k (N : BirthDeathChain) (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
    ∫ x, (if k ≤ x then (1 : ℝ) else 0) ∂(bdKernel N j) =
    (if k ≤ j then 1 else 0) + N.p (k-1) * (if j = k - 1 ∧ 1 ≤ j then 1 else 0)
    - N.q k * (if j = k then 1 else 0) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [bdKernel_zero N, integral_dirac]
    simp only [show ¬ (k ≤ 0) from by omega, ite_false, show ¬ (0 = k) from by omega]
    norm_num
  · simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
      ProbabilityTheory.Kernel.coe_mk, holdProb]
    have hint : ∀ (r : ℝ) (m : ℕ),
        Integrable (fun x : ℕ => if k ≤ x then (1:ℝ) else 0)
          (ENNReal.ofReal r • Measure.dirac m) :=
      fun r m => integrable_ofReal_smul_dirac _ r m
    rw [integral_add_measure ((hint _ _).add_measure (hint _ _)) (hint _ _),
        integral_add_measure (hint _ _) (hint _ _)]
    simp only [integral_smul_measure, integral_dirac]
    have hp := N.p_nonneg j; have hq := N.q_nonneg j; have hpq := N.pq_le_one j
    rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq,
        ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    by_cases hjk : j < k - 1
    · simp only [show ¬ (k ≤ j + 1) from by omega, show ¬ (k ≤ j - 1) from by omega,
                  show ¬ (k ≤ j) from by omega, ite_false,
                  show ¬ (j = k - 1 ∧ 1 ≤ j) from by omega, show ¬ (j = k) from by omega]
      ring
    · by_cases hjk2 : j = k - 1
      · subst hjk2
        simp only [show k ≤ k - 1 + 1 from by omega, ite_true,
                    show ¬ (k ≤ k - 1 - 1) from by omega, ite_false,
                    show ¬ (k ≤ k - 1) from by omega,
                    show ¬ (k - 1 = k) from by omega, show 1 ≤ k - 1 from by omega, and_self]
        ring
      · by_cases hjk3 : j = k
        · simp only [hjk3, show k ≤ k + 1 from by omega, ite_true,
                      show ¬ (k ≤ k - 1) from by omega, ite_false, le_refl,
                      show ¬ (k = k - 1 ∧ 1 ≤ k) from by omega]
          ring
        · simp only [show k ≤ j + 1 from by omega, ite_true,
                      show k ≤ j - 1 from by omega, show k ≤ j from by omega,
                      show ¬ (j = k - 1 ∧ 1 ≤ j) from by omega,
                      show ¬ (j = k) from by omega, ite_false]
          ring

/-- Integrability of the drift for the ≥k indicator. -/
lemma bd_integrable_ge_k_drift (N : BirthDeathChain) (k : ℕ) (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Integrable (fun x : ℕ => N.p (k-1) * (if x = k - 1 ∧ 1 ≤ x then (1:ℝ) else 0)
        - N.q k * (if x = k then 1 else 0)) μ := by
  apply Integrable.sub
  · apply Integrable.const_mul
    have : (fun x : ℕ => if x = k - 1 ∧ 1 ≤ x then (1:ℝ) else 0) =
        Set.indicator {x : ℕ | x = k - 1 ∧ 1 ≤ x} (fun _ => 1) := by
      ext x; simp [Set.indicator_apply, Set.mem_setOf_eq]
    rw [this]; exact (integrable_const _).indicator ((Set.to_countable _).measurableSet)
  · apply Integrable.const_mul
    have : (fun x : ℕ => if x = k then (1:ℝ) else 0) =
        Set.indicator {k} (fun _ => 1) := by ext x; simp [Set.indicator_apply]
    rw [this]; exact (integrable_const _).indicator (measurableSet_singleton _)

/-- Integrability of the ≥k indicator. -/
lemma bd_integrable_ge_k (k : ℕ) (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Integrable (fun x : ℕ => if k ≤ x then (1 : ℝ) else 0) μ := by
  have : (fun x : ℕ => if k ≤ x then (1 : ℝ) else 0) =
      Set.indicator {x : ℕ | k ≤ x} (fun _ => 1) := by
    ext x; simp [Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]; exact (integrable_const _).indicator ((Set.to_countable _).measurableSet)

/-- One-step telescope for the ≥k indicator. -/
lemma bd_ge_k_one_step
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (k : ℕ) (hk : 1 ≤ k) (n₀ : ℕ) (t : ℕ) :
    ∫ x, (if k ≤ x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) (t + 1)) n₀ =
    ∫ x, (if k ≤ x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) t) n₀ +
    ∫ x, (N.p (k-1) * (if x = k-1 ∧ 1 ≤ x then (1:ℝ) else 0)
        - N.q k * (if x = k then 1 else 0)) ∂(kernelIter (bdKernel N) t) n₀ := by
  rw [kernelIter_succ]
  haveI : IsMarkovKernel (kernelIter (bdKernel N) t) := kernelIter_isMarkov t
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    (kernelIter_isMarkov t).isProbabilityMeasure n₀
  have hint_comp : Integrable (fun x : ℕ => if k ≤ x then (1:ℝ) else 0)
      ((bdKernel N ∘ₖ kernelIter (bdKernel N) t) n₀) := by
    rw [← kernelIter_succ]
    haveI : IsMarkovKernel (kernelIter (bdKernel N) (t+1)) := kernelIter_isMarkov (t+1)
    exact bd_integrable_ge_k k _
  rw [Kernel.integral_comp hint_comp]
  simp_rw [bd_kernel_integral_ge_k N k hk]
  have hint1 := bd_integrable_ge_k k ((kernelIter (bdKernel N) t) n₀)
  have hint2 := bd_integrable_ge_k_drift N k ((kernelIter (bdKernel N) t) n₀)
  have heq : (fun j : ℕ => (if k ≤ j then (1:ℝ) else 0) +
      N.p (k - 1) * (if j = k - 1 ∧ 1 ≤ j then 1 else 0) -
      N.q k * (if j = k then 1 else 0)) =
    (fun j : ℕ => (if k ≤ j then (1:ℝ) else 0) +
      (N.p (k - 1) * (if j = k - 1 ∧ 1 ≤ j then 1 else 0) -
        N.q k * (if j = k then 1 else 0))) := by ext j; ring
  rw [heq, integral_add hint1 hint2]

/-- Full telescope for the ≥k indicator:
    P(X_T ≥ k) = 1_{n₀≥k} + Σ_{t<T} [p(k-1)·P(X_t=k-1) - q(k)·P(X_t=k)]. -/
lemma bd_ge_k_telescope
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (k : ℕ) (hk : 1 ≤ k) (n₀ : ℕ) (T : ℕ) :
    ∫ x, (if k ≤ x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) T) n₀ =
    (if k ≤ n₀ then 1 else 0) +
    ∑ t ∈ Finset.range T,
      ∫ x, (N.p (k-1) * (if x = k-1 ∧ 1 ≤ x then (1:ℝ) else 0)
          - N.q k * (if x = k then 1 else 0)) ∂(kernelIter (bdKernel N) t) n₀ := by
  induction T with
  | zero => simp [kernelIter_zero, Kernel.id_apply, integral_dirac]
  | succ T ih => rw [bd_ge_k_one_step N k hk, ih, Finset.sum_range_succ]; ring

/-- Drift integral for the ≥k indicator in terms of singleton measures. -/
lemma integral_ge_k_drift (N : BirthDeathChain) (k : ℕ) (hk : 1 ≤ k)
    (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    ∫ x, (N.p (k-1) * (if x = k-1 ∧ 1 ≤ x then (1:ℝ) else 0)
        - N.q k * (if x = k then 1 else 0)) ∂μ =
    N.p (k-1) * (if 1 ≤ k - 1 then (μ {k-1}).toReal else 0) - N.q k * (μ {k}).toReal := by
  rw [integral_sub]
  · congr 1
    · rw [integral_const_mul]; congr 1
      by_cases hk1 : 1 ≤ k - 1
      · simp only [hk1, ite_true]
        have heq : (fun x : ℕ => if x = k - 1 ∧ 1 ≤ x then (1:ℝ) else 0) =
            fun x => if x = k - 1 then 1 else 0 := by
          ext x; by_cases hx : x = k - 1 <;> simp [hx, show 1 ≤ k - 1 from hk1]
        rw [heq, show (fun x : ℕ => if x = k - 1 then (1:ℝ) else 0) =
            Set.indicator {k-1} (fun _ => 1) from by ext x; simp [Set.indicator_apply]]
        rw [integral_indicator (measurableSet_singleton _)]
        simp [MeasureTheory.integral_const, smul_eq_mul]
      · simp only [hk1, ite_false]
        have hk1' : k = 1 := by omega
        subst hk1'
        simp only [show (1 : ℕ) - 1 = 0 from rfl]
        have : (fun x : ℕ => if x = 0 ∧ 1 ≤ x then (1:ℝ) else 0) = fun _ => 0 := by
          ext x; simp [show ¬ (x = 0 ∧ 1 ≤ x) from by omega]
        rw [this, integral_zero]
    · rw [integral_const_mul]; congr 1
      rw [show (fun x : ℕ => if x = k then (1:ℝ) else 0) =
          Set.indicator {k} (fun _ => 1) from by ext x; simp [Set.indicator_apply]]
      rw [integral_indicator (measurableSet_singleton _)]
      simp [MeasureTheory.integral_const, smul_eq_mul]
  · apply Integrable.const_mul
    have : (fun x : ℕ => if x = k - 1 ∧ 1 ≤ x then (1:ℝ) else 0) =
        Set.indicator {x : ℕ | x = k - 1 ∧ 1 ≤ x} (fun _ => 1) := by
      ext x; simp [Set.indicator_apply, Set.mem_setOf_eq]
    rw [this]; exact (integrable_const _).indicator ((Set.to_countable _).measurableSet)
  · apply Integrable.const_mul
    rw [show (fun x : ℕ => if x = k then (1:ℝ) else 0) =
        Set.indicator {k} (fun _ => 1) from by ext x; simp [Set.indicator_apply]]
    exact (integrable_const _).indicator (measurableSet_singleton _)

/-- From the ≥k telescope: q(k)·Σ P(X_t=k) ≤ 1 + p(k-1)·Σ P(X_t=k-1) for k ≥ 2. -/
lemma bd_sum_singleton_k_bound
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (k : ℕ) (hk : 2 ≤ k) (n₀ : ℕ) (T : ℕ) :
    N.q k * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {k}).toReal ≤
    1 + N.p (k-1) * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {k-1}).toReal := by
  haveI : ∀ t, IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    fun t => (kernelIter_isMarkov t).isProbabilityMeasure n₀
  have htel := bd_ge_k_telescope N k (by omega) n₀ T
  have hnn : 0 ≤ ∫ x, (if k ≤ x then (1:ℝ) else 0) ∂(kernelIter (bdKernel N) T) n₀ :=
    integral_nonneg (fun x => by by_cases h : k ≤ x <;> simp [h])
  have hdrift_expand : ∀ t,
      ∫ x, (N.p (k-1) * (if x = k-1 ∧ 1 ≤ x then (1:ℝ) else 0)
          - N.q k * (if x = k then 1 else 0)) ∂(kernelIter (bdKernel N) t) n₀ =
      N.p (k-1) * ((kernelIter (bdKernel N) t) n₀ {k-1}).toReal
      - N.q k * ((kernelIter (bdKernel N) t) n₀ {k}).toReal := by
    intro t; rw [integral_ge_k_drift N k (by omega)]; simp only [show 1 ≤ k - 1 from by omega, ite_true]
  simp_rw [hdrift_expand] at htel
  rw [htel] at hnn
  have hsplit : ∑ t ∈ Finset.range T,
      (N.p (k - 1) * ((kernelIter (bdKernel N) t) n₀ {k - 1}).toReal -
        N.q k * ((kernelIter (bdKernel N) t) n₀ {k}).toReal) =
      N.p (k-1) * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {k - 1}).toReal -
      N.q k * ∑ t ∈ Finset.range T, ((kernelIter (bdKernel N) t) n₀ {k}).toReal := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit] at hnn
  linarith [show (if k ≤ n₀ then (1:ℝ) else 0) ≤ 1 from by split_ifs <;> linarith]

/-! ## Expected extinction time — helper lemmas -/

/-- Measure of a finset as a set ≤ sum of singleton measures (toReal). -/
private lemma measure_finset_le_sum_singletons_toReal
    {μ : Measure ℕ} [IsFiniteMeasure μ] (s : Finset ℕ) :
    (μ (↑s : Set ℕ)).toReal ≤ ∑ k ∈ s, (μ {k}).toReal := by
  calc (μ (↑s : Set ℕ)).toReal
      ≤ (∑ k ∈ s, μ {k}).toReal :=
        ENNReal.toReal_mono
          (ENNReal.sum_lt_top.mpr
            (fun k _ => (measure_ne_top μ _).lt_top) |>.ne)
          (by rw [show (↑s : Set ℕ) = ⋃ k ∈ s, ({k} : Set ℕ) from by ext j; simp]
              exact measure_biUnion_finset_le s (fun k => {k}))
    _ = ∑ k ∈ s, (μ {k}).toReal :=
        ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)

/-- T-uniform bound on low-state occupancy sums Σ_k Σ_{t<T} P(X_t=k) for k ∈ [1,m].
    The bound F is independent of T and n₁. Uses indicator telescoping. -/
private lemma bd_sum_low_states_bound_uniform
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ T, ∀ n₁, 0 < n₁ →
      ∑ k ∈ Finset.Icc 1 m,
        ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {k}).toReal ≤ F := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      exact ⟨1 / δ, by positivity, fun T n₁ hn₁ => by
        simp only [Finset.Icc_self, Finset.sum_singleton]
        exact bd_sum_singleton_one_le N δ hδ hDeath n₁ hn₁ T⟩
    · have hm1 : 1 ≤ m := by omega
      obtain ⟨F₀, hF₀nn, hF₀bound⟩ := ih hm1
      refine ⟨F₀ + (1 + F₀) / δ, by positivity, fun T n₁ hn₁ => ?_⟩
      have hdisj : Disjoint (Finset.Icc 1 m) ({m+1} : Finset ℕ) := by
        apply Finset.disjoint_left.mpr
        intro k hk hmem
        simp only [Finset.mem_singleton] at hmem; subst hmem
        simp only [Finset.mem_Icc] at hk; omega
      rw [show Finset.Icc 1 (m + 1) = Finset.Icc 1 m ∪ {m+1} from by
            ext k; simp [Finset.mem_Icc]; omega,
          Finset.sum_union hdisj, Finset.sum_singleton]
      have hlow := hF₀bound T n₁ hn₁
      have hk_bound := bd_sum_singleton_k_bound N (m+1) (by omega) n₁ T
      simp only [show m + 1 - 1 = m from by omega] at hk_bound
      have hq_bound : δ ≤ N.q (m + 1) := hDeath (m+1) (by omega)
      have hsum_m1_nn : 0 ≤ ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {m+1}).toReal :=
        Finset.sum_nonneg (fun t _ => ENNReal.toReal_nonneg)
      have hm_le_F : ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {m}).toReal ≤ F₀ := by
        calc _ = ∑ k ∈ ({m} : Finset ℕ), ∑ t ∈ Finset.range T,
                ((kernelIter (bdKernel N) t) n₁ {k}).toReal := by
              simp [Finset.sum_singleton]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                (fun k hk => by
                  simp only [Finset.mem_singleton] at hk; subst hk
                  simp [Finset.mem_Icc]; omega)
                (fun k _ _ => Finset.sum_nonneg (fun t _ => ENNReal.toReal_nonneg))
          _ ≤ F₀ := hlow
      have hp_le : N.p m ≤ 1 := by linarith [N.pq_le_one m, N.q_nonneg m]
      have h4 : ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {m+1}).toReal ≤ (1 + F₀) / δ := by
        rw [le_div_iff₀ hδ]
        calc (∑ t ∈ Finset.range T,
              ((kernelIter (bdKernel N) t) n₁ {m+1}).toReal) * δ
            ≤ (∑ t ∈ Finset.range T,
              ((kernelIter (bdKernel N) t) n₁ {m+1}).toReal) * N.q (m+1) :=
              mul_le_mul_of_nonneg_left hq_bound hsum_m1_nn
          _ = N.q (m+1) * ∑ t ∈ Finset.range T,
              ((kernelIter (bdKernel N) t) n₁ {m+1}).toReal := by ring
          _ ≤ 1 + N.p m * ∑ t ∈ Finset.range T,
              ((kernelIter (bdKernel N) t) n₁ {m}).toReal := hk_bound
          _ ≤ 1 + 1 * F₀ := by
              have : N.p m * ∑ t ∈ Finset.range T,
                  ((kernelIter (bdKernel N) t) n₁ {m}).toReal ≤ 1 * F₀ :=
                mul_le_mul hp_le hm_le_F
                  (Finset.sum_nonneg (fun t _ => ENNReal.toReal_nonneg))
                  (by linarith)
              linarith
          _ = 1 + F₀ := by ring
      linarith

/-- T-uniform bound on total survival probability for BD chains with eventual
    negative drift and a global death rate lower bound:
    ∃ C₀ ≥ 0, ∀ T n₁, Σ_{t<T} P(X_t > 0).toReal ≤ n₁/ε + C₀. -/
lemma bd_survival_sum_uniform
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (ε : ℝ) (hε : 0 < ε) (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ T, ∀ n₁, 0 < n₁ →
      ∑ t ∈ Finset.range T,
        ((kernelIter (bdKernel N) t) n₁ {j | 0 < j}).toReal ≤
        n₁ / ε + C₀ := by
  by_cases hn₀ : n₀ ≤ 1
  · refine ⟨0, le_refl _, fun T n₁ hn₁ => ?_⟩
    simp only [add_zero]
    exact bd_survival_sum_le_init N ε hε (fun n hn => hDrift n (by omega) hn) n₁ T
  · push_neg at hn₀
    obtain ⟨F, hFnn, hFbound⟩ :=
      bd_sum_low_states_bound_uniform N δ hδ hDeath (n₀ - 1) (by omega)
    refine ⟨(1 + 1/ε) * F, by positivity, fun T n₁ hn₁ => ?_⟩
    haveI : ∀ t, IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₁) :=
      fun t => (kernelIter_isMarkov t).isProbabilityMeasure n₁
    have h_split_sum :
        ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {j | 0 < j}).toReal ≤
        ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {j | n₀ ≤ j}).toReal +
        ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro t _
      set μ := (kernelIter (bdKernel N) t) n₁
      calc (μ {j | 0 < j}).toReal
          ≤ (μ ({j | n₀ ≤ j} ∪ {j | 0 < j ∧ j < n₀})).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _)
              (measure_mono (fun j hj => by simp at hj ⊢; omega))
        _ ≤ (μ {j | n₀ ≤ j} + μ {j | 0 < j ∧ j < n₀}).toReal :=
            ENNReal.toReal_mono
              ((ENNReal.add_lt_top.mpr ⟨(measure_ne_top _ _).lt_top,
                (measure_ne_top _ _).lt_top⟩).ne)
              (measure_union_le _ _)
        _ = _ := ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
    have h_low_le :
        ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal ≤ F := by
      have hpw : ∀ t,
          ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal ≤
          ∑ k ∈ Finset.Icc 1 (n₀ - 1),
            ((kernelIter (bdKernel N) t) n₁ {k}).toReal := by
        intro t
        have hsub : ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ) ⊆ ↑(Finset.Icc 1 (n₀ - 1)) := by
          intro j hj
          simp only [Finset.coe_Icc, Set.mem_Icc]
          exact ⟨hj.1, Nat.le_sub_one_of_lt hj.2⟩
        calc _ ≤ ((kernelIter (bdKernel N) t) n₁ ↑(Finset.Icc 1 (n₀ - 1))).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
          _ ≤ _ := measure_finset_le_sum_singletons_toReal _
      calc _ ≤ ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc 1 (n₀ - 1),
                ((kernelIter (bdKernel N) t) n₁ {k}).toReal :=
            Finset.sum_le_sum (fun t _ => hpw t)
        _ = ∑ k ∈ Finset.Icc 1 (n₀ - 1), ∑ t ∈ Finset.range T,
              ((kernelIter (bdKernel N) t) n₁ {k}).toReal := Finset.sum_comm
        _ ≤ F := hFbound T n₁ hn₁
    have h_high_bound :
        ε * ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {j | n₀ ≤ j}).toReal ≤
        ↑n₁ + ∑ t ∈ Finset.range T,
          ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal := by
      have hpw : ∀ j : ℕ,
          N.p j - N.q j ≤
          -ε * ({j : ℕ | n₀ ≤ j} : Set ℕ).indicator (fun _ => (1:ℝ)) j +
          ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ).indicator (fun _ => (1:ℝ)) j := by
        intro j
        by_cases hj0 : j = 0
        · subst hj0
          rw [N.absorb_zero.1, N.absorb_zero.2,
            Set.indicator_of_notMem (show (0:ℕ) ∉ ({j : ℕ | n₀ ≤ j} : Set ℕ) from by
              simp only [Set.mem_setOf_eq]; omega),
            Set.indicator_of_notMem (show (0:ℕ) ∉ ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ) from by
              simp only [Set.mem_setOf_eq]; omega)]
          norm_num
        · have hj_pos : 0 < j := by omega
          by_cases hjn : n₀ ≤ j
          · rw [Set.indicator_of_mem (show j ∈ ({j : ℕ | n₀ ≤ j} : Set ℕ) from hjn),
              Set.indicator_of_notMem (show j ∉ ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ) from by
                simp; intro; omega)]
            linarith [hDrift j hjn hj_pos]
          · rw [Set.indicator_of_notMem (show j ∉ ({j : ℕ | n₀ ≤ j} : Set ℕ) from by
                simp only [Set.mem_setOf_eq]; omega),
              Set.indicator_of_mem (show j ∈ ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ) from
                ⟨hj_pos, by omega⟩)]
            linarith [N.pq_le_one j, N.q_nonneg j]
      have hint : ∀ t,
          ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) t) n₁ ≤
          -ε * ((kernelIter (bdKernel N) t) n₁ {j | n₀ ≤ j}).toReal +
          ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal := by
        intro t; set μ := (kernelIter (bdKernel N) t) n₁
        calc ∫ j, (N.p j - N.q j) ∂μ
            ≤ ∫ j, (-ε * ({j : ℕ | n₀ ≤ j} : Set ℕ).indicator (fun _ => (1:ℝ)) j +
                ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ).indicator (fun _ => (1:ℝ)) j) ∂μ :=
              integral_mono (bd_integrable_drift N μ)
                (Integrable.add
                  (((integrable_const 1).indicator ((Set.to_countable _).measurableSet)).const_mul _)
                  ((integrable_const 1).indicator ((Set.to_countable _).measurableSet)))
                hpw
          _ = -ε * ∫ j, ({j : ℕ | n₀ ≤ j} : Set ℕ).indicator (fun _ => (1:ℝ)) j ∂μ +
              ∫ j, ({j : ℕ | 0 < j ∧ j < n₀} : Set ℕ).indicator (fun _ => (1:ℝ)) j ∂μ := by
              rw [integral_add
                (((integrable_const 1).indicator ((Set.to_countable _).measurableSet)).const_mul _)
                ((integrable_const 1).indicator ((Set.to_countable _).measurableSet)),
                integral_const_mul]
          _ = _ := by
              congr 1
              · congr 1
                rw [integral_indicator ((Set.to_countable _).measurableSet)]
                simp [MeasureTheory.integral_const, smul_eq_mul]; rfl
              · rw [integral_indicator ((Set.to_countable _).measurableSet)]
                simp [MeasureTheory.integral_const, smul_eq_mul]; rfl
      have htel := bd_telescope_sum N n₁ T
      have hnn := bd_expected_nonneg N n₁ T
      rw [htel] at hnn
      have hsd : ∑ t ∈ Finset.range T,
          ∫ j, (N.p j - N.q j) ∂(kernelIter (bdKernel N) t) n₁ ≤
          -ε * ∑ t ∈ Finset.range T,
            ((kernelIter (bdKernel N) t) n₁ {j | n₀ ≤ j}).toReal +
          ∑ t ∈ Finset.range T,
            ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal := by
        calc _ ≤ ∑ t ∈ Finset.range T,
              (-ε * ((kernelIter (bdKernel N) t) n₁ {j | n₀ ≤ j}).toReal +
               ((kernelIter (bdKernel N) t) n₁ {j | 0 < j ∧ j < n₀}).toReal) :=
              Finset.sum_le_sum (fun t _ => hint t)
          _ = _ := by simp only [Finset.mul_sum, Finset.sum_add_distrib]
      nlinarith
    have h_sh_le : ∑ t ∈ Finset.range T,
        ((kernelIter (bdKernel N) t) n₁ {j | n₀ ≤ j}).toReal ≤ (↑n₁ + F) / ε := by
      rw [le_div_iff₀ hε]; linarith
    have h4 : (↑n₁ + F) / ε + F = ↑n₁ / ε + (1 + 1/ε) * F := by field_simp; ring
    linarith

/-- Eventual negative drift and a global positive death probability imply
almost-sure extinction.  This is the qualitative consequence of the uniform
survival-sum estimate and does not use the later exponential-tail argument. -/
lemma bd_extinction_almost_sure
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (ε : ℝ) (hε : 0 < ε) (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n →
      N.p n - N.q n ≤ -ε)
    (δ : ℝ) (hδ : 0 < δ)
    (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (n : ℕ) :
    bdPathMeasure N n {ω | extinctionTime ω = ⊤} = 0 := by
  by_cases hn : n = 0
  · subst n
    have hzero :
        bdPathMeasure N 0 {ω | extinctionTime ω = ⊤} ≤
          bdPathMeasure N 0 {ω | 0 < ω 0} := by
      apply measure_mono
      intro ω hω
      change extinctionTime ω = ⊤ at hω
      have hlt : (0 : WithTop ℕ) < extinctionTime ω := by
        rw [hω]
        simp
      exact Nat.pos_of_ne_zero
        (ext_time_gt_imp_nonzero ω 0 hlt)
    have hcoord :
        bdPathMeasure N 0 {ω | 0 < ω 0} =
          (kernelIter (bdKernel N) 0) 0 {j | 0 < j} :=
      bdPathMeasure_coord_eq N 0 0 _
        ((Set.to_countable _).measurableSet)
    rw [hcoord] at hzero
    simp [kernelIter_zero, Kernel.id_apply] at hzero
    exact hzero
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨C₀, hC₀, hsum⟩ :=
      bd_survival_sum_uniform N ε hε n₀ hDrift
        δ hδ hDeath
    let P := bdPathMeasure N n
    let E : Set (ℕ → ℕ) := {ω | extinctionTime ω = ⊤}
    haveI : IsProbabilityMeasure P := by
      dsimp [P, bdPathMeasure]
      unfold homogeneousPathMeasure
      infer_instance
    have hE_le : ∀ t,
        P E ≤ (kernelIter (bdKernel N) t) n {j | 0 < j} := by
      intro t
      calc
        P E ≤ P {ω | 0 < ω t} := by
          apply measure_mono
          intro ω hω
          have hlt : (t : WithTop ℕ) < extinctionTime ω := by
            simp [E] at hω
            simp [hω]
          exact Nat.pos_of_ne_zero
            (ext_time_gt_imp_nonzero ω t hlt)
        _ = (kernelIter (bdKernel N) t) n {j | 0 < j} := by
          exact bdPathMeasure_coord_eq N n t _
            ((Set.to_countable _).measurableSet)
    by_contra hP
    have hPpos : 0 < P E := pos_iff_ne_zero.mpr hP
    have hPtop : P E ≠ ⊤ := measure_ne_top _ _
    have hqpos : 0 < (P E).toReal :=
      ENNReal.toReal_pos hPpos.ne' hPtop
    obtain ⟨T, hT⟩ := exists_nat_gt
      ((n / ε + C₀) / (P E).toReal)
    have hlower :
        (T : ℝ) * (P E).toReal ≤
          ∑ t ∈ Finset.range T,
            ((kernelIter (bdKernel N) t) n
              {j | 0 < j}).toReal := by
      calc
        (T : ℝ) * (P E).toReal =
            ∑ _t ∈ Finset.range T, (P E).toReal := by
              simp
        _ ≤ ∑ t ∈ Finset.range T,
              ((kernelIter (bdKernel N) t) n
                {j | 0 < j}).toReal :=
          Finset.sum_le_sum fun t ht => by
            haveI : IsProbabilityMeasure
                ((kernelIter (bdKernel N) t) n) :=
              (kernelIter_isMarkov t).isProbabilityMeasure n
            exact ENNReal.toReal_mono (measure_ne_top _ _)
              (hE_le t)
    have hupper := hsum T n hnpos
    have hcontra :
        n / ε + C₀ < (T : ℝ) * (P E).toReal := by
      exact (div_lt_iff₀ hqpos).mp hT
    linarith

/-! ## Expected extinction time — ENNReal bridge -/

private lemma measurableSet_pos_at (t : ℕ) :
    MeasurableSet ({ω : ℕ → ℕ | 0 < ω t}) := by
  have : {ω : ℕ → ℕ | 0 < ω t} = (fun ω => ω t) ⁻¹' {k | 0 < k} := by ext ω; simp
  rw [this]; exact (measurable_pi_apply t) (measurableSet_Ioi)

/-- Pointwise: τ.untopD 0 ≤ Σ_t 1_{ω(t) > 0} as ENNReal. -/
private lemma extinction_le_tsum_indicator (ω : ℕ → ℕ) :
    (((extinctionTime ω).untopD 0 : ℕ) : ℝ≥0∞) ≤
    ∑' t : ℕ, ({ω' : ℕ → ℕ | 0 < ω' t}).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [show (((extinctionTime ω).untopD 0 : ℕ) : ℝ≥0∞) =
      ∑ t ∈ Finset.range ((extinctionTime ω).untopD 0), (1 : ℝ≥0∞) from by simp]
  calc ∑ t ∈ Finset.range ((extinctionTime ω).untopD 0), (1 : ℝ≥0∞)
      ≤ ∑ t ∈ Finset.range ((extinctionTime ω).untopD 0),
          ({ω' : ℕ → ℕ | 0 < ω' t}).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
        apply Finset.sum_le_sum; intro t ht
        simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [if_pos]
        simp only [Finset.mem_range] at ht
        have hlt : (t : WithTop ℕ) < extinctionTime ω := by
          by_cases h : extinctionTime ω = ⊤
          · simp [h] at ht
          · cases hext : extinctionTime ω with
            | top => simp [hext] at h
            | coe n =>
              simp only [hext, WithTop.untopD_coe] at ht
              exact WithTop.coe_lt_coe.mpr ht
        exact Nat.pos_of_ne_zero (ext_time_gt_imp_nonzero ω t hlt)
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- E[τ] ≤ Σ_t (kernelIter t) n₀ {j | 0 < j} as ENNReal. -/
private lemma expectedExtinctionTime_le_tsum_survival
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (n₀ : ℕ) :
    expectedExtinctionTime N n₀ ≤
    ∑' t : ℕ, (kernelIter (bdKernel N) t) n₀ {j | 0 < j} := by
  calc expectedExtinctionTime N n₀
      ≤ ∑' t, (bdPathMeasure N n₀) {ω | 0 < ω t} := by
        unfold expectedExtinctionTime
        calc _ ≤ ∫⁻ ω, ∑' t, ({ω' : ℕ → ℕ | 0 < ω' t}).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂_ := lintegral_mono extinction_le_tsum_indicator
          _ = ∑' t, ∫⁻ ω, ({ω' : ℕ → ℕ | 0 < ω' t}).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂_ :=
            lintegral_tsum (fun t =>
              (measurable_const.indicator (measurableSet_pos_at t)).aemeasurable)
          _ = _ := by congr 1; ext t; exact lintegral_indicator_one (measurableSet_pos_at t)
    _ = _ := by
        congr 1; ext t
        have : {ω : ℕ → ℕ | 0 < ω t} = {ω | ω t ∈ {j : ℕ | 0 < j}} := by ext; simp
        rw [this]; exact bdPathMeasure_coord_eq N n₀ t _
          ((Set.to_countable {j : ℕ | 0 < j}).measurableSet)

/-- ENNReal tsum ≤ ofReal B when all Real partial sums are ≤ B. -/
lemma ennreal_tsum_le_of_toReal_sum_le
    {a : ℕ → ℝ≥0∞} (ha : ∀ t, a t ≠ ⊤) {B : ℝ} (hB : 0 ≤ B)
    (hsum : ∀ T, ∑ t ∈ Finset.range T, (a t).toReal ≤ B) :
    ∑' t, a t ≤ ENNReal.ofReal B := by
  apply ENNReal.tsum_le_of_sum_range_le; intro T
  calc ∑ t ∈ Finset.range T, a t
      = ENNReal.ofReal (∑ t ∈ Finset.range T, (a t).toReal) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => ENNReal.toReal_nonneg)]
        apply Finset.sum_congr rfl; intro t _; rw [ENNReal.ofReal_toReal (ha t)]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hsum T)

/-- Foster-Lyapunov bound: for a birth-death chain where the drift is eventually
    bounded above by -ε (i.e., p(n) - q(n) ≤ -ε for large n), and the death rate
    is uniformly bounded below by δ > 0, the expected extinction time grows at
    most linearly. -/
lemma bd_expected_extinction_linear
    (N : BirthDeathChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)]
    (ε : ℝ) (hε : 0 < ε) (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, n₀ ≤ n →
      (expectedExtinctionTime N n).toReal ≤ C * ↑n := by
  obtain ⟨C₀, hC₀nn, hC₀bound⟩ := bd_survival_sum_uniform N ε hε n₀ hDrift δ hδ hDeath
  refine ⟨1/ε + C₀ + 1, by positivity, fun n₁ hn₁ => ?_⟩
  by_cases hn₁0 : n₁ = 0
  · subst hn₁0; simp only [Nat.cast_zero, mul_zero]
    -- E[τ_0] = 0 since state 0 is absorbing
    have hle := expectedExtinctionTime_le_tsum_survival N 0
    have hzero : ∑' t, (kernelIter (bdKernel N) t) 0 {j | 0 < j} = 0 := by
      simp only [ENNReal.tsum_eq_zero]
      intro t; rw [kernelIter_bdKernel_zero]; simp
    rw [hzero] at hle
    have := le_antisymm hle zero_le
    simp [this]
  · have hn₁pos : 0 < n₁ := by omega
    have h1 := expectedExtinctionTime_le_tsum_survival N n₁
    have h2 : ∑' t, (kernelIter (bdKernel N) t) n₁ {j | 0 < j} ≤
        ENNReal.ofReal (↑n₁ / ε + C₀) :=
      ennreal_tsum_le_of_toReal_sum_le
        (fun t => by have := kernelIter_isMarkov (K := bdKernel N) (n := t); exact measure_ne_top _ _)
        (by positivity) (fun T => hC₀bound T n₁ hn₁pos)
    have h3 : expectedExtinctionTime N n₁ ≤ ENNReal.ofReal (↑n₁ / ε + C₀) :=
      le_trans h1 h2
    have hne : expectedExtinctionTime N n₁ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) h3
    have h4 : (expectedExtinctionTime N n₁).toReal ≤ ↑n₁ / ε + C₀ := by
      rw [← ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ ↑n₁ / ε + C₀)]
      exact (ENNReal.toReal_le_toReal hne ENNReal.ofReal_ne_top).mpr h3
    calc (expectedExtinctionTime N n₁).toReal
        ≤ ↑n₁ / ε + C₀ := h4
      _ ≤ (1/ε) * ↑n₁ + C₀ * 1 := le_of_eq (by ring)
      _ ≤ (1/ε) * ↑n₁ + C₀ * ↑n₁ := by
          gcongr; exact_mod_cast hn₁pos
      _ = (1/ε + C₀) * ↑n₁ := by ring
      _ ≤ (1/ε + C₀ + 1) * ↑n₁ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith

/-- ENNReal form of the Foster--Lyapunov estimate, uniform over every starting
    state.  This is the form needed when restarting the chain at a random
    non-holding epoch. -/
lemma bd_expected_extinction_linear_ennreal
    (N : BirthDeathChain)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)]
    (ε : ℝ) (hε : 0 < ε) (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      expectedExtinctionTime N n ≤ ENNReal.ofReal (C * (n : ℝ)) := by
  obtain ⟨C₀, hC₀nn, hC₀bound⟩ :=
    bd_survival_sum_uniform N ε hε n₀ hDrift δ hδ hDeath
  refine ⟨1 / ε + C₀ + 1, by positivity, fun n => ?_⟩
  by_cases hn0 : n = 0
  · subst n
    have hle := expectedExtinctionTime_le_tsum_survival N 0
    have hzero :
        ∑' t, (kernelIter (bdKernel N) t) 0 {j | 0 < j} = 0 := by
      simp only [ENNReal.tsum_eq_zero]
      intro t
      rw [kernelIter_bdKernel_zero]
      simp
    rw [hzero] at hle
    have heq : expectedExtinctionTime N 0 = 0 :=
      le_antisymm hle zero_le
    simp [heq]
  · have hnpos : 0 < n := by omega
    have hsurv := expectedExtinctionTime_le_tsum_survival N n
    have hsum :
        ∑' t, (kernelIter (bdKernel N) t) n {j | 0 < j} ≤
          ENNReal.ofReal ((n : ℝ) / ε + C₀) :=
      ennreal_tsum_le_of_toReal_sum_le
        (fun t => by
          have := kernelIter_isMarkov (K := bdKernel N) (n := t)
          exact measure_ne_top _ _)
        (by positivity) (fun T => hC₀bound T n hnpos)
    calc
      expectedExtinctionTime N n
          ≤ ENNReal.ofReal ((n : ℝ) / ε + C₀) :=
        hsurv.trans hsum
      _ ≤ ENNReal.ofReal ((1 / ε + C₀ + 1) * (n : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          (n : ℝ) / ε + C₀
              ≤ (1 / ε) * (n : ℝ) + C₀ * (n : ℝ) := by
                have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
                have hmul : C₀ * 1 ≤ C₀ * (n : ℝ) :=
                  mul_le_mul_of_nonneg_left hnR hC₀nn
                rw [div_eq_mul_inv, one_div]
                linarith
          _ ≤ (1 / ε + C₀ + 1) * (n : ℝ) := by
                have hnR : (0 : ℝ) ≤ n := by positivity
                nlinarith

/-! ## Exponential supermartingale for survival decay -/

/-- Exponential survival function: c^x · 1_{x>0}. -/
noncomputable def expSurvENNReal (c : ℝ) (x : ℕ) : ℝ≥0∞ :=
  if 0 < x then ENNReal.ofReal (c ^ x) else 0

private lemma expSurvENNReal_measurable (c : ℝ) : Measurable (expSurvENNReal c) :=
  measurable_of_countable _

/-- Lintegral of `expSurvENNReal c` against `bdKernel` at state y ≥ 1 equals
    the real-valued formula `ofReal(p·c^{y+1} + h·c^y + q·c^{y-1})`. -/
private lemma bd_lintegral_expSurv_eq (N : BirthDeathChain) (c : ℝ) (hc : 0 < c)
    (y : ℕ) (hy : 0 < y) :
    ∫⁻ x, expSurvENNReal c x ∂(bdKernel N y) =
    ENNReal.ofReal (N.p y * c ^ (y + 1) + holdProb N y * c ^ y +
      N.q y * (if 1 < y then c ^ (y - 1) else 0)) := by
  simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
    ProbabilityTheory.Kernel.coe_mk]
  rw [lintegral_add_measure, lintegral_add_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hp := N.p_nonneg y; have hq := N.q_nonneg y; have hpq := N.pq_le_one y
  have hh : 0 ≤ holdProb N y := by simp [holdProb]; linarith
  have hcp : ∀ k : ℕ, 0 ≤ c ^ k := fun k => pow_nonneg (le_of_lt hc) k
  simp only [expSurvENNReal, show 0 < y + 1 from by omega, hy, ↓reduceIte]
  rcases y with _ | y; · omega
  rcases y with _ | y
  · simp only [show ¬(0 < (0 : ℕ)) from by omega, ↓reduceIte,
      show ¬(1 < (1 : ℕ)) from by omega, mul_zero, add_zero]
    rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hh,
        ← ENNReal.ofReal_add (mul_nonneg hp (hcp _)) (mul_nonneg hh (hcp _))]
  · have hh2 : 0 ≤ holdProb N (y + 2) := by simp [holdProb]; linarith
    simp only [show 0 < y + 1 from by omega, show 1 < y + 2 from by omega, ↓reduceIte,
      show y + 2 - 1 = y + 1 from by omega]
    rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul hh2, ← ENNReal.ofReal_mul hq]
    rw [← ENNReal.ofReal_add (mul_nonneg hp (hcp _)) (mul_nonneg hq (hcp _)),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hp (hcp _)) (mul_nonneg hq (hcp _)))
                              (mul_nonneg hh2 (hcp _))]
    ring_nf

/-- One-step exponential supermartingale bound: ∫⁻ g d(bdK y) ≤ ρ · g(y).
    Here g(x) = c^x · 1_{x>0}, c = 1 + ε/4, ρ = 1 - (c-1)·ε/2.
    Requires FULL drift: p(n) - q(n) ≤ -ε for ALL n ≥ 1. -/
private lemma bd_lintegral_expSurv_one_step (N : BirthDeathChain) (c ε : ℝ) (hε : 0 < ε)
    (hc : c = 1 + ε / 4) [IsMarkovKernel (bdKernel N)]
    (hDrift : ∀ n, 0 < n → N.p n - N.q n ≤ -ε) (y : ℕ) :
    ∫⁻ x, expSurvENNReal c x ∂(bdKernel N y) ≤
    ENNReal.ofReal (1 - (c - 1) * ε / 2) * expSurvENNReal c y := by
  have hc_pos : 0 < c := by rw [hc]; linarith
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · -- y = 0: absorbing state, integral = 0
    have h0 : N.p 0 = 0 := N.absorb_zero.1; have h1 : N.q 0 = 0 := N.absorb_zero.2
    simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
      ProbabilityTheory.Kernel.coe_mk, h0, h1, holdProb, h0, h1]
    simp only [add_zero, sub_zero, ENNReal.ofReal_zero, zero_smul, zero_add,
      ENNReal.ofReal_one, one_smul, show (0:ℕ) - 1 = 0 from rfl,
      MeasureTheory.lintegral_dirac, expSurvENNReal, show ¬(0 < (0:ℕ)) from by omega,
      ↓reduceIte, mul_zero, le_refl]
  · -- y ≥ 1: use algebraic bound
    rw [bd_lintegral_expSurv_eq N c hc_pos y hy]
    simp only [expSurvENNReal, hy, ↓reduceIte]
    -- ρ = 1 - (c-1)·ε/2 ≥ 0 since ε ≤ 1 (from drift bound)
    have hε_le : ε ≤ 1 := by
      have := hDrift 1 Nat.one_pos
      have := N.pq_le_one 1; have := N.p_nonneg 1
      linarith
    rw [← ENNReal.ofReal_mul (by rw [hc]; nlinarith [sq_nonneg ε])]
    apply ENNReal.ofReal_le_ofReal
    have hp := N.p_nonneg y; have hq := N.q_nonneg y; have hpq := N.pq_le_one y
    rcases y with _ | y; · omega
    rcases y with _ | y
    · -- y = 1: no death-to-0 term
      -- After rcases, the goal has (0+1) instead of 1; normalize
      have : (0 : ℕ) + 1 = 1 := by omega
      simp only [this, holdProb]
      simp only [show ¬((1 : ℕ) < 1) from by omega, ↓reduceIte, mul_zero, add_zero,
        pow_one]
      rw [hc]; nlinarith [sq_nonneg ε, sq_nonneg (N.p 1), hDrift 1 Nat.one_pos]
    · -- y ≥ 2: full three-term bound
      -- After rcases, goal has (y+1+1); normalize to (y+2)
      have hidx : y + 1 + 1 = y + 2 := by omega
      simp only [hidx]
      simp only [show (1 : ℕ) < y + 2 from by omega, ↓reduceIte,
        show y + 2 - 1 = y + 1 from by omega, show y + 2 + 1 = y + 3 from by omega]
      have hcpow : 0 < c ^ (y + 1) := pow_pos hc_pos _
      suffices h : N.p (y+2) * c ^ 2 + holdProb N (y+2) * c + N.q (y+2) ≤
                   (1 - (c - 1) * ε / 2) * c by
        have h1 : c ^ (y+3) = c ^ (y+1) * c ^ 2 := by ring
        have h2 : c ^ (y+2) = c ^ (y+1) * c := by ring
        calc N.p (y + 2) * c ^ (y + 3) + holdProb N (y + 2) * c ^ (y + 2) + N.q (y + 2) * c ^ (y + 1)
            = c ^ (y + 1) * (N.p (y + 2) * c ^ 2 + holdProb N (y + 2) * c + N.q (y + 2)) := by
              rw [h1, h2]; ring
          _ ≤ c ^ (y + 1) * ((1 - (c - 1) * ε / 2) * c) :=
              mul_le_mul_of_nonneg_left h (le_of_lt hcpow)
          _ = (1 - (c - 1) * ε / 2) * c ^ (y + 2) := by rw [h2]; ring
      simp only [holdProb]
      rw [hc]; nlinarith [sq_nonneg ε, sq_nonneg (N.p (y+2)), sq_nonneg (N.q (y+2)),
                           hDrift (y+2) (by omega)]

/-- Multi-step exponential supermartingale bound: ∫⁻ g d(K^t n) ≤ ρ^t · g(n).
    Uses `kernelIter_lintegral_add` for the inductive step. -/
private lemma bd_lintegral_expSurv_multi (N : BirthDeathChain) (c ε : ℝ) (hε : 0 < ε)
    (hc : c = 1 + ε / 4) [IsMarkovKernel (bdKernel N)]
    (hDrift : ∀ n, 0 < n → N.p n - N.q n ≤ -ε) :
    ∀ t n : ℕ,
    ∫⁻ x, expSurvENNReal c x ∂(kernelIter (bdKernel N) t) n ≤
    ENNReal.ofReal (1 - (c - 1) * ε / 2) ^ t * expSurvENNReal c n := by
  intro t; induction t with
  | zero => intro n; simp [kernelIter_zero, Kernel.id_apply, MeasureTheory.lintegral_dirac]
  | succ t ih =>
    intro n
    set ρ := ENNReal.ofReal (1 - (c-1)*ε/2)
    rw [kernelIter_lintegral_add (bdKernel N) t 1 n
        (expSurvENNReal c) (expSurvENNReal_measurable c)]
    have h1 : kernelIter (bdKernel N) 1 = bdKernel N := by
      simp [kernelIter_succ, kernelIter_zero, Kernel.comp_id]
    simp_rw [h1]
    calc ∫⁻ y, ∫⁻ x, expSurvENNReal c x ∂(bdKernel N) y ∂(kernelIter (bdKernel N) t) n
        ≤ ∫⁻ y, (ρ * expSurvENNReal c y) ∂(kernelIter (bdKernel N) t) n :=
          lintegral_mono (fun y => bd_lintegral_expSurv_one_step N c ε hε hc hDrift y)
      _ = ρ * ∫⁻ y, expSurvENNReal c y ∂(kernelIter (bdKernel N) t) n :=
          lintegral_const_mul _ (expSurvENNReal_measurable c)
      _ ≤ ρ * (ρ ^ t * expSurvENNReal c n) := mul_le_mul_left' (ih n) ρ
      _ = ρ ^ (t + 1) * expSurvENNReal c n := by rw [pow_succ]; ring

/-- Exponential decay of survival probability for BD chains with FULL negative drift.
    For c = 1 + ε/4 and ρ = 1 - (c-1)·ε/2: P(X_t > 0 | X_0 = n) ≤ c^n · ρ^t. -/
lemma bd_survival_exp_decay (N : BirthDeathChain) (ε : ℝ) (hε : 0 < ε)
    [IsMarkovKernel (bdKernel N)]
    (hDrift : ∀ n, 0 < n → N.p n - N.q n ≤ -ε)
    (t n : ℕ) (hn : 0 < n) :
    (kernelIter (bdKernel N) t) n {x | 0 < x} ≤
    ENNReal.ofReal ((1 + ε / 4) ^ n) * ENNReal.ofReal (1 - ε ^ 2 / 8) ^ t := by
  set c := 1 + ε / 4
  set ρ := 1 - (c - 1) * ε / 2
  have hc_pos : 0 < c := by show 0 < 1 + ε / 4; linarith
  -- ρ = 1 - (ε/4)·(ε/2) = 1 - ε²/8
  have hρ_eq : ρ = 1 - ε ^ 2 / 8 := by show 1 - (1 + ε / 4 - 1) * ε / 2 = 1 - ε ^ 2 / 8; ring
  -- 1_{x>0} ≤ g(x) since c^x ≥ 1 for x ≥ 1
  have hge : ∀ x : ℕ, Set.indicator {x | 0 < x} (fun _ => (1 : ℝ≥0∞)) x ≤ expSurvENNReal c x := by
    intro x
    simp only [expSurvENNReal]
    split_ifs with hx
    · -- 0 < x: need to show 1_{x>0}(x) ≤ c^x, i.e., 1 ≤ c^x
      simp only [Set.indicator_of_mem (show x ∈ {x | 0 < x} from hx)]
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (show (1 : ℝ) ≤ 1 + ε / 4 by linarith))
    · push_neg at hx
      have hx0 : x = 0 := by omega
      subst hx0; simp
  calc (kernelIter (bdKernel N) t) n {x | 0 < x}
      = ∫⁻ x, Set.indicator {x | 0 < x} (fun _ => 1) x ∂(kernelIter (bdKernel N) t) n := by
        rw [lintegral_indicator ((Set.to_countable _).measurableSet)]; simp
    _ ≤ ∫⁻ x, expSurvENNReal c x ∂(kernelIter (bdKernel N) t) n := lintegral_mono hge
    _ ≤ ENNReal.ofReal ρ ^ t * expSurvENNReal c n :=
        bd_lintegral_expSurv_multi N c ε hε rfl hDrift t n
    _ = ENNReal.ofReal (c ^ n) * ENNReal.ofReal ρ ^ t := by
        simp only [expSurvENNReal, hn, ↓reduceIte]; ring
    _ = ENNReal.ofReal ((1 + ε/4) ^ n) * ENNReal.ofReal (1 - ε^2/8) ^ t := by
        simp only [c, ρ, hρ_eq]

/-! ## Non-holding epochs and restart probability -/

/-- The path is constantly `x` through time `t`. -/
private def constantPrefix (x t : ℕ) (ω : ℕ → ℕ) : Prop :=
  ∀ i, i ≤ t → ω i = x

/-- Starting from `x`, the first departure from `x` is an upward step.

    This event allows an arbitrary finite number of holding steps before the
    departure.  It is the paper's indicator that the next non-holding step is
    a birth. -/
def firstDepartureBirthFrom (x : ℕ) : Set (ℕ → ℕ) :=
  {ω | ∃ t, constantPrefix x t ω ∧ ω (t + 1) = x + 1}

private lemma measurableSet_constantPrefix (x t : ℕ) :
    MeasurableSet {ω : ℕ → ℕ | constantPrefix x t ω} := by
  let z : ∀ _ : Finset.Iic t, ℕ := fun _ => x
  have hEq :
      {ω : ℕ → ℕ | constantPrefix x t ω} =
        (frestrictLe t) ⁻¹' ({z} : Set (∀ _ : Finset.Iic t, ℕ)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      simp only [frestrictLe_apply, z]
      exact h i (Finset.mem_Iic.mp i.2)
    · intro h i hi
      have hi' := congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩
      simpa only [frestrictLe_apply, z] using hi'
  rw [hEq]
  exact (measurableSet_singleton z).preimage (measurable_frestrictLe t)

lemma measurableSet_firstDepartureBirthFrom (x : ℕ) :
    MeasurableSet (firstDepartureBirthFrom x) := by
  rw [show firstDepartureBirthFrom x =
      ⋃ t : ℕ, {ω | constantPrefix x t ω} ∩ {ω | ω (t + 1) = x + 1} from by
    ext ω
    simp [firstDepartureBirthFrom]]
  apply MeasurableSet.iUnion
  intro t
  exact (measurableSet_constantPrefix x t).inter (by measurability)

/-- Split according to whether the first departure is immediate or follows one hold. -/
private lemma firstDepartureBirthFrom_rec (x : ℕ) :
    firstDepartureBirthFrom x =
      {ω | ω 0 = x ∧ ω 1 = x + 1} ∪
        ({ω | ω 0 = x ∧ ω 1 = x} ∩
          (pathShift 1) ⁻¹' firstDepartureBirthFrom x) := by
  ext ω
  constructor
  · rintro ⟨t, hpref, hbirth⟩
    rcases t with _ | t
    · left
      exact ⟨hpref 0 le_rfl, hbirth⟩
    · right
      constructor
      · exact ⟨hpref 0 (by omega), hpref 1 (by omega)⟩
      · refine ⟨t, ?_, ?_⟩
        · intro i hi
          simpa only [pathShift, Nat.add_comm] using hpref (i + 1) (by omega)
        · simpa only [pathShift, Nat.add_comm, Nat.add_left_comm] using hbirth
  · rintro (hbirth | ⟨hhold, t, hpref, hbirth⟩)
    · refine ⟨0, ?_, hbirth.2⟩
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]
      exact hbirth.1
    · refine ⟨t + 1, ?_, ?_⟩
      · intro i hi
        rcases i with _ | i
        · exact hhold.1
        · simpa only [pathShift, Nat.add_comm] using hpref i (by omega)
      · simpa only [pathShift, Nat.add_comm, Nat.add_left_comm] using hbirth

private lemma bdKernel_up_singleton (N : BirthDeathChain) (x : ℕ) :
    bdKernel N x {x + 1} = ENNReal.ofReal (N.p x) := by
  rw [bdKernel_apply_singleton]
  have h : ¬x + 1 = x - 1 := by omega
  simp [h]

private lemma bdKernel_same_singleton (N : BirthDeathChain) (x : ℕ)
    (hx : 0 < x) :
    bdKernel N x {x} = ENNReal.ofReal (holdProb N x) := by
  rw [bdKernel_apply_singleton]
  have h2 : ¬x = x - 1 := by omega
  simp [h2]

/-- At state `x`, the probability that the next non-holding step is a birth is
    at most `p(x)/(p(x)+q(x))`.

    The proof follows the paper's holding-step argument.  If `A` is the event
    in question, then `P(A) ≤ p(x) + h(x) P(A)` by the Markov restart lemma;
    rearranging gives the claimed ratio. -/
lemma firstDepartureBirthFrom_prob_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (x : ℕ) (hx : 0 < x) (hqpos : 0 < N.q x) :
    bdPathMeasure N x (firstDepartureBirthFrom x) ≤
      ENNReal.ofReal (N.p x / (N.p x + N.q x)) := by
  let P := bdPathMeasure N x
  let A := firstDepartureBirthFrom x
  let U : Set (ℕ → ℕ) := {ω | ω 0 = x ∧ ω 1 = x + 1}
  let H : Set (ℕ → ℕ) := {ω | ω 0 = x ∧ ω 1 = x}
  letI : IsProbabilityMeasure P := by
    simp only [P, bdPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hAmeas : MeasurableSet A := measurableSet_firstDepartureBirthFrom x
  have hHmeas : MeasurableSet H := by measurability
  have hHcyl : isCylinderUpTo 1 H := by
    intro ω ω' heq hω
    exact ⟨heq 0 (by omega) ▸ hω.1, heq 1 le_rfl ▸ hω.2⟩
  have hP_U : P U = ENNReal.ofReal (N.p x) := by
    have h0 : P {ω | ω 0 ≠ x} = 0 := by
      change bdPathMeasure N x {ω | ω 0 ≠ x} = 0
      rw [show {ω : ℕ → ℕ | ω 0 ≠ x} = {ω | ω 0 ∈ ({x} : Set ℕ)ᶜ} by
        ext ω; simp]
      rw [bdPathMeasure_coord_eq N x 0 {x}ᶜ (measurableSet_singleton x).compl]
      simp [kernelIter_zero, Kernel.id_apply]
    apply le_antisymm
    · calc
        P U ≤ P {ω | ω 1 = x + 1} := measure_mono fun _ h => h.2
        _ = _ := by
          change bdPathMeasure N x {ω | ω 1 = x + 1} = _
          rw [show {ω : ℕ → ℕ | ω 1 = x + 1} =
              {ω | ω 1 ∈ ({x + 1} : Set ℕ)} by ext ω; simp]
          rw [bdPathMeasure_coord_eq N x 1 {x + 1} (measurableSet_singleton _),
            kernelIter_one]
          exact bdKernel_up_singleton N x
    · calc
        ENNReal.ofReal (N.p x) = P {ω | ω 1 = x + 1} := by
          change _ = bdPathMeasure N x {ω | ω 1 = x + 1}
          rw [show {ω : ℕ → ℕ | ω 1 = x + 1} =
              {ω | ω 1 ∈ ({x + 1} : Set ℕ)} by ext ω; simp]
          rw [bdPathMeasure_coord_eq N x 1 {x + 1} (measurableSet_singleton _),
            kernelIter_one, bdKernel_up_singleton N x]
        _ ≤ P (U ∪ {ω | ω 0 ≠ x}) := by
          apply measure_mono
          intro ω hω
          by_cases h : ω 0 = x
          · left; exact ⟨h, hω⟩
          · right; exact h
        _ ≤ P U + P {ω | ω 0 ≠ x} := measure_union_le _ _
        _ = P U := by rw [h0, add_zero]
  have hP_H : P H = ENNReal.ofReal (holdProb N x) := by
    have h0 : P {ω | ω 0 ≠ x} = 0 := by
      change bdPathMeasure N x {ω | ω 0 ≠ x} = 0
      rw [show {ω : ℕ → ℕ | ω 0 ≠ x} = {ω | ω 0 ∈ ({x} : Set ℕ)ᶜ} by
        ext ω; simp]
      rw [bdPathMeasure_coord_eq N x 0 {x}ᶜ (measurableSet_singleton x).compl]
      simp [kernelIter_zero, Kernel.id_apply]
    apply le_antisymm
    · calc
        P H ≤ P {ω | ω 1 = x} := measure_mono fun _ h => h.2
        _ = _ := by
          change bdPathMeasure N x {ω | ω 1 = x} = _
          rw [show {ω : ℕ → ℕ | ω 1 = x} =
              {ω | ω 1 ∈ ({x} : Set ℕ)} by ext ω; simp]
          rw [bdPathMeasure_coord_eq N x 1 {x} (measurableSet_singleton _),
            kernelIter_one]
          exact bdKernel_same_singleton N x hx
    · calc
        ENNReal.ofReal (holdProb N x) = P {ω | ω 1 = x} := by
          change _ = bdPathMeasure N x {ω | ω 1 = x}
          rw [show {ω : ℕ → ℕ | ω 1 = x} =
              {ω | ω 1 ∈ ({x} : Set ℕ)} by ext ω; simp]
          rw [bdPathMeasure_coord_eq N x 1 {x} (measurableSet_singleton _),
            kernelIter_one, bdKernel_same_singleton N x hx]
        _ ≤ P (H ∪ {ω | ω 0 ≠ x}) := by
          apply measure_mono
          intro ω hω
          by_cases h : ω 0 = x
          · left; exact ⟨h, hω⟩
          · right; exact h
        _ ≤ P H + P {ω | ω 0 ≠ x} := measure_union_le _ _
        _ = P H := by rw [h0, add_zero]
  have hshift :
      P (H ∩ (pathShift 1) ⁻¹' A) ≤ P A * P H := by
    apply homogeneousPathMeasure_markov_bound (bdKernel N) x 1 (P A)
      H A hHmeas hAmeas hHcyl
    intro ω hω
    change bdPathMeasure N (ω 1) A ≤ P A
    rw [hω.2]
  have hrec : A = U ∪ (H ∩ (pathShift 1) ⁻¹' A) :=
    firstDepartureBirthFrom_rec x
  have hineq : P A ≤ ENNReal.ofReal (N.p x) +
      P A * ENNReal.ofReal (holdProb N x) := by
    calc
      P A = P (U ∪ (H ∩ (pathShift 1) ⁻¹' A)) := congrArg P hrec
      _ ≤ P U + P (H ∩ (pathShift 1) ⁻¹' A) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (N.p x) + P A * P H := by
        rw [hP_U]
        gcongr
      _ = _ := by rw [hP_H]
  have hpq_pos : 0 < N.p x + N.q x := by
    linarith [N.p_nonneg x]
  have hhold_nn : 0 ≤ holdProb N x := by
    simp [holdProb]
    linarith [N.pq_le_one x]
  have hPA_ne : P A ≠ ⊤ := measure_ne_top _ _
  have hmul_ne : P A * ENNReal.ofReal (holdProb N x) ≠ ⊤ :=
    ENNReal.mul_ne_top hPA_ne ENNReal.ofReal_ne_top
  have hRHS_ne : ENNReal.ofReal (N.p x) +
      P A * ENNReal.ofReal (holdProb N x) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hmul_ne⟩
  have hreal := ENNReal.toReal_mono hRHS_ne hineq
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hmul_ne,
    ENNReal.toReal_ofReal (N.p_nonneg x),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hhold_nn] at hreal
  have hPAreal :
      (P A).toReal ≤ N.p x / (N.p x + N.q x) := by
    simp only [holdProb] at hreal
    rw [le_div_iff₀ hpq_pos]
    nlinarith
  rw [← ENNReal.toReal_le_toReal hPA_ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (div_nonneg (N.p_nonneg x) hpq_pos.le)]
  exact hPAreal

/-- Extinction tail is bounded by the marginal survival probability.
    P(τ ≥ t+1 | X₀ = m) ≤ P(X_t > 0 | X₀ = m) = K^t(m)({x | 0 < x}). -/
lemma extinctionTail_le_marginal (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (m t : ℕ) :
    extinctionTail N m (t + 1) ≤ (kernelIter (bdKernel N) t) m {x | 0 < x} := by
  -- extinctionTail N m (t+1) = bdPathMeasure N m {ω | τ ≥ t+1}
  -- ⊆ bdPathMeasure N m {ω | ω t > 0} because τ > t implies ω t ≠ 0
  -- = (K^t m) {x | 0 < x} by marginal = kernelIter
  unfold extinctionTail
  calc bdPathMeasure N m {ω | extinctionTime ω ≥ ↑(t + 1)}
      ≤ bdPathMeasure N m {ω | 0 < ω t} := by
        apply measure_mono
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have : (↑t : WithTop ℕ) < extinctionTime ω := by
          have h1 : (↑t : WithTop ℕ) < ↑(t + 1) := by exact_mod_cast Nat.lt_succ_iff.mpr le_rfl
          exact lt_of_lt_of_le h1 hω
        exact Nat.pos_of_ne_zero (ext_time_gt_imp_nonzero ω t this)
    _ = ((bdPathMeasure N m).map (fun ω => ω t)) {x | 0 < x} := by
        rw [Measure.map_apply (measurable_pi_apply t) ((Set.to_countable _).measurableSet)]
        rfl
    _ = (kernelIter (bdKernel N) t) m {x | 0 < x} := by
        unfold bdPathMeasure
        rw [homogeneousPathMeasure_dirac_marginal]

/-- For 0 < r < 1 and any k, there exists n₀ such that r^n ≤ 1/(n+1)^k for n ≥ n₀.
    Uses `isLittleO_pow_const_const_pow_of_one_lt` from Mathlib. -/
lemma exp_decay_le_poly_inv (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ENNReal.ofReal (r ^ n) ≤ ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
  -- From n^k = o((1/r)^n), extract: ∃ N, ∀ n ≥ N, n^k ≤ c * (1/r)^n
  have hr_inv : 1 < 1 / r := (one_lt_div hr0).mpr hr1
  have hlit := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k hr_inv
  rw [Asymptotics.isLittleO_iff] at hlit
  -- Use c = (1/2)^k so that (n+1)^k ≤ 2^k * n^k ≤ (1/r)^n
  have hc : (0 : ℝ) < (1/2) ^ k := pow_pos (by norm_num) k
  have hev := hlit hc
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  -- Take n₀ = max N 1 to ensure n ≥ 1
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn_ge_N : N ≤ n := le_of_max_le_left hn
  have hn_ge_1 : 1 ≤ n := le_of_max_le_right hn
  have hNn := hN n hn_ge_N
  simp only [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg' n) k),
    Real.norm_of_nonneg (pow_nonneg (le_of_lt (lt_trans zero_lt_one hr_inv)) n)] at hNn
  -- hNn : n^k ≤ (1/2)^k * (1/r)^n
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  -- Key: r^n * (n+1)^k ≤ 1
  have hkey : r ^ n * ((n + 1 : ℕ) : ℝ) ^ k ≤ 1 := by
    have hnn : (n : ℝ) + 1 ≤ 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn_ge_1
      linarith
    calc r ^ n * ((n + 1 : ℕ) : ℝ) ^ k
        = r ^ n * (↑n + 1) ^ k := by push_cast; ring_nf
      _ ≤ r ^ n * (2 * ↑n) ^ k := by gcongr
      _ = r ^ n * (2 ^ k * (↑n) ^ k) := by ring_nf
      _ = 2 ^ k * (r ^ n * (↑n) ^ k) := by ring
      _ ≤ 2 ^ k * (r ^ n * ((1/2) ^ k * (1/r) ^ n)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hNn (le_of_lt hrn_pos)
      _ = 2 ^ k * ((1/2) ^ k * ((1/r) ^ n * r ^ n)) := by ring
      _ = 2 ^ k * ((1/2) ^ k * 1) := by
          congr 1; congr 1
          rw [one_div, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hr0), one_pow]
      _ = 1 := by rw [mul_one, ← mul_pow, show (2 : ℝ) * (1/2) = 1 from by ring, one_pow]
  -- Convert to ENNReal
  by_cases hk0 : k = 0
  · subst hk0; simp [ENNReal.ofReal_le_one.mpr (pow_le_one₀ (le_of_lt hr0) (le_of_lt hr1))]
  · rw [show ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ =
        ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ) ^ k) from by
      rw [one_div, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_inv_of_pos (pow_pos (by positivity : (0 : ℝ) < ↑(n + 1)) k)]]
    apply ENNReal.ofReal_le_ofReal
    rw [one_div, inv_eq_one_div, le_div_iff₀
      (pow_pos (by positivity : (0 : ℝ) < ↑(n + 1)) k)]
    linarith

/-- logSqScaleNat n ≥ (logScale n)² = (log(n+1))² as a real. -/
private lemma logSqScaleNat_ge_logSq (n : ℕ) :
    (logScale n) ^ 2 ≤ (logSqScaleNat n : ℝ) := by
  unfold logSqScaleNat logSqScale
  have h3 : 0 ≤ ⌈(logScale n) ^ 2⌉ := Int.ceil_nonneg (sq_nonneg _)
  calc (logScale n) ^ 2 ≤ ↑⌈(logScale n) ^ 2⌉ := Int.le_ceil _
    _ = (↑(⌈(logScale n) ^ 2⌉.toNat) : ℝ) := by exact_mod_cast (Int.toNat_of_nonneg h3).symm

/-- Helper: x^m = exp(m · log x) for x > 0 and m : ℕ. -/
private lemma pow_eq_exp_mul_log (x : ℝ) (hx : 0 < x) (m : ℕ) :
    x ^ m = Real.exp (↑m * Real.log x) := by
  conv_lhs => rw [(Real.exp_log hx).symm]
  exact (Real.exp_nat_mul (Real.log x) m).symm

/-- Geometric decay through logSq scale eventually beats any polynomial inverse.
    D·β^{C·logSqScaleNat(n)} ≤ ((n+1)^k)⁻¹ for large n.
    Key idea: β^{(log n)²} = exp(-(log n)² · |log β|) = n^{-|log β|·log n},
    which decays super-polynomially since the effective exponent grows with n. -/
private lemma geom_logSq_le_poly_inv (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (D : ℝ) (hD : 0 < D) (k : ℕ) :
    ∃ C n₀ : ℕ, 0 < C ∧ ∀ n : ℕ, n₀ ≤ n →
      ENNReal.ofReal (D * β ^ (C * logSqScaleNat n)) ≤ ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
  set L := -Real.log β with hL_def
  have hL : 0 < L := neg_pos.mpr (Real.log_neg hβ0 hβ1)
  have hlog_tend : Filter.Tendsto (fun n : ℕ => Real.log ((↑n : ℝ) + 1))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  -- Find N where log(n+1) ≥ (k+1)/L for all n ≥ N
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n, N ≤ n → (↑k + 1) / L ≤ Real.log ((↑n : ℝ) + 1) := by
    have hev := hlog_tend.eventually_ge_atTop ((↑k + 1) / L)
    rwa [Filter.eventually_atTop] at hev
  refine ⟨1, max (max N (Nat.ceil D)) 1, by omega, fun n hn => ?_⟩
  simp only [one_mul]
  have hn_ge_N : N ≤ n := by omega
  have hn_ge_1 : 1 ≤ n := by omega
  have hlog_pos : 0 < Real.log ((↑n : ℝ) + 1) :=
    Real.log_pos (by have : (1 : ℝ) ≤ ↑n := Nat.one_le_cast.mpr hn_ge_1; linarith)
  have hlog_ge : (↑k + 1) / L ≤ Real.log ((↑n : ℝ) + 1) := hN n hn_ge_N
  have hD_le : D ≤ (↑n : ℝ) + 1 := by
    calc D ≤ ↑(Nat.ceil D) := Nat.le_ceil D
      _ ≤ (↑n : ℝ) + 1 := by exact_mod_cast (show Nat.ceil D ≤ n + 1 from by omega)
  set m := logSqScaleNat n
  have hm_ge : (Real.log ((↑n : ℝ) + 1)) ^ 2 ≤ (↑m : ℝ) := logSqScaleNat_ge_logSq n
  -- Core exponent bound: m·log β + k·log(n+1) ≤ -log(n+1)
  -- From m ≥ (log(n+1))² and L·log(n+1) ≥ k+1
  have h_exp_bound : ↑m * Real.log β + ↑k * Real.log ((↑n : ℝ) + 1) ≤
      -Real.log ((↑n : ℝ) + 1) := by
    have h3 : (↑m : ℝ) * Real.log β ≤ -(Real.log ((↑n : ℝ) + 1))^2 * L := by
      have : Real.log β = -L := by rw [hL_def]; ring
      rw [this]; nlinarith [hm_ge]
    have h4 : (↑k + 1) * Real.log ((↑n : ℝ) + 1) ≤
        (Real.log ((↑n : ℝ) + 1))^2 * L := by
      have h5 : (↑k + 1) ≤ L * Real.log ((↑n : ℝ) + 1) := by
        have := (div_le_iff₀ hL).mp hlog_ge; linarith
      nlinarith [hlog_pos.le]
    linarith
  -- β^m · (n+1)^k ≤ 1/(n+1) via exp/log
  have h_prod_le : β ^ m * ((↑n : ℝ) + 1) ^ k ≤ ((↑n : ℝ) + 1)⁻¹ := by
    rw [pow_eq_exp_mul_log β hβ0 m,
        pow_eq_exp_mul_log _ (by positivity : (0:ℝ) < ↑n + 1) k, ← Real.exp_add]
    calc Real.exp (↑m * Real.log β + ↑k * Real.log ((↑n : ℝ) + 1))
        ≤ Real.exp (-Real.log ((↑n : ℝ) + 1)) := Real.exp_le_exp.mpr h_exp_bound
      _ = ((↑n : ℝ) + 1)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < ↑n + 1)]
  -- D · β^m · (n+1)^k ≤ D/(n+1) ≤ 1
  have hkey : D * β ^ m * ((↑n : ℝ) + 1) ^ k ≤ 1 := by
    calc D * β ^ m * ((↑n : ℝ) + 1) ^ k
        = D * (β ^ m * ((↑n : ℝ) + 1) ^ k) := by ring
      _ ≤ D * ((↑n : ℝ) + 1)⁻¹ := mul_le_mul_of_nonneg_left h_prod_le hD.le
      _ = D / ((↑n : ℝ) + 1) := by rw [div_eq_mul_inv]
      _ ≤ 1 := by rwa [div_le_one (by positivity : (0:ℝ) < ↑n + 1)]
  -- Convert to ENNReal
  rcases k.eq_zero_or_pos with rfl | hk_pos
  · simp only [pow_zero, inv_one, mul_one] at hkey ⊢
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  · rw [show ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ =
        ENNReal.ofReal (1 / ((↑n + 1 : ℝ)) ^ k) from by
      rw [one_div, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_inv_of_pos
            (pow_pos (by positivity : (0 : ℝ) < ↑(n + 1)) k)]
      push_cast; ring_nf]
    apply ENNReal.ofReal_le_ofReal
    rw [one_div, inv_eq_one_div,
        le_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < ↑n + 1) k)]
    linarith

/-- One-step Foster-Lyapunov bound with additive correction for EVENTUAL drift.
    For states ≥ n₀ with drift ≤ -ε: ∫g ≤ ρ·g(y) ≤ ρ·g(y) + B.
    For states 0 < y < n₀: ∫g ≤ c^{y+1} ≤ c^{n₀} = B.
    Combined: ∫g ≤ ρ·g(y) + B where B = c^{n₀}. -/
private lemma bd_lintegral_expSurv_one_step_eventual (N : BirthDeathChain) (c ε : ℝ) (hε : 0 < ε)
    (hc : c = 1 + ε / 4) (n₀ : ℕ) [IsMarkovKernel (bdKernel N)]
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε) (y : ℕ) :
    ∫⁻ x, expSurvENNReal c x ∂(bdKernel N y) ≤
    ENNReal.ofReal (1 - (c - 1) * ε / 2) * expSurvENNReal c y +
      ENNReal.ofReal (c ^ n₀) := by
  have hc_pos : 0 < c := by rw [hc]; linarith
  have hε_le : ε ≤ 2 := by
    by_contra h; push_neg at h
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
    · have := hDrift 1 (by omega) (by omega); have := N.pq_le_one 1; have := N.p_nonneg 1; linarith
    · have := hDrift n₀ le_rfl hn₀; have := N.pq_le_one n₀; have := N.p_nonneg n₀; linarith
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · -- y = 0: absorbing, ∫g = 0
    simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
      ProbabilityTheory.Kernel.coe_mk, N.absorb_zero.1, N.absorb_zero.2, holdProb]
    simp [expSurvENNReal, show ¬(0 < (0:ℕ)) from by omega]
  · -- y ≥ 1
    by_cases hy_high : n₀ ≤ y
    · -- High region: full drift at this state, so supermartingale bound applies
      have hDy : N.p y - N.q y ≤ -ε := hDrift y hy_high hy
      -- Directly prove the one-step bound at state y
      rw [bd_lintegral_expSurv_eq N c hc_pos y hy]
      simp only [expSurvENNReal, hy, ↓reduceIte]
      -- Need: ofReal(p·c^{y+1}+h·c^y+q·c^{y-1?}) ≤ ρ·ofReal(c^y) + B
      -- Since ρ·c^y already bounds the lhs (same algebra as full-drift proof),
      -- it suffices to show the algebraic bound, then add B ≥ 0.
      suffices h : ENNReal.ofReal (N.p y * c ^ (y + 1) + holdProb N y * c ^ y +
          N.q y * (if 1 < y then c ^ (y - 1) else 0)) ≤
          ENNReal.ofReal (1 - (c - 1) * ε / 2) * ENNReal.ofReal (c ^ y) by
        calc _ ≤ ENNReal.ofReal (1 - (c - 1) * ε / 2) * ENNReal.ofReal (c ^ y) := h
          _ ≤ _ := le_add_right le_rfl
      -- Algebraic bound: same as in bd_lintegral_expSurv_one_step
      rw [← ENNReal.ofReal_mul (by rw [hc]; nlinarith [sq_nonneg ε])]
      apply ENNReal.ofReal_le_ofReal
      have hp := N.p_nonneg y; have hq := N.q_nonneg y; have hpq := N.pq_le_one y
      rcases y with _ | y; · omega
      rcases y with _ | y
      · -- y = 1: n₀ ≤ 1, so n₀ = 0 or n₀ = 1
        have : (0 : ℕ) + 1 = 1 := by omega
        simp only [this, holdProb]
        simp only [show ¬((1 : ℕ) < 1) from by omega, ↓reduceIte, mul_zero, add_zero, pow_one]
        rw [hc]; nlinarith [sq_nonneg ε, sq_nonneg (N.p 1), hDy]
      · -- y ≥ 2
        have hidx : y + 1 + 1 = y + 2 := by omega
        simp only [hidx]
        simp only [show (1 : ℕ) < y + 2 from by omega, ↓reduceIte,
          show y + 2 - 1 = y + 1 from by omega, show y + 2 + 1 = y + 3 from by omega]
        have hcpow : 0 < c ^ (y + 1) := pow_pos hc_pos _
        suffices hsuff : N.p (y+2) * c ^ 2 + holdProb N (y+2) * c + N.q (y+2) ≤
                     (1 - (c - 1) * ε / 2) * c by
          have h1 : c ^ (y+3) = c ^ (y+1) * c ^ 2 := by ring
          have h2 : c ^ (y+2) = c ^ (y+1) * c := by ring
          calc N.p (y + 2) * c ^ (y + 3) + holdProb N (y + 2) * c ^ (y + 2) +
                N.q (y + 2) * c ^ (y + 1)
              = c ^ (y + 1) * (N.p (y + 2) * c ^ 2 + holdProb N (y + 2) * c + N.q (y + 2)) := by
                rw [h1, h2]; ring
            _ ≤ c ^ (y + 1) * ((1 - (c - 1) * ε / 2) * c) :=
                mul_le_mul_of_nonneg_left hsuff (le_of_lt hcpow)
            _ = (1 - (c - 1) * ε / 2) * c ^ (y + 2) := by rw [h2]; ring
        simp only [holdProb]
        rw [hc]; nlinarith [sq_nonneg ε, sq_nonneg (N.p (y+2)), sq_nonneg (N.q (y+2)),
                             hDy]
    · -- Low region: 0 < y < n₀
      push_neg at hy_high
      -- Bound ∫g ≤ c^{y+1} ≤ c^{n₀} = B
      -- At state y, the kernel sends to y-1, y, y+1 with probs q, h, p
      rw [bd_lintegral_expSurv_eq N c hc_pos y hy]
      have hp := N.p_nonneg y; have hq := N.q_nonneg y; have hpq := N.pq_le_one y
      have hh : 0 ≤ holdProb N y := by simp [holdProb]; linarith
      -- The sum p·c^{y+1} + h·c^y + q·c^{y-1} ≤ c^{y+1}
      have hbound : N.p y * c ^ (y + 1) + holdProb N y * c ^ y +
          N.q y * (if 1 < y then c ^ (y - 1) else 0) ≤ c ^ (y + 1) := by
        have hc1 : 1 ≤ c := by rw [hc]; linarith
        have hcpow : ∀ k, 0 ≤ c ^ k := fun k => pow_nonneg (le_of_lt hc_pos) k
        have h_ite : N.q y * (if 1 < y then c ^ (y - 1) else 0) ≤
            N.q y * c ^ (y + 1) := by
          split_ifs with h
          · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by omega)) hq
          · simp [mul_nonneg hq (hcpow _)]
        calc N.p y * c ^ (y + 1) + holdProb N y * c ^ y +
              N.q y * (if 1 < y then c ^ (y - 1) else 0)
            ≤ N.p y * c ^ (y + 1) + holdProb N y * c ^ (y + 1) +
              N.q y * c ^ (y + 1) := by
              have h1 : holdProb N y * c ^ y ≤ holdProb N y * c ^ (y + 1) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (Nat.le_succ y)) hh
              linarith
          _ = (N.p y + holdProb N y + N.q y) * c ^ (y + 1) := by ring
          _ = 1 * c ^ (y + 1) := by
              congr 1; simp [holdProb]; ring
          _ = c ^ (y + 1) := one_mul _
      -- c^{y+1} ≤ c^{n₀} since y+1 ≤ n₀
      have hyp1 : y + 1 ≤ n₀ := by omega
      have hcy : c ^ (y + 1) ≤ c ^ n₀ :=
        pow_le_pow_right₀ (by rw [hc]; linarith) hyp1
      calc ENNReal.ofReal (N.p y * c ^ (y + 1) + holdProb N y * c ^ y +
              N.q y * (if 1 < y then c ^ (y - 1) else 0))
          ≤ ENNReal.ofReal (c ^ n₀) := by
            apply ENNReal.ofReal_le_ofReal; linarith
        _ ≤ ENNReal.ofReal (1 - (c - 1) * ε / 2) * expSurvENNReal c y +
              ENNReal.ofReal (c ^ n₀) := le_add_left le_rfl

/-- Multi-step Foster-Lyapunov iteration with additive correction.
    If one-step bound is ∫g ≤ ρ·g + B, then multi-step:
    ∫g d(K^t) ≤ ρ^t·g(n) + M where M = B/(1-ρ) expressed as a real constant. -/
private lemma bd_lintegral_expSurv_multi_eventual (N : BirthDeathChain) (c ε : ℝ) (hε : 0 < ε)
    (hc : c = 1 + ε / 4) (n₀ : ℕ) [IsMarkovKernel (bdKernel N)]
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε) :
    let ρ := ENNReal.ofReal (1 - (c - 1) * ε / 2)
    let B := ENNReal.ofReal (c ^ n₀)
    let M := ENNReal.ofReal (c ^ n₀ * (2 / ε ^ 2 * 8))
    ∀ t n : ℕ,
    ∫⁻ x, expSurvENNReal c x ∂(kernelIter (bdKernel N) t) n ≤
    ρ ^ t * expSurvENNReal c n + M := by
  intro ρ B M
  -- Key: ρ · M + B ≤ M
  have hε_le : ε ≤ 2 := by
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
    · have := hDrift 1 (by omega) (by omega); have := N.pq_le_one 1; have := N.p_nonneg 1; linarith
    · have := hDrift n₀ le_rfl hn₀; have := N.pq_le_one n₀; have := N.p_nonneg n₀; linarith
  have hc_pos : 0 < c := by rw [hc]; linarith
  have hρ_val : 1 - (c - 1) * ε / 2 = 1 - ε ^ 2 / 8 := by rw [hc]; ring
  have hρ_lt_1_real : 1 - (c - 1) * ε / 2 < 1 := by nlinarith [sq_nonneg ε]
  have hρ_nonneg : 0 ≤ 1 - (c - 1) * ε / 2 := by nlinarith [sq_nonneg ε]
  -- M_real = c^n₀ * 16/ε²; ρ_real * M_real + c^n₀ ≤ M_real iff c^n₀ ≤ (1-ρ_real)*M_real
  -- (1-ρ_real) * M_real = ε²/8 * c^n₀ * 16/ε² = 2*c^n₀ ≥ c^n₀
  have hcn₀ : 0 ≤ c ^ n₀ := pow_nonneg (le_of_lt hc_pos) n₀
  have hM_real : 0 ≤ c ^ n₀ * (2 / ε ^ 2 * 8) := by positivity
  have hρM_B_real : (1 - (c-1)*ε/2) * (c^n₀ * (2/ε^2*8)) + c^n₀ ≤ c^n₀*(2/ε^2*8) := by
    -- Suffices to show: c^n₀ ≤ (c-1)*ε/2 * (c^n₀ * (2/ε^2*8))
    -- = c^n₀ * ((c-1)*ε/2 * (2/ε^2*8)) = c^n₀ * (8*(c-1)/(ε))
    -- With c = 1+ε/4: (c-1) = ε/4, so 8*(ε/4)/ε = 2. So RHS = 2*c^n₀ ≥ c^n₀.
    suffices h : c ^ n₀ ≤ (c - 1) * ε / 2 * (c ^ n₀ * (2 / ε ^ 2 * 8)) by linarith
    have hε_pos : ε > 0 := hε
    have hε2 : ε ^ 2 > 0 := by positivity
    have key : (c - 1) * ε / 2 * (2 / ε ^ 2 * 8) = 2 := by
      rw [hc]; field_simp; ring
    calc c ^ n₀ ≤ 2 * c ^ n₀ := le_mul_of_one_le_left hcn₀ one_le_two
      _ = (c - 1) * ε / 2 * (2 / ε ^ 2 * 8) * c ^ n₀ := by rw [key]
      _ = (c - 1) * ε / 2 * (c ^ n₀ * (2 / ε ^ 2 * 8)) := by ring
  have hρM_add_B : ρ * M + B ≤ M := by
    rw [show ρ = ENNReal.ofReal (1 - (c-1)*ε/2) from rfl,
        show M = ENNReal.ofReal (c^n₀ * (2/ε^2*8)) from rfl,
        show B = ENNReal.ofReal (c^n₀) from rfl]
    rw [← ENNReal.ofReal_mul hρ_nonneg, ← ENNReal.ofReal_add (by positivity) hcn₀]
    exact ENNReal.ofReal_le_ofReal hρM_B_real
  intro t; induction t with
  | zero =>
    intro n; simp [kernelIter_zero, Kernel.id_apply, MeasureTheory.lintegral_dirac]
  | succ t ih =>
    intro n
    rw [kernelIter_lintegral_add (bdKernel N) t 1 n
        (expSurvENNReal c) (expSurvENNReal_measurable c)]
    have h1 : kernelIter (bdKernel N) 1 = bdKernel N := by
      simp [kernelIter_succ, kernelIter_zero, Kernel.comp_id]
    simp_rw [h1]
    calc ∫⁻ y, ∫⁻ x, expSurvENNReal c x ∂(bdKernel N) y ∂(kernelIter (bdKernel N) t) n
        ≤ ∫⁻ y, (ρ * expSurvENNReal c y + B) ∂(kernelIter (bdKernel N) t) n :=
          lintegral_mono (fun y =>
            bd_lintegral_expSurv_one_step_eventual N c ε hε hc n₀ hDrift y)
      _ = ρ * ∫⁻ y, expSurvENNReal c y ∂(kernelIter (bdKernel N) t) n + B := by
          rw [lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const,
              lintegral_const_mul _ (expSurvENNReal_measurable c)]
          haveI : IsMarkovKernel (kernelIter (bdKernel N) t) := kernelIter_isMarkov t
          rw [show (kernelIter (bdKernel N) t) n Set.univ = 1 from measure_univ]; simp
      _ ≤ ρ * (ρ ^ t * expSurvENNReal c n + M) + B := by
          gcongr; exact ih n
      _ ≤ ρ ^ (t + 1) * expSurvENNReal c n + M := by
          have step1 : ρ * (ρ ^ t * expSurvENNReal c n + M) + B =
              ρ ^ (t + 1) * expSurvENNReal c n + (ρ * M + B) := by
            rw [mul_add, ← mul_assoc, ← pow_succ', add_assoc]
          rw [step1]; gcongr

/-- Survival bound for BD chains with EVENTUAL negative drift.
    P(X_t > 0 | X_0 = n) ≤ ρ^t · c^n + M
    where c = 1+ε/4, ρ = 1-ε²/8, M = c^n₀ · 16/ε².
    The first term decays exponentially in both t and n; the second is constant. -/
private lemma bd_survival_exp_decay_eventual (N : BirthDeathChain) (ε : ℝ) (hε : 0 < ε)
    (n₀ : ℕ) [IsMarkovKernel (bdKernel N)]
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (t n : ℕ) (hn : 0 < n) :
    (kernelIter (bdKernel N) t) n {x | 0 < x} ≤
    ENNReal.ofReal ((1 - ε ^ 2 / 8) ^ t * (1 + ε / 4) ^ n) +
      ENNReal.ofReal ((1 + ε / 4) ^ n₀ * (2 / ε ^ 2 * 8)) := by
  have hε_le : ε ≤ 2 := by
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
    · have := hDrift 1 (by omega) (by omega)
      have := N.pq_le_one 1; have := N.p_nonneg 1; linarith
    · have := hDrift n₀ le_rfl hn₀
      have := N.pq_le_one n₀; have := N.p_nonneg n₀; linarith
  have hc_val : (1 : ℝ) + ε / 4 > 0 := by linarith
  have hρ_nonneg : 0 ≤ 1 - (1 + ε / 4 - 1) * ε / 2 := by nlinarith [sq_nonneg ε]
  -- 1_{x>0} ≤ g(x)
  have hge : ∀ x : ℕ, Set.indicator {x | 0 < x} (fun _ => (1 : ℝ≥0∞)) x ≤
      expSurvENNReal (1 + ε / 4) x := by
    intro x; simp only [expSurvENNReal]
    split_ifs with hx
    · simp only [Set.indicator_of_mem (show x ∈ {x | 0 < x} from hx)]
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε / 4))
    · push_neg at hx
      have hx0 : x = 0 := by omega
      subst hx0; simp
  calc (kernelIter (bdKernel N) t) n {x | 0 < x}
      = ∫⁻ x, Set.indicator {x | 0 < x} (fun _ => 1) x ∂(kernelIter (bdKernel N) t) n := by
        rw [lintegral_indicator ((Set.to_countable _).measurableSet)]; simp
    _ ≤ ∫⁻ x, expSurvENNReal (1 + ε / 4) x ∂(kernelIter (bdKernel N) t) n :=
        lintegral_mono hge
    _ ≤ ENNReal.ofReal (1 - ((1 + ε / 4) - 1) * ε / 2) ^ t *
            expSurvENNReal (1 + ε / 4) n +
          ENNReal.ofReal ((1 + ε / 4) ^ n₀ * (2 / ε ^ 2 * 8)) :=
        bd_lintegral_expSurv_multi_eventual N (1 + ε / 4) ε hε rfl n₀ hDrift t n
    _ = ENNReal.ofReal ((1 - ((1 + ε / 4) - 1) * ε / 2) ^ t) *
            ENNReal.ofReal ((1 + ε / 4) ^ n) +
          ENNReal.ofReal ((1 + ε / 4) ^ n₀ * (2 / ε ^ 2 * 8)) := by
        simp only [expSurvENNReal, hn, ↓reduceIte]
        rw [ENNReal.ofReal_pow hρ_nonneg]
    _ = ENNReal.ofReal ((1 - ((1 + ε / 4) - 1) * ε / 2) ^ t * (1 + ε / 4) ^ n) +
          ENNReal.ofReal ((1 + ε / 4) ^ n₀ * (2 / ε ^ 2 * 8)) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg hρ_nonneg t)]
    _ = ENNReal.ofReal ((1 - ε ^ 2 / 8) ^ t * (1 + ε / 4) ^ n) +
          ENNReal.ofReal ((1 + ε / 4) ^ n₀ * (2 / ε ^ 2 * 8)) := by
        congr 1; congr 1; congr 1; ring

/-- The iterated kernel at absorbing state 0 gives back {0} with probability 1.
    Since state 0 is absorbing (p(0) = q(0) = 0), K^t(0) = δ_0 for all t. -/
private lemma kernelIter_bd_at_zero (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)] (t : ℕ) :
    (kernelIter (bdKernel N) t) 0 {0} = 1 := by
  induction t with
  | zero => simp [kernelIter_zero, Kernel.id_apply]
  | succ t ih =>
    have : (kernelIter (bdKernel N) (t + 1)) 0 {0} =
        ∫⁻ j, (kernelIter (bdKernel N) t) j {0} ∂(bdKernel N) 0 := by
      have : (kernelIter (bdKernel N) (t + 1)) 0 {0} =
          ((bdKernel N) 0).bind (fun j => (kernelIter (bdKernel N) t) j) {0} := by
        rw [kernelIter_succ_right]; rfl
      rw [this, Measure.bind_apply ((Set.to_countable _).measurableSet)
        (Kernel.measurable _).aemeasurable]
    rw [this, bdKernel_zero, lintegral_dirac, ih]

/-- From state k, the probability of reaching 0 in exactly k consecutive down-steps
    is at least δ^k. Proved by induction using Chapman-Kolmogorov. -/
private lemma bd_straight_down_absorption (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n) :
    ∀ k : ℕ, ENNReal.ofReal (δ ^ k) ≤ (kernelIter (bdKernel N) k) k {0} := by
  intro k; induction k with
  | zero =>
    simp [kernelIter_zero, Kernel.id_apply, Set.mem_singleton_iff]
  | succ k ih =>
    have h_ck : (kernelIter (bdKernel N) (k + 1)) (k + 1) {0} =
        ∫⁻ j, (kernelIter (bdKernel N) k) j {0} ∂(bdKernel N) (k + 1) := by
      have : (kernelIter (bdKernel N) (k + 1)) (k + 1) {0} =
          ((bdKernel N) (k + 1)).bind (fun j => (kernelIter (bdKernel N) k) j) {0} := by
        rw [kernelIter_succ_right]; rfl
      rw [this, Measure.bind_apply ((Set.to_countable _).measurableSet)
        (Kernel.measurable _).aemeasurable]
    rw [h_ck, bdKernel_apply,
      lintegral_add_measure, lintegral_add_measure,
      lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac, lintegral_dirac, lintegral_dirac]
    simp only [smul_eq_mul, Nat.succ_sub_one]
    calc ENNReal.ofReal (δ ^ (k + 1))
        = ENNReal.ofReal δ * ENNReal.ofReal (δ ^ k) := by
          rw [← ENNReal.ofReal_mul hδ.le]; congr 1; ring
      _ ≤ ENNReal.ofReal (N.q (k + 1)) * (kernelIter (bdKernel N) k) k {0} := by
          calc ENNReal.ofReal δ * ENNReal.ofReal (δ ^ k)
              ≤ ENNReal.ofReal (N.q (k + 1)) * ENNReal.ofReal (δ ^ k) := by
                apply mul_le_mul_of_nonneg_right
                  (ENNReal.ofReal_le_ofReal (hDeath (k + 1) (by omega))) zero_le
            _ ≤ ENNReal.ofReal (N.q (k + 1)) * (kernelIter (bdKernel N) k) k {0} := by
                exact mul_le_mul_of_nonneg_left ih zero_le
      _ ≤ ENNReal.ofReal (N.p (k + 1)) * (kernelIter (bdKernel N) k) (k + 1 + 1) {0} +
            ENNReal.ofReal (N.q (k + 1)) * (kernelIter (bdKernel N) k) k {0} :=
          le_add_left le_rfl
      _ ≤ _ := le_add_right le_rfl

/-- For state m ≤ n₀ with positive death rate δ, the absorption probability in n₀ steps
    is at least δ^n₀. This uses the straight-down path and absorbing state at 0. -/
private lemma bd_bounded_absorption (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (δ : ℝ) (hδ : 0 < δ) (hδ_le : δ ≤ 1)
    (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (n₀ : ℕ) (m : ℕ) (hm : 0 < m) (hm_le : m ≤ n₀) :
    ENNReal.ofReal (δ ^ n₀) ≤ (kernelIter (bdKernel N) n₀) m {0} := by
  have h1 : δ ^ n₀ ≤ δ ^ m := pow_le_pow_of_le_one hδ.le hδ_le hm_le
  have h2 := bd_straight_down_absorption N δ hδ hDeath m
  have h3 : (kernelIter (bdKernel N) m) m {0} ≤
      (kernelIter (bdKernel N) n₀) m {0} := by
    rw [show n₀ = m + (n₀ - m) from by omega]
    rw [kernelIter_measure_add (bdKernel N) m (n₀ - m) m {0}
      ((Set.to_countable _).measurableSet)]
    calc (kernelIter (bdKernel N) m) m {0}
        = ∫⁻ j, Set.indicator {(0 : ℕ)} (fun _ => 1) j
            ∂(kernelIter (bdKernel N) m) m := by
          rw [lintegral_indicator ((Set.to_countable _).measurableSet)]; simp
      _ ≤ ∫⁻ j, (kernelIter (bdKernel N) (n₀ - m)) j {0}
            ∂(kernelIter (bdKernel N) m) m := by
          apply lintegral_mono; intro j
          simp only [Set.indicator_apply, Pi.one_apply]
          split_ifs with hj
          · rw [Set.mem_singleton_iff.mp hj, kernelIter_bd_at_zero]
          · exact zero_le
  exact ((ENNReal.ofReal_le_ofReal h1).trans h2).trans h3

/-! ## IsMarkovKernel instance for bdKernel -/

/-- `bdKernel N` is a Markov kernel: total mass at each state is 1. -/
instance bdKernel_isMarkovKernel (N : BirthDeathChain) :
    ProbabilityTheory.IsMarkovKernel (bdKernel N) where
  isProbabilityMeasure a := ⟨by
    simp only [bdKernel, ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk,
      Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    have hp := N.p_nonneg a
    have hq := N.q_nonneg a
    have hpq := N.pq_le_one a
    rw [← ENNReal.ofReal_add hp hq,
        ← ENNReal.ofReal_add (by linarith) (by simp [holdProb]; linarith)]
    simp [holdProb]⟩

/-! ## IsMarkovKernel instance for lvKernel -/

/-- All individual weight terms in the LV kernel are nonneg (as reals). -/
private lemma lv_weights_nonneg (params : LVParams) (s : PopState) :
    0 ≤ params.beta * (s.1 : ℝ) ∧
    0 ≤ params.beta * (s.2 : ℝ) ∧
    0 ≤ params.delta * (s.1 : ℝ) ∧
    0 ≤ params.delta * (s.2 : ℝ) ∧
    0 ≤ params.alpha0 * (s.1 : ℝ) * s.2 ∧
    0 ≤ params.alpha1 * (s.1 : ℝ) * s.2 ∧
    0 ≤ params.gamma0 * ((s.1 : ℝ) * (s.1 - 1) / 2) ∧
    0 ≤ params.gamma1 * ((s.2 : ℝ) * (s.2 - 1) / 2) := by
  have hx0 : (0 : ℝ) ≤ s.1 := Nat.cast_nonneg _
  have hx1 : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg _
  have hx0_1 : (0 : ℝ) ≤ (s.1 : ℝ) * ((s.1 : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos s.1 with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ (s.1 : ℝ) := by exact_mod_cast h
      exact mul_nonneg hx0 (by linarith)
  have hx1_1 : (0 : ℝ) ≤ (s.2 : ℝ) * ((s.2 : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos s.2 with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ (s.2 : ℝ) := by exact_mod_cast h
      exact mul_nonneg hx1 (by linarith)
  refine ⟨mul_nonneg params.beta_nonneg hx0, mul_nonneg params.beta_nonneg hx1,
    mul_nonneg params.delta_nonneg hx0, mul_nonneg params.delta_nonneg hx1,
    mul_nonneg (mul_nonneg params.alpha0_nonneg hx0) hx1,
    mul_nonneg (mul_nonneg params.alpha1_nonneg hx0) hx1,
    mul_nonneg params.gamma0_nonneg (div_nonneg hx0_1 (by norm_num)),
    mul_nonneg params.gamma1_nonneg (div_nonneg hx1_1 (by norm_num))⟩

/-- The 8 individual weight terms sum to `lvTotalPropensity`. -/
private lemma lv_weight_sum (params : LVParams) (s : PopState) :
    params.beta * (s.1 : ℝ) + params.beta * (s.2 : ℝ) +
    params.delta * (s.1 : ℝ) + params.delta * (s.2 : ℝ) +
    params.alpha0 * (s.1 : ℝ) * s.2 + params.alpha1 * (s.1 : ℝ) * s.2 +
    params.gamma0 * ((s.1 : ℝ) * (s.1 - 1) / 2) +
    params.gamma1 * ((s.2 : ℝ) * (s.2 - 1) / 2) =
    lvTotalPropensity params s := by
  simp only [lvTotalPropensity]
  ring

/-- `lvKernel v params` is a Markov kernel. -/
instance lvKernel_isMarkovKernel (v : LVVariant) (params : LVParams) :
    ProbabilityTheory.IsMarkovKernel (lvKernel v params) where
  isProbabilityMeasure s := ⟨by
    simp only [lvKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
      ProbabilityTheory.Kernel.coe_mk]
    by_cases hφ : lvTotalPropensity params s = 0
    · simp [hφ]
    · rw [dif_neg hφ]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := lv_weights_nonneg params s
      have hφ_pos : 0 < lvTotalPropensity params s := by
        rcases lt_or_eq_of_le (show 0 ≤ lvTotalPropensity params s from by
          rw [← lv_weight_sum]; linarith) with h | h
        · exact h
        · exact absurd h.symm hφ
      have hinvφ : (0 : ℝ) ≤ 1 / lvTotalPropensity params s := by positivity
      cases v <;> simp only [] <;> {
        simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul,
          Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by linarith) h3,
            ← ENNReal.ofReal_add (by linarith) h4, ← ENNReal.ofReal_add (by linarith) h5,
            ← ENNReal.ofReal_add (by linarith) h6, ← ENNReal.ofReal_add (by linarith) h7,
            ← ENNReal.ofReal_add (by linarith) h8, lv_weight_sum,
            ← ENNReal.ofReal_mul hinvφ, one_div_mul_cancel hφ, ENNReal.ofReal_one] }⟩

/-! ## Harmonicity of h(a,b) = a/(a+b) for NSD kernel -/

section Harmonicity

/-- Algebraic identity for superharmonic excess in NSD kernel.
    With β=δ=0, α₀=α₁=α, γ₀=γ₁=γ, the excess φ·h(a,b) − (weighted sum)
    equals (γ-2α)·a·b·(a-b) / (2·(a+b)·(a+b-1)). -/
lemma nsd_superharmonic_excess_identity (a b α γ : ℝ)
    (hn : a + b ≠ 0) (hn1 : a + b - 1 ≠ 0) :
    (2 * α * a * b + γ * (a * (a - 1) + b * (b - 1)) / 2) * (a / (a + b)) -
    ((α * a * b + γ * a * (a - 1) / 2) * ((a - 1) / (a + b - 1)) +
     (α * a * b + γ * b * (b - 1) / 2) * (a / (a + b - 1))) =
    (γ - 2 * α) * a * b * (a - b) / (2 * (a + b) * (a + b - 1)) := by
  field_simp
  ring

/-- The demographic birth and death terms cancel from the NSD
    superharmonicity excess.  Thus the same excess identity holds for
    arbitrary common birth and death rates. -/
lemma nsd_superharmonic_excess_identity_general
    (a b α γ β δ : ℝ)
    (hn : a + b ≠ 0) (hnp1 : a + b + 1 ≠ 0)
    (hn1 : a + b - 1 ≠ 0) :
    (β * (a + b) + δ * (a + b) + 2 * α * a * b +
        γ * (a * (a - 1) + b * (b - 1)) / 2) * (a / (a + b)) -
      (β * a * ((a + 1) / (a + b + 1)) +
       β * b * (a / (a + b + 1)) +
       (δ * a + α * a * b + γ * a * (a - 1) / 2) *
          ((a - 1) / (a + b - 1)) +
       (δ * b + α * a * b + γ * b * (b - 1) / 2) *
          (a / (a + b - 1))) =
      (γ - 2 * α) * a * b * (a - b) /
        (2 * (a + b) * (a + b - 1)) := by
  field_simp
  ring

/-- For symmetric NSD competition with `γ ≥ 2α`, arbitrary common
    demographic rates, and `a ≥ b`, the population proportion `a/(a+b)`
    is superharmonic until the two populations meet. -/
lemma nsd_superharmonic_weighted_le_general
    (a b α γ β δ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a)
    (hγα : 2 * α ≤ γ)
    (hn : a + b ≠ 0) (hnp1 : a + b + 1 ≠ 0)
    (hn1 : a + b - 1 ≠ 0)
    (hab1 : 1 ≤ a + b) :
    β * a * ((a + 1) / (a + b + 1)) +
      β * b * (a / (a + b + 1)) +
      (δ * a + α * a * b + γ * a * (a - 1) / 2) *
        ((a - 1) / (a + b - 1)) +
      (δ * b + α * a * b + γ * b * (b - 1) / 2) *
        (a / (a + b - 1)) ≤
      (β * (a + b) + δ * (a + b) + 2 * α * a * b +
        γ * (a * (a - 1) + b * (b - 1)) / 2) *
          (a / (a + b)) := by
  have hexcess :=
    nsd_superharmonic_excess_identity_general
      a b α γ β δ hn hnp1 hn1
  have hden : 0 ≤ 2 * (a + b) * (a + b - 1) := by
    have hsum : 0 ≤ a + b := by linarith
    have hpred : 0 ≤ a + b - 1 := by linarith
    positivity
  have hnum : 0 ≤ (γ - 2 * α) * a * b * (a - b) := by
    have hγ : 0 ≤ γ - 2 * α := by linarith
    have hgap : 0 ≤ a - b := by linarith
    positivity
  have hfrac :
      0 ≤ (γ - 2 * α) * a * b * (a - b) /
        (2 * (a + b) * (a + b - 1)) :=
    div_nonneg hnum hden
  linarith

end Harmonicity

/-! ## Forced-absorb chain and geometric tail infrastructure -/

/-- Modified BD chain that forces deterministic death at states ≤ n₀.
    For y > n₀: same transitions as N. For 0 < y ≤ n₀: p = 0, q = 1 (go to y-1).
    For y = 0: absorbing (same as N). -/
noncomputable def bdChainForcedAbsorb (N : BirthDeathChain) (n₀ : ℕ) : BirthDeathChain where
  p := fun y => if n₀ < y then N.p y else 0
  q := fun y => if 0 < y ∧ y ≤ n₀ then 1 else N.q y
  p_nonneg := fun y => by
    show 0 ≤ (if n₀ < y then N.p y else 0)
    split_ifs <;> [exact N.p_nonneg y; exact le_refl 0]
  q_nonneg := fun y => by
    show 0 ≤ (if 0 < y ∧ y ≤ n₀ then 1 else N.q y)
    split_ifs <;> [linarith; exact N.q_nonneg y]
  pq_le_one := fun y => by
    show (if n₀ < y then N.p y else 0) + (if 0 < y ∧ y ≤ n₀ then 1 else N.q y) ≤ 1
    split_ifs with h1 h2
    · -- n₀ < y AND 0 < y ∧ y ≤ n₀: impossible
      omega
    · -- n₀ < y AND ¬(0 < y ∧ y ≤ n₀): p = N.p y, q = N.q y
      exact N.pq_le_one y
    · -- ¬(n₀ < y) AND 0 < y ∧ y ≤ n₀: p = 0, q = 1
      linarith
    · -- ¬(n₀ < y) AND ¬(0 < y ∧ y ≤ n₀): p = 0, q = N.q y
      have := N.q_nonneg y; have := N.p_nonneg y; have := N.pq_le_one y; linarith
  absorb_zero := by
    constructor
    · show (if n₀ < 0 then N.p 0 else 0) = 0
      simp [show ¬(n₀ < 0) from by omega]
    · show (if 0 < 0 ∧ 0 ≤ n₀ then 1 else N.q 0) = 0
      simp [show ¬(0 < 0 ∧ 0 ≤ n₀) from by omega, N.absorb_zero.2]

/-- The forced-absorb chain has the same p as N for states above n₀. -/
lemma bdChainForcedAbsorb_p_above (N : BirthDeathChain) (n₀ y : ℕ) (hy : n₀ < y) :
    (bdChainForcedAbsorb N n₀).p y = N.p y := by
  show (if n₀ < y then N.p y else 0) = N.p y; simp [hy]

/-- The forced-absorb chain has the same q as N for states above n₀. -/
lemma bdChainForcedAbsorb_q_above (N : BirthDeathChain) (n₀ y : ℕ) (hy : n₀ < y) :
    (bdChainForcedAbsorb N n₀).q y = N.q y := by
  show (if 0 < y ∧ y ≤ n₀ then 1 else N.q y) = N.q y
  simp [show ¬(0 < y ∧ y ≤ n₀) from by omega]

/-- The forced-absorb chain has full negative drift at ALL positive states,
    given that N has drift ≤ -ε at states ≥ n₀ and ε ≤ 1. -/
lemma bdChainForcedAbsorb_full_drift (N : BirthDeathChain) (ε : ℝ) (hε : 0 < ε)
    (n₀ : ℕ) (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (hε1 : ε ≤ 1) :
    ∀ n, 0 < n → (bdChainForcedAbsorb N n₀).p n - (bdChainForcedAbsorb N n₀).q n ≤ -ε := by
  intro n hn
  by_cases h : n₀ < n
  · rw [bdChainForcedAbsorb_p_above N n₀ n h, bdChainForcedAbsorb_q_above N n₀ n h]
    exact hDrift n (le_of_lt h) hn
  · push_neg at h
    -- n ≤ n₀, 0 < n: forced absorb gives p = 0, q = 1
    have hp : (bdChainForcedAbsorb N n₀).p n = 0 := by
      show (if n₀ < n then N.p n else 0) = 0; simp [show ¬(n₀ < n) from not_lt.mpr h]
    have hq : (bdChainForcedAbsorb N n₀).q n = 1 := by
      show (if 0 < n ∧ n ≤ n₀ then 1 else N.q n) = 1; simp [show 0 < n ∧ n ≤ n₀ from ⟨hn, h⟩]
    rw [hp, hq]; linarith

/-- Consecutive deaths lemma: from state m, the BD chain reaches 0 within m steps
    with probability ≥ δ^m, where δ is a lower bound on the death rate. -/
lemma bd_consecutive_deaths (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (m : ℕ) (hm : 0 < m) :
    ENNReal.ofReal (δ ^ m) ≤ (kernelIter (bdKernel N) m) m {0} := by
  induction m with
  | zero => exact absurd hm (by omega)
  | succ m ih =>
    have hm1_pos : 0 < m + 1 := Nat.succ_pos _
    have hq_bound : ENNReal.ofReal (N.q (m + 1)) ≤ (bdKernel N (m + 1)) {m} := by
      rw [bdKernel_apply_singleton]
      have h1 : m ≠ m + 1 + 1 := by omega
      have h2 : m = m + 1 - 1 := by omega
      have h3 : m ≠ m + 1 := by omega
      rw [if_neg h1, if_pos h2, if_neg h3]
      simp
    have hbase : ENNReal.ofReal (δ ^ m) ≤ (kernelIter (bdKernel N) m) m {0} := by
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · simp [kernelIter_zero, Kernel.id_apply]
      · exact ih hm_pos
    -- The goal after kernelIter_succ is (K ∘ₘ K^m)(m+1){0}
    -- which by comp_apply equals ∫⁻ y, K^m(y){0} ∂K(m+1)
    suffices h : ENNReal.ofReal (δ ^ (m + 1)) ≤
        ∫⁻ y, (kernelIter (bdKernel N) m) y {0} ∂(bdKernel N (m + 1)) by
      rw [kernelIter_succ_right, Kernel.comp_apply']; exact h
      exact measurableSet_singleton _
    calc ENNReal.ofReal (δ ^ (m + 1))
        = ENNReal.ofReal (δ ^ m) * ENNReal.ofReal δ := by
          rw [pow_succ, ENNReal.ofReal_mul (pow_nonneg (le_of_lt hδ) _)]
      _ ≤ (kernelIter (bdKernel N) m) m {0} * ENNReal.ofReal δ := by
          exact mul_le_mul_right' hbase _
      _ ≤ (kernelIter (bdKernel N) m) m {0} * ENNReal.ofReal (N.q (m + 1)) := by
          exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal (hDeath _ hm1_pos)) _
      _ ≤ (kernelIter (bdKernel N) m) m {0} * (bdKernel N (m + 1)) {m} := by
          exact mul_le_mul_left' hq_bound _
      _ ≤ ∫⁻ y, (kernelIter (bdKernel N) m) y {0} ∂(bdKernel N (m + 1)) := by
          rw [← lintegral_indicator_const ((Set.to_countable {m}).measurableSet)]
          apply lintegral_mono; intro y
          by_cases hy : y = m
          · simp [hy, Set.indicator_apply]
          · simp only [Set.indicator_apply, Set.mem_singleton_iff, hy, ↓reduceIte, mul_zero]
            exact zero_le

/-! ## Geometric tail for extinction in absorbing BD chains -/

/-- Chapman-Kolmogorov decomposition: survival at time t₁+t₂ equals
    integrating survival at time t₂ over the marginal at time t₁. -/
private lemma survival_chapman_kolmogorov (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (m t₁ t₂ : ℕ) :
    (kernelIter (bdKernel N) (t₁ + t₂)) m {x | 0 < x} =
    ∫⁻ y, (kernelIter (bdKernel N) t₂) y {x | 0 < x}
      ∂((kernelIter (bdKernel N) t₁) m) := by
  rw [kernelIter_add, Kernel.comp_apply' _ _ _ ((Set.to_countable _).measurableSet)]

/-- Survival probability is monotone decreasing in time for absorbing BD chains.
    This uses the fact that 0 is an absorbing state, so {X_t > 0} ⊇ {X_{t+1} > 0}. -/
private lemma survival_mono (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (m t₁ t₂ : ℕ) (h : t₁ ≤ t₂) :
    (kernelIter (bdKernel N) t₂) m {x | 0 < x} ≤
    (kernelIter (bdKernel N) t₁) m {x | 0 < x} := by
  -- Induct on the difference d = t₂ - t₁
  suffices ∀ d : ℕ, (kernelIter (bdKernel N) (t₁ + d)) m {x | 0 < x} ≤
      (kernelIter (bdKernel N) t₁) m {x | 0 < x} by
    have hd := this (t₂ - t₁)
    rwa [Nat.add_sub_cancel' h] at hd
  intro d; induction d with
  | zero => simp
  | succ d ih =>
    calc (kernelIter (bdKernel N) (t₁ + (d + 1))) m {x | 0 < x}
        ≤ (kernelIter (bdKernel N) (t₁ + d)) m {x | 0 < x} := by
          -- One-step decrease: P(X_{t+1} > 0) ≤ P(X_t > 0) because 0 is absorbing
          rw [show t₁ + (d + 1) = (t₁ + d) + 1 from by omega]
          rw [survival_chapman_kolmogorov N m (t₁ + d) 1]
          calc ∫⁻ y, (kernelIter (bdKernel N) 1) y {x | 0 < x}
                ∂((kernelIter (bdKernel N) (t₁ + d)) m)
              ≤ ∫⁻ y, Set.indicator {x | 0 < x} (fun _ => 1) y
                  ∂((kernelIter (bdKernel N) (t₁ + d)) m) := by
                apply lintegral_mono; intro y
                by_cases hy : 0 < y
                · simp only [Set.indicator_of_mem (show y ∈ {x | 0 < x} from hy)]
                  rw [kernelIter_succ, kernelIter_zero, Kernel.comp_id]
                  haveI : IsProbabilityMeasure ((bdKernel N) y) :=
                    IsMarkovKernel.isProbabilityMeasure y
                  exact prob_le_one
                · push_neg at hy
                  have hy0 : y = 0 := by omega
                  subst hy0
                  simp only [kernelIter_bdKernel_zero, Measure.dirac_apply,
                    Set.indicator_apply, Set.mem_setOf_eq, lt_irrefl, ite_false]
                  exact le_refl 0
            _ = (kernelIter (bdKernel N) (t₁ + d)) m {x | 0 < x} := by
                rw [lintegral_indicator ((Set.to_countable _).measurableSet)]; simp
      _ ≤ (kernelIter (bdKernel N) t₁) m {x | 0 < x} := ih

/-- Key bound: from state y ≤ B with δ ≤ q(n), survival after B steps is ≤ 1 - δ^B.
    Uses consecutive deaths and survival monotonicity. -/
private lemma survival_from_bounded (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (δ : ℝ) (hδ : 0 < δ) (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (B : ℕ) (y : ℕ) (hy : 0 < y) (hyB : y ≤ B) (t : ℕ) (ht : B ≤ t) :
    (kernelIter (bdKernel N) t) y {x | 0 < x} ≤ ENNReal.ofReal (1 - δ ^ B) := by
  -- P(τ > t | X₀=y) ≤ P(τ > B | X₀=y) ≤ P(τ > y | X₀=y) ≤ 1 - δ^y ≤ 1 - δ^B
  calc (kernelIter (bdKernel N) t) y {x | 0 < x}
      ≤ (kernelIter (bdKernel N) y) y {x | 0 < x} :=
        survival_mono N y y t (le_trans hyB ht)
    _ = 1 - (kernelIter (bdKernel N) y) y {0} := by
        -- {x > 0} is complement of {0} in ℕ, and K^y(y) is a probability measure
        haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) y) y) :=
          (kernelIter_isMarkov (K := bdKernel N) y).isProbabilityMeasure y
        rw [show ({x : ℕ | 0 < x} : Set ℕ) = {0}ᶜ from by ext x; simp [Nat.pos_iff_ne_zero]]
        exact prob_compl_eq_one_sub (measurableSet_singleton 0)
    _ ≤ 1 - ENNReal.ofReal (δ ^ y) := by
        exact tsub_le_tsub_left (bd_consecutive_deaths N δ hδ hDeath y hy) 1
    _ ≤ ENNReal.ofReal (1 - δ ^ B) := by
        -- 1 - δ^y ≤ 1 - δ^B since δ^y ≥ δ^B (δ ≤ 1, y ≤ B)
        have hδ1 : δ ≤ 1 := by
          have h1 := hDeath 1 Nat.one_pos
          have h2 := N.pq_le_one 1
          have h3 := N.p_nonneg 1
          linarith
        have hδy : 0 ≤ δ ^ y := pow_nonneg (le_of_lt hδ) y
        have hδy_ge : δ ^ B ≤ δ ^ y :=
          pow_le_pow_of_le_one (le_of_lt hδ) hδ1 hyB
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hδy]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ## Tail comparison and WhpTailBound monotonicity -/

/-- The number of births in the first t transitions is at most t. -/
private lemma birthsUpTo_le (ω : ℕ → ℕ) (t : ℕ) : birthsUpTo ω t ≤ t := by
  unfold birthsUpTo
  calc Finset.sum (Finset.range t) (fun i => if ω (i + 1) = ω i + 1 then 1 else 0)
      ≤ Finset.sum (Finset.range t) (fun _ => 1) := by
        apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
    _ = t := by simp

/-- Births before extinction is at most the extinction time (when finite).
    If extinction never occurs, births is 0. -/
private lemma birthsBeforeExtinction_le_extinctionTime (ω : ℕ → ℕ) :
    birthsBeforeExtinction ω ≤ (extinctionTime ω).untopD 0 := by
  unfold birthsBeforeExtinction
  match h : extinctionTime ω with
  | ⊤ => simp [h]
  | (t : ℕ) => simp [h]; exact birthsUpTo_le ω t

/-- Birth tail is pointwise ≤ extinction tail:
    P(births ≥ t) ≤ P(τ ≥ t) since births ≤ τ. -/
lemma birthTail_le_extinctionTail (N : BirthDeathChain) (m t : ℕ)
    [IsMarkovKernel (bdKernel N)] :
    birthTail N m t ≤ extinctionTail N m t := by
  unfold birthTail extinctionTail
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  -- Need: t ≤ birthsBeforeExtinction ω → extinctionTime ω ≥ t
  unfold birthsBeforeExtinction at hω
  match h : extinctionTime ω with
  | ⊤ => exact le_top
  | (τ : ℕ) =>
    rw [h] at hω
    -- hω : t ≤ birthsUpTo ω τ, and birthsUpTo ω τ ≤ τ
    have hle : birthsUpTo ω τ ≤ τ := birthsUpTo_le ω τ
    exact_mod_cast le_trans hω hle

lemma lvKernel_nsd_harmonic_integral
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hφ : lvTotalPropensity params (a, b) ≠ 0)
    (hHarm :
      params.beta * a * h (a + 1, b) + params.beta * b * h (a, b + 1) +
      (params.delta * a + params.alpha1 * a * b +
        params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) * h (a - 1, b) +
      (params.delta * b + params.alpha0 * a * b +
        params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) * h (a, b - 1) =
      lvTotalPropensity params (a, b) * h (a, b)) :
    ∫ x, h x ∂(lvKernel .nonSelfDestructive params) (a, b) = h (a, b) := by
  -- Cast facts
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  have hga : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := div_nonneg (by nlinarith) (by norm_num)
  have hgb : 0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 := div_nonneg (by nlinarith) (by norm_num)
  have hφ_pos : 0 < lvTotalPropensity params (a, b) := by
    refine lt_of_le_of_ne ?_ (Ne.symm hφ)
    unfold lvTotalPropensity
    linarith [mul_nonneg params.beta_nonneg ha', mul_nonneg params.beta_nonneg hb',
      mul_nonneg params.delta_nonneg ha', mul_nonneg params.delta_nonneg hb',
      mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb',
      mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb',
      mul_nonneg params.gamma0_nonneg hga, mul_nonneg params.gamma1_nonneg hgb]
  rw [lvKernel_nsd_apply params a b hφ, integral_smul_measure]
  -- Integrability of h against each weighted Dirac
  have isd := fun c s => integrable_ofReal_smul_dirac h c (α := PopState) s
  have iadd := fun {μ ν : Measure PopState} (hμ : Integrable h μ)
    (hν : Integrable h ν) => hμ.add_measure hν
  have i1 := isd (params.beta * a) (a + 1, b)
  have i2 := isd (params.beta * b) (a, b + 1)
  have i3 := isd (params.delta * a) (a - 1, b)
  have i4 := isd (params.delta * b) (a, b - 1)
  have i5 := isd (params.alpha0 * a * b) (a, b - 1)
  have i6 := isd (params.alpha1 * a * b) (a - 1, b)
  have i7 := isd (params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) (a - 1, b)
  have i8 := isd (params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) (a, b - 1)
  -- Split 8-term measure sum into individual integrals
  rw [integral_add_measure (iadd (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7) i8,
    integral_add_measure (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7,
    integral_add_measure (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6,
    integral_add_measure (iadd (iadd (iadd i1 i2) i3) i4) i5,
    integral_add_measure (iadd (iadd i1 i2) i3) i4,
    integral_add_measure (iadd i1 i2) i3,
    integral_add_measure i1 i2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hφ_pos.le),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma0_nonneg hga),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma1_nonneg hgb)]
  field_simp
  linarith [one_div_mul_cancel hφ]

/-- Superharmonic counterpart of `lvKernel_nsd_harmonic_integral`. -/
lemma lvKernel_nsd_superharmonic_integral
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hφ : lvTotalPropensity params (a, b) ≠ 0)
    (hSuper :
      params.beta * a * h (a + 1, b) + params.beta * b * h (a, b + 1) +
      (params.delta * a + params.alpha1 * a * b +
        params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) * h (a - 1, b) +
      (params.delta * b + params.alpha0 * a * b +
        params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) * h (a, b - 1) ≤
      lvTotalPropensity params (a, b) * h (a, b)) :
    ∫ x, h x ∂(lvKernel .nonSelfDestructive params) (a, b) ≤ h (a, b) := by
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  have hga : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 :=
    div_nonneg (by nlinarith) (by norm_num)
  have hgb : 0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 :=
    div_nonneg (by nlinarith) (by norm_num)
  have hφ_pos : 0 < lvTotalPropensity params (a, b) := by
    refine lt_of_le_of_ne ?_ (Ne.symm hφ)
    unfold lvTotalPropensity
    linarith [mul_nonneg params.beta_nonneg ha',
      mul_nonneg params.beta_nonneg hb',
      mul_nonneg params.delta_nonneg ha',
      mul_nonneg params.delta_nonneg hb',
      mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb',
      mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb',
      mul_nonneg params.gamma0_nonneg hga,
      mul_nonneg params.gamma1_nonneg hgb]
  rw [lvKernel_nsd_apply params a b hφ, integral_smul_measure]
  have isd := fun c s =>
    integrable_ofReal_smul_dirac h c (α := PopState) s
  have iadd := fun {μ ν : Measure PopState} (hμ : Integrable h μ)
    (hν : Integrable h ν) => hμ.add_measure hν
  have i1 := isd (params.beta * a) (a + 1, b)
  have i2 := isd (params.beta * b) (a, b + 1)
  have i3 := isd (params.delta * a) (a - 1, b)
  have i4 := isd (params.delta * b) (a, b - 1)
  have i5 := isd (params.alpha0 * a * b) (a, b - 1)
  have i6 := isd (params.alpha1 * a * b) (a - 1, b)
  have i7 := isd
    (params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) (a - 1, b)
  have i8 := isd
    (params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) (a, b - 1)
  rw [integral_add_measure
      (iadd (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7) i8,
    integral_add_measure
      (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7,
    integral_add_measure
      (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6,
    integral_add_measure (iadd (iadd (iadd i1 i2) i3) i4) i5,
    integral_add_measure (iadd (iadd i1 i2) i3) i4,
    integral_add_measure (iadd i1 i2) i3,
    integral_add_measure i1 i2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_ofReal
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hφ_pos.le),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg hb'),
    ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb'),
    ENNReal.toReal_ofReal
      (mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma0_nonneg hga),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma1_nonneg hgb)]
  field_simp
  nlinarith [hSuper, one_div_mul_cancel hφ]

/-! ## SD kernel integral computation -/

/-- The SD LV kernel integral gives the harmonicity formula.
    If `h` satisfies the algebraic harmonicity condition at `(a,b)`,
    then `∫ h ∂(lvKernel SD params)(a,b) = h(a,b)`.
    Note: in SD, both Inter0 and Inter1 map to (a-1,b-1). -/
lemma lvKernel_sd_harmonic_integral
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hφ : lvTotalPropensity params (a, b) ≠ 0)
    (hHarm :
      params.beta * a * h (a + 1, b) + params.beta * b * h (a, b + 1) +
      params.delta * a * h (a - 1, b) + params.delta * b * h (a, b - 1) +
      (params.alpha0 + params.alpha1) * a * b * h (a - 1, b - 1) +
      params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) * h (a - 2, b) +
      params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) * h (a, b - 2) =
      lvTotalPropensity params (a, b) * h (a, b)) :
    ∫ x, h x ∂(lvKernel .selfDestructive params) (a, b) = h (a, b) := by
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  have hga : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := div_nonneg (by nlinarith) (by norm_num)
  have hgb : 0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 := div_nonneg (by nlinarith) (by norm_num)
  have hφ_pos : 0 < lvTotalPropensity params (a, b) := by
    refine lt_of_le_of_ne ?_ (Ne.symm hφ)
    unfold lvTotalPropensity
    linarith [mul_nonneg params.beta_nonneg ha', mul_nonneg params.beta_nonneg hb',
      mul_nonneg params.delta_nonneg ha', mul_nonneg params.delta_nonneg hb',
      mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb',
      mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb',
      mul_nonneg params.gamma0_nonneg hga, mul_nonneg params.gamma1_nonneg hgb]
  rw [lvKernel_sd_apply params a b hφ, integral_smul_measure]
  have isd := fun c s => integrable_ofReal_smul_dirac h c (α := PopState) s
  have iadd := fun {μ ν : Measure PopState} (hμ : Integrable h μ)
    (hν : Integrable h ν) => hμ.add_measure hν
  have i1 := isd (params.beta * a) (a + 1, b)
  have i2 := isd (params.beta * b) (a, b + 1)
  have i3 := isd (params.delta * a) (a - 1, b)
  have i4 := isd (params.delta * b) (a, b - 1)
  have i5 := isd (params.alpha0 * a * b) (a - 1, b - 1)
  have i6 := isd (params.alpha1 * a * b) (a - 1, b - 1)
  have i7 := isd (params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) (a - 2, b)
  have i8 := isd (params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) (a, b - 2)
  rw [integral_add_measure (iadd (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7) i8,
    integral_add_measure (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7,
    integral_add_measure (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6,
    integral_add_measure (iadd (iadd (iadd i1 i2) i3) i4) i5,
    integral_add_measure (iadd (iadd i1 i2) i3) i4,
    integral_add_measure (iadd i1 i2) i3,
    integral_add_measure i1 i2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hφ_pos.le),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma0_nonneg hga),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma1_nonneg hgb)]
  field_simp
  linarith [one_div_mul_cancel hφ]

/-- Superharmonic counterpart of `lvKernel_sd_harmonic_integral`. -/
lemma lvKernel_sd_superharmonic_integral
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hφ : lvTotalPropensity params (a, b) ≠ 0)
    (hSuper :
      params.beta * a * h (a + 1, b) + params.beta * b * h (a, b + 1) +
      params.delta * a * h (a - 1, b) + params.delta * b * h (a, b - 1) +
      (params.alpha0 + params.alpha1) * a * b * h (a - 1, b - 1) +
      params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) * h (a - 2, b) +
      params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) * h (a, b - 2) ≤
      lvTotalPropensity params (a, b) * h (a, b)) :
    ∫ x, h x ∂(lvKernel .selfDestructive params) (a, b) ≤ h (a, b) := by
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.le
  have ha1 : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  have hga : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) / 2 := div_nonneg (by nlinarith) (by norm_num)
  have hgb : 0 ≤ (b : ℝ) * ((b : ℝ) - 1) / 2 := div_nonneg (by nlinarith) (by norm_num)
  have hφ_pos : 0 < lvTotalPropensity params (a, b) := by
    refine lt_of_le_of_ne ?_ (Ne.symm hφ)
    unfold lvTotalPropensity
    linarith [mul_nonneg params.beta_nonneg ha', mul_nonneg params.beta_nonneg hb',
      mul_nonneg params.delta_nonneg ha', mul_nonneg params.delta_nonneg hb',
      mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb',
      mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb',
      mul_nonneg params.gamma0_nonneg hga, mul_nonneg params.gamma1_nonneg hgb]
  rw [lvKernel_sd_apply params a b hφ, integral_smul_measure]
  have isd := fun c s => integrable_ofReal_smul_dirac h c (α := PopState) s
  have iadd := fun {μ ν : Measure PopState} (hμ : Integrable h μ)
    (hν : Integrable h ν) => hμ.add_measure hν
  have i1 := isd (params.beta * a) (a + 1, b)
  have i2 := isd (params.beta * b) (a, b + 1)
  have i3 := isd (params.delta * a) (a - 1, b)
  have i4 := isd (params.delta * b) (a, b - 1)
  have i5 := isd (params.alpha0 * a * b) (a - 1, b - 1)
  have i6 := isd (params.alpha1 * a * b) (a - 1, b - 1)
  have i7 := isd (params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) (a - 2, b)
  have i8 := isd (params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) (a, b - 2)
  rw [integral_add_measure (iadd (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7) i8,
    integral_add_measure (iadd (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6) i7,
    integral_add_measure (iadd (iadd (iadd (iadd i1 i2) i3) i4) i5) i6,
    integral_add_measure (iadd (iadd (iadd i1 i2) i3) i4) i5,
    integral_add_measure (iadd (iadd i1 i2) i3) i4,
    integral_add_measure (iadd i1 i2) i3,
    integral_add_measure i1 i2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hφ_pos.le),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.beta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg ha'),
    ENNReal.toReal_ofReal (mul_nonneg params.delta_nonneg hb'),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg params.alpha0_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg params.alpha1_nonneg ha') hb'),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma0_nonneg hga),
    ENNReal.toReal_ofReal (mul_nonneg params.gamma1_nonneg hgb)]
  field_simp
  nlinarith [hSuper, one_div_mul_cancel hφ]

/-! ## Consensus = harmonic function

The discrete optional stopping theorem for bounded harmonic functions on
absorbing Markov chains: if h is [0,1]-valued and harmonic at interior states,
with boundary values h(a,0) = 1 and h(0,b) = 0, then
P(majority wins | X₀ = (a,b)) = h(a,b).

For chains with β=δ=0, we prove this via kernel iteration concentration:
after finitely many steps, the chain reaches {(1,0),(0,1)}, and
K^N({(1,0)}) = h(a,b) by harmonic iteration. -/

section OptionalStopping

/-! ### SD kernel concentration infrastructure

For the SD LV chain with β=δ=0: each non-absorbing step decreases total
population by exactly 2, so after N = (a+b-1)/2 steps the measure concentrates
on {(1,0),(0,1)}. -/

private lemma weighted_dirac_bad_set_zero
    (w : ℝ) (t : ℕ × ℕ) (m : ℕ)
    (hw : w ≤ 0 ∨ t.1 + t.2 = m) :
    ENNReal.ofReal w * Measure.dirac t {s' : ℕ × ℕ | s'.1 + s'.2 ≠ m} = 0 := by
  rcases hw with hw | ht
  · simp [ENNReal.ofReal_eq_zero.mpr hw]
  · simp [Measure.dirac_apply, ht]

lemma sd_kernel_totalPop_decrease
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)]
    (a' b' : ℕ) (hs : 2 ≤ a' + b') :
    (lvKernel LVVariant.selfDestructive params) (a', b')
      {s' : ℕ × ℕ | s'.1 + s'.2 ≠ a' + b' - 2} = 0 := by
  have hα0 := params.alpha0_nonneg
  have hα1 := params.alpha1_nonneg
  have hφ : lvTotalPropensity params (a', b') ≠ 0 := by
    intro heq; simp only [lvTotalPropensity, hBeta, hDelta, zero_mul, add_zero] at heq
    have t3 : 0 ≤ params.gamma0 * (↑a' * (↑a' - 1) / 2) := by
      rcases Nat.eq_zero_or_pos a' with rfl | h; · simp
      exact mul_nonneg hGamma0.le (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr h))) (by norm_num))
    have t4 : 0 ≤ params.gamma1 * (↑b' * (↑b' - 1) / 2) := by
      rcases Nat.eq_zero_or_pos b' with rfl | h; · simp
      exact mul_nonneg hGamma1.le (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr h))) (by norm_num))
    have tα : 0 ≤ (params.alpha0 + params.alpha1) * ↑a' * ↑b' := by positivity
    have ha1 : a' ≤ 1 := by
      by_contra hc; push_neg at hc
      exact absurd (by linarith : params.gamma0 * (↑a' * (↑a' - 1) / 2) = 0) (ne_of_gt
        (mul_pos hGamma0 (div_pos (mul_pos (Nat.cast_pos.mpr (by omega))
          (sub_pos.mpr (by exact_mod_cast show (1 : ℕ) < a' by omega))) (by norm_num))))
    have hb1 : b' ≤ 1 := by
      by_contra hc; push_neg at hc
      exact absurd (by linarith : params.gamma1 * (↑b' * (↑b' - 1) / 2) = 0) (ne_of_gt
        (mul_pos hGamma1 (div_pos (mul_pos (Nat.cast_pos.mpr (by omega))
          (sub_pos.mpr (by exact_mod_cast show (1 : ℕ) < b' by omega))) (by norm_num))))
    rcases show a' = 1 ∧ b' = 1 from by omega with ⟨rfl, rfl⟩
    simp only [Nat.cast_one] at heq; linarith
  rw [lvKernel_sd_apply params a' b' hφ, Measure.smul_apply]
  simp only [hBeta, hDelta, zero_mul, ENNReal.ofReal_zero, zero_smul, add_zero, zero_add,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  set m := a' + b' - 2
  have h_inter : ∀ (α : ℝ), 0 ≤ α → (α * ↑a' * ↑b' ≤ 0 ∨ (a' - 1) + (b' - 1) = m) := by
    intro α hα
    rcases Nat.eq_zero_or_pos a' with rfl | ha
    · left; simp
    · rcases Nat.eq_zero_or_pos b' with rfl | hb
      · left; simp
      · right; omega
  have h_intra0 : params.gamma0 * (↑a' * (↑a' - 1) / 2) ≤ 0 ∨ (a' - 2) + b' = m := by
    rcases Nat.lt_or_ge a' 2 with h | h
    · left
      rcases Nat.eq_zero_or_pos a' with rfl | ha
      · simp
      · have ha1 : a' = 1 := by omega
        subst ha1; simp [Nat.cast_one]
    · right; omega
  have h_intra1 : params.gamma1 * (↑b' * (↑b' - 1) / 2) ≤ 0 ∨ a' + (b' - 2) = m := by
    rcases Nat.lt_or_ge b' 2 with h | h
    · left
      rcases Nat.eq_zero_or_pos b' with rfl | hb
      · simp
      · have hb1 : b' = 1 := by omega
        subst hb1; simp [Nat.cast_one]
    · right; omega
  rw [weighted_dirac_bad_set_zero _ (a'-1, b'-1) m (h_inter _ hα0),
      weighted_dirac_bad_set_zero _ (a'-1, b'-1) m (h_inter _ hα1),
      weighted_dirac_bad_set_zero _ (a'-2, b') m h_intra0,
      weighted_dirac_bad_set_zero _ (a', b'-2) m h_intra1]; simp

/-- After n steps of the SD kernel with β=δ=0, totalPop = a+b-2n. -/
lemma sd_kernelIter_totalPop
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)]
    (a b : ℕ) (hOdd : Odd (a + b))
    (n : ℕ) (hn : n ≤ (a + b - 1) / 2) :
    (kernelIter (lvKernel LVVariant.selfDestructive params) n) (a, b)
      {s : ℕ × ℕ | s.1 + s.2 ≠ a + b - 2 * n} = 0 := by
  induction n with
  | zero => simp [kernelIter_zero, Kernel.id_apply, Measure.dirac_apply]
  | succ n ih =>
    have hn' : n ≤ (a + b - 1) / 2 := by omega
    set S := {s : ℕ × ℕ | s.1 + s.2 = a + b - 2 * n}
    set S' := {s : ℕ × ℕ | s.1 + s.2 = a + b - 2 * (n + 1)}
    have hSm : MeasurableSet S := (Set.to_countable _).measurableSet
    have hS'm : MeasurableSet S' := (Set.to_countable _).measurableSet
    have hStep : ∀ x ∈ S, (lvKernel LVVariant.selfDestructive params) x S'ᶜ = 0 := by
      intro ⟨a', b'⟩ hx
      simp only [S, Set.mem_setOf_eq] at hx
      have hpop_ge2 : 2 ≤ a' + b' := by rw [hx]; obtain ⟨k, hk⟩ := hOdd; omega
      have := sd_kernel_totalPop_decrease params hBeta hDelta hGamma0 hGamma1
        hAlphaSum a' b' hpop_ge2
      have hset : S'ᶜ = {s' : ℕ × ℕ | s'.1 + s'.2 ≠ a' + b' - 2} := by
        simp only [S', Set.compl_setOf]
        ext ⟨x, y⟩; simp only [Set.mem_setOf_eq]
        constructor <;> intro h <;> omega
      rw [hset]; exact this
    exact kernelIter_concentrated_step _ _ _ S S' hSm hS'm (ih hn') hStep

/-- K^N(a,b) concentrates on {(1,0),(0,1)} where N = (a+b-1)/2. -/
lemma sd_kernelIter_concentrated_on_absorbing
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hOdd : Odd (a + b)) :
    let N := (a + b - 1) / 2
    (kernelIter (lvKernel LVVariant.selfDestructive params) N) (a, b)
      {s : ℕ × ℕ | s ≠ (1, 0) ∧ s ≠ (0, 1)} = 0 := by
  intro N
  have := sd_kernelIter_totalPop params hBeta hDelta hGamma0 hGamma1
    hAlphaSum a b hOdd N le_rfl
  have h_pop1 : a + b - 2 * N = 1 := by obtain ⟨k, hk⟩ := hOdd; omega
  rw [h_pop1] at this
  apply le_antisymm _ zero_le
  calc (kernelIter (lvKernel LVVariant.selfDestructive params) N) (a, b)
          {s : ℕ × ℕ | s ≠ (1, 0) ∧ s ≠ (0, 1)}
      ≤ (kernelIter (lvKernel LVVariant.selfDestructive params) N) (a, b)
          {s : ℕ × ℕ | s.1 + s.2 ≠ 1} := by
        apply measure_mono; intro ⟨x, y⟩ h
        simp only [Set.mem_setOf_eq, ne_eq, Prod.mk.injEq, not_and] at h ⊢
        obtain ⟨h1, h2⟩ := h; intro heq
        have : x = 0 ∨ x = 1 := by omega
        rcases this with rfl | rfl
        · exact h2 rfl (by omega)
        · exact h1 rfl (by omega)
    _ = 0 := this

/-- One-step absorbing: when species 1 is dead (s.2=0) and β=δ=0,
    the kernel assigns zero mass to states where species 1 is alive. -/
lemma sd_kernel_species1_dead_absorbing
    (params : LVParams) (s : PopState)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hs : s.2 = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    (lvKernel LVVariant.selfDestructive params) s
      {s' : PopState | s'.2 ≠ 0} = 0 := by
  simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  by_cases hφ : lvTotalPropensity params s = 0
  · simp [hφ, hs]
  · simp only [hBeta, hDelta, hs, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, zero_add, add_zero, hφ, ↓reduceDIte,
      zero_div]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (by measurability : MeasurableSet {s' : PopState | s'.2 ≠ 0})]
    simp [Set.mem_setOf_eq]

/-- One-step absorbing: when species 0 is dead (s.1=0) and β=δ=0,
    the kernel assigns zero mass to states where species 0 is alive. -/
lemma sd_kernel_species0_dead_absorbing
    (params : LVParams) (s : PopState)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hs : s.1 = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    (lvKernel LVVariant.selfDestructive params) s
      {s' : PopState | s'.1 ≠ 0} = 0 := by
  simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  by_cases hφ : lvTotalPropensity params s = 0
  · simp [hφ, hs]
  · simp only [hBeta, hDelta, hs, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, zero_add, add_zero, hφ, ↓reduceDIte,
      zero_div]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ (by measurability : MeasurableSet {s' : PopState | s'.1 ≠ 0})]
    simp [Set.mem_setOf_eq]

/-- One-step absorbing for SD: when species 1 is dead (s.2=0),
    the kernel assigns zero mass to states where species 1 is alive.
    Unlike `sd_kernel_species1_dead_absorbing`, this requires NO parameter
    restrictions: all species-1 rates have factor b=s.2=0. -/
lemma sd_kernel_species1_dead_absorbing_general
    (params : LVParams) (s : PopState)
    (hs : s.2 = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    (lvKernel LVVariant.selfDestructive params) s
      {s' : PopState | s'.2 ≠ 0} = 0 := by
  by_cases hφ : lvTotalPropensity params s = 0
  · have hker := lvKernel_apply_zero_propensity .selfDestructive params s hφ
    rw [hker, Measure.dirac_apply' _ (by measurability)]; simp [hs]
  · simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
    simp only [hs, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, zero_add, add_zero, hφ, ↓reduceDIte, zero_div]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      Nat.cast_zero, zero_mul, mul_zero,
      ENNReal.ofReal_zero, add_zero]
    simp only [Measure.dirac_apply' _ (by measurability : MeasurableSet {s' : PopState | s'.2 ≠ 0})]
    simp [Set.mem_setOf_eq]

/-- One-step absorbing for SD: when species 0 is dead (s.1=0),
    the kernel assigns zero mass to states where species 0 is alive.
    Unlike `sd_kernel_species0_dead_absorbing`, this requires NO parameter
    restrictions: all species-0 rates have factor a=s.1=0. -/
lemma sd_kernel_species0_dead_absorbing_general
    (params : LVParams) (s : PopState)
    (hs : s.1 = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    (lvKernel LVVariant.selfDestructive params) s
      {s' : PopState | s'.1 ≠ 0} = 0 := by
  by_cases hφ : lvTotalPropensity params s = 0
  · have hker := lvKernel_apply_zero_propensity .selfDestructive params s hφ
    rw [hker, Measure.dirac_apply' _ (by measurability)]; simp [hs]
  · simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
    simp only [hs, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, zero_add, add_zero, hφ, ↓reduceDIte, zero_div]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      Nat.cast_zero, zero_mul, mul_zero,
      ENNReal.ofReal_zero, add_zero]
    simp only [Measure.dirac_apply' _ (by measurability : MeasurableSet {s' : PopState | s'.1 ≠ 0})]
    simp [Set.mem_setOf_eq]

/-! ### NSD kernel absorbing and concentration infrastructure

For the NSD LV chain: boundary states {s.1=0} and {s.2=0} are absorbing for ALL
parameters (not just β=δ=0), because birth rate ∝ current count of that species.
With β=δ=0, each step decreases total population by 1, concentrating on
{(1,0),(0,1)} after N=a+b-1 steps. -/

/-- One-step absorbing: when species 1 is dead (s.2=0),
    the NSD kernel assigns zero mass to states where species 1 is alive. -/
lemma nsd_kernel_species1_dead_absorbing
    (params : LVParams) (s : PopState)
    (hs : s.2 = 0)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    (lvKernel LVVariant.nonSelfDestructive params) s
      {s' : PopState | s'.2 ≠ 0} = 0 := by
  by_cases hφ : lvTotalPropensity params s = 0
  · have hker := lvKernel_apply_zero_propensity .nonSelfDestructive params s hφ
    rw [hker, Measure.dirac_apply' _ (by measurability)]; simp [hs]
  · simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
    simp only [hs, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, zero_add, add_zero, hφ, ↓reduceDIte, zero_div]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      Nat.cast_zero, zero_mul, mul_zero,
      ENNReal.ofReal_zero, add_zero]
    simp only [Measure.dirac_apply' _ (by measurability : MeasurableSet {s' : PopState | s'.2 ≠ 0})]
    simp [Set.mem_setOf_eq]

/-- One-step absorbing: when species 0 is dead (s.1=0),
    the NSD kernel assigns zero mass to states where species 0 is alive. -/
lemma nsd_kernel_species0_dead_absorbing
    (params : LVParams) (s : PopState)
    (hs : s.1 = 0)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    (lvKernel LVVariant.nonSelfDestructive params) s
      {s' : PopState | s'.1 ≠ 0} = 0 := by
  by_cases hφ : lvTotalPropensity params s = 0
  · have hker := lvKernel_apply_zero_propensity .nonSelfDestructive params s hφ
    rw [hker, Measure.dirac_apply' _ (by measurability)]; simp [hs]
  · simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
    simp only [hs, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, zero_add, add_zero, hφ, ↓reduceDIte, zero_div]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
      Nat.cast_zero, zero_mul, mul_zero,
      ENNReal.ofReal_zero, add_zero]
    simp only [Measure.dirac_apply' _ (by measurability : MeasurableSet {s' : PopState | s'.1 ≠ 0})]
    simp [Set.mem_setOf_eq]

/-- Multi-step absorbing: K^m concentrates on {s'.2=0} when starting from s.2=0 (NSD). -/
lemma nsd_kernelIter_species1_dead_absorbing
    (params : LVParams) (s : PopState)
    (hs : s.2 = 0) (m : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    (kernelIter (lvKernel LVVariant.nonSelfDestructive params) m) s
      {s' : PopState | s'.2 ≠ 0} = 0 := by
  induction m with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    rw [Measure.dirac_apply' _ (by measurability)]
    simp [Set.mem_setOf_eq, hs]
  | succ n ih =>
    rw [kernelIter_succ, Kernel.comp_apply]
    have hbind : (⇑(lvKernel LVVariant.nonSelfDestructive params) ∘ₘ
      (kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s)
      {s' | s'.2 ≠ 0} =
      ∫⁻ y, (lvKernel LVVariant.nonSelfDestructive params) y {s' | s'.2 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s) := by
      apply Measure.bind_apply <;> measurability
    rw [hbind]
    apply le_antisymm _ zero_le
    have hpw : ∀ (y : PopState),
        (lvKernel LVVariant.nonSelfDestructive params) y {s' : PopState | s'.2 ≠ 0}
        ≤ Set.indicator {s' : PopState | s'.2 ≠ 0} (1 : PopState → ℝ≥0∞) y := by
      intro y; by_cases hy : y.2 = 0
      · simp [Set.indicator, Set.mem_setOf_eq, hy,
          nsd_kernel_species1_dead_absorbing params y hy]
      · simp [Set.indicator, Set.mem_setOf_eq, hy]; exact prob_le_one
    calc ∫⁻ y, (lvKernel LVVariant.nonSelfDestructive params) y {s' | s'.2 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s)
      ≤ ∫⁻ y, Set.indicator {s' : PopState | s'.2 ≠ 0} (1 : PopState → ℝ≥0∞) y
        ∂((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s) :=
        lintegral_mono hpw
      _ = ((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s)
        {s' | s'.2 ≠ 0} := lintegral_indicator_one (by measurability)
      _ = 0 := ih

/-- Multi-step absorbing: K^m concentrates on {s'.1=0} when starting from s.1=0 (NSD). -/
lemma nsd_kernelIter_species0_dead_absorbing
    (params : LVParams) (s : PopState)
    (hs : s.1 = 0) (m : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    (kernelIter (lvKernel LVVariant.nonSelfDestructive params) m) s
      {s' : PopState | s'.1 ≠ 0} = 0 := by
  induction m with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    rw [Measure.dirac_apply' _ (by measurability)]
    simp [Set.mem_setOf_eq, hs]
  | succ n ih =>
    rw [kernelIter_succ, Kernel.comp_apply]
    have hbind : (⇑(lvKernel LVVariant.nonSelfDestructive params) ∘ₘ
      (kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s)
      {s' | s'.1 ≠ 0} =
      ∫⁻ y, (lvKernel LVVariant.nonSelfDestructive params) y {s' | s'.1 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s) := by
      apply Measure.bind_apply <;> measurability
    rw [hbind]
    apply le_antisymm _ zero_le
    have hpw : ∀ (y : PopState),
        (lvKernel LVVariant.nonSelfDestructive params) y {s' : PopState | s'.1 ≠ 0}
        ≤ Set.indicator {s' : PopState | s'.1 ≠ 0} (1 : PopState → ℝ≥0∞) y := by
      intro y; by_cases hy : y.1 = 0
      · simp [Set.indicator, Set.mem_setOf_eq, hy,
          nsd_kernel_species0_dead_absorbing params y hy]
      · simp [Set.indicator, Set.mem_setOf_eq, hy]; exact prob_le_one
    calc ∫⁻ y, (lvKernel LVVariant.nonSelfDestructive params) y {s' | s'.1 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s)
      ≤ ∫⁻ y, Set.indicator {s' : PopState | s'.1 ≠ 0} (1 : PopState → ℝ≥0∞) y
        ∂((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s) :=
        lintegral_mono hpw
      _ = ((kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) s)
        {s' | s'.1 ≠ 0} := lintegral_indicator_one (by measurability)
      _ = 0 := ih

/-- NSD kernel with β=δ=0: each non-absorbing step decreases total population by 1. -/
lemma nsd_kernel_totalPop_decrease
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (a' b' : ℕ) (hs : 2 ≤ a' + b') :
    (lvKernel LVVariant.nonSelfDestructive params) (a', b')
      {s' : ℕ × ℕ | s'.1 + s'.2 ≠ a' + b' - 1} = 0 := by
  have hα0 := params.alpha0_nonneg
  have hα1 := params.alpha1_nonneg
  have hφ : lvTotalPropensity params (a', b') ≠ 0 := by
    intro heq; simp only [lvTotalPropensity, hBeta, hDelta, zero_mul, add_zero] at heq
    have tα0 : 0 ≤ params.alpha0 * ↑a' * ↑b' :=
      mul_nonneg (mul_nonneg hα0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have tα1 : 0 ≤ params.alpha1 * ↑a' * ↑b' :=
      mul_nonneg (mul_nonneg hα1 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have t3 : 0 ≤ params.gamma0 * (↑a' * (↑a' - 1) / 2) := by
      rcases Nat.eq_zero_or_pos a' with rfl | h; · simp
      exact mul_nonneg hGamma0.le (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr h))) (by norm_num))
    have t4 : 0 ≤ params.gamma1 * (↑b' * (↑b' - 1) / 2) := by
      rcases Nat.eq_zero_or_pos b' with rfl | h; · simp
      exact mul_nonneg hGamma1.le (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr h))) (by norm_num))
    have ha1 : a' ≤ 1 := by
      by_contra hc; push_neg at hc
      have : params.gamma0 * (↑a' * (↑a' - 1) / 2) > 0 :=
        mul_pos hGamma0 (div_pos (mul_pos (Nat.cast_pos.mpr (by omega))
          (sub_pos.mpr (by exact_mod_cast (show 1 < a' by omega)))) (by norm_num))
      linarith
    have hb1 : b' ≤ 1 := by
      by_contra hc; push_neg at hc
      have : params.gamma1 * (↑b' * (↑b' - 1) / 2) > 0 :=
        mul_pos hGamma1 (div_pos (mul_pos (Nat.cast_pos.mpr (by omega))
          (sub_pos.mpr (by exact_mod_cast (show 1 < b' by omega)))) (by norm_num))
      linarith
    obtain ⟨rfl, rfl⟩ : a' = 1 ∧ b' = 1 := by omega
    simp only [Nat.cast_one, mul_one, one_mul, sub_self, zero_div, mul_zero, add_zero] at heq
    linarith
  rw [lvKernel_nsd_apply params a' b' hφ, Measure.smul_apply]
  simp only [hBeta, hDelta, zero_mul, ENNReal.ofReal_zero, zero_smul, add_zero, zero_add,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  set m := a' + b' - 1 with hm_def
  set t0 : ℕ × ℕ := (a', b' - 1)
  set t1 : ℕ × ℕ := (a' - 1, b')
  have h_a0 : params.alpha0 * ↑a' * ↑b' ≤ 0 ∨ t0.1 + t0.2 = m := by
    rcases Nat.eq_zero_or_pos b' with rfl | hb; · left; simp
    right; simp [t0]; omega
  have h_a1 : params.alpha1 * ↑a' * ↑b' ≤ 0 ∨ t1.1 + t1.2 = m := by
    rcases Nat.eq_zero_or_pos a' with rfl | ha; · left; simp
    right; simp [t1]; omega
  have h_g0 : params.gamma0 * (↑a' * (↑a' - 1) / 2) ≤ 0 ∨ t1.1 + t1.2 = m := by
    rcases Nat.eq_zero_or_pos a' with rfl | ha; · left; simp
    right; simp [t1]; omega
  have h_g1 : params.gamma1 * (↑b' * (↑b' - 1) / 2) ≤ 0 ∨ t0.1 + t0.2 = m := by
    rcases Nat.eq_zero_or_pos b' with rfl | hb; · left; simp
    right; simp [t0]; omega
  rw [weighted_dirac_bad_set_zero _ t0 m h_a0,
      weighted_dirac_bad_set_zero _ t1 m h_a1,
      weighted_dirac_bad_set_zero _ t1 m h_g0,
      weighted_dirac_bad_set_zero _ t0 m h_g1]; simp

/-- After n steps of the NSD kernel with β=δ=0, totalPop = a+b-n. -/
lemma nsd_kernelIter_totalPop
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hn : n ≤ a + b - 1) :
    (kernelIter (lvKernel LVVariant.nonSelfDestructive params) n) (a, b)
      {s : ℕ × ℕ | s.1 + s.2 ≠ a + b - n} = 0 := by
  induction n with
  | zero => simp [kernelIter_zero, Kernel.id_apply]
  | succ n ih =>
    have hn' : n ≤ a + b - 1 := by omega
    set S := {s : ℕ × ℕ | s.1 + s.2 = a + b - n}
    set S' := {s : ℕ × ℕ | s.1 + s.2 = a + b - (n + 1)}
    have hSm : MeasurableSet S := (Set.to_countable _).measurableSet
    have hS'm : MeasurableSet S' := (Set.to_countable _).measurableSet
    have hStep : ∀ x ∈ S, (lvKernel LVVariant.nonSelfDestructive params) x S'ᶜ = 0 := by
      intro ⟨a', b'⟩ hx
      simp only [S, Set.mem_setOf_eq] at hx
      have hpop_ge2 : 2 ≤ a' + b' := by omega
      have := nsd_kernel_totalPop_decrease params hBeta hDelta hGamma0 hGamma1 hAlphaSum
        a' b' hpop_ge2
      have hset : S'ᶜ = {s' : ℕ × ℕ | s'.1 + s'.2 ≠ a' + b' - 1} := by
        simp only [S', Set.compl_setOf]
        ext ⟨x, y⟩; simp only [Set.mem_setOf_eq]; omega
      rw [hset]; exact this
    exact kernelIter_concentrated_step _ _ _ S S' hSm hS'm (ih hn') hStep

/-- K^N(a,b) concentrates on {(1,0),(0,1)} where N = a+b-1 (NSD with β=δ=0). -/
lemma nsd_kernelIter_concentrated_on_absorbing
    (params : LVParams)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (kernelIter (lvKernel LVVariant.nonSelfDestructive params) (a + b - 1)) (a, b)
      ({(1, 0), (0, 1)} : Set (ℕ × ℕ))ᶜ = 0 := by
  have := nsd_kernelIter_totalPop params hBeta hDelta hGamma0 hGamma1 hAlphaSum
    a b ha hb (a + b - 1) le_rfl
  have h_pop1 : a + b - (a + b - 1) = 1 := by omega
  rw [h_pop1] at this
  apply le_antisymm _ zero_le
  calc (kernelIter (lvKernel LVVariant.nonSelfDestructive params) (a + b - 1)) (a, b)
          ({(1, 0), (0, 1)} : Set (ℕ × ℕ))ᶜ
      ≤ (kernelIter (lvKernel LVVariant.nonSelfDestructive params) (a + b - 1)) (a, b)
          {s : ℕ × ℕ | s.1 + s.2 ≠ 1} := by
        apply measure_mono; intro ⟨x, y⟩ h
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or, Prod.mk.injEq] at h
        simp only [Set.mem_setOf_eq]
        push_neg at h; obtain ⟨h1, h2⟩ := h
        intro hsum; have : x ≤ 1 := by omega
        interval_cases x <;> omega
    _ = 0 := this

/-- h is harmonic at all states with population m ≥ 2 under NSD with β=δ=0. -/
lemma nsd_harmonic_on_pop
    (params : LVParams) (h : PopState → ℝ)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' →
      params.beta * a' * h (a' + 1, b') + params.beta * b' * h (a', b' + 1) +
      (params.delta * a' + params.alpha1 * a' * b' +
        params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2)) * h (a' - 1, b') +
      (params.delta * b' + params.alpha0 * a' * b' +
        params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2)) * h (a', b' - 1) =
      lvTotalPropensity params (a', b') * h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    (m : ℕ) (hm : 2 ≤ m)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (x : PopState) (hx : x.1 + x.2 = m) :
    ∫ y, h y ∂(lvKernel .nonSelfDestructive params) x = h x := by
  obtain ⟨a', b'⟩ := x; simp only at hx
  -- Helper: for boundary (c, 0) with c ≥ 2, kernel = δ_{(c-1, 0)}
  have boundary_fst : ∀ c : ℕ, 2 ≤ c →
      (lvKernel .nonSelfDestructive params) (c, 0) = Measure.dirac (c - 1, 0) := by
    intro c hc
    have hc2 : (c : ℝ) ≥ 2 := by exact_mod_cast hc
    have hpos : 0 < params.gamma0 * (↑c * (↑c - 1) / 2) :=
      mul_pos hGamma0 (div_pos (mul_pos (by linarith) (by linarith)) (by norm_num))
    have hφ : lvTotalPropensity params (c, 0) ≠ 0 := by
      unfold lvTotalPropensity
      simp only [hBeta, hDelta, Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_add, zero_div]
      linarith
    have hφ_eq : lvTotalPropensity params (c, 0) = params.gamma0 * (↑c * (↑c - 1) / 2) := by
      simp [lvTotalPropensity, hBeta, hDelta]
    rw [lvKernel_nsd_apply params c 0 hφ, hφ_eq]
    simp only [hBeta, hDelta, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, add_zero, zero_add, zero_div]
    ext s
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_one, one_div, ← mul_assoc,
      ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) ENNReal.ofReal_ne_top,
      one_mul]
  -- Helper: for boundary (0, d) with d ≥ 2, kernel = δ_{(0, d-1)}
  have boundary_snd : ∀ d : ℕ, 2 ≤ d →
      (lvKernel .nonSelfDestructive params) (0, d) = Measure.dirac (0, d - 1) := by
    intro d hd
    have hd2 : (d : ℝ) ≥ 2 := by exact_mod_cast hd
    have hpos : 0 < params.gamma1 * (↑d * (↑d - 1) / 2) :=
      mul_pos hGamma1 (div_pos (mul_pos (by linarith) (by linarith)) (by norm_num))
    have hφ : lvTotalPropensity params (0, d) ≠ 0 := by
      unfold lvTotalPropensity
      simp only [hBeta, hDelta, Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_add, zero_div]
      linarith
    have hφ_eq : lvTotalPropensity params (0, d) = params.gamma1 * (↑d * (↑d - 1) / 2) := by
      simp [lvTotalPropensity, hBeta, hDelta]
    rw [lvKernel_nsd_apply params 0 d hφ, hφ_eq]
    simp only [hBeta, hDelta, Nat.cast_zero, mul_zero, zero_mul,
      ENNReal.ofReal_zero, zero_smul, add_zero, zero_add, zero_div]
    ext s
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_one, one_div, ← mul_assoc,
      ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) ENNReal.ofReal_ne_top,
      one_mul]
  rcases Nat.eq_zero_or_pos a' with rfl | ha'
  · -- a' = 0, b' ≥ 2
    have hb2 : 2 ≤ b' := by omega
    rw [boundary_snd b' hb2,
      integral_dirac' h _ (measurable_of_countable h).stronglyMeasurable,
      hBnd0, hBnd0]
  · rcases Nat.eq_zero_or_pos b' with rfl | hb'
    · -- b' ≥ 2, a' = 0
      have ha2 : 2 ≤ a' := by omega
      rw [boundary_fst a' ha2,
        integral_dirac' h _ (measurable_of_countable h).stronglyMeasurable,
        hBnd1 (a' - 1) (by omega), hBnd1 a' ha']
    · -- Interior: a' > 0, b' > 0
      by_cases hφ : lvTotalPropensity params (a', b') = 0
      · -- Propensity = 0: kernel is δ_{(a',b')}, trivially harmonic
        simp only [lvKernel, Kernel.ofFunOfCountable, Kernel.coe_mk, hφ, ↓reduceDIte]
        exact integral_dirac' h _ (measurable_of_countable h).stronglyMeasurable
      · exact lvKernel_nsd_harmonic_integral params h a' b' ha' hb' hφ (hHarm a' b' ha' hb')

private lemma nat_cast_mul_pred_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (Nat.one_le_cast.mpr hn))

/-- Bounded version of concentrated harmonic integral:
    conditions only for k < N suffice to prove result at step N. -/
lemma kernelIter_harmonic_integral_at
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (h : α → ℝ) (s₀ : α) (N : ℕ) (S : ℕ → Set α)
    (hConc : ∀ k, k < N → (kernelIter K k) s₀ (S k)ᶜ = 0)
    (hHarm : ∀ k, k < N → ∀ x ∈ S k, ∫ y, h y ∂K x = h x)
    (hInt : ∀ k, k ≤ N → Integrable h ((kernelIter K k) s₀)) :
    ∫ x, h x ∂(kernelIter K N) s₀ = h s₀ := by
  induction N with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    exact integral_dirac' h s₀ (measurable_of_countable h).stronglyMeasurable
  | succ n ih =>
    have ih' := ih (fun k hk => hConc k (Nat.lt_succ_of_lt hk))
      (fun k hk => hHarm k (Nat.lt_succ_of_lt hk))
      (fun k hk => hInt k (Nat.le_succ_of_le hk))
    rw [kernelIter_succ, Kernel.integral_comp (hInt (n + 1) le_rfl)]
    have hae : (fun x => ∫ y, h y ∂K x) =ᵐ[(kernelIter K n) s₀] h := by
      rw [Filter.EventuallyEq, ae_iff]
      apply le_antisymm _ zero_le
      calc (kernelIter K n s₀) {x | (fun x => ∫ y, h y ∂K x) x ≠ h x}
          ≤ (kernelIter K n s₀) (S n)ᶜ := by
            apply measure_mono; intro x hx hxS; exact hx (hHarm n (Nat.lt_succ_self n) x hxS)
        _ = 0 := hConc n (Nat.lt_succ_self n)
    rw [integral_congr_ae hae]; exact ih'

/-- Superharmonic variant: if `∫ h ∂K x ≤ h x` a.e. on each concentration set,
    then the iterated kernel integral is ≤ h(s₀). -/
lemma kernelIter_superharmonic_integral_le_at
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (h : α → ℝ) (s₀ : α) (N : ℕ) (S : ℕ → Set α)
    (hConc : ∀ k, k < N → (kernelIter K k) s₀ (S k)ᶜ = 0)
    (hSuper : ∀ k, k < N → ∀ x ∈ S k, ∫ y, h y ∂K x ≤ h x)
    (hInt : ∀ k, k ≤ N → Integrable h ((kernelIter K k) s₀)) :
    ∫ x, h x ∂(kernelIter K N) s₀ ≤ h s₀ := by
  induction N with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    exact le_of_eq (integral_dirac' h s₀ (measurable_of_countable h).stronglyMeasurable)
  | succ n ih =>
    have ih' := ih (fun k hk => hConc k (Nat.lt_succ_of_lt hk))
      (fun k hk => hSuper k (Nat.lt_succ_of_lt hk))
      (fun k hk => hInt k (Nat.le_succ_of_le hk))
    rw [kernelIter_succ, Kernel.integral_comp (hInt (n + 1) le_rfl)]
    have hae : (fun x => ∫ y, h y ∂K x) ≤ᵐ[(kernelIter K n) s₀] h := by
      rw [Filter.EventuallyLE, ae_iff]
      apply le_antisymm _ zero_le
      calc (kernelIter K n s₀) {x | ¬ (fun x => ∫ y, h y ∂K x) x ≤ h x}
          ≤ (kernelIter K n s₀) (S n)ᶜ := by
            apply measure_mono; intro x hx hxS
            exact hx (hSuper n (Nat.lt_succ_self n) x hxS)
        _ = 0 := hConc n (Nat.lt_succ_self n)
    calc ∫ x, (fun x => ∫ y, h y ∂K x) x ∂(kernelIter K n) s₀
        ≤ ∫ x, h x ∂(kernelIter K n) s₀ := by
          exact integral_mono_ae
            ((hInt (n + 1) le_rfl).integral_comp)
            (hInt n (Nat.le_succ n)) hae
      _ ≤ h s₀ := ih'

/-- With β=δ=0 and γ₀>0, the SD kernel at state (j,0) with j≥2 is a Dirac at (j-2,0). -/
lemma sd_kernel_measure_at_consensus0
    (params : LVParams) (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0)
    [IsMarkovKernel (lvKernel .selfDestructive params)] (j : ℕ) (hj : 2 ≤ j) :
    (lvKernel .selfDestructive params) (j, 0) = Measure.dirac (j - 2, 0) := by
  have hj_pos : 0 < j := by omega
  have hj1 : (1 : ℝ) < (j : ℝ) := by exact_mod_cast show 1 < j by omega
  have hga : 0 < (j : ℝ) * ((j : ℝ) - 1) / 2 :=
    div_pos (mul_pos (Nat.cast_pos.mpr hj_pos) (sub_pos.mpr hj1)) (by norm_num)
  have hφ : lvTotalPropensity params ((j : ℕ), 0) ≠ 0 := by
    intro heq
    simp only [lvTotalPropensity, hBeta, hDelta, zero_mul, add_zero, Nat.cast_zero,
      mul_zero, zero_add] at heq
    linarith [mul_pos hGamma0 hga]
  have hφ_val : lvTotalPropensity params ((j : ℕ), 0) =
      params.gamma0 * ((j : ℝ) * ((j : ℝ) - 1) / 2) := by
    simp [lvTotalPropensity, hBeta, hDelta]
  have hφ_pos : 0 < lvTotalPropensity params ((j : ℕ), 0) := by
    rw [hφ_val]; exact mul_pos hGamma0 hga
  rw [lvKernel_sd_apply params j 0 hφ]; ext S _
  simp only [Measure.smul_apply, smul_eq_mul, hBeta, hDelta, Nat.cast_zero, zero_mul,
    mul_zero, ENNReal.ofReal_zero, zero_smul, add_zero, zero_add, zero_div]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg one_pos.le hφ_pos.le), hφ_val,
    div_mul_cancel₀ _ (ne_of_gt (mul_pos hGamma0 hga)), ENNReal.ofReal_one, one_mul]

/-- With β=δ=0 and γ₁>0, the SD kernel at state (0,j) with j≥2 is a Dirac at (0,j-2). -/
lemma sd_kernel_measure_at_consensus1
    (params : LVParams) (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma1 : 0 < params.gamma1)
    [IsMarkovKernel (lvKernel .selfDestructive params)] (j : ℕ) (hj : 2 ≤ j) :
    (lvKernel .selfDestructive params) (0, j) = Measure.dirac (0, j - 2) := by
  have hj_pos : 0 < j := by omega
  have hj1 : (1 : ℝ) < (j : ℝ) := by exact_mod_cast show 1 < j by omega
  have hgb : 0 < (j : ℝ) * ((j : ℝ) - 1) / 2 :=
    div_pos (mul_pos (Nat.cast_pos.mpr hj_pos) (sub_pos.mpr hj1)) (by norm_num)
  have hφ : lvTotalPropensity params (0, (j : ℕ)) ≠ 0 := by
    intro heq
    simp only [lvTotalPropensity, hBeta, hDelta, zero_mul, add_zero, Nat.cast_zero,
      mul_zero, zero_add] at heq
    linarith [mul_pos hGamma1 hgb]
  have hφ_val : lvTotalPropensity params (0, (j : ℕ)) =
      params.gamma1 * ((j : ℝ) * ((j : ℝ) - 1) / 2) := by
    simp [lvTotalPropensity, hBeta, hDelta]
  have hφ_pos : 0 < lvTotalPropensity params (0, (j : ℕ)) := by
    rw [hφ_val]; exact mul_pos hGamma1 hgb
  rw [lvKernel_sd_apply params 0 j hφ]; ext S _
  simp only [Measure.smul_apply, smul_eq_mul, hBeta, hDelta, Nat.cast_zero, zero_mul,
    mul_zero, ENNReal.ofReal_zero, zero_smul, add_zero, zero_add, zero_div]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg one_pos.le hφ_pos.le), hφ_val,
    div_mul_cancel₀ _ (ne_of_gt (mul_pos hGamma1 hgb)), ENNReal.ofReal_one, one_mul]

/-- For the SD kernel with β=δ=0, any bounded function h satisfying the harmonicity
    equation has ∫ h dK(x) = h(x) for all x with odd total population ≥ 1. -/
lemma sd_harmonic_on_odd_pop
    (params : LVParams) (h : PopState → ℝ)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' → Odd (a' + b') →
      params.beta * a' * h (a' + 1, b') + params.beta * b' * h (a', b' + 1) +
      params.delta * a' * h (a' - 1, b') + params.delta * b' * h (a', b' - 1) +
      (params.alpha0 + params.alpha1) * a' * b' * h (a' - 1, b' - 1) +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2) * h (a' - 2, b') +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2) * h (a', b' - 2) =
      lvTotalPropensity params (a', b') * h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    [IsMarkovKernel (lvKernel .selfDestructive params)]
    (m : ℕ) (hm : Odd m) (hm1 : 1 ≤ m) :
    ∀ x : PopState, x.1 + x.2 = m →
      ∫ y, h y ∂(lvKernel .selfDestructive params) x = h x := by
  intro ⟨a', b'⟩ hab; simp only at hab
  by_cases ha0 : a' = 0
  · subst ha0; simp only [zero_add] at hab
    by_cases hb1 : b' = 1
    · subst hb1
      rw [lvKernel_apply_zero_propensity _ _ _
        (by simp [lvTotalPropensity, hBeta, hDelta])]
      exact integral_dirac _ (0, 1)
    · have hb2 : 2 ≤ b' := by omega
      rw [sd_kernel_measure_at_consensus1 params hBeta hDelta hGamma1 b' hb2]
      rw [integral_dirac _ (0, b' - 2), hBnd0, hBnd0]
  · by_cases hb0 : b' = 0
    · subst hb0; simp only [add_zero] at hab
      by_cases ha1 : a' = 1
      · subst ha1
        rw [lvKernel_apply_zero_propensity _ _ _
          (by simp [lvTotalPropensity, hBeta, hDelta])]
        exact integral_dirac _ (1, 0)
      · have ha2 : 2 ≤ a' := by omega
        have ha_odd : Odd a' := hab ▸ hm
        rw [sd_kernel_measure_at_consensus0 params hBeta hDelta hGamma0 a' ha2]
        rw [integral_dirac _ (a' - 2, 0)]
        rw [hBnd1 (a' - 2) (by obtain ⟨k, hk⟩ := ha_odd; omega),
            hBnd1 a' (by omega)]
    · have ha : 0 < a' := Nat.pos_of_ne_zero ha0
      have hb : 0 < b' := Nat.pos_of_ne_zero hb0
      have hOdd : Odd (a' + b') := hab ▸ hm
      have hφ : lvTotalPropensity params (a', b') ≠ 0 := by
        intro heq
        simp only [lvTotalPropensity, hBeta, hDelta, zero_mul, add_zero, zero_add] at heq
        have ha' : (0 : ℝ) < (a' : ℝ) := Nat.cast_pos.mpr ha
        have hb' : (0 : ℝ) < (b' : ℝ) := Nat.cast_pos.mpr hb
        have : a' ≥ 2 ∨ b' ≥ 2 := by obtain ⟨k, hk⟩ := hOdd; omega
        rcases this with ha2 | hb2
        · have h1lt : (1 : ℝ) < (a' : ℝ) := by exact_mod_cast show 1 < a' by omega
          nlinarith [mul_pos hGamma0 (div_pos (mul_pos ha' (sub_pos.mpr h1lt))
              (by norm_num : (0:ℝ) < 2)),
            mul_nonneg (add_nonneg params.alpha0_nonneg params.alpha1_nonneg)
              (mul_nonneg ha'.le hb'.le),
            mul_nonneg params.gamma1_nonneg
              (div_nonneg (nat_cast_mul_pred_nonneg b') (by norm_num : (0:ℝ) ≤ 2))]
        · have h1lt : (1 : ℝ) < (b' : ℝ) := by exact_mod_cast show 1 < b' by omega
          nlinarith [mul_pos hGamma1 (div_pos (mul_pos hb' (sub_pos.mpr h1lt))
              (by norm_num : (0:ℝ) < 2)),
            mul_nonneg (add_nonneg params.alpha0_nonneg params.alpha1_nonneg)
              (mul_nonneg ha'.le hb'.le),
            mul_nonneg params.gamma0_nonneg
              (div_nonneg (nat_cast_mul_pred_nonneg a') (by norm_num : (0:ℝ) ≤ 2))]
      exact lvKernel_sd_harmonic_integral params h a' b' ha hb hφ
        (hHarm a' b' ha hb hOdd)

/-- The kernel computation: K^N(a,b)({(1,0)}) = ENNReal.ofReal(h(a,b)) for any
    bounded harmonic function h with boundary values h(a',0)=1 and h(0,b')=0. -/
lemma sd_kernelIter_value
    (params : LVParams)
    (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hOdd : Odd (a + b))
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1)
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' → Odd (a' + b') →
      params.beta * a' * h (a' + 1, b') + params.beta * b' * h (a', b' + 1) +
      params.delta * a' * h (a' - 1, b') + params.delta * b' * h (a', b' - 1) +
      (params.alpha0 + params.alpha1) * a' * b' * h (a' - 1, b' - 1) +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2) * h (a' - 2, b') +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2) * h (a', b' - 2) =
      lvTotalPropensity params (a', b') * h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    let N := (a + b - 1) / 2
    (kernelIter (lvKernel LVVariant.selfDestructive params) N) (a, b) {(1, 0)} =
      ENNReal.ofReal (h (a, b)) := by
  intro N
  let S : ℕ → Set PopState := fun n => {s | s.1 + s.2 = a + b - 2 * n}
  have hConc : ∀ k, k < N →
      (kernelIter (lvKernel .selfDestructive params) k) (a, b) (S k)ᶜ = 0 :=
    fun k hk => sd_kernelIter_totalPop params hBeta hDelta hGamma0 hGamma1
      hAlphaSum a b hOdd k (by omega)
  have hHarmS : ∀ k, k < N → ∀ x ∈ S k,
      ∫ y, h y ∂(lvKernel .selfDestructive params) x = h x := by
    intro k hk x hx
    simp only [S, Set.mem_setOf_eq] at hx
    apply sd_harmonic_on_odd_pop params h hBeta hDelta hGamma0 hGamma1 hHarm hBnd1 hBnd0
      (a + b - 2 * k)
    · obtain ⟨j, hj⟩ := hOdd; exact ⟨j - k, by omega⟩
    · omega
    · exact hx
  have hInteg : ∀ k, k ≤ N →
      Integrable h ((kernelIter (lvKernel .selfDestructive params) k) (a, b)) := by
    intro k _
    haveI : IsProbabilityMeasure
        ((kernelIter (lvKernel .selfDestructive params) k) (a, b)) :=
      (kernelIter_isMarkov k).isProbabilityMeasure (a, b)
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(hBound x).1], (hBound x).2⟩
  have h_int := kernelIter_harmonic_integral_at _ h (a, b) N S hConc hHarmS hInteg
  have h_conc_N := sd_kernelIter_concentrated_on_absorbing params hBeta hDelta hGamma0
    hGamma1 hAlphaSum a b ha hb hOdd
  haveI : IsProbabilityMeasure
      ((kernelIter (lvKernel .selfDestructive params) N) (a, b)) :=
    (kernelIter_isMarkov N).isProbabilityMeasure (a, b)
  have h_meas := integral_eq_measure_of_concentrated
    ((kernelIter (lvKernel .selfDestructive params) N) (a, b))
    h (1, 0) (0, 1) (by simp) h_conc_N (hBnd1 1 one_pos) (hBnd0 1)
  have h_eq : ((kernelIter (lvKernel .selfDestructive params) N) (a, b)
      {(1, 0)}).toReal = h (a, b) := by
    rw [← h_meas, h_int]
  rw [← h_eq, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

/-! ### Path-level helpers for consensus proofs -/

/-- At a hittingAfter time that is finite, the process is in the target set. -/
lemma at_hitting_time' {Ω β : Type*} {u : ℕ → Ω → β} {s : Set β}
    {n t : ℕ} {ω : Ω}
    (h : hittingAfter u s n ω = ↑t) : u t ω ∈ s := by
  obtain ⟨j, hjIcc, hjs⟩ := hittingAfter_le_iff.mp (le_of_eq h)
  have hjt : j ≤ t := (Set.mem_Icc.mp hjIcc).2
  have hle_j := hittingAfter_le_iff.mpr
    ⟨j, Set.mem_Icc.mpr ⟨(Set.mem_Icc.mp hjIcc).1, le_refl j⟩, hjs⟩
  rw [h] at hle_j
  have htj : t ≤ j := WithTop.coe_le_coe.mp hle_j
  rwa [← le_antisymm hjt htj]

lemma reachedConsensus_at_consensusTime' (ω : ℕ → PopState) (t : ℕ)
    (h : consensusTime ω = ↑t) : reachedConsensus (ω t) :=
  (at_hitting_time' h : popCoord t ω ∈ {s : PopState | reachedConsensus s})

lemma consensusTime_le_of_reached' (ω : ℕ → PopState) (N : ℕ)
    (h : reachedConsensus (ω N)) : consensusTime ω ≤ ↑N :=
  hittingAfter_le_iff.mpr ⟨N, Set.mem_Icc.mpr ⟨Nat.zero_le N, le_refl N⟩, h⟩

/-- If consensus is never reached, it is also never reached after dropping
    the first coordinate. -/
lemma consensusTime_pathShift_one_eq_top
    (ω : ℕ → PopState)
    (hct : consensusTime ω = ⊤) :
    consensusTime (pathShift 1 ω) = ⊤ := by
  cases hs : consensusTime (pathShift 1 ω) with
  | top => rfl
  | coe t =>
      exfalso
      have hreach :
          reachedConsensus (ω (t + 1)) := by
        have := reachedConsensus_at_consensusTime'
          (pathShift 1 ω) t hs
        simpa [pathShift, Nat.add_comm] using this
      have hle := consensusTime_le_of_reached' ω (t + 1) hreach
      rw [hct] at hle
      exact (not_le_of_gt (WithTop.coe_lt_top (t + 1))) hle

/-- If the first consensus time is `t+1`, then after dropping coordinate zero
    the first consensus time is `t`. -/
lemma consensusTime_pathShift_one_eq_succ
    (ω : ℕ → PopState) (t : ℕ)
    (hct : consensusTime ω = ↑(t + 1)) :
    consensusTime (pathShift 1 ω) = ↑t := by
  rw [consensusTime_eq_coe_iff]
  constructor
  · have hreach :=
      (consensusTime_eq_coe_iff ω (t + 1)).mp hct |>.1
    simpa [pathShift, Nat.add_comm] using hreach
  · intro j hj
    have hnot :=
      (consensusTime_eq_coe_iff ω (t + 1)).mp hct |>.2 (j + 1) (by omega)
    simpa [pathShift, Nat.add_comm] using hnot

lemma propagate_zero_fst (ω : ℕ → PopState) (t N : ℕ) (htN : t ≤ N)
    (hNR : ∀ s, t ≤ s → s < N → (ω s).1 = 0 → (ω (s + 1)).1 = 0)
    (h0 : (ω t).1 = 0) : (ω N).1 = 0 := by
  suffices ∀ k, t + k ≤ N → (ω (t + k)).1 = 0 by
    have := this (N - t) (by omega); rwa [Nat.add_sub_cancel' htN] at this
  intro k; induction k with
  | zero => intro; simpa
  | succ n ih => intro hle; exact hNR (t + n) (by omega) (by omega) (ih (by omega))

lemma propagate_zero_snd (ω : ℕ → PopState) (t N : ℕ) (htN : t ≤ N)
    (hNR : ∀ s, t ≤ s → s < N → (ω s).2 = 0 → (ω (s + 1)).2 = 0)
    (h0 : (ω t).2 = 0) : (ω N).2 = 0 := by
  suffices ∀ k, t + k ≤ N → (ω (t + k)).2 = 0 by
    have := this (N - t) (by omega); rwa [Nat.add_sub_cancel' htN] at this
  intro k; induction k with
  | zero => intro; simpa
  | succ n ih => intro hle; exact hNR (t + n) (by omega) (by omega) (ih (by omega))

/-- On a "nice" path (concentrated + no-revival), MCE ↔ ω(N)=(1,0). -/
lemma mce_iff_omega_N (a b : ℕ) (hba : b < a) (ω : ℕ → PopState) (N : ℕ)
    (hConc : ω N ∈ ({(1, 0), (0, 1)} : Set PopState))
    (hNR0 : ∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0)
    (hNR1 : ∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0) :
    majorityConsensusEvent (a, b) ω ↔ ω N = (1, 0) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hConc
  constructor
  · intro hMCE; unfold majorityConsensusEvent at hMCE
    rcases hct : consensusTime ω with _ | t
    · simp only [hct] at hMCE
    · simp only [hct] at hMCE
      rcases hMCE with ⟨_, _, ht2⟩ | ⟨hnsm, _⟩
      · have hrc : reachedConsensus (ω N) := by
          rcases hConc with h | h <;> rw [h] <;> simp [reachedConsensus]
        have htN : t ≤ N := by
          have h1 := consensusTime_le_of_reached' ω N hrc
          rw [hct] at h1; exact WithTop.coe_le_coe.mp h1
        have := propagate_zero_snd ω t N htN (fun s hs1 hs2 => hNR1 s hs2) ht2
        rcases hConc with h | h; exact h
        exfalso; rw [h] at this; simp at this
      · exact absurd (show species0Majority (a, b) from Nat.le_of_lt hba) hnsm
  · intro hωN
    have hle := consensusTime_le_of_reached' ω N (by rw [hωN]; simp [reachedConsensus])
    obtain ⟨t, hct, htN⟩ := WithTop.le_coe_iff.mp hle
    have hcons := reachedConsensus_at_consensusTime' ω t hct
    have ht1 : 0 < (ω t).1 := by
      by_contra hp; push_neg at hp
      have := propagate_zero_fst ω t N htN
        (fun s hs1 hs2 => hNR0 s hs2) (Nat.eq_zero_of_le_zero hp)
      rw [hωN] at this; simp at this
    have ht2 : (ω t).2 = 0 := by
      rcases hcons with h | h; exfalso; omega; exact h
    unfold majorityConsensusEvent; simp only [hct]
    left; exact ⟨Nat.le_of_lt hba, ht1, ht2⟩

/-- On the diagonal `(m,m)`, MCE is equivalent to `ω(N) = (1,0)` on nice paths,
    because the tie-breaking convention designates species `0` as the majority. -/
lemma mce_iff_omega_N_diag (m : ℕ) (ω : ℕ → PopState) (N : ℕ)
    (hConc : ω N ∈ ({(1, 0), (0, 1)} : Set PopState))
    (hNR0 : ∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0)
    (hNR1 : ∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0) :
    majorityConsensusEvent (m, m) ω ↔ ω N = (1, 0) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hConc
  constructor
  · intro hMCE; unfold majorityConsensusEvent at hMCE
    rcases hct : consensusTime ω with _ | t
    · simp only [hct] at hMCE
    · simp only [hct] at hMCE
      rcases hMCE with ⟨_, _, h2⟩ | ⟨hnmaj, _⟩
      · have hrc : reachedConsensus (ω N) := by
          rcases hConc with h | h <;> rw [h] <;> simp [reachedConsensus]
        have htN : t ≤ N := by
          have h := consensusTime_le_of_reached' ω N hrc
          rw [hct] at h; exact WithTop.coe_le_coe.mp h
        have := propagate_zero_snd ω t N htN (fun s hs1 hs2 => hNR1 s hs2) h2
        rcases hConc with h | h
        · exact h
        · exfalso; rw [h] at this; simp at this
      · exact absurd (show species0Majority (m, m) from by simp [species0Majority]) hnmaj
  · intro hωN
    have hle := consensusTime_le_of_reached' ω N (by rw [hωN]; simp [reachedConsensus])
    obtain ⟨t, hct, htN⟩ := WithTop.le_coe_iff.mp hle
    have hcons := reachedConsensus_at_consensusTime' ω t hct
    have ht1 : 0 < (ω t).1 := by
      by_contra hp; push_neg at hp
      have := propagate_zero_fst ω t N htN
        (fun s hs1 hs2 => hNR0 s hs2) (Nat.eq_zero_of_le_zero hp)
      rw [hωN] at this; simp at this
    have ht2 : (ω t).2 = 0 := by
      rcases hcons with h | h; exact absurd h (by omega); exact h
    unfold majorityConsensusEvent; simp only [hct]
    exact Or.inl ⟨show species0Majority (m, m) from by simp [species0Majority], ht1, ht2⟩

/-- NSD kernel iteration value: K^N({(1,0)}) = h(a,b) where N = a+b-1. -/
lemma nsd_kernelIter_value
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1)
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' →
      params.beta * a' * h (a' + 1, b') + params.beta * b' * h (a', b' + 1) +
      (params.delta * a' + params.alpha1 * a' * b' +
        params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2)) * h (a' - 1, b') +
      (params.delta * b' + params.alpha0 * a' * b' +
        params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2)) * h (a', b' - 1) =
      lvTotalPropensity params (a', b') * h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    let N := a + b - 1
    (kernelIter (lvKernel LVVariant.nonSelfDestructive params) N) (a, b) {(1, 0)} =
      ENNReal.ofReal (h (a, b)) := by
  intro N
  let S : ℕ → Set PopState := fun n => {s | s.1 + s.2 = a + b - n}
  have hConc : ∀ k, k < N →
      (kernelIter (lvKernel .nonSelfDestructive params) k) (a, b) (S k)ᶜ = 0 :=
    fun k hk => by
      convert nsd_kernelIter_totalPop params hBeta hDelta hGamma0 hGamma1 hAlphaSum
        a b ha hb k (by omega) using 2
      ext s
      simp [S]
  have hHarmS : ∀ k, k < N → ∀ x ∈ S k,
      ∫ y, h y ∂(lvKernel .nonSelfDestructive params) x = h x := by
    intro k hk x hx
    simp only [S, Set.mem_setOf_eq] at hx
    exact nsd_harmonic_on_pop params h hBeta hDelta hGamma0 hGamma1 hHarm hBnd1 hBnd0
      (a + b - k) (by omega) x hx
  have hInteg : ∀ k, k ≤ N →
      Integrable h ((kernelIter (lvKernel .nonSelfDestructive params) k) (a, b)) := by
    intro k _
    haveI : IsProbabilityMeasure
        ((kernelIter (lvKernel .nonSelfDestructive params) k) (a, b)) :=
      (kernelIter_isMarkov k).isProbabilityMeasure (a, b)
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(hBound x).1], (hBound x).2⟩
  have h_int := kernelIter_harmonic_integral_at _ h (a, b) N S hConc hHarmS hInteg
  have h_conc_N := nsd_kernelIter_concentrated_on_absorbing params hBeta hDelta
    hGamma0 hGamma1 hAlphaSum a b ha hb
  haveI : IsProbabilityMeasure
      ((kernelIter (lvKernel .nonSelfDestructive params) N) (a, b)) :=
    (kernelIter_isMarkov N).isProbabilityMeasure (a, b)
  -- Convert complement form for integral_eq_measure_of_concentrated
  have h_conc_N' : ((kernelIter (lvKernel .nonSelfDestructive params) N) (a, b))
      {s : ℕ × ℕ | s ≠ (1, 0) ∧ s ≠ (0, 1)} = 0 := by
    apply le_antisymm _ zero_le
    calc _ ≤ ((kernelIter (lvKernel .nonSelfDestructive params) N) (a, b))
            ({(1, 0), (0, 1)} : Set (ℕ × ℕ))ᶜ := by
          apply measure_mono; intro ⟨x, y⟩ hs
          simp only [Set.mem_setOf_eq, Prod.mk.injEq, ne_eq] at hs
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
            Prod.mk.injEq, not_or, not_and]
          exact ⟨fun h1 h2 => hs.1 ⟨h1, h2⟩, fun h1 h2 => hs.2 ⟨h1, h2⟩⟩
      _ = 0 := h_conc_N
  have h_meas := integral_eq_measure_of_concentrated
    ((kernelIter (lvKernel .nonSelfDestructive params) N) (a, b))
    h (1, 0) (0, 1) (by simp) h_conc_N' (hBnd1 1 one_pos) (hBnd0 1)
  have h_eq : ((kernelIter (lvKernel .nonSelfDestructive params) N) (a, b)
      {(1, 0)}).toReal = h (a, b) := by
    rw [← h_meas, h_int]
  rw [← h_eq, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

/-- Path-level no-revival for species 1 under NSD dynamics:
    P[ω(s).2 = 0 ∧ ω(s+1).2 ≠ 0] = 0. -/
lemma nsd_path_no_revival_species1
    (params : LVParams) (s₀ : PopState) (s : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s₀
      {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} = 0 := by
  let K := lvKernel LVVariant.nonSelfDestructive params
  let g : PopState → ℝ≥0∞ := fun x => if x.2 = 0 then 1 else 0
  let φ : PopState → ℝ≥0∞ := fun y => if y.2 ≠ 0 then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas : MeasurableSet {ω' : ℕ → PopState | (ω' s).2 = 0 ∧ (ω' (s + 1)).2 ≠ 0} :=
    .inter ((measurable_pi_apply s).snd (measurableSet_singleton 0))
      ((measurable_pi_apply (s+1)).snd (measurableSet_singleton 0).compl)
  unfold lvPathMeasure
  have hconv : (homogeneousPathMeasure (Measure.dirac s₀) K)
      {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} =
      ∫⁻ ω', g (ω' s) * φ (ω' (s + 1)) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) := by
    rw [← lintegral_indicator_one hmeas]; congr 1; ext ω'
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]; split_ifs <;> simp_all
  rw [hconv, homogeneousPathMeasure_joint_lintegral K s₀ s g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {y | y.2 ≠ 0} := by
    intro x; have : φ = Set.indicator {y : PopState | y.2 ≠ 0} 1 := by
      ext y; simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this]; exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]; simp_rw [show ∀ x, g x * K x {y | y.2 ≠ 0} = 0 from fun x => by
    simp only [g]; split_ifs with h
    · simp only [one_mul]; exact nsd_kernel_species1_dead_absorbing params x h
    · simp]; exact lintegral_zero

/-- Path-level no-revival for species 0 under NSD dynamics:
    P[ω(s).1 = 0 ∧ ω(s+1).1 ≠ 0] = 0. -/
lemma nsd_path_no_revival_species0
    (params : LVParams) (s₀ : PopState) (s : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s₀
      {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} = 0 := by
  let K := lvKernel LVVariant.nonSelfDestructive params
  let g : PopState → ℝ≥0∞ := fun x => if x.1 = 0 then 1 else 0
  let φ : PopState → ℝ≥0∞ := fun y => if y.1 ≠ 0 then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas : MeasurableSet {ω' : ℕ → PopState | (ω' s).1 = 0 ∧ (ω' (s + 1)).1 ≠ 0} :=
    .inter ((measurable_pi_apply s).fst (measurableSet_singleton 0))
      ((measurable_pi_apply (s+1)).fst (measurableSet_singleton 0).compl)
  unfold lvPathMeasure
  have hconv : (homogeneousPathMeasure (Measure.dirac s₀) K)
      {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} =
      ∫⁻ ω', g (ω' s) * φ (ω' (s + 1)) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) := by
    rw [← lintegral_indicator_one hmeas]; congr 1; ext ω'
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]; split_ifs <;> simp_all
  rw [hconv, homogeneousPathMeasure_joint_lintegral K s₀ s g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {y | y.1 ≠ 0} := by
    intro x; have : φ = Set.indicator {y : PopState | y.1 ≠ 0} 1 := by
      ext y; simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this]; exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]; simp_rw [show ∀ x, g x * K x {y | y.1 ≠ 0} = 0 from fun x => by
    simp only [g]; split_ifs with h
    · simp only [one_mul]; exact nsd_kernel_species0_dead_absorbing params x h
    · simp]; exact lintegral_zero

/-- Multi-step no-revival for species 0 under NSD:
    P[ω(t).1 = 0 ∧ ω(t+j).1 ≠ 0] = 0 for all j. -/
lemma nsd_path_species0_dead_forward
    (params : LVParams) (s₀ : PopState) (t j : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s₀
      {ω | (ω t).1 = 0 ∧ (ω (t + j)).1 ≠ 0} = 0 := by
  induction j with
  | zero =>
    convert measure_empty (μ := lvPathMeasure .nonSelfDestructive params s₀)
    ext ω; simp [Set.mem_setOf_eq]
  | succ n ih =>
    apply le_antisymm _ zero_le
    have hsub : (({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + (n + 1))).1 ≠ 0}) :
        Set (ℕ → PopState)) ⊆
        {ω | (ω t).1 = 0 ∧ (ω (t + n)).1 ≠ 0} ∪
        {ω | (ω (t + n)).1 = 0 ∧ (ω (t + n + 1)).1 ≠ 0} := by
      intro ω ⟨h1, h2⟩
      by_cases h : (ω (t + n)).1 = 0
      · right; exact ⟨h, by rwa [show t + (n + 1) = t + n + 1 from by omega] at h2⟩
      · left; exact ⟨h1, h⟩
    have h1 := measure_mono (μ := lvPathMeasure .nonSelfDestructive params s₀) hsub
    have h2 := measure_union_le (μ := lvPathMeasure .nonSelfDestructive params s₀)
      {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + n)).1 ≠ 0}
      {ω : ℕ → PopState | (ω (t + n)).1 = 0 ∧ (ω (t + n + 1)).1 ≠ 0}
    rw [ih, nsd_path_no_revival_species0 params s₀ (t + n), add_zero] at h2
    exact le_trans (le_trans h1 h2) (le_refl 0)

/-- Multi-step no-revival for species 1 under NSD:
    P[ω(t).2 = 0 ∧ ω(t+j).2 ≠ 0] = 0 for all j. -/
lemma nsd_path_species1_dead_forward
    (params : LVParams) (s₀ : PopState) (t j : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params s₀
      {ω | (ω t).2 = 0 ∧ (ω (t + j)).2 ≠ 0} = 0 := by
  induction j with
  | zero =>
    convert measure_empty (μ := lvPathMeasure .nonSelfDestructive params s₀)
    ext ω; simp [Set.mem_setOf_eq]
  | succ n ih =>
    apply le_antisymm _ zero_le
    have hsub : (({ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + (n + 1))).2 ≠ 0}) :
        Set (ℕ → PopState)) ⊆
        {ω | (ω t).2 = 0 ∧ (ω (t + n)).2 ≠ 0} ∪
        {ω | (ω (t + n)).2 = 0 ∧ (ω (t + n + 1)).2 ≠ 0} := by
      intro ω ⟨h1, h2⟩
      by_cases h : (ω (t + n)).2 = 0
      · right; exact ⟨h, by rwa [show t + (n + 1) = t + n + 1 from by omega] at h2⟩
      · left; exact ⟨h1, h⟩
    have h1 := measure_mono (μ := lvPathMeasure .nonSelfDestructive params s₀) hsub
    have h2 := measure_union_le (μ := lvPathMeasure .nonSelfDestructive params s₀)
      {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + n)).2 ≠ 0}
      {ω : ℕ → PopState | (ω (t + n)).2 = 0 ∧ (ω (t + n + 1)).2 ≠ 0}
    rw [ih, nsd_path_no_revival_species1 params s₀ (t + n), add_zero] at h2
    exact le_trans (le_trans h1 h2) (le_refl 0)

/-- Consensus = harmonic function for the NSD LV chain with β=δ=0.
    If h is [0,1]-valued and harmonic, with h(a,0)=1 and h(0,b)=0,
    then P(majority wins | X₀=(a,b)) = h(a,b). -/
lemma consensus_eq_harmonic_nsd
    (params : LVParams)
    (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hba : b < a)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1)
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' →
      params.beta * a' * h (a' + 1, b') + params.beta * b' * h (a', b' + 1) +
      (params.delta * a' + params.alpha1 * a' * b' +
        params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2)) * h (a' - 1, b') +
      (params.delta * b' + params.alpha0 * a' * b' +
        params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2)) * h (a', b' - 1) =
      lvTotalPropensity params (a', b') * h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)] :
    majorityConsensusProb LVVariant.nonSelfDestructive params (a, b) =
      ENNReal.ofReal (h (a, b)) := by
  let N := a + b - 1
  have hKernel := nsd_kernelIter_value params h a b ha hb hBeta hDelta
    hGamma0 hGamma1 hAlphaSum hBound hHarm hBnd1 hBnd0
  have hTarget : lvPathMeasure .nonSelfDestructive params (a, b) {ω | ω N = (1, 0)} =
      ENNReal.ofReal (h (a, b)) := by
    have : {ω : ℕ → PopState | ω N = (1, 0)} = (fun ω => ω N) ⁻¹' {(1, 0)} := by ext; simp
    unfold lvPathMeasure; rw [this,
      ← Measure.map_apply (measurable_pi_apply N) (by measurability),
      homogeneousPathMeasure_dirac_marginal, hKernel]
  suffices hmce :
    lvPathMeasure .nonSelfDestructive params (a, b) {ω | majorityConsensusEvent (a, b) ω} =
    lvPathMeasure .nonSelfDestructive params (a, b) {ω | ω N = (1, 0)} by
    unfold majorityConsensusProb; rw [hmce, hTarget]
  set P := lvPathMeasure .nonSelfDestructive params (a, b) with hP_def
  -- Null sets
  have hNull0 : ∀ s, P {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} = 0 :=
    fun s => nsd_path_no_revival_species0 params (a, b) s
  have hNull1 : ∀ s, P {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} = 0 :=
    fun s => nsd_path_no_revival_species1 params (a, b) s
  have hNullConc : P {ω | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} = 0 := by
    change lvPathMeasure .nonSelfDestructive params (a, b) _ = 0
    unfold lvPathMeasure
    rw [show {ω : ℕ → PopState | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} =
        (fun ω => ω N) ⁻¹' ({(1, 0), (0, 1)} : Set PopState)ᶜ from rfl,
      ← Measure.map_apply (measurable_pi_apply N) (by measurability),
      homogeneousPathMeasure_dirac_marginal]
    convert nsd_kernelIter_concentrated_on_absorbing params hBeta hDelta
      hGamma0 hGamma1 hAlphaSum a b ha hb using 2
  -- Bad set is null
  have hBad : P {ω | ¬(ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
      (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
      (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0))} = 0 := by
    have hBadNull : P ({ω : ℕ → PopState | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} ∪
        (⋃ s, {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0}) ∪
        (⋃ s, {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0})) = 0 :=
      measure_union_null (measure_union_null hNullConc (measure_iUnion_null hNull0))
        (measure_iUnion_null hNull1)
    apply measure_mono_null _ hBadNull
    intro ω hω
    rcases not_and_or.mp hω with hc | hbc
    · exact Set.mem_union_left _ (Set.mem_union_left _ hc)
    · rcases not_and_or.mp hbc with h0 | h1
      · have ⟨s, hs⟩ := not_forall.mp h0; push_neg at hs
        obtain ⟨_, h1, h2⟩ := hs
        exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨s, h1, h2⟩))
      · have ⟨s, hs⟩ := not_forall.mp h1; push_neg at hs
        obtain ⟨_, h1, h2⟩ := hs
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨s, h1, h2⟩)
  -- MCE ↔ ω(N)=(1,0) on nice paths
  have hEquiv : ∀ ω, (ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
      (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
      (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0)) →
      (majorityConsensusEvent (a, b) ω ↔ ω N = (1, 0)) := by
    intro ω ⟨hC, h0, h1⟩; exact mce_iff_omega_N a b hba ω N hC h0 h1
  -- le_antisymm
  apply le_antisymm
  · calc P {ω | majorityConsensusEvent (a, b) ω}
        ≤ P ({ω | ω N = (1, 0)} ∪ {ω | ¬(ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
          (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
          (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0))}) := by
            apply measure_mono; intro ω hω; simp only [Set.mem_union, Set.mem_setOf_eq]
            by_cases hG : ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
              (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
              (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0)
            · exact Or.inl ((hEquiv ω hG).mp hω)
            · exact Or.inr hG
      _ ≤ P {ω | ω N = (1, 0)} + P _ := measure_union_le _ _
      _ = P {ω | ω N = (1, 0)} := by rw [hBad, add_zero]
  · calc P {ω | ω N = (1, 0)}
        ≤ P ({ω | majorityConsensusEvent (a, b) ω} ∪ {ω | ¬(ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
          (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
          (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0))}) := by
            apply measure_mono; intro ω hω; simp only [Set.mem_union, Set.mem_setOf_eq]
            by_cases hG : ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
              (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
              (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0)
            · exact Or.inl ((hEquiv ω hG).mpr hω)
            · exact Or.inr hG
      _ ≤ P {ω | majorityConsensusEvent (a, b) ω} + P _ := measure_union_le _ _
      _ = P {ω | majorityConsensusEvent (a, b) ω} := by rw [hBad, add_zero]

/-- Path-level no-revival for species 1 under SD dynamics with β=δ=0:
    P[ω(s).2 = 0 ∧ ω(s+1).2 ≠ 0] = 0. -/
private lemma sd_path_no_revival_species1
    (params : LVParams) (s₀ : PopState) (s : ℕ)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    lvPathMeasure .selfDestructive params s₀
      {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} = 0 := by
  let K := lvKernel LVVariant.selfDestructive params
  let g : PopState → ℝ≥0∞ := fun x => if x.2 = 0 then 1 else 0
  let φ : PopState → ℝ≥0∞ := fun y => if y.2 ≠ 0 then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas : MeasurableSet {ω' : ℕ → PopState | (ω' s).2 = 0 ∧ (ω' (s + 1)).2 ≠ 0} :=
    .inter ((measurable_pi_apply s).snd (measurableSet_singleton 0))
      ((measurable_pi_apply (s+1)).snd (measurableSet_singleton 0).compl)
  unfold lvPathMeasure
  have hconv : (homogeneousPathMeasure (Measure.dirac s₀) K)
      {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} =
      ∫⁻ ω', g (ω' s) * φ (ω' (s + 1)) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) := by
    rw [← lintegral_indicator_one hmeas]; congr 1; ext ω'
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]; split_ifs <;> simp_all
  rw [hconv, homogeneousPathMeasure_joint_lintegral K s₀ s g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {y | y.2 ≠ 0} := by
    intro x; have : φ = Set.indicator {y : PopState | y.2 ≠ 0} 1 := by
      ext y; simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this]; exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]; simp_rw [show ∀ x, g x * K x {y | y.2 ≠ 0} = 0 from fun x => by
    simp only [g]; split_ifs with h
    · simp only [one_mul]; exact sd_kernel_species1_dead_absorbing params x hBeta hDelta h
    · simp]; exact lintegral_zero

/-- Path-level no-revival for species 0 under SD dynamics with β=δ=0:
    P[ω(s).1 = 0 ∧ ω(s+1).1 ≠ 0] = 0. -/
private lemma sd_path_no_revival_species0
    (params : LVParams) (s₀ : PopState) (s : ℕ)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    lvPathMeasure .selfDestructive params s₀
      {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} = 0 := by
  let K := lvKernel LVVariant.selfDestructive params
  let g : PopState → ℝ≥0∞ := fun x => if x.1 = 0 then 1 else 0
  let φ : PopState → ℝ≥0∞ := fun y => if y.1 ≠ 0 then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas : MeasurableSet {ω' : ℕ → PopState | (ω' s).1 = 0 ∧ (ω' (s + 1)).1 ≠ 0} :=
    .inter ((measurable_pi_apply s).fst (measurableSet_singleton 0))
      ((measurable_pi_apply (s+1)).fst (measurableSet_singleton 0).compl)
  unfold lvPathMeasure
  have hconv : (homogeneousPathMeasure (Measure.dirac s₀) K)
      {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} =
      ∫⁻ ω', g (ω' s) * φ (ω' (s + 1)) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) := by
    rw [← lintegral_indicator_one hmeas]; congr 1; ext ω'
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]; split_ifs <;> simp_all
  rw [hconv, homogeneousPathMeasure_joint_lintegral K s₀ s g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {y | y.1 ≠ 0} := by
    intro x; have : φ = Set.indicator {y : PopState | y.1 ≠ 0} 1 := by
      ext y; simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this]; exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]; simp_rw [show ∀ x, g x * K x {y | y.1 ≠ 0} = 0 from fun x => by
    simp only [g]; split_ifs with h
    · simp only [one_mul]; exact sd_kernel_species0_dead_absorbing params x hBeta hDelta h
    · simp]; exact lintegral_zero

/-- Path-level no-revival for species 1 under SD dynamics (general, no β=δ=0 required):
    P[ω(s).2 = 0 ∧ ω(s+1).2 ≠ 0] = 0. -/
lemma sd_path_no_revival_species1_general
    (params : LVParams) (s₀ : PopState) (s : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    lvPathMeasure .selfDestructive params s₀
      {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} = 0 := by
  let K := lvKernel LVVariant.selfDestructive params
  let g : PopState → ℝ≥0∞ := fun x => if x.2 = 0 then 1 else 0
  let φ : PopState → ℝ≥0∞ := fun y => if y.2 ≠ 0 then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas : MeasurableSet {ω' : ℕ → PopState | (ω' s).2 = 0 ∧ (ω' (s + 1)).2 ≠ 0} :=
    .inter ((measurable_pi_apply s).snd (measurableSet_singleton 0))
      ((measurable_pi_apply (s+1)).snd (measurableSet_singleton 0).compl)
  unfold lvPathMeasure
  have hconv : (homogeneousPathMeasure (Measure.dirac s₀) K)
      {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} =
      ∫⁻ ω', g (ω' s) * φ (ω' (s + 1)) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) := by
    rw [← lintegral_indicator_one hmeas]; congr 1; ext ω'
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]; split_ifs <;> simp_all
  rw [hconv, homogeneousPathMeasure_joint_lintegral K s₀ s g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {y | y.2 ≠ 0} := by
    intro x; have : φ = Set.indicator {y : PopState | y.2 ≠ 0} 1 := by
      ext y; simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this]; exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]; simp_rw [show ∀ x, g x * K x {y | y.2 ≠ 0} = 0 from fun x => by
    simp only [g]; split_ifs with h
    · simp only [one_mul]; exact sd_kernel_species1_dead_absorbing_general params x h
    · simp]; exact lintegral_zero

/-- Path-level no-revival for species 0 under SD dynamics (general, no β=δ=0 required):
    P[ω(s).1 = 0 ∧ ω(s+1).1 ≠ 0] = 0. -/
lemma sd_path_no_revival_species0_general
    (params : LVParams) (s₀ : PopState) (s : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    lvPathMeasure .selfDestructive params s₀
      {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} = 0 := by
  let K := lvKernel LVVariant.selfDestructive params
  let g : PopState → ℝ≥0∞ := fun x => if x.1 = 0 then 1 else 0
  let φ : PopState → ℝ≥0∞ := fun y => if y.1 ≠ 0 then 1 else 0
  have hgm : Measurable g := by measurability
  have hφm : Measurable φ := by measurability
  have hmeas : MeasurableSet {ω' : ℕ → PopState | (ω' s).1 = 0 ∧ (ω' (s + 1)).1 ≠ 0} :=
    .inter ((measurable_pi_apply s).fst (measurableSet_singleton 0))
      ((measurable_pi_apply (s+1)).fst (measurableSet_singleton 0).compl)
  unfold lvPathMeasure
  have hconv : (homogeneousPathMeasure (Measure.dirac s₀) K)
      {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} =
      ∫⁻ ω', g (ω' s) * φ (ω' (s + 1)) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) := by
    rw [← lintegral_indicator_one hmeas]; congr 1; ext ω'
    simp only [g, φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]; split_ifs <;> simp_all
  rw [hconv, homogeneousPathMeasure_joint_lintegral K s₀ s g φ hgm hφm]
  have hinner : ∀ x, ∫⁻ y, φ y ∂(K x) = K x {y | y.1 ≠ 0} := by
    intro x; have : φ = Set.indicator {y : PopState | y.1 ≠ 0} 1 := by
      ext y; simp only [φ, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this]; exact lintegral_indicator_one (by measurability)
  simp_rw [hinner]; simp_rw [show ∀ x, g x * K x {y | y.1 ≠ 0} = 0 from fun x => by
    simp only [g]; split_ifs with h
    · simp only [one_mul]; exact sd_kernel_species0_dead_absorbing_general params x h
    · simp]; exact lintegral_zero

/-- Multi-step no-revival for species 1 under SD:
    P[ω(t).2 = 0 ∧ ω(t+j).2 ≠ 0] = 0 for all j. -/
lemma sd_path_species1_dead_forward
    (params : LVParams) (s₀ : PopState) (t j : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    lvPathMeasure .selfDestructive params s₀
      {ω | (ω t).2 = 0 ∧ (ω (t + j)).2 ≠ 0} = 0 := by
  induction j with
  | zero =>
    convert measure_empty (μ := lvPathMeasure .selfDestructive params s₀)
    ext ω; simp [Set.mem_setOf_eq]
  | succ n ih =>
    apply le_antisymm _ zero_le
    have hsub : (({ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + (n + 1))).2 ≠ 0}) :
        Set (ℕ → PopState)) ⊆
        {ω | (ω t).2 = 0 ∧ (ω (t + n)).2 ≠ 0} ∪
        {ω | (ω (t + n)).2 = 0 ∧ (ω (t + n + 1)).2 ≠ 0} := by
      intro ω ⟨h1, h2⟩
      by_cases h : (ω (t + n)).2 = 0
      · right; exact ⟨h, by rwa [show t + (n + 1) = t + n + 1 from by omega] at h2⟩
      · left; exact ⟨h1, h⟩
    have h1 := measure_mono (μ := lvPathMeasure .selfDestructive params s₀) hsub
    have h2 := measure_union_le (μ := lvPathMeasure .selfDestructive params s₀)
      {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + n)).2 ≠ 0}
      {ω : ℕ → PopState | (ω (t + n)).2 = 0 ∧ (ω (t + n + 1)).2 ≠ 0}
    rw [ih, sd_path_no_revival_species1_general params s₀ (t + n), add_zero] at h2
    exact le_trans (le_trans h1 h2) (le_refl 0)

/-- Multi-step no-revival for species 0 under SD:
    P[ω(t).1 = 0 ∧ ω(t+j).1 ≠ 0] = 0 for all j. -/
lemma sd_path_species0_dead_forward
    (params : LVParams) (s₀ : PopState) (t j : ℕ)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    lvPathMeasure .selfDestructive params s₀
      {ω | (ω t).1 = 0 ∧ (ω (t + j)).1 ≠ 0} = 0 := by
  induction j with
  | zero =>
    convert measure_empty (μ := lvPathMeasure .selfDestructive params s₀)
    ext ω; simp [Set.mem_setOf_eq]
  | succ n ih =>
    apply le_antisymm _ zero_le
    have hsub : (({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + (n + 1))).1 ≠ 0}) :
        Set (ℕ → PopState)) ⊆
        {ω | (ω t).1 = 0 ∧ (ω (t + n)).1 ≠ 0} ∪
        {ω | (ω (t + n)).1 = 0 ∧ (ω (t + n + 1)).1 ≠ 0} := by
      intro ω ⟨h1, h2⟩
      by_cases h : (ω (t + n)).1 = 0
      · right; exact ⟨h, by rwa [show t + (n + 1) = t + n + 1 from by omega] at h2⟩
      · left; exact ⟨h1, h⟩
    have h1 := measure_mono (μ := lvPathMeasure .selfDestructive params s₀) hsub
    have h2 := measure_union_le (μ := lvPathMeasure .selfDestructive params s₀)
      {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + n)).1 ≠ 0}
      {ω : ℕ → PopState | (ω (t + n)).1 = 0 ∧ (ω (t + n + 1)).1 ≠ 0}
    rw [ih, sd_path_no_revival_species0_general params s₀ (t + n), add_zero] at h2
    exact le_trans (le_trans h1 h2) (le_refl 0)

/-- Unified multi-step no-revival for species 1 under any LV variant:
    P[ω(t).2 = 0 ∧ ω(t+j).2 ≠ 0] = 0 for all j and both SD/NSD. -/
lemma lv_path_species1_dead_forward
    (v : LVVariant) (params : LVParams) (s₀ : PopState) (t j : ℕ)
    [IsMarkovKernel (lvKernel v params)] :
    lvPathMeasure v params s₀
      {ω | (ω t).2 = 0 ∧ (ω (t + j)).2 ≠ 0} = 0 := by
  cases v with
  | nonSelfDestructive => exact nsd_path_species1_dead_forward params s₀ t j
  | selfDestructive => exact sd_path_species1_dead_forward params s₀ t j

/-- Unified multi-step no-revival for species 0 under any LV variant:
    P[ω(t).1 = 0 ∧ ω(t+j).1 ≠ 0] = 0 for all j and both SD/NSD. -/
lemma lv_path_species0_dead_forward
    (v : LVVariant) (params : LVParams) (s₀ : PopState) (t j : ℕ)
    [IsMarkovKernel (lvKernel v params)] :
    lvPathMeasure v params s₀
      {ω | (ω t).1 = 0 ∧ (ω (t + j)).1 ≠ 0} = 0 := by
  cases v with
  | nonSelfDestructive => exact nsd_path_species0_dead_forward params s₀ t j
  | selfDestructive => exact sd_path_species0_dead_forward params s₀ t j

lemma intraspecific_only_constant_failure
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0) (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    ∀ a b : Nat, 0 < b → b < a →
      ∃ ε : Real, 0 < ε ∧
        majorityConsensusProb v params (a, b) ≤ 1 - ENNReal.ofReal ε := by
  intro a b hb hba
  -- Strategy: exhibit a path where species 0 dies 'a' individual-death steps,
  -- reaching state (0,b). At (0,b), species 1 wins (¬MCE). So P[¬MCE] > 0.
  --
  -- Explicitly: transitions (a,b)→(a-1,b)→…→(0,b) each happen with prob δ*k/φ(k,b)>0.
  -- Therefore P[ω(a)=(0,b)] > 0. Since MCE requires species 1 to die (ω(t).2=0)
  -- which (by no-revival for species 1, using α₁=0) cannot be followed by ω(a).2=b>0,
  -- the events {MCE} and {ω(a)=(0,b)} are almost disjoint (null intersection).
  -- Hence P[MCE] ≤ 1 - P[ω(a)=(0,b)] = 1 - ENNReal.ofReal ε.
  set K := lvKernel v params
  set P := lvPathMeasure v params (a, b) with hPdef
  -- lvPathMeasure is a probability measure (since the path measure is constructed from
  -- the Markov kernel, which is Markov by assumption)
  haveI hProb : IsProbabilityMeasure P := by
    show IsProbabilityMeasure (homogeneousPathMeasure (Measure.dirac (a, b)) (lvKernel v params))
    unfold homogeneousPathMeasure
    infer_instance
  set Ewin := {ω : ℕ → PopState | ω a = (0, b)} with hEwin_def
  set MCEset := {ω : ℕ → PopState | majorityConsensusEvent (a, b) ω} with hMCE_def
  -- Measurability (only Ewin needed below)
  have hEwin_meas : MeasurableSet Ewin := by measurability
  -- STEP 1: Translate Ewin to a kernel-iteration event
  have hEwin_eq : P Ewin = (kernelIter K a) (a, b) {(0, b)} := by
    rw [hEwin_def, hPdef, lvPathMeasure]
    rw [show {ω : ℕ → PopState | ω a = (0, b)} = (fun ω => ω a) ⁻¹' {(0, b)} from rfl]
    rw [← Measure.map_apply (measurable_pi_apply a) (measurableSet_singleton _)]
    rw [homogeneousPathMeasure_dirac_marginal]
  -- STEP 2: Ewin has positive measure.
  -- The path (a,b)→(a-1,b)→…→(0,b) via individual-death-of-species-0 steps
  -- has probability ∏ₖ δ*k/φ(k,b) > 0. Formal lower bound via Chapman-Kolmogorov
  -- applied inductively: K(k,b){(k-1,b)} = δ*k/φ(k,b) > 0 (since δ>0, k>0, φ>0).
  have hEwin_pos : 0 < P Ewin := by
    rw [hEwin_eq]
    -- (K^a)(a,b){(0,b)} > 0: proved by induction on a using Chapman-Kolmogorov.
    -- Each step: K(k,b){(k-1,b)} = δ*k/φ(k,b) > 0 (only individual-death contributes
    -- since α₀=α₁=0 and intraspecific terms vanish at count k for the death transition).
    -- Path: (a,b)→(a-1,b)→…→(0,b) via individual death of species 0
    let path : Fin (a + 1) → PopState := fun i => (a - i.val, b)
    have hpath0 : path 0 = (a, b) := by simp [path]
    have hpathLast : path (Fin.last a) = (0, b) := by simp [path, Fin.last]
    -- Each step K(a-i,b){(a-i-1,b)} > 0 by lvKernel_death0_pos
    have hsteps : ∀ i : Fin a, 0 < K (path i.castSucc) {path i.succ} := fun i => by
      simp only [path, Fin.coe_castSucc, Fin.val_succ]
      rw [show (a - (i.val + 1), b) = (a - i.val - 1, b) from by congr 1]
      exact lvKernel_death0_pos v params (a - i.val) b (by omega) hDelta
    calc (0 : ℝ≥0∞)
        < ∏ i : Fin a, K (path i.castSucc) {path i.succ} :=
            ENNReal.fin_prod_pos (fun i => hsteps i)
      _ ≤ (kernelIter K a) (path 0) {path (Fin.last a)} :=
            kernelIter_path_lower K a path
      _ = (kernelIter K a) (a, b) {(0, b)} := by rw [hpath0, hpathLast]
  -- STEP 3: The events MCEset and Ewin have null intersection.
  -- Proof: if ω ∈ MCEset then consensusTime ω = t with ω(t).2=0; by no-revival for
  -- species 1 (α₁=0 makes (x₀,0) absorbing: kernel mass on {s'.2≠0} is 0), we get
  -- ω(a).2=0 a.s. But Ewin requires ω(a).2=b>0. Contradiction (a.s.), giving null set.
  have hNullInt : P (MCEset ∩ Ewin) = 0 := by
    -- MCEset ∩ Ewin ⊆ D1 ∪ D2 where D1, D2 each have measure 0.
    -- D1 = ⋃_{t≤a} {(ω t).2=0 ∧ (ω a).2≠0}: MCE at t≤a causes species1 revival contradiction
    -- D2 = ⋃_{j≥1} {(ω a).1=0 ∧ (ω(a+j)).1≠0}: Ewin→species0 dead, MCE at t>a causes revival
    apply le_antisymm _ zero_le
    have hb_ne : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
    -- Key null families indexed by Fin(a+1) and ℕ
    have hD1 : ∀ t : Fin (a + 1), P {ω | (ω t.val).2 = 0 ∧ (ω a).2 ≠ 0} = 0 := fun t => by
      have ht : t.val ≤ a := Nat.lt_succ_iff.mp t.isLt
      have heq : {ω : ℕ → PopState | (ω t.val).2 = 0 ∧ (ω a).2 ≠ 0} =
              {ω | (ω t.val).2 = 0 ∧ (ω (t.val + (a - t.val))).2 ≠ 0} := by
        congr 1; ext ω; simp [Nat.add_sub_cancel' ht]
      rw [heq]; exact lv_path_species1_dead_forward v params (a, b) t.val (a - t.val)
    have hD2 : ∀ j : ℕ, P {ω | (ω a).1 = 0 ∧ (ω (a + j + 1)).1 ≠ 0} = 0 := fun j => by
      have heq : {ω : ℕ → PopState | (ω a).1 = 0 ∧ (ω (a + j + 1)).1 ≠ 0} =
              {ω | (ω a).1 = 0 ∧ (ω (a + (j + 1))).1 ≠ 0} := by
        congr 1
      rw [heq]; exact lv_path_species0_dead_forward v params (a, b) a (j + 1)
    -- MCEset ∩ Ewin ⊆ (⋃ t : Fin(a+1), D1 t) ∪ (⋃ j : ℕ, D2 j)
    have hsub : MCEset ∩ Ewin ⊆
        (⋃ t : Fin (a + 1), {ω | (ω t.val).2 = 0 ∧ (ω a).2 ≠ 0}) ∪
        (⋃ j : ℕ, {ω | (ω a).1 = 0 ∧ (ω (a + j + 1)).1 ≠ 0}) := by
      intro ω ⟨hMCE, hE⟩
      simp only [hEwin_def, Set.mem_setOf_eq] at hE
      have hω2 : (ω a).2 ≠ 0 := by rw [hE]; exact hb_ne
      have hω1 : (ω a).1 = 0 := by rw [hE]
      simp only [hMCE_def, Set.mem_setOf_eq] at hMCE
      unfold majorityConsensusEvent at hMCE
      rcases hct : consensusTime ω with _ | t
      · simp only [hct] at hMCE
      · simp only [hct] at hMCE
        have hMaj : species0Majority (a, b) := by simp [species0Majority]; omega
        rcases hMCE with ⟨_, htpos, ht2⟩ | ⟨hnsm, _⟩
        · by_cases hle : t ≤ a
          · left; exact Set.mem_iUnion.mpr ⟨⟨t, by omega⟩, ht2, hω2⟩
          · right; exact Set.mem_iUnion.mpr ⟨t - a - 1, hω1, by
              have heq : a + (t - a - 1) + 1 = t := by omega
              rw [heq]; exact htpos.ne'⟩
        · exact absurd hMaj hnsm
    calc P (MCEset ∩ Ewin)
        ≤ P ((⋃ t : Fin (a + 1), {ω | (ω t.val).2 = 0 ∧ (ω a).2 ≠ 0}) ∪
              (⋃ j : ℕ, {ω | (ω a).1 = 0 ∧ (ω (a + j + 1)).1 ≠ 0})) :=
            measure_mono hsub
      _ ≤ P (⋃ t : Fin (a + 1), {ω | (ω t.val).2 = 0 ∧ (ω a).2 ≠ 0}) +
            P (⋃ j : ℕ, {ω | (ω a).1 = 0 ∧ (ω (a + j + 1)).1 ≠ 0}) :=
            measure_union_le _ _
      _ ≤ (∑' t : Fin (a + 1), P {ω | (ω t.val).2 = 0 ∧ (ω a).2 ≠ 0}) +
            ∑' j : ℕ, P {ω | (ω a).1 = 0 ∧ (ω (a + j + 1)).1 ≠ 0} :=
            add_le_add (measure_iUnion_le _) (measure_iUnion_le _)
      _ = 0 := by simp [hD1, hD2]
  -- STEP 4: P[MCE] ≤ 1 - P[Ewin] (from null intersection and sub-probability)
  have hSum : P MCEset ≤ 1 - P Ewin := by
    -- MCEset ⊆ (MCEset \ Ewin) ∪ (MCEset ∩ Ewin), so P(MCE) ≤ P(MCE\E) + 0
    have hMCE_le : P MCEset ≤ P (MCEset \ Ewin) := by
      calc P MCEset
          = P ((MCEset \ Ewin) ∪ (MCEset ∩ Ewin)) := by
            congr 1; exact (Set.diff_union_inter MCEset Ewin).symm
        _ ≤ P (MCEset \ Ewin) + P (MCEset ∩ Ewin) := measure_union_le _ _
        _ = P (MCEset \ Ewin) := by rw [hNullInt, add_zero]
    -- (MCEset \ Ewin) and Ewin are disjoint, so P(MCE\E) + P(E) ≤ 1
    have hDisj : Disjoint (MCEset \ Ewin) Ewin :=
      Set.disjoint_left.mpr fun _ hx hxE => hx.2 hxE
    have hDE_E : P (MCEset \ Ewin) + P Ewin ≤ 1 := by
      calc P (MCEset \ Ewin) + P Ewin
          = P ((MCEset \ Ewin) ∪ Ewin) := (measure_union hDisj hEwin_meas).symm
        _ ≤ 1 := prob_le_one
    -- Combine: P(MCE) ≤ P(MCE\E) ≤ 1 - P(E)
    have hEfin : P Ewin ≠ ⊤ := measure_ne_top _ _
    have hEle1 : P Ewin ≤ 1 := prob_le_one
    exact hMCE_le.trans (ENNReal.le_sub_of_add_le_right hEfin hDE_E)
  -- STEP 5: Set ε = P[Ewin].toReal > 0 and conclude MCE ≤ 1 - ENNReal.ofReal ε
  refine ⟨(P Ewin).toReal, ?_, ?_⟩
  · -- ε > 0 since P[Ewin] > 0 and P[Ewin] < ⊤
    exact ENNReal.toReal_pos hEwin_pos.ne' (measure_ne_top _ _)
  · -- MCE ≤ 1 - ENNReal.ofReal ε = 1 - P[Ewin]
    unfold majorityConsensusProb
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact hSum

/-- Optional stopping for bounded harmonic functions on the SD LV chain.
    The harmonicity condition is only required at states with the same parity
    as the initial state, since SD events (with β=δ=0) preserve population parity. -/
lemma consensus_eq_harmonic_sd
    (params : LVParams)
    (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hOdd : Odd (a + b))
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1)
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' → Odd (a' + b') →
      params.beta * a' * h (a' + 1, b') + params.beta * b' * h (a', b' + 1) +
      params.delta * a' * h (a' - 1, b') + params.delta * b' * h (a', b' - 1) +
      (params.alpha0 + params.alpha1) * a' * b' * h (a' - 1, b' - 1) +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2) * h (a' - 2, b') +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2) * h (a', b' - 2) =
      lvTotalPropensity params (a', b') * h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    majorityConsensusProb LVVariant.selfDestructive params (a, b) =
      ENNReal.ofReal (h (a, b)) := by
  have hba_strict : b < a := by
    rcases Nat.eq_or_lt_of_le hba with rfl | h'
    · exact absurd hOdd (by intro ⟨k, hk⟩; omega)
    · exact h'
  let N := (a + b - 1) / 2
  have hKernel := sd_kernelIter_value params h a b ha hb hOdd hBeta hDelta
    hGamma0 hGamma1 hAlphaSum hBound hHarm hBnd1 hBnd0
  have hTarget : lvPathMeasure .selfDestructive params (a, b) {ω | ω N = (1, 0)} =
      ENNReal.ofReal (h (a, b)) := by
    have : {ω : ℕ → PopState | ω N = (1, 0)} = (fun ω => ω N) ⁻¹' {(1, 0)} := by ext; simp
    unfold lvPathMeasure; rw [this,
      ← Measure.map_apply (measurable_pi_apply N) (by measurability),
      homogeneousPathMeasure_dirac_marginal, hKernel]
  suffices hmce :
    lvPathMeasure .selfDestructive params (a, b) {ω | majorityConsensusEvent (a, b) ω} =
    lvPathMeasure .selfDestructive params (a, b) {ω | ω N = (1, 0)} by
    unfold majorityConsensusProb; rw [hmce, hTarget]
  set P := lvPathMeasure .selfDestructive params (a, b) with hP_def
  -- Null sets for no-revival and concentration
  have hNull0 : ∀ s, P {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0} = 0 :=
    fun s => sd_path_no_revival_species0 params (a, b) s hBeta hDelta
  have hNull1 : ∀ s, P {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0} = 0 :=
    fun s => sd_path_no_revival_species1 params (a, b) s hBeta hDelta
  have hNullConc : P {ω | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} = 0 := by
    change lvPathMeasure .selfDestructive params (a, b) _ = 0
    unfold lvPathMeasure
    rw [show {ω : ℕ → PopState | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} =
        (fun ω => ω N) ⁻¹' ({(1, 0), (0, 1)} : Set PopState)ᶜ from rfl,
      ← Measure.map_apply (measurable_pi_apply N) (by measurability),
      homogeneousPathMeasure_dirac_marginal]
    convert sd_kernelIter_concentrated_on_absorbing params hBeta hDelta
      hGamma0 hGamma1 hAlphaSum a b ha hb hOdd using 2
    ext s; simp [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  -- Bad set (complement of "nice" paths) is null
  have hBad : P {ω | ¬(ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
      (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
      (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0))} = 0 := by
    have hBadNull : P ({ω : ℕ → PopState | ω N ∈ ({(1, 0), (0, 1)} : Set PopState)ᶜ} ∪
        (⋃ s, {ω | (ω s).1 = 0 ∧ (ω (s + 1)).1 ≠ 0}) ∪
        (⋃ s, {ω | (ω s).2 = 0 ∧ (ω (s + 1)).2 ≠ 0})) = 0 :=
      measure_union_null (measure_union_null hNullConc (measure_iUnion_null hNull0))
        (measure_iUnion_null hNull1)
    apply measure_mono_null _ hBadNull
    intro ω hω
    rcases not_and_or.mp hω with hc | hbc
    · exact Set.mem_union_left _ (Set.mem_union_left _ hc)
    · rcases not_and_or.mp hbc with h0 | h1
      · have ⟨s, hs⟩ := not_forall.mp h0; push_neg at hs
        obtain ⟨_, h1, h2⟩ := hs
        exact Set.mem_union_left _ (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨s, h1, h2⟩))
      · have ⟨s, hs⟩ := not_forall.mp h1; push_neg at hs
        obtain ⟨_, h1, h2⟩ := hs
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨s, h1, h2⟩)
  -- MCE ↔ ω(N)=(1,0) on nice paths
  have hEquiv : ∀ ω, (ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
      (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
      (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0)) →
      (majorityConsensusEvent (a, b) ω ↔ ω N = (1, 0)) := by
    intro ω ⟨hC, h0, h1⟩; exact mce_iff_omega_N a b hba_strict ω N hC h0 h1
  -- le_antisymm: MCE and Target differ only on null set
  apply le_antisymm
  · calc P {ω | majorityConsensusEvent (a, b) ω}
        ≤ P ({ω | ω N = (1, 0)} ∪ {ω | ¬(ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
          (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
          (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0))}) := by
            apply measure_mono; intro ω hω; simp only [Set.mem_union, Set.mem_setOf_eq]
            by_cases hG : ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
              (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
              (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0)
            · exact Or.inl ((hEquiv ω hG).mp hω)
            · exact Or.inr hG
      _ ≤ P {ω | ω N = (1, 0)} + P _ := measure_union_le _ _
      _ = P {ω | ω N = (1, 0)} := by rw [hBad, add_zero]
  · calc P {ω | ω N = (1, 0)}
        ≤ P ({ω | majorityConsensusEvent (a, b) ω} ∪ {ω | ¬(ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
          (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
          (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0))}) := by
            apply measure_mono; intro ω hω; simp only [Set.mem_union, Set.mem_setOf_eq]
            by_cases hG : ω N ∈ ({(1, 0), (0, 1)} : Set PopState) ∧
              (∀ s < N, (ω s).1 = 0 → (ω (s + 1)).1 = 0) ∧
              (∀ s < N, (ω s).2 = 0 → (ω (s + 1)).2 = 0)
            · exact Or.inl ((hEquiv ω hG).mpr hω)
            · exact Or.inr hG
      _ ≤ P {ω | majorityConsensusEvent (a, b) ω} + P _ := measure_union_le _ _
      _ = P {ω | majorityConsensusEvent (a, b) ω} := by rw [hBad, add_zero]

/-! ### Monotone coupling for NSD intraspecific competition

For NSD chains with symmetric parameters (α₀=α₁, γ₀=γ₁), increasing
intra-specific competition γ can only decrease the majority consensus probability.
This follows from a coupling argument: the chain with higher γ has a higher
probability of the majority species flipping (see paper Corollary `cor:nsd-intra`). -/

/-- Recursive harmonic function for NSD consensus: h(0,_) = 0, h(_+1,0) = 1,
    h(a+1,b+1) = (wM·h(a,b+1) + wP·h(a+1,b)) / φ where wM,wP are transition weights. -/
noncomputable def nsdHF (α γ : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | (_+1), 0 => 1
  | (a+1), (b+1) =>
    let a' := ((a : ℝ) + 1)
    let b' := ((b : ℝ) + 1)
    let wM := α * a' * b' + γ * a' * (a' - 1) / 2
    let wP := α * a' * b' + γ * b' * (b' - 1) / 2
    let phi := wM + wP
    if phi = 0 then 0
    else (wM * nsdHF α γ a (b+1) + wP * nsdHF α γ (a+1) b) / phi
termination_by a b => a + b

private lemma nsdHF_phi_pos (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (a b : ℕ) :
    0 < α * ((a : ℝ) + 1) * ((b : ℝ) + 1) + γ * ((a : ℝ) + 1) * (a : ℝ) / 2 +
        (α * ((a : ℝ) + 1) * ((b : ℝ) + 1) + γ * ((b : ℝ) + 1) * (b : ℝ) / 2) := by
  have : 0 < α * ((a : ℝ) + 1) * ((b : ℝ) + 1) := by positivity
  linarith [show 0 ≤ γ * ((a : ℝ) + 1) * (a : ℝ) / 2 from by positivity,
    show 0 ≤ γ * ((b : ℝ) + 1) * (b : ℝ) / 2 from by positivity]

lemma nsdHF_swap (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (a b : ℕ) (hab : 0 < a + b) :
    nsdHF α γ a b + nsdHF α γ b a = 1 := by
  suffices ∀ n : ℕ, 0 < n → ∀ a b : ℕ, a + b = n → nsdHF α γ a b + nsdHF α γ b a = 1 from
    this (a+b) hab a b rfl
  intro n; induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn a b hab
    match a, b with
    | 0, 0 => omega
    | 0, (_+1) => simp [nsdHF]
    | (_+1), 0 => simp [nsdHF]
    | (a+1), (b+1) =>
      have hs : ∀ c:ℕ, ((c:ℝ)+1-1)=(c:ℝ) := fun c => by ring
      have hp := nsdHF_phi_pos α γ hα hγ a b; have hne := ne_of_gt hp
      have ih1 := ih (a+(b+1)) (by omega) (by omega) a (b+1) rfl
      have ih2 := ih ((a+1)+b) (by omega) (by omega) (a+1) b rfl
      show nsdHF α γ (a+1) (b+1) + nsdHF α γ (b+1) (a+1) = 1
      unfold nsdHF; simp only [hs]; rw [if_neg hne]
      have hne2 : ¬(α*(↑b+1)*(↑a+1)+γ*(↑b+1)*↑b/2+(α*(↑b+1)*(↑a+1)+γ*(↑a+1)*↑a/2)=0) := by
        intro h; exact hne (by linarith [show α*(↑b+1)*(↑a+1)=α*(↑a+1)*(↑b+1) from by ring])
      rw [if_neg hne2]
      conv_lhs =>
        rw [show α*(↑b+1)*(↑a+1)+γ*(↑b+1)*↑b/2+(α*(↑b+1)*(↑a+1)+γ*(↑a+1)*↑a/2) =
            α*(↑a+1)*(↑b+1)+γ*(↑a+1)*↑a/2+(α*(↑a+1)*(↑b+1)+γ*(↑b+1)*↑b/2) from by ring]
        rw [show α*(↑b+1)*(↑a+1)+γ*(↑b+1)*↑b/2 = α*(↑a+1)*(↑b+1)+γ*(↑b+1)*↑b/2 from by ring]
        rw [show α*(↑b+1)*(↑a+1)+γ*(↑a+1)*↑a/2 = α*(↑a+1)*(↑b+1)+γ*(↑a+1)*↑a/2 from by ring]
      rw [← add_div, div_eq_one_iff_eq hne]
      rw [show nsdHF α γ (b+1) a = 1-nsdHF α γ a (b+1) from by linarith,
          show nsdHF α γ b (a+1) = 1-nsdHF α γ (a+1) b from by linarith]; ring

lemma nsdHF_diag (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (a : ℕ) (ha : 0 < a) :
    nsdHF α γ a a = 1/2 := by have := nsdHF_swap α γ hα hγ a a (by omega); linarith

lemma nsdHF_bounds (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (a b : ℕ) :
    0 ≤ nsdHF α γ a b ∧ nsdHF α γ a b ≤ 1 := by
  suffices key : ∀ n, ∀ a b : ℕ, a + b ≤ n →
      0 ≤ nsdHF α γ a b ∧ nsdHF α γ a b ≤ 1 from key (a + b) a b le_rfl
  intro n; induction n with
  | zero =>
    intro a b hab
    have ha : a = 0 := (Nat.eq_zero_of_add_eq_zero (Nat.le_zero.mp hab)).1
    subst ha; simp [nsdHF]
  | succ n ih =>
    intro a b hab
    match a, b with
    | 0, _ => simp [nsdHF]
    | (_+1), 0 => simp [nsdHF]
    | (a+1), (b+1) =>
      unfold nsdHF
      simp only [show ((a : ℝ) + 1 - 1) = (a : ℝ) from by ring,
                  show ((b : ℝ) + 1 - 1) = (b : ℝ) from by ring]
      set wM := α * ((a : ℝ) + 1) * ((b : ℝ) + 1) + γ * ((a : ℝ) + 1) * (a : ℝ) / 2
      set wP := α * ((a : ℝ) + 1) * ((b : ℝ) + 1) + γ * ((b : ℝ) + 1) * (b : ℝ) / 2
      by_cases hphi : wM + wP = 0
      · simp [hphi]
      · rw [if_neg hphi]
        have hphi_pos : 0 < wM + wP := by
          have := nsdHF_phi_pos α γ hα hγ a b; simp only [wM, wP] at this ⊢; linarith
        have hwM : 0 ≤ wM := by simp only [wM]; positivity
        have hwP : 0 ≤ wP := by simp only [wP]; positivity
        have ih1 := ih a (b+1) (by omega)
        have ih2 := ih (a+1) b (by omega)
        refine ⟨div_nonneg (add_nonneg (mul_nonneg hwM ih1.1) (mul_nonneg hwP ih2.1))
          (le_of_lt hphi_pos), ?_⟩
        rw [div_le_one hphi_pos]
        have h1 : wM * nsdHF α γ a (b + 1) ≤ wM * 1 := mul_le_mul_of_nonneg_left ih1.2 hwM
        have h2 : wP * nsdHF α γ (a + 1) b ≤ wP * 1 := mul_le_mul_of_nonneg_left ih2.2 hwP
        simp only [mul_one] at h1 h2; linarith

/-- φ · nsdHF(a+1,b+1) = wM · nsdHF(a,b+1) + wP · nsdHF(a+1,b) -/
lemma nsdHF_unfold_mul (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (a b : ℕ) :
    let wM := α * ((a : ℝ) + 1) * ((b : ℝ) + 1) + γ * ((a : ℝ) + 1) * (a : ℝ) / 2
    let wP := α * ((a : ℝ) + 1) * ((b : ℝ) + 1) + γ * ((b : ℝ) + 1) * (b : ℝ) / 2
    (wM + wP) * nsdHF α γ (a+1) (b+1) =
      wM * nsdHF α γ a (b+1) + wP * nsdHF α γ (a+1) b := by
  intro wM wP
  have hp : 0 < wM + wP := by
    have : 0 < α * ((a : ℝ) + 1) * ((b : ℝ) + 1) := by positivity
    simp only [wM, wP]; linarith [
      show 0 ≤ γ * ((a : ℝ) + 1) * (a : ℝ) / 2 from by positivity,
      show 0 ≤ γ * ((b : ℝ) + 1) * (b : ℝ) / 2 from by positivity]
  have key : nsdHF α γ (a+1) (b+1) =
      (wM * nsdHF α γ a (b+1) + wP * nsdHF α γ (a+1) b) / (wM + wP) := by
    show nsdHF α γ (a+1) (b+1) = _
    rw [nsdHF]
    simp only [show ((a:ℝ)+1-1) = (↑a:ℝ) from by ring,
               show ((b:ℝ)+1-1) = (↑b:ℝ) from by ring]
    rw [if_neg (ne_of_gt hp)]
  rw [key]; exact mul_div_cancel₀ _ (ne_of_gt hp)

/-- Key ratio bound: nsdHF(a,b) · (a+b) ≤ a when γ ≥ 2α and b ≤ a. -/
lemma nsdHF_ratio_mul (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (hγα : 2*α ≤ γ)
    (a b : ℕ) (hba : b ≤ a) (ha : 0 < a) :
    nsdHF α γ a b * ((a:ℝ)+(b:ℝ)) ≤ (a:ℝ) := by
  suffices key : ∀ s, ∀ a b : ℕ, a+b=s → b≤a → 0<a →
      nsdHF α γ a b * ((a:ℝ)+(b:ℝ)) ≤ (a:ℝ) from key (a+b) a b rfl hba ha
  intro s; induction s using Nat.strongRecOn with
  | ind s ih =>
    intro a b hs hba ha
    obtain ⟨a,rfl⟩ : ∃ a', a=a'+1 := ⟨a-1, by omega⟩
    rcases b with _|b
    · simp [nsdHF, add_zero]
    · rcases eq_or_lt_of_le hba with heq|hlt
      · have hab : a = b := by omega
        rw [hab, nsdHF_diag α γ hα hγ (b+1) (by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
        linarith [show (0:ℝ) ≤ b from Nat.cast_nonneg b]
      · have hs' : ∀ c:ℕ, ((c:ℝ)+1-1)=(c:ℝ) := fun c => by ring
        have hp := nsdHF_phi_pos α γ hα hγ a b
        unfold nsdHF; simp only [hs']; rw [if_neg (ne_of_gt hp)]
        have i1 : nsdHF α γ a (b+1)*((a:ℝ)+((b:ℝ)+1)) ≤ (a:ℝ) := by
          have := ih (a+(b+1)) (by omega) a (b+1) rfl (by omega) (by omega)
          push_cast at this; linarith
        have i2 : nsdHF α γ (a+1) b*(((a:ℝ)+1)+(b:ℝ)) ≤ ((a:ℝ)+1) := by
          have := ih ((a+1)+b) (by omega) (a+1) b rfl (by omega) (by omega)
          push_cast at this; linarith
        rw [show ((a+1:ℕ):ℝ)=(a:ℝ)+1 from by push_cast;ring,
            show ((b+1:ℕ):ℝ)=(b:ℝ)+1 from by push_cast;ring, div_mul_eq_mul_div, div_le_iff₀ hp]
        nlinarith [
          mul_le_mul_of_nonneg_left i1
            (show 0≤α*((a:ℝ)+1)*((b:ℝ)+1)+γ*((a:ℝ)+1)*(a:ℝ)/2 from by positivity),
          mul_le_mul_of_nonneg_left i2
            (show 0≤α*((a:ℝ)+1)*((b:ℝ)+1)+γ*((b:ℝ)+1)*(b:ℝ)/2 from by positivity),
          show 0≤(γ-2*α)*((a:ℝ)+1)*((b:ℝ)+1)*((a:ℝ)-(b:ℝ)) from
            mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity))
              (sub_nonneg.mpr (Nat.cast_le.mpr (by omega))),
          show 0≤((a:ℝ)+(b:ℝ)+1) from by positivity]

private lemma mcp_diag_le (params : LVParams) (hSym : params.alpha0 = params.alpha1)
    (hSymγ : params.gamma0 = params.gamma1) (m : ℕ) (hm : 0 < m)
    [ProbabilityTheory.IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    majorityConsensusProb .nonSelfDestructive params (m, m) ≤
      ENNReal.ofReal ((m : ℝ) / ((m : ℝ) + (m : ℝ))) := by
  have hval : (m : ℝ) / ((m : ℝ) + (m : ℝ)) = 1 / 2 := by
    have : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm; field_simp; ring
  rw [hval, show ENNReal.ofReal (1/2:ℝ) = (2:ENNReal)⁻¹ from by
    simp [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_ofNat]]
  set μ := lvPathMeasure .nonSelfDestructive params (m, m) with hμ_def
  haveI : IsProbabilityMeasure μ := by
    rw [hμ_def]; unfold lvPathMeasure homogeneousPathMeasure; infer_instance
  have hswap_meas : Measurable swapTraj := by
    rw [measurable_pi_iff]; intro n
    exact (measurable_of_countable PopState.swap).comp (measurable_pi_apply n)
  have hA_meas := measurableSet_majorityConsensusEvent_diag m
  set A := {ω : ℕ → PopState | majorityConsensusEvent (m, m) ω}
  have hC_meas : MeasurableSet (swapTraj ⁻¹' A) := hA_meas.preimage hswap_meas
  have h_double : μ A + μ A ≤ 1 := by
    have hA_eq : μ A = μ (swapTraj ⁻¹' A) := by
      rw [← Measure.map_apply hswap_meas hA_meas,
          lvPathMeasure_swap_invariant .nonSelfDestructive params hSym hSymγ m]
    calc μ A + μ A = μ A + μ (swapTraj ⁻¹' A) := by rw [hA_eq]
      _ = μ (A ∪ swapTraj ⁻¹' A) :=
        (measure_union (disjoint_majorityConsensus_swap_diag m) hC_meas).symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  change μ A ≤ _
  rw [ENNReal.le_inv_iff_mul_le, mul_comm]; rwa [two_mul]

/-- Superharmonic upper bound on consensus probability.
    For NSD with β=δ=0, symmetric α, and γ ≥ 2α, the function h(a,b) = a/(a+b)
    is superharmonic, giving majorityConsensusProb ≤ a/(a+b).

    When b < a, this uses the kernel iteration with superharmonic inequality.
    When b = a, the result follows from swap invariance (MCE ≤ 1/2 = a/(a+b)). -/
lemma consensus_le_superharmonic_nsd
    (params : LVParams)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hSym : params.alpha0 = params.alpha1)
    (hSymγ : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (hBeta0 : params.beta = 0) (hDelta0 : params.delta = 0)
    (hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (hGamma0 : 0 < params.gamma0) (hGamma1 : 0 < params.gamma1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    majorityConsensusProb .nonSelfDestructive params (a, b) ≤
      ENNReal.ofReal ((a : ℝ) / (a + b)) := by
  rcases eq_or_lt_of_le hba with hab | hba_lt
  · rw [hab]; exact mcp_diag_le params hSym hSymγ a ha
  · have hα_pos : 0 < params.alpha0 := by linarith [hSym ▸ hAlphaSum]
    have hγ_nn : 0 ≤ params.gamma0 := le_of_lt hGamma0
    set hfun : PopState → ℝ := fun s => nsdHF params.alpha0 params.gamma0 s.1 s.2
    have hMCP : majorityConsensusProb .nonSelfDestructive params (a, b) =
        ENNReal.ofReal (hfun (a, b)) := by
      apply consensus_eq_harmonic_nsd params hfun a b ha hb hba_lt hBeta0 hDelta0
        hGamma0 hGamma1 hAlphaSum
      · intro s; exact nsdHF_bounds _ _ hα_pos hγ_nn s.1 s.2
      · intro a' b' ha' hb'
        obtain ⟨a0, rfl⟩ : ∃ x, a' = x + 1 := ⟨a' - 1, by omega⟩
        obtain ⟨b0, rfl⟩ : ∃ x, b' = x + 1 := ⟨b' - 1, by omega⟩
        simp only [hfun, hBeta0, hDelta0, zero_mul, zero_add, mul_zero, add_zero,
                    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
                    show (↑a0+1-1:ℝ) = ↑a0 from by ring, show (↑b0+1-1:ℝ) = ↑b0 from by ring]
        rw [← hSym, ← hSymγ]
        unfold lvTotalPropensity
        simp only [hBeta0, hDelta0, zero_mul, zero_add, add_zero,
                    Nat.cast_add, Nat.cast_one,
                    show (↑a0+1-1:ℝ) = ↑a0 from by ring, show (↑b0+1-1:ℝ) = ↑b0 from by ring]
        rw [hSym, hSymγ, ← hSym, ← hSymγ]
        linarith [nsdHF_unfold_mul params.alpha0 params.gamma0 hα_pos hγ_nn a0 b0]
      · intro a' ha'; simp only [hfun]
        obtain ⟨a0, rfl⟩ : ∃ x, a'=x+1 := ⟨a'-1, by omega⟩; simp [nsdHF]
      · intro b'; simp [hfun, nsdHF]
    rw [hMCP]; apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (show (0:ℝ)<↑a+↑b from by positivity)]
    exact nsdHF_ratio_mul _ _ hα_pos hγ_nn hGe a b (le_of_lt hba_lt) ha

end OptionalStopping

/-! ## SD harmonicity: h(a,b) = a/(a+b) is harmonic for SD with β=δ=0, γ=2α -/

/-- Consensus-absorbing LV kernel: agrees with the standard LV kernel at
    interior states (both species present), but makes consensus states
    (one species extinct) absorbing. This is the "stopped" kernel for the
    stopped martingale argument. -/
noncomputable def lvKernelAbsorb (v : LVVariant) (params : LVParams) :
    Kernel PopState PopState :=
  Kernel.ofFunOfCountable fun s : PopState =>
    if s.1 = 0 ∨ s.2 = 0 then Measure.dirac s
    else (lvKernel v params) s

instance lvKernelAbsorb_isMarkov (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)] : IsMarkovKernel (lvKernelAbsorb v params) := by
  constructor
  intro s
  constructor
  simp only [lvKernelAbsorb, Kernel.ofFunOfCountable, Kernel.coe_mk]
  split_ifs with h
  · exact Measure.dirac.isProbabilityMeasure.measure_univ
  · exact (IsMarkovKernel.isProbabilityMeasure s).measure_univ

/-- At interior states, the absorbing kernel agrees with the standard kernel. -/
lemma lvKernelAbsorb_interior (v : LVVariant) (params : LVParams) (s : PopState)
    (h1 : 0 < s.1) (h2 : 0 < s.2) :
    (lvKernelAbsorb v params) s = (lvKernel v params) s := by
  simp only [lvKernelAbsorb, Kernel.ofFunOfCountable, Kernel.coe_mk,
    show ¬(s.1 = 0 ∨ s.2 = 0) from by omega, ↓reduceIte]

/-- At consensus states, the absorbing kernel is Dirac. -/
lemma lvKernelAbsorb_consensus (v : LVVariant) (params : LVParams) (s : PopState)
    (h : s.1 = 0 ∨ s.2 = 0) :
    (lvKernelAbsorb v params) s = Measure.dirac s := by
  simp only [lvKernelAbsorb, Kernel.ofFunOfCountable, Kernel.coe_mk, h, ↓reduceIte]

/-- If h is harmonic for the LV kernel at interior states, and h is constant
    on consensus classes (h(a,0) = 1 for a > 0, h(0,b) = 0), then h is
    harmonic for the absorbing kernel at ALL states. -/
lemma lvKernelAbsorb_harmonic_everywhere
    (params : LVParams)
    (h : PopState → ℝ) (v : LVVariant)
    [IsMarkovKernel (lvKernel v params)]
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' → ∫ x, h x ∂(lvKernel v params) (a', b') = h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0) :
    ∀ s : PopState, ∫ x, h x ∂(lvKernelAbsorb v params) s = h s := by
  intro ⟨a', b'⟩
  by_cases ha : a' = 0
  · rw [lvKernelAbsorb_consensus v params (a', b') (Or.inl ha)]
    rw [integral_dirac' h (a', b') (measurable_of_countable h).stronglyMeasurable]
  · by_cases hb : b' = 0
    · rw [lvKernelAbsorb_consensus v params (a', b') (Or.inr hb)]
      rw [integral_dirac' h (a', b') (measurable_of_countable h).stronglyMeasurable]
    · rw [lvKernelAbsorb_interior v params (a', b') (by omega) (by omega)]
      exact hHarm a' b' (by omega) (by omega)

/-- Under neutral NSD (α₀=α₁=α, γ₀=γ₁=2α), the total propensity at an interior
    state (a',b') equals n·(β+δ+α·(n-1)) where n = a'+b'.
    This depends ONLY on the total population, not the split. -/
lemma nsd_neutral_totalPropensity_eq
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a' b' : ℕ) :
    lvTotalPropensity params (a', b') =
      (a' + b' : ℝ) * (params.beta + params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) := by
  simp only [lvTotalPropensity, hEq0, hEq1]
  rw [hNeutral]
  ring

/-- The birth-death chain for the total population of a neutral NSD LV chain.
    State n represents total population a'+b' = n.
    For n ≥ 2 (interior states): p(n) + q(n) = 1, no hold.
    States 0 and 1 are absorbing (consensus or extinct). -/
noncomputable def nsdTotalPopBDChain (params : LVParams) : BirthDeathChain where
  p := fun n =>
    if n ≤ 1 then 0
    else params.beta / (params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1))
  q := fun n =>
    if n ≤ 1 then 0
    else (params.delta + params.alpha0 * ((n : ℝ) - 1)) /
      (params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1))
  p_nonneg := fun n => by
    split_ifs <;> [exact le_refl 0; exact div_nonneg (LVParams.beta_nonneg params)
      (by have := LVParams.beta_nonneg params; have := LVParams.delta_nonneg params;
          have := LVParams.alpha0_nonneg params;
          have : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ n));
          positivity)]
  q_nonneg := fun n => by
    split_ifs <;> [exact le_refl 0; exact div_nonneg
      (by have := LVParams.delta_nonneg params; have := LVParams.alpha0_nonneg params;
          have : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ n));
          positivity)
      (by have := LVParams.beta_nonneg params; have := LVParams.delta_nonneg params;
          have := LVParams.alpha0_nonneg params;
          have : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ n));
          positivity)]
  pq_le_one := fun n => by
    by_cases h : n ≤ 1
    · simp [h]
    · push_neg at h
      simp only [show ¬(n ≤ 1) from by omega, ↓reduceIte]
      have hα := LVParams.alpha0_nonneg params
      have hβ := LVParams.beta_nonneg params
      have hδ := LVParams.delta_nonneg params
      have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast (by omega : 1 ≤ n))
      have hden_nn : (0 : ℝ) ≤ params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1) := by
        positivity
      by_cases hden0 : params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1) = 0
      · simp [hden0, div_zero]
      · have hden : 0 < params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1) :=
          lt_of_le_of_ne hden_nn (Ne.symm hden0)
        have : params.beta / (params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1)) +
               (params.delta + params.alpha0 * ((n : ℝ) - 1)) /
                 (params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1)) =
               (params.beta + (params.delta + params.alpha0 * ((n : ℝ) - 1))) /
                 (params.beta + params.delta + params.alpha0 * ((n : ℝ) - 1)) := by
          rw [← add_div]
        rw [this, div_le_one hden]
        linarith
  absorb_zero := by simp

/-- The total-population BD chain has negative drift at large states.
    For n ≥ n₀ where n₀ depends on β/α, drift ≤ -ε < 0.
    Uses: α(n-1) ≥ β+1 for n ≥ n₀, making the numerator β-δ-α(n-1) ≤ -1. -/
lemma nsdTotalPopBDChain_drift (params : LVParams) (hAlpha : 0 < params.alpha0) :
    ∃ n₀ : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ n, n₀ ≤ n → 0 < n →
        (nsdTotalPopBDChain params).p n - (nsdTotalPopBDChain params).q n ≤ -ε := by
  -- Choose n₀ so that α(n₀-1) ≥ β + 1
  set n₀ := Nat.ceil ((params.beta + 1) / params.alpha0) + 2
  have hβ := LVParams.beta_nonneg params
  have hδ := LVParams.delta_nonneg params
  have hn₀_ge2 : 2 ≤ n₀ := by omega
  have hn₀_cast : (1 : ℝ) ≤ (↑n₀ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀_ge2
    linarith
  have hn₀_ge : params.alpha0 * ((↑n₀ : ℝ) - 1) ≥ params.beta + 1 := by
    have h1 : (params.beta + 1) / params.alpha0 ≤ ↑(Nat.ceil ((params.beta + 1) / params.alpha0)) :=
      Nat.le_ceil _
    have h2 : (↑(Nat.ceil ((params.beta + 1) / params.alpha0)) : ℝ) ≤ (↑n₀ : ℝ) - 1 := by
      simp [n₀]; push_cast; linarith
    calc params.alpha0 * ((↑n₀ : ℝ) - 1) ≥ params.alpha0 * ((params.beta + 1) / params.alpha0) := by
          exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (le_of_lt hAlpha)
      _ = params.beta + 1 := by field_simp
  -- den(n₀) and the key gap
  set d₀ := params.beta + params.delta + params.alpha0 * ((↑n₀ : ℝ) - 1)
  have hd₀_pos : (0 : ℝ) < d₀ := by simp only [d₀]; linarith
  have hgap : params.delta + params.alpha0 * ((↑n₀ : ℝ) - 1) - params.beta ≥ 1 := by linarith
  -- ε = (δ + α(n₀-1) - β) / den(n₀) ≥ 1/den(n₀) > 0
  set ε := (params.delta + params.alpha0 * ((↑n₀ : ℝ) - 1) - params.beta) / d₀
  refine ⟨n₀, ε, div_pos (by linarith) hd₀_pos, ?_, ?_⟩
  · rw [div_le_one hd₀_pos]; simp only [d₀]; linarith
  · intro n hn hn_pos
    have hn_ge2 : 2 ≤ n := by omega
    simp only [nsdTotalPopBDChain, show ¬(n ≤ 1) from by omega, ↓reduceIte]
    have hnn₀ : (↑n₀ : ℝ) - 1 ≤ (↑n : ℝ) - 1 := by
      have : (↑n₀ : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
      linarith
    have hden_n : (0 : ℝ) < params.beta + params.delta + params.alpha0 * ((↑n : ℝ) - 1) := by
      linarith [mul_le_mul_of_nonneg_left hnn₀ (le_of_lt hAlpha)]
    -- Key: drift = -1 + 2β/den(n) ≤ -1 + 2β/den(n₀) = -ε
    -- First, rewrite p - q as a single fraction
    have hdrift : params.beta / (params.beta + params.delta + params.alpha0 * ((↑n : ℝ) - 1)) -
        (params.delta + params.alpha0 * ((↑n : ℝ) - 1)) /
          (params.beta + params.delta + params.alpha0 * ((↑n : ℝ) - 1)) =
        -1 + 2 * params.beta / (params.beta + params.delta + params.alpha0 * ((↑n : ℝ) - 1)) := by
      field_simp
      ring
    rw [hdrift]
    have hε_eq : -ε = -1 + 2 * params.beta / d₀ := by
      simp only [ε]; field_simp; ring
    rw [hε_eq]
    -- 2β/den(n) ≤ 2β/den(n₀) since den(n) ≥ den(n₀) and β ≥ 0
    have hden_le : d₀ ≤ params.beta + params.delta + params.alpha0 * ((↑n : ℝ) - 1) := by
      simp only [d₀]; linarith [mul_le_mul_of_nonneg_left hnn₀ (le_of_lt hAlpha)]
    linarith [div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * params.beta)
      hd₀_pos hden_le]

/-- For the NSD kernel from interior state (a',b') with n=a'+b', the total
    population changes by ±1 with probabilities matching `nsdTotalPopBDChain`.
    Key fact: the transition probabilities depend only on n, not the split (a',b').
    Proof uses `nsd_neutral_totalPropensity_eq` to show φ = n·(β+δ+α(n-1)). -/
lemma nsd_kernel_totalPop_marginal
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    (a' b' : ℕ) (ha' : 0 < a') (hb' : 0 < b') :
    let K := lvKernel LVVariant.nonSelfDestructive params
    let n := a' + b'
    K (a', b') {s : PopState | s.1 + s.2 = n + 1} =
      ENNReal.ofReal ((nsdTotalPopBDChain params).p n) ∧
    K (a', b') {s : PopState | s.1 + s.2 + 1 = n} =
      ENNReal.ofReal ((nsdTotalPopBDChain params).q n) := by
  dsimp
  set den : ℝ := params.beta + params.delta +
      params.alpha0 * (((a' : ℝ) + b') - 1) with hden
  have hn_pos_nat : 0 < a' + b' := by omega
  have hn_pos : (0 : ℝ) < (((a' + b' : ℕ) : ℝ)) := by exact_mod_cast hn_pos_nat
  have hn1_pos : (0 : ℝ) < ((a' : ℝ) + b') - 1 := by
    have ha1 : (1 : ℝ) ≤ (a' : ℝ) := Nat.one_le_cast.mpr ha'
    have hb1 : (1 : ℝ) ≤ (b' : ℝ) := Nat.one_le_cast.mpr hb'
    linarith
  have hn1_nonneg : (0 : ℝ) ≤ ((a' : ℝ) + b') - 1 := le_of_lt hn1_pos
  have hinner_nonneg : 0 ≤ params.delta +
      params.alpha0 * (((a' : ℝ) + b') - 1) := by
    have hαterm : 0 ≤ params.alpha0 * (((a' : ℝ) + b') - 1) :=
      mul_nonneg (le_of_lt hAlpha) hn1_nonneg
    linarith [params.delta_nonneg, hαterm]
  have hden_pos : 0 < den := by
    rw [hden]
    have hαterm : 0 < params.alpha0 * (((a' : ℝ) + b') - 1) := mul_pos hAlpha hn1_pos
    linarith [params.beta_nonneg, params.delta_nonneg, hαterm]
  have hφ_eq : lvTotalPropensity params (a', b') = (((a' + b' : ℕ) : ℝ)) * den := by
    simpa [hden] using nsd_neutral_totalPropensity_eq params hNeutral hEq0 hEq1 a' b'
  have hφ_eq' : lvTotalPropensity params (a', b') = (((a' : ℝ) + b')) * den := by
    simpa [Nat.cast_add] using hφ_eq
  have hφ_pos : 0 < lvTotalPropensity params (a', b') := by
    rw [hφ_eq]
    exact mul_pos hn_pos hden_pos
  have hφ : lvTotalPropensity params (a', b') ≠ 0 := ne_of_gt hφ_pos
  have hinvφ_nonneg : 0 ≤ 1 / lvTotalPropensity params (a', b') := by positivity
  set U : Set PopState := {s : PopState | s.1 + s.2 = a' + b' + 1} with hU
  set D : Set PopState := {s : PopState | s.1 + s.2 + 1 = a' + b'} with hD
  have hU_b0 : (a' + 1) + b' = a' + b' + 1 := by omega
  have hU_b1 : a' + (b' + 1) = a' + b' + 1 := by omega
  have hU_d0 : ¬((a' - 1) + b' = a' + b' + 1) := by omega
  have hU_d1 : ¬(a' + (b' - 1) = a' + b' + 1) := by omega
  have hD_b0 : ¬((a' + 1) + b' + 1 = a' + b') := by omega
  have hD_b1 : ¬(a' + (b' + 1) + 1 = a' + b') := by omega
  have hD_d0 : (a' - 1) + b' + 1 = a' + b' := by omega
  have hD_d1 : a' + (b' - 1) + 1 = a' + b' := by omega
  constructor
  · change (lvKernel LVVariant.nonSelfDestructive params) (a', b') U =
      ENNReal.ofReal ((nsdTotalPopBDChain params).p (a' + b'))
    rw [lvKernel_nsd_apply params a' b' hφ, Measure.smul_apply]
    have hβa : 0 ≤ params.beta * a' := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    have hβb : 0 ≤ params.beta * b' := mul_nonneg params.beta_nonneg (Nat.cast_nonneg _)
    simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hU, Set.indicator,
      Set.mem_setOf_eq,
      hU_b0, hU_b1, hU_d0, hU_d1]
    rw [← ENNReal.ofReal_add hβa hβb]
    rw [← ENNReal.ofReal_mul (show 0 ≤ (lvTotalPropensity params (a', b'))⁻¹ by positivity)]
    have hβsum : params.beta * a' + params.beta * b' =
        params.beta * (((a' : ℝ) + b')) := by ring
    rw [hβsum]
    have hnot_le1 : ¬(a' + b' ≤ 1) := by omega
    simp [nsdTotalPopBDChain, hnot_le1]
    rw [← hden]
    have hnum_nonneg : 0 ≤ (lvTotalPropensity params (a', b'))⁻¹ *
        (params.beta * (((a' : ℝ) + b'))) := by
      exact mul_nonneg (by positivity) (mul_nonneg params.beta_nonneg (by positivity))
    have hq_nonneg : 0 ≤ params.beta / den := div_nonneg params.beta_nonneg hden_pos.le
    apply (ENNReal.ofReal_eq_ofReal_iff hnum_nonneg hq_nonneg).2
    rw [hφ_eq']
    have hn_ne : ((a' : ℝ) + b') ≠ 0 := by positivity
    have hden_ne : den ≠ 0 := ne_of_gt hden_pos
    field_simp [hn_ne, hden_ne]
  · change (lvKernel LVVariant.nonSelfDestructive params) (a', b') D =
      ENNReal.ofReal ((nsdTotalPopBDChain params).q (a' + b'))
    rw [lvKernel_nsd_apply params a' b' hφ, Measure.smul_apply]
    have hδa : 0 ≤ params.delta * a' := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have hδb : 0 ≤ params.delta * b' := mul_nonneg params.delta_nonneg (Nat.cast_nonneg _)
    have hα0ab : 0 ≤ params.alpha0 * a' * b' :=
      mul_nonneg (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hα1ab : 0 ≤ params.alpha1 * a' * b' :=
      mul_nonneg (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hga : 0 ≤ (a' : ℝ) * ((a' : ℝ) - 1) / 2 := by
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr ha'))) (by norm_num)
    have hgb : 0 ≤ (b' : ℝ) * ((b' : ℝ) - 1) / 2 := by
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (sub_nonneg.mpr (Nat.one_le_cast.mpr hb'))) (by norm_num)
    have hγ0 : 0 ≤ params.gamma0 * (a' * (a' - 1) / 2) := mul_nonneg params.gamma0_nonneg hga
    have hγ1 : 0 ≤ params.gamma1 * (b' * (b' - 1) / 2) := mul_nonneg params.gamma1_nonneg hgb
    simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hD, Set.indicator,
      Set.mem_setOf_eq,
      hD_b0, hD_b1, hD_d0, hD_d1]
    have hsum1 : 0 ≤ params.delta * a' + params.delta * b' := by linarith [hδa, hδb]
    have hsum2 : 0 ≤ params.delta * a' + params.delta * b' + params.alpha0 * a' * b' := by
      linarith [hsum1, hα0ab]
    have hsum3 : 0 ≤ params.delta * a' + params.delta * b' +
        params.alpha0 * a' * b' + params.alpha1 * a' * b' := by
      linarith [hsum2, hα1ab]
    have hsum4 : 0 ≤ params.delta * a' + params.delta * b' + params.alpha0 * a' * b' +
        params.alpha1 * a' * b' + params.gamma0 * (a' * (a' - 1) / 2) := by
      linarith [hsum3, hγ0]
    rw [← ENNReal.ofReal_add hδa hδb,
      ← ENNReal.ofReal_add hsum1 hα0ab,
      ← ENNReal.ofReal_add hsum2 hα1ab,
      ← ENNReal.ofReal_add hsum3 hγ0,
      ← ENNReal.ofReal_add hsum4 hγ1]
    rw [← ENNReal.ofReal_mul (show 0 ≤ (lvTotalPropensity params (a', b'))⁻¹ by positivity)]
    have hEq1' : params.gamma1 = 2 * params.alpha0 := by
      simpa [hNeutral] using hEq1
    have hnum_eq : params.delta * a' + params.delta * b' + params.alpha0 * a' * b' +
        params.alpha1 * a' * b' + params.gamma0 * (a' * (a' - 1) / 2) +
        params.gamma1 * (b' * (b' - 1) / 2) =
        (((a' : ℝ) + b')) *
          (params.delta + params.alpha0 * (((a' : ℝ) + b') - 1)) := by
      rw [← hNeutral, hEq0, hEq1']
      ring_nf
    rw [hnum_eq]
    have hnot_le1 : ¬(a' + b' ≤ 1) := by omega
    simp [nsdTotalPopBDChain, hnot_le1]
    rw [← hden]
    have hnum_nonneg : 0 ≤ (lvTotalPropensity params (a', b'))⁻¹ *
        ((((a' : ℝ) + b')) *
          (params.delta + params.alpha0 * (((a' : ℝ) + b') - 1))) := by
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hinner_nonneg)
    have hq_nonneg : 0 ≤
        (params.delta + params.alpha0 * (((a' : ℝ) + b') - 1)) / den :=
      div_nonneg hinner_nonneg hden_pos.le
    apply (ENNReal.ofReal_eq_ofReal_iff hnum_nonneg hq_nonneg).2
    rw [hφ_eq']
    have hn_ne : ((a' : ℝ) + b') ≠ 0 := by positivity
    have hden_ne : den ≠ 0 := ne_of_gt hden_pos
    field_simp [hn_ne, hden_ne]

/-! ## Single-species embedded chains (for intraspecific-only analysis)

When both interspecific competition rates are zero (α₀=α₁=0), the two-species
LV dynamics decomposes: the trajectory of each species (looking only at events
that affect that species) is a single-species birth-death chain independent of
the other species count. These chains are key for the paper's proof of the
intraspecific-only constant failure probability (Section 8.2 of paper.tex).

The paper uses the CONTINUOUS-TIME version (Gillespie/CTMC), where independence
holds exactly (species' clock rates are independent Poisson processes when α=0).
In discrete time, the two species are NOT marginally independent (the total
propensity in the denominator couples them). However, we can still define the
single-species chain and prove it is a NiceChain, which yields bounds needed
for the Lean formalization.
-/

/-- The single-species birth-death chain for **species 0** when interspecific
    competition is absent (α₀=α₁=0).

    In the LV system with α=0, species 0's count evolves independently of
    species 1 (in continuous time). The embedded discrete-time chain for
    species 0 has transition probabilities:
    - `p(n) = β·n / (β·n + δ·n + γ₀·n·(n-1)/2)` [birth]
    - `q(n) = (δ·n + γ₀·n·(n-1)/2) / (β·n + δ·n + γ₀·n·(n-1)/2)` [death]

    For n ≥ 1 and after cancelling n:
    - `p(n) = β / (β + δ + γ₀·(n-1)/2)` → 0 as n → ∞ (so p ≤ C/n)
    - `q(n) = (δ + γ₀·(n-1)/2) / (β + δ + γ₀·(n-1)/2)` ≥ δ/(β+δ) > 0

    This chain is a NiceChain (see `species0Chain_isNice`) when δ > 0 and γ₀ > 0.
    This gives mean extinction time Θ(n) from initial count n.

    **Paper connection**: Section 8.2, `lemma:continuous-extinction` — the
    continuous-time extinction time has mean O(1) (due to quadratic death rate
    Θ(n²)); the discrete-time embedded chain has Θ(n) mean extinction, which
    gives a weaker but still positive probability lower bound for fixed (a,b). -/
noncomputable def species0Chain (params : LVParams) : BirthDeathChain where
  p := fun n =>
    if n = 0 then 0
    else params.beta / (params.beta + params.delta + params.gamma0 * ((n : ℝ) - 1) / 2)
  q := fun n =>
    if n = 0 then 0
    else (params.delta + params.gamma0 * ((n : ℝ) - 1) / 2) /
         (params.beta + params.delta + params.gamma0 * ((n : ℝ) - 1) / 2)
  p_nonneg := fun n => by
    split_ifs with h
    · exact le_refl 0
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero h
      have hβ := LVParams.beta_nonneg params
      have hδ := LVParams.delta_nonneg params
      have hγ := LVParams.gamma0_nonneg params
      have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 :=
        sub_nonneg.mpr (by exact_mod_cast hn_pos)
      apply div_nonneg hβ
      have : (0 : ℝ) ≤ params.gamma0 * ((n : ℝ) - 1) / 2 := by positivity
      linarith
  q_nonneg := fun n => by
    split_ifs with h
    · exact le_refl 0
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero h
      have hβ := LVParams.beta_nonneg params
      have hδ := LVParams.delta_nonneg params
      have hγ := LVParams.gamma0_nonneg params
      have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 :=
        sub_nonneg.mpr (by exact_mod_cast hn_pos)
      apply div_nonneg
      · have : (0 : ℝ) ≤ params.gamma0 * ((n : ℝ) - 1) / 2 := by positivity
        linarith
      · have : (0 : ℝ) ≤ params.gamma0 * ((n : ℝ) - 1) / 2 := by positivity
        linarith
  pq_le_one := fun n => by
    by_cases h0 : n = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      have hβ := LVParams.beta_nonneg params
      have hδ := LVParams.delta_nonneg params
      have hγ := LVParams.gamma0_nonneg params
      have hn_pos : 0 < n := Nat.pos_of_ne_zero h0
      have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 :=
        sub_nonneg.mpr (by exact_mod_cast hn_pos)
      have hγn : (0 : ℝ) ≤ params.gamma0 * ((n : ℝ) - 1) / 2 := by positivity
      set den := params.beta + params.delta + params.gamma0 * ((n : ℝ) - 1) / 2
      have hden_nn : 0 ≤ den := by simp [den]; linarith
      by_cases hden0 : den = 0
      · simp [hden0, div_zero]
      · have hden : 0 < den := lt_of_le_of_ne hden_nn (Ne.symm hden0)
        have heq : params.beta / den + (params.delta + params.gamma0 * ((n : ℝ) - 1) / 2) / den =
               (params.beta + (params.delta + params.gamma0 * ((n : ℝ) - 1) / 2)) / den := by
          rw [← add_div]
        rw [heq, div_le_one hden]
        have : den = params.beta + params.delta + params.gamma0 * ((n : ℝ) - 1) / 2 := rfl
        linarith [hγn]
  absorb_zero := by simp

/-- The species 0 chain has a positive lower bound on q for all n ≥ 1.
    Specifically, `q(n) ≥ δ/(β+δ)` when δ > 0.

    This is because for n=1, the intraspecific term γ₀·(n-1)/2 = 0, so
    q(1) = δ/(β+δ). For n ≥ 2, the intraspecific term is positive,
    making q(n) ≥ q(1).

    **Paper connection**: This provides D = δ/(β+δ) > 0 for the NiceChain
    instance, giving mean extinction time O(n) from initial count n. -/
lemma species0Chain_q_lower_bound
    (params : LVParams)
    (hDelta : 0 < params.delta) (hBeta : 0 ≤ params.beta)
    (hGamma0 : 0 ≤ params.gamma0)
    (n : ℕ) (hn : 0 < n) :
    params.delta / (params.beta + params.delta) ≤ (species0Chain params).q n := by
  simp only [species0Chain, Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  have hδ := hDelta.le
  have hβ := hBeta
  have hγ := hGamma0
  have hn1 : (0 : ℝ) ≤ ((n : ℝ) - 1) / 2 :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hn)) two_pos.le
  set den := params.beta + params.delta + params.gamma0 * ((n : ℝ) - 1) / 2
  have hden : 0 < params.beta + params.delta := by linarith
  have hdenbd : 0 < den := by
    simp [den]; linarith [mul_nonneg hγ hn1]
  have hn1r : (0 : ℝ) ≤ params.gamma0 * ((n : ℝ) - 1) / 2 := by
    apply div_nonneg _ two_pos.le
    exact mul_nonneg hγ (sub_nonneg.mpr (by exact_mod_cast hn))
  -- Suffices to show: δ * den ≤ (δ+γ(n-1)/2) * (β+δ)
  -- Expanding: δβ + δ² + δγ(n-1)/2 ≤ δβ + δ² + γ(n-1)/2·β + γ(n-1)/2·δ
  -- i.e., 0 ≤ γ(n-1)/2·β, which holds since β,γ,n-1 ≥ 0
  have key : params.delta * den ≤
      (params.delta + params.gamma0 * ((n:ℝ)-1)/2) * (params.beta + params.delta) := by
    simp only [den]; nlinarith [mul_nonneg hβ hn1r]
  have lhs_eq : params.delta / (params.beta + params.delta) =
      params.delta * den / ((params.beta + params.delta) * den) := by
    field_simp
  have rhs_eq : (params.delta + params.gamma0 * ((n:ℝ)-1)/2) / den =
      (params.delta + params.gamma0 * ((n:ℝ)-1)/2) * (params.beta + params.delta) /
      ((params.beta + params.delta) * den) := by
    field_simp
  rw [lhs_eq, rhs_eq]
  apply div_le_div_of_nonneg_right key (mul_pos hden hdenbd).le

/-- The species 0 chain has p(n) ≤ C/n for C = 2β/γ₀ when γ₀ > 0.

    From p(n) = β / (β + δ + γ₀·(n-1)/2):
    n · p(n) = n·β / (β + δ + γ₀·(n-1)/2)
             ≤ n·β / (γ₀·(n-1)/2)      [drop positive terms in denominator]
             = 2β·n / (γ₀·(n-1))
             → 2β/γ₀  as n → ∞.

    More precisely, n · p(n) ≤ 2β/γ₀ + 2β/γ₀ = 4β/γ₀ for all n ≥ 2.
    This bounds p(n) ≤ (4β/γ₀)/n, giving C = 4β/γ₀ + 1 (to handle n=1). -/
lemma species0Chain_p_upper_bound
    (params : LVParams)
    (hGamma0 : 0 < params.gamma0)
    (n : ℕ) (hn : 0 < n) :
    (species0Chain params).p n ≤ (2 * params.beta / params.gamma0 + 1) / n := by
  simp only [species0Chain, Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  have hβ := LVParams.beta_nonneg params
  have hδ := LVParams.delta_nonneg params
  have hγ := hGamma0.le
  have hγ' := hGamma0
  -- If β = 0, then p = 0 ≤ RHS which is ≥ 0
  by_cases hβ0 : params.beta = 0
  · simp only [hβ0, zero_div, zero_add, mul_zero, zero_add]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hβ' : 0 < params.beta := lt_of_le_of_ne (LVParams.beta_nonneg params) (Ne.symm hβ0)
  -- Bound: p(n) = β / (β + δ + γ·(n-1)/2) ≤ β / (γ·(n-1)/2) for n ≥ 2
  -- For n=1: p(1) = β/(β+δ) ≤ β/1 ≤ (2β/γ+1)/1 ✓ (as β/(β+δ) ≤ 1 ≤ 2β/γ+1)
  by_cases hn1 : n = 1
  · simp only [hn1, Nat.cast_one]
    have hbd : 0 < params.beta + params.delta := by linarith
    have hkey : params.beta / (params.beta + params.delta + params.gamma0 * ((1:ℝ) - 1) / 2) ≤ 1 := by
      have : params.beta + params.delta + params.gamma0 * ((1:ℝ) - 1) / 2 = params.beta + params.delta := by
        ring
      rw [this, div_le_one hbd]; linarith
    linarith [div_pos (mul_pos two_pos hβ') hγ']
  · have hn2 : 2 ≤ n := by omega
    have hn1' : (1 : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hγn1 : 0 < params.gamma0 * ((n : ℝ) - 1) / 2 := by positivity
    have hden : 0 < params.beta + params.delta + params.gamma0 * ((n : ℝ) - 1) / 2 :=
      by linarith
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    -- Need: β/den ≤ (2β/γ+1)/n, i.e., β*n ≤ (2β/γ+1)*den
    -- Key: (2β/γ)*γ(n-1)/2 = β(n-1) and (2β/γ+1)*den ≥ β(n-1) + den ≥ β*n
    have hprod : (2 * params.beta / params.gamma0) * (params.gamma0 * ((n:ℝ)-1) / 2) =
                 params.beta * ((n:ℝ) - 1) := by field_simp
    have key : params.beta * n ≤ (2 * params.beta / params.gamma0 + 1) *
               (params.beta + params.delta + params.gamma0 * ((n:ℝ)-1) / 2) := by
      nlinarith [mul_pos hβ' hn_pos,
                 mul_pos (div_pos (mul_pos two_pos hβ') hγ') hγn1,
                 mul_nonneg hδ hn_pos.le]
    have key2 : params.beta / (params.beta + params.delta + params.gamma0 * ((n:ℝ)-1) / 2) ≤
                (2 * params.beta / params.gamma0 + 1) / n := by
      rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hn_pos]
      linarith [key]
    exact key2

/-- When δ > 0 and γ₀ > 0 and β ≥ 0, the species 0 chain is a NiceChain with:
    - D = δ / (β + δ) > 0  (lower bound on q)
    - C = 2β/γ₀ + 1       (bound for n·p(n))

    This means the mean extinction time from initial count n is Θ(n).
    Combined with `kernelIter_path_lower`, this gives the key positivity bound
    needed for `intraspecific_only_constant_failure` (paper Section 8.2). -/
noncomputable def species0Chain_isNice
    (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma0 : 0 < params.gamma0) : NiceChain where
  toBirthDeathChain := species0Chain params
  C := 2 * params.beta / params.gamma0 + 1
  D := params.delta / (params.beta + params.delta)
  C_pos := by
    have := LVParams.beta_nonneg params
    positivity
  D_pos := by
    have := LVParams.beta_nonneg params
    positivity
  p_le := fun n hn => species0Chain_p_upper_bound params hGamma0 n hn
  q_ge := fun n hn => species0Chain_q_lower_bound params hDelta (LVParams.beta_nonneg params)
                        hGamma0.le n hn
end LVConsensus
