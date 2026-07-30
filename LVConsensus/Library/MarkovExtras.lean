import LVConsensus.MarkovLib

/-!
# Markov library extras

General results about birth-death chains, Markov kernels and path measures that
were proved in the course of this project but that **no paper-facing result
depends on**.  They are kept because a follow-up development in this direction
would plausibly reuse them.

They live here rather than in `MarkovLib.lean` so that `MarkovLib.lean` contains
only material that is load-bearing for the paper results.  This file is imported
by `LVConsensus.lean`, so everything below is compiled by `lake build` and
scanned by `check_sorry.sh`; it cannot rot silently.

Grouped by topic: harmonic-integral identities for `bdKernel`, `kernelIter` and
`homogeneousPathMeasure`; birth-death drift and superharmonicity; absorption
monotonicity for `kernelIter`; path-measure positivity and absorbing gaps; a
Markov inequality and survival monotonicity for birth-death chains; NSD neutral
harmonicity and weight identities; forced-absorption chains; a `WhpTailBound`
comparison; SD absorbing-state iterates and SD neutral harmonicity;
`lvKernelAbsorb` harmonic and absorption lemmas; and a survival comparison
between the NSD consensus chain and a dominating birth-death chain.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

/-- If `f` is harmonic for the BD kernel at state `n`, then `∫ f ∂K(n) = f(n)`. -/
lemma bdKernel_harmonic_integral (N : BirthDeathChain) (n : ℕ) (f : ℕ → ℝ)
    (hHarm : N.p n * f (n + 1) + N.q n * f (n - 1) + holdProb N n * f n = f n) :
    ∫ x, f x ∂(bdKernel N n) = f n := by
  rw [bdKernel_integral]; exact hHarm

/-- Concentrated harmonic integral: if K^n(s₀) concentrates on Sₙ and h is
    harmonic on Sₙ for each n, then ∫ h dK^n = h(s₀). -/
lemma kernelIter_harmonic_integral_concentrated
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (h : α → ℝ) (s₀ : α)
    (S : ℕ → Set α)
    (hConc : ∀ n, (kernelIter K n) s₀ (S n)ᶜ = 0)
    (hHarm : ∀ n, ∀ x ∈ S n, ∫ y, h y ∂K x = h x)
    (hInt : ∀ (n : ℕ), Integrable h ((kernelIter K n) s₀)) :
    ∀ (n : ℕ), ∫ x, h x ∂(kernelIter K n) s₀ = h s₀ := by
  intro n
  induction n with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    exact integral_dirac' h s₀ (measurable_of_countable h).stronglyMeasurable
  | succ n ih =>
    rw [kernelIter_succ]
    have hMK : IsMarkovKernel (kernelIter K n) := kernelIter_isMarkov n
    rw [Kernel.integral_comp (hInt (n + 1))]
    have hae : (fun x => ∫ y, h y ∂K x) =ᵐ[(kernelIter K n) s₀] h := by
      rw [Filter.EventuallyEq, ae_iff]
      apply le_antisymm _ zero_le
      calc (kernelIter K n s₀) {x | (fun x => ∫ y, h y ∂K x) x ≠ h x}
          ≤ (kernelIter K n s₀) (S n)ᶜ := by
            apply measure_mono; intro x hx hxS; exact hx (hHarm n x hxS)
        _ = 0 := hConc n
    rw [integral_congr_ae hae]; exact ih

/-- If h is harmonic for K, then ∫ h(ω(n)) dP = h(s₀) for all n on path space. -/
lemma homogeneousPathMeasure_harmonic_integral
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (h : α → ℝ) (s₀ : α)
    (hHarm : ∀ s, ∫ x, h x ∂K s = h s)
    (hInt : ∀ (n : ℕ), Integrable h ((kernelIter K n) s₀))
    (n : ℕ) :
    ∫ ω, h (ω n) ∂(homogeneousPathMeasure (Measure.dirac s₀) K) = h s₀ := by
  have hmeas : Measurable (fun ω : ℕ → α => ω n) := measurable_pi_apply n
  have hh : Measurable h := measurable_of_countable h
  calc ∫ ω, h (ω n) ∂(homogeneousPathMeasure (Measure.dirac s₀) K)
      = ∫ x, h x ∂((homogeneousPathMeasure (Measure.dirac s₀) K).map (fun ω => ω n)) := by
        rw [integral_map hmeas.aemeasurable hh.aestronglyMeasurable]
    _ = ∫ x, h x ∂(kernelIter K n) s₀ := by rw [homogeneousPathMeasure_dirac_marginal]
    _ = h s₀ := kernelIter_harmonic_integral K h s₀ hHarm hInt n

/-- One-step drift of the identity function at state `n` for a birth-death chain:
    `E[X₁ - X₀ | X₀ = n] = p(n) - q(n)`. -/
lemma bd_drift_identity (N : BirthDeathChain) (n : ℕ) :
    (N.p n : ℝ) * ((n : ℝ) + 1) + N.q n * ((n : ℝ) - 1) +
      holdProb N n * (n : ℝ) = (n : ℝ) + N.p n - N.q n := by
  simp only [holdProb]
  ring

/-- The BD kernel is superharmonic for the identity when drift is nonpositive:
    if `p(n) ≤ q(n)` then `∫ x ∂K(n) ≤ n`. -/
lemma bd_kernel_superharmonic_id (N : BirthDeathChain) (n : ℕ) (hn : 0 < n)
    (hDrift : N.p n ≤ N.q n) :
    ∫ x, (x : ℝ) ∂(bdKernel N n) ≤ n := by
  rw [bd_kernel_integral_id N n hn]; linarith

/-- From state `m`, the probability of reaching 0 in `m` steps is at least
    `∏_{j=1}^{m} q(j)`. This is because each down-step has probability `q(j)`. -/
lemma kernelIter_bd_absorption_lower
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (m : ℕ) :
    (∏ j ∈ Finset.range m, ENNReal.ofReal (N.q (j + 1))) ≤
      (kernelIter (bdKernel N) m) m {0} := by
  induction m with
  | zero =>
    simp [kernelIter_zero, ProbabilityTheory.Kernel.id_apply,
          Measure.dirac_apply' _ (measurableSet_singleton _)]
  | succ m ih =>
    rw [kernelIter_succ_right, ProbabilityTheory.Kernel.comp_apply]
    rw [Measure.bind_apply (measurableSet_singleton 0)
        (ProbabilityTheory.Kernel.measurable
          (kernelIter (bdKernel N) m)).aemeasurable]
    rw [Finset.prod_range_succ]
    have hdown : bdKernel N (m + 1) {m} =
        ENNReal.ofReal (N.q (m + 1)) := by
      have : bdKernel N (m + 1) {(m + 1) - 1} =
          ENNReal.ofReal (N.q (m + 1)) :=
        bdKernel_down_singleton N (m + 1) (by omega)
      simpa using this
    calc (∏ j ∈ Finset.range m, ENNReal.ofReal (N.q (j + 1))) *
            ENNReal.ofReal (N.q (m + 1))
        ≤ (kernelIter (bdKernel N) m) m {0} *
            ENNReal.ofReal (N.q (m + 1)) :=
          mul_le_mul_of_nonneg_right ih zero_le
      _ = (kernelIter (bdKernel N) m) m {0} *
            bdKernel N (m + 1) {m} := by rw [hdown]
      _ ≤ ∫⁻ j, (kernelIter (bdKernel N) m) j {0}
              ∂(bdKernel N (m + 1)) :=
          lintegral_ge_singleton_mul _ m _

/-- Absorption probability is monotone: once absorbed, the chain stays at 0.
    Formally, `K^t(n₀)({0}) ≤ K^{t+s}(n₀)({0})` for all `s`. -/
lemma kernelIter_bd_absorption_mono (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t s : ℕ) :
    (kernelIter (bdKernel N) t) n₀ {0} ≤
      (kernelIter (bdKernel N) (t + s)) n₀ {0} := by
  rw [kernelIter_add, ProbabilityTheory.Kernel.comp_apply]
  rw [Measure.bind_apply (measurableSet_singleton 0)
      (ProbabilityTheory.Kernel.measurable
        (kernelIter (bdKernel N) s)).aemeasurable]
  have h0 : (kernelIter (bdKernel N) s) 0 {0} = 1 := by
    rw [kernelIter_bdKernel_zero]
    simp [Measure.dirac_apply' _ (measurableSet_singleton _)]
  calc (kernelIter (bdKernel N) t) n₀ {0}
      = 1 * (kernelIter (bdKernel N) t) n₀ {0} := by ring
    _ = (kernelIter (bdKernel N) s) 0 {0} *
          (kernelIter (bdKernel N) t) n₀ {0} := by rw [h0]
    _ ≤ ∫⁻ j, (kernelIter (bdKernel N) s) j {0}
            ∂(kernelIter (bdKernel N) t) n₀ :=
        lintegral_ge_singleton_mul _ 0 _

/-- P(X_t ≠ 0) = 1 - K^t(n₀)({0}). -/
lemma bdPathMeasure_nonzero_at
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    bdPathMeasure N n₀ {ω | ω t ≠ 0} = 1 - (kernelIter (bdKernel N) t) n₀ {0} := by
  have hset : {ω : ℕ → ℕ | ω t ≠ 0} = {ω | ω t ∈ ({0} : Set ℕ)ᶜ} := by
    ext ω; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hset, bdPathMeasure_coord_eq N n₀ t _ (MeasurableSet.compl (measurableSet_singleton _))]
  have hfin : (kernelIter (bdKernel N) t) n₀ {0} ≠ ⊤ := by
    haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
      (kernelIter_isMarkov t).isProbabilityMeasure n₀
    exact measure_ne_top _ _
  rw [measure_compl (measurableSet_singleton _) hfin]
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    (kernelIter_isMarkov t).isProbabilityMeasure n₀
  rw [measure_univ]

/-- Path-level absorption: P(ω(s) = 0 ∧ ω(t) ≠ 0) = 0 for s ≤ t.
    Once the chain is at 0, it stays at 0 (at the path-measure level). -/
lemma bdPathMeasure_absorbing_gap
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (s t : ℕ) (hst : s ≤ t) :
    bdPathMeasure N n₀ {ω | ω s = 0 ∧ ω t ≠ 0} = 0 := by
  induction t with
  | zero =>
    have hs0 : s = 0 := by omega
    subst hs0
    convert measure_empty (μ := bdPathMeasure N n₀); ext ω; simp
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hst with rfl | hst'
    · convert measure_empty (μ := bdPathMeasure N n₀); ext ω; simp
    · apply le_antisymm _ zero_le
      calc bdPathMeasure N n₀ {ω | ω s = 0 ∧ ω (t + 1) ≠ 0}
          ≤ bdPathMeasure N n₀ ({ω | ω s = 0 ∧ ω t ≠ 0} ∪
              {ω | ω t = 0 ∧ ω (t + 1) ≠ 0}) :=
            measure_mono (fun ω ⟨h1, h2⟩ => by
              by_cases h3 : ω t = 0
              · right; exact ⟨h3, h2⟩
              · left; exact ⟨h1, h3⟩)
        _ ≤ _ + _ := measure_union_le _ _
        _ = 0 := by rw [ih (by omega : s ≤ t), bdPathMeasure_absorbing_step]; ring

/-- Markov inequality for kernel iterates: P(X_t ≥ k) ≤ (n₀ + t) / k. -/
lemma bd_markov_ineq
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) (k : ℕ) (hk : 0 < k) :
    (kernelIter (bdKernel N) t) n₀ {j | k ≤ j} ≤
    (↑n₀ + ↑t : ℝ≥0∞) / ↑k := by
  have hk_ne : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hk_ne_top : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
  rw [ENNReal.le_div_iff_mul_le (Or.inl hk_ne) (Or.inl hk_ne_top)]
  have hmeas : MeasurableSet {j : ℕ | k ≤ j} := (Set.to_countable _).measurableSet
  calc (kernelIter (bdKernel N) t n₀) {j | k ≤ j} * ↑k
      = ↑k * (kernelIter (bdKernel N) t n₀) {j | k ≤ j} := mul_comm _ _
    _ = ∫⁻ _ in {j : ℕ | k ≤ j}, (k : ℝ≥0∞)
          ∂(kernelIter (bdKernel N) t) n₀ := by
        rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ j in {j : ℕ | k ≤ j}, (j : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ := by
        apply lintegral_mono_ae; rw [ae_restrict_iff' hmeas]
        exact .of_forall fun j (hj : k ≤ j) => by exact_mod_cast hj
    _ ≤ ∫⁻ j, (j : ℝ≥0∞) ∂(kernelIter (bdKernel N) t) n₀ :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ↑n₀ + ↑t := bd_lintegral_id_bound N n₀ t

/-- Survival probability is non-increasing: P(X_{t+1} ≠ 0) ≤ P(X_t ≠ 0). -/
lemma bd_survival_antimono
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (t : ℕ) :
    (kernelIter (bdKernel N) (t + 1)) n₀ {0}ᶜ ≤
    (kernelIter (bdKernel N) t) n₀ {0}ᶜ := by
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n₀) :=
    (kernelIter_isMarkov t).isProbabilityMeasure n₀
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) (t + 1)) n₀) :=
    (kernelIter_isMarkov (t + 1)).isProbabilityMeasure n₀
  have h0 : MeasurableSet ({0} : Set ℕ) := measurableSet_singleton 0
  rw [measure_compl h0 (measure_ne_top _ _), measure_compl h0 (measure_ne_top _ _)]
  simp only [measure_univ]
  exact tsub_le_tsub_left (bd_absorption_mono N n₀ t) 1

/-- When drift ≤ 0 globally, P(X_t ≥ 1) ≤ n₀ for all t. -/
lemma bd_survival_le_init_global
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (n₀ : ℕ) (hDrift : ∀ n, 0 < n → N.p n ≤ N.q n) (t : ℕ) :
    ((kernelIter (bdKernel N) t) n₀ {0}ᶜ).toReal ≤ ↑n₀ :=
  (bd_survival_le_expected N n₀ t).trans (bd_expected_nonincreasing N n₀ hDrift t)

/-- Main harmonicity identity: for NSD with α₀=α₁=α and γ₀=γ₁=2α,
    the weighted sum of h(x,y) = x/(x+y) at the four target states
    equals φ · h(a,b), where φ is the total propensity.

    The four target groups are:
    - Birth0 (weight β·a) → (a+1,b): h = (a+1)/(a+b+1)
    - Birth1 (weight β·b) → (a,b+1): h = a/(a+b+1)
    - Down0 (weight a·(δ+α(a+b-1))) → (a-1,b): h = (a-1)/(a+b-1)
    - Down1 (weight b·(δ+α(a+b-1))) → (a,b-1): h = a/(a+b-1)
-/
lemma nsd_neutral_harmonicity (a b α β δ : ℝ)
    (hn : a + b ≠ 0) (hn1 : a + b + 1 ≠ 0) (hn_1 : a + b - 1 ≠ 0) :
    β * a * ((a + 1) / (a + b + 1)) + β * b * (a / (a + b + 1)) +
    a * (δ + α * (a + b - 1)) * ((a - 1) / (a + b - 1)) +
    b * (δ + α * (a + b - 1)) * (a / (a + b - 1)) =
    (a + b) * (β + δ + α * (a + b - 1)) * (a / (a + b)) := by
  field_simp
  ring

/-- Superharmonicity excess: when γ ≥ 2α and a ≥ b, the function h(a,b) = a/(a+b)
    is superharmonic. The difference φ·h − (weighted sum) equals
    (γ − 2α) · a · b · (a − b) / (2 · (a+b) · (a+b−1)) ≥ 0.

    This lemma shows the numerator of the excess is nonneg. -/
lemma nsd_superharmonicity_excess_nonneg (a b α γ : ℝ)
    (hγ : 2 * α ≤ γ) (hab : b ≤ a) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (γ - 2 * α) * a * b * (a - b) := by
  have h1 : 0 ≤ γ - 2 * α := by linarith
  have h2 : 0 ≤ a - b := by linarith
  positivity

/-- Combined weight to state (a-1, b) in the NSD kernel with α₀=α₁=α:
    Death0 + Inter1 + Intra0 = a · (δ + α·b + γ₀·(a-1)/2). -/
lemma nsd_weight_down0 (a b α δ γ₀ : ℝ) :
    δ * a + α * a * b + γ₀ * (a * (a - 1) / 2) =
    a * (δ + α * b + γ₀ * (a - 1) / 2) := by ring

/-- Combined weight to state (a, b-1) in the NSD kernel with α₀=α₁=α:
    Death1 + Inter0 + Intra1 = b · (δ + α·a + γ₁·(b-1)/2). -/
lemma nsd_weight_down1 (a b α δ γ₁ : ℝ) :
    δ * b + α * a * b + γ₁ * (b * (b - 1) / 2) =
    b * (δ + α * a + γ₁ * (b - 1) / 2) := by ring

/-- For neutral NSD (γ₀=γ₁=2α), the combined weight to (a-1,b) simplifies
    to a · (δ + α · (a+b-1)). -/
lemma nsd_neutral_weight_down0 (a b α δ : ℝ) :
    δ * a + α * a * b + (2 * α) * (a * (a - 1) / 2) =
    a * (δ + α * (a + b - 1)) := by ring

/-- For neutral NSD (γ₀=γ₁=2α), the combined weight to (a,b-1) simplifies
    to b · (δ + α · (a+b-1)). -/
lemma nsd_neutral_weight_down1 (a b α δ : ℝ) :
    δ * b + α * a * b + (2 * α) * (b * (b - 1) / 2) =
    b * (δ + α * (a + b - 1)) := by ring

/-- For NSD with β=δ=0, symmetric α, γ ≥ 2α, and a ≥ b, the weighted sum
    of h at target states is ≤ φ·h(a,b). -/
lemma nsd_superharmonic_weighted_le (a b α γ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a)
    (hα : 0 ≤ α) (hγα : 2 * α ≤ γ)
    (hn : a + b ≠ 0) (hn1 : a + b - 1 ≠ 0) (hab1 : 1 ≤ a + b) :
    (α * a * b + γ * a * (a - 1) / 2) * ((a - 1) / (a + b - 1)) +
    (α * a * b + γ * b * (b - 1) / 2) * (a / (a + b - 1)) ≤
    (2 * α * a * b + γ * (a * (a - 1) + b * (b - 1)) / 2) * (a / (a + b)) := by
  have hexcess := nsd_superharmonic_excess_identity a b α γ hn hn1
  linarith [show 0 ≤ (γ - 2 * α) * a * b * (a - b) / (2 * (a + b) * (a + b - 1)) from by
    apply div_nonneg
    · have : 0 ≤ γ - 2 * α := by linarith
      have : 0 ≤ a - b := by linarith
      positivity
    · have : 0 < a + b := by linarith
      have : 0 < a + b - 1 := lt_of_le_of_ne (by linarith) (Ne.symm hn1)
      positivity]

/-- The forced-absorb chain's kernel agrees with N's kernel at states > n₀. -/
lemma bdKernel_forcedAbsorb_eq_above (N : BirthDeathChain) (n₀ y : ℕ) (hy : n₀ < y) :
    bdKernel (bdChainForcedAbsorb N n₀) y = bdKernel N y := by
  have hp := bdChainForcedAbsorb_p_above N n₀ y hy
  have hq := bdChainForcedAbsorb_q_above N n₀ y hy
  have hh : holdProb (bdChainForcedAbsorb N n₀) y = holdProb N y := by
    simp [holdProb, hp, hq]
  ext S
  rw [bdKernel_apply, bdKernel_apply]
  rw [hp, hq, hh]

/-- The forced-absorb chain's survival bound: P(X'_t > 0 | X'_0 = m) ≤ c^m · ρ^t
    where c = 1 + ε/4, ρ = 1 - ε²/8. Uses full drift of the forced-absorb chain. -/
lemma bdChainForcedAbsorb_survival (N : BirthDeathChain) (ε : ℝ) (hε : 0 < ε)
    (n₀ : ℕ) (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (t m : ℕ) (hm : 0 < m) :
    (kernelIter (bdKernel (bdChainForcedAbsorb N n₀)) t) m {x | 0 < x} ≤
    ENNReal.ofReal ((1 + ε / 4) ^ m) * ENNReal.ofReal (1 - ε ^ 2 / 8) ^ t := by
  -- First check if ε ≤ 1 (otherwise the drift hypothesis is vacuously false)
  by_cases hε1 : ε ≤ 1
  · exact bd_survival_exp_decay (bdChainForcedAbsorb N n₀) ε hε
      (bdChainForcedAbsorb_full_drift N ε hε n₀ hDrift hε1) t m hm
  · -- ε > 1: drift hypothesis is vacuously false (p - q ≥ -1 always)
    push_neg at hε1
    exfalso
    -- For any positive state n, p(n) - q(n) ≥ -(p(n) + q(n)) ≥ -1 > -ε
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
    · have := hDrift 1 (Nat.zero_le _) Nat.one_pos
      have := N.p_nonneg 1; have := N.pq_le_one 1; linarith
    · have := hDrift n₀ le_rfl hn₀
      have := N.p_nonneg n₀; have := N.pq_le_one n₀; linarith

/-- WhpTailBound is monotone: if tail₁ ≤ tail₂ pointwise, the bound transfers. -/
lemma whpTailBound_of_le
    {tail1 tail2 : Nat → Nat → ℝ≥0∞} {f : Nat → Nat}
    (hle : ∀ n t, tail1 n t ≤ tail2 n t)
    (h : WhpTailBound tail2 f) :
    WhpTailBound tail1 f := by
  intro k
  obtain ⟨C, n₀, hC, hBound⟩ := h k
  exact ⟨C, n₀, hC, fun n hn => (hle n (C * f n)).trans (hBound n hn)⟩

/-- Multi-step absorbing: K^m concentrates on {s'.2=0} when starting from s.2=0. -/
lemma sd_kernelIter_species1_dead_absorbing
    (params : LVParams) (s : PopState) (m : ℕ)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hs : s.2 = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    (kernelIter (lvKernel LVVariant.selfDestructive params) m) s
      {s' : PopState | s'.2 ≠ 0} = 0 := by
  induction m with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    rw [Measure.dirac_apply' _ (by measurability)]
    simp [Set.mem_setOf_eq, hs]
  | succ n ih =>
    rw [kernelIter_succ, Kernel.comp_apply]
    have hbind : (⇑(lvKernel LVVariant.selfDestructive params) ∘ₘ
      (kernelIter (lvKernel LVVariant.selfDestructive params) n) s)
      {s' | s'.2 ≠ 0} =
      ∫⁻ y, (lvKernel LVVariant.selfDestructive params) y {s' | s'.2 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.selfDestructive params) n) s) := by
      apply Measure.bind_apply <;> measurability
    rw [hbind]
    apply le_antisymm _ zero_le
    have hpw : ∀ (y : PopState),
        (lvKernel LVVariant.selfDestructive params) y {s' : PopState | s'.2 ≠ 0}
        ≤ Set.indicator {s' : PopState | s'.2 ≠ 0} (1 : PopState → ℝ≥0∞) y := by
      intro y
      by_cases hy : y.2 = 0
      · simp [Set.indicator, Set.mem_setOf_eq, hy,
          sd_kernel_species1_dead_absorbing params y hBeta hDelta hy]
      · simp [Set.indicator, Set.mem_setOf_eq, hy]
        exact prob_le_one
    calc ∫⁻ y, (lvKernel LVVariant.selfDestructive params) y {s' | s'.2 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.selfDestructive params) n) s)
      ≤ ∫⁻ y, Set.indicator {s' : PopState | s'.2 ≠ 0} (1 : PopState → ℝ≥0∞) y
        ∂((kernelIter (lvKernel LVVariant.selfDestructive params) n) s) :=
        lintegral_mono hpw
      _ = ((kernelIter (lvKernel LVVariant.selfDestructive params) n) s)
        {s' | s'.2 ≠ 0} := lintegral_indicator_one (by measurability)
      _ = 0 := ih

/-- Multi-step absorbing: K^m concentrates on {s'.1=0} when starting from s.1=0. -/
lemma sd_kernelIter_species0_dead_absorbing
    (params : LVParams) (s : PopState) (m : ℕ)
    (hBeta : params.beta = 0) (hDelta : params.delta = 0)
    (hs : s.1 = 0)
    [IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    (kernelIter (lvKernel LVVariant.selfDestructive params) m) s
      {s' : PopState | s'.1 ≠ 0} = 0 := by
  induction m with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    rw [Measure.dirac_apply' _ (by measurability)]
    simp [Set.mem_setOf_eq, hs]
  | succ n ih =>
    rw [kernelIter_succ, Kernel.comp_apply]
    have hbind : (⇑(lvKernel LVVariant.selfDestructive params) ∘ₘ
      (kernelIter (lvKernel LVVariant.selfDestructive params) n) s)
      {s' | s'.1 ≠ 0} =
      ∫⁻ y, (lvKernel LVVariant.selfDestructive params) y {s' | s'.1 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.selfDestructive params) n) s) := by
      apply Measure.bind_apply <;> measurability
    rw [hbind]
    apply le_antisymm _ zero_le
    have hpw : ∀ (y : PopState),
        (lvKernel LVVariant.selfDestructive params) y {s' : PopState | s'.1 ≠ 0}
        ≤ Set.indicator {s' : PopState | s'.1 ≠ 0} (1 : PopState → ℝ≥0∞) y := by
      intro y
      by_cases hy : y.1 = 0
      · simp [Set.indicator, Set.mem_setOf_eq, hy,
          sd_kernel_species0_dead_absorbing params y hBeta hDelta hy]
      · simp [Set.indicator, Set.mem_setOf_eq, hy]
        exact prob_le_one
    calc ∫⁻ y, (lvKernel LVVariant.selfDestructive params) y {s' | s'.1 ≠ 0}
        ∂((kernelIter (lvKernel LVVariant.selfDestructive params) n) s)
      ≤ ∫⁻ y, Set.indicator {s' : PopState | s'.1 ≠ 0} (1 : PopState → ℝ≥0∞) y
        ∂((kernelIter (lvKernel LVVariant.selfDestructive params) n) s) :=
        lintegral_mono hpw
      _ = ((kernelIter (lvKernel LVVariant.selfDestructive params) n) s)
        {s' | s'.1 ≠ 0} := lintegral_indicator_one (by measurability)
      _ = 0 := ih

/-- For SD with β=δ=0 and α₀=α₁=α, γ₀=γ₁=2α, the weighted sum of h at
    the three target state types equals φ * h. -/
lemma sd_neutral_harmonicity (a b α : ℝ)
    (hn : a + b ≠ 0) (hn_2 : a + b - 2 ≠ 0) :
    2 * α * a * b * ((a - 1) / (a + b - 2)) +
    α * a * (a - 1) * ((a - 2) / (a + b - 2)) +
    α * b * (b - 1) * (a / (a + b - 2)) =
    α * (a + b) * (a + b - 1) * (a / (a + b)) := by
  field_simp
  ring

-- =========================================================================
-- Consensus-absorbing kernel and harmonic stopped martingale
-- =========================================================================

/-- The absorbing kernel iterated N times gives ∫ h = h(a,b).
    This is the key "stopped martingale" identity. -/
lemma lvKernelAbsorb_iter_harmonic
    (params : LVParams)
    (h : PopState → ℝ) (v : LVVariant) (a b : ℕ) (N : ℕ)
    [IsMarkovKernel (lvKernel v params)]
    (hHarm : ∀ a' b' : ℕ, 0 < a' → 0 < b' → ∫ x, h x ∂(lvKernel v params) (a', b') = h (a', b'))
    (hBnd1 : ∀ a' : ℕ, 0 < a' → h (a', 0) = 1)
    (hBnd0 : ∀ b' : ℕ, h (0, b') = 0)
    (hBound : ∀ s : PopState, 0 ≤ h s ∧ h s ≤ 1) :
    ∫ x, h x ∂(kernelIter (lvKernelAbsorb v params) N) (a, b) = h (a, b) := by
  have hMK : IsMarkovKernel (lvKernelAbsorb v params) := lvKernelAbsorb_isMarkov v params
  have hAllHarm := lvKernelAbsorb_harmonic_everywhere params h v hHarm hBnd1 hBnd0
  apply kernelIter_harmonic_integral (lvKernelAbsorb v params) h (a, b) hAllHarm
  intro n
  haveI : IsProbabilityMeasure
      ((kernelIter (lvKernelAbsorb v params) n) (a, b)) :=
    (kernelIter_isMarkov n).isProbabilityMeasure (a, b)
  apply Integrable.mono (integrable_const (1 : ℝ))
    (measurable_of_countable h).aestronglyMeasurable
  filter_upwards with x
  simp only [Real.norm_eq_abs, norm_one]
  exact abs_le.mpr ⟨by linarith [(hBound x).1], (hBound x).2⟩

/-- The absorbing kernel K̃^N on any absorbing set A is monotone increasing:
    K̃^{N+1}(s₀)(A) ≥ K̃^N(s₀)(A). The proof uses the Chapman-Kolmogorov
    decomposition: K̃^{N+1}(A) = ∫ K̃(s)(A) dK̃^N(s) = K̃^N(A) + ∫_{Aᶜ} K̃(s)(A) dK̃^N(s)
    ≥ K̃^N(A), where the first integral over A uses K̃(s)(A) = 1 for absorbing
    states s ∈ A (K̃(s) = δ_s and s ∈ A). -/
lemma lvKernelAbsorb_absorbing_mono
    (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)]
    (s₀ : PopState) (N : ℕ)
    (A : Set PopState) (hA : MeasurableSet A)
    (hAbsorb : ∀ s ∈ A, s.1 = 0 ∨ s.2 = 0) :
    (kernelIter (lvKernelAbsorb v params) N) s₀ A ≤
    (kernelIter (lvKernelAbsorb v params) (N + 1)) s₀ A := by
  set Ka := lvKernelAbsorb v params with hKa_def
  haveI hMK : IsMarkovKernel Ka := lvKernelAbsorb_isMarkov v params
  rw [kernelIter_succ]
  rw [show (Ka ∘ₖ kernelIter Ka N) s₀ A =
    ∫⁻ s, Ka s A ∂(kernelIter Ka N) s₀ from
    Kernel.comp_apply' _ _ _ hA]
  rw [← lintegral_add_compl _ hA]
  have hA_part : ∫⁻ s in A, Ka s A ∂(kernelIter Ka N) s₀ =
      (kernelIter Ka N) s₀ A := by
    have hone : ∀ s ∈ A, Ka s A = 1 := fun s hs => by
      rw [hKa_def, lvKernelAbsorb_consensus v params s (hAbsorb s hs)]
      exact Measure.dirac_apply_of_mem hs
    trans ∫⁻ _ in A, (1 : ℝ≥0∞) ∂(kernelIter Ka N) s₀
    · exact lintegral_congr_ae (ae_restrict_of_forall_mem hA fun s hs => hone s hs)
    · exact setLIntegral_one A
  rw [hA_part]
  exact le_add_right le_rfl

/-- K̃^N never places mass on (0,0) when starting from an interior state.
    This is because the LV chain can never reach (0,0) from interior without
    first passing through a consensus state (a',0) or (0,b'), where K̃ absorbs. -/
lemma lvKernelAbsorb_no_extinction
    (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)]
    (hv : v = .nonSelfDestructive)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    (kernelIter (lvKernelAbsorb v params) N) (a, b) {(0, 0)} = 0 := by
  subst v
  induction N with
  | zero =>
    rw [kernelIter_zero, Kernel.id_apply]
    have hne : (a, b) ≠ (0, 0) := by intro h; simp [Prod.mk.injEq] at h; omega
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    simp [hne]
  | succ N ih =>
    set Ka := lvKernelAbsorb .nonSelfDestructive params with hKa_def
    haveI : IsMarkovKernel Ka := lvKernelAbsorb_isMarkov .nonSelfDestructive params
    rw [kernelIter_succ]
    rw [show (Ka ∘ₖ kernelIter Ka N) (a, b) {(0, 0)} =
      ∫⁻ s, Ka s {(0, 0)} ∂(kernelIter Ka N) (a, b) from
      Kernel.comp_apply' _ _ _ (measurableSet_singleton _)]
    have hzero_offdiag : ∀ s : PopState, s ≠ (0, 0) → Ka s {(0, 0)} = 0 := by
      intro s hs
      rcases s with ⟨a', b'⟩
      by_cases hcons : a' = 0 ∨ b' = 0
      · rw [hKa_def, lvKernelAbsorb_consensus .nonSelfDestructive params (a', b') hcons]
        rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
        simp [hs]
      · have ha' : 0 < a' := by omega
        have hb' : 0 < b' := by omega
        rw [hKa_def, lvKernelAbsorb_interior .nonSelfDestructive params (a', b') ha' hb']
        by_cases hφ : lvTotalPropensity params (a', b') = 0
        · rw [lvKernel_apply_zero_propensity .nonSelfDestructive params (a', b') hφ]
          rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
          simp [hs]
        · rw [lvKernel_nsd_apply params a' b' hφ]
          simp [Measure.smul_apply, smul_eq_mul, Measure.add_apply, ha'.ne', hb'.ne']
    have hpw : ∀ s : PopState,
        Ka s {(0, 0)} ≤ Set.indicator ({(0, 0)} : Set PopState) (1 : PopState → ℝ≥0∞) s := by
      intro s
      by_cases hs0 : s = (0, 0)
      · subst hs0
        simpa [Set.indicator] using (prob_le_one : Ka (0, 0) {(0, 0)} ≤ 1)
      · have hz : Ka s {(0, 0)} = 0 := hzero_offdiag s hs0
        simp [Set.indicator, hs0, hz]
    apply le_antisymm _ zero_le
    calc
      ∫⁻ s, Ka s {(0, 0)} ∂(kernelIter Ka N) (a, b)
          ≤ ∫⁻ s, Set.indicator ({(0, 0)} : Set PopState) (1 : PopState → ℝ≥0∞) s
              ∂(kernelIter Ka N) (a, b) :=
            lintegral_mono hpw
      _ = (kernelIter Ka N) (a, b) {(0, 0)} := lintegral_indicator_one (by measurability)
      _ = 0 := by simpa [hKa_def] using ih

-- =========================================================================
-- Total population BD chain for neutral NSD consensus
-- =========================================================================

/-- Before consensus, the LV total-population marginal at time t is dominated
    by the BD chain `nsdTotalPopBDChain`. Specifically, the probability that
    the LV chain has NOT reached consensus (total pop > 1) by time t is at most
    the BD chain survival probability.
    This is the coupling argument: at interior states, both chains have identical
    total-population transitions, so paths staying in the interior agree. -/
lemma nsd_consensus_survival_le_bd
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    [IsMarkovKernel (lvKernel LVVariant.nonSelfDestructive params)]
    (t : ℕ) :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | ∀ s ≤ t, 0 < (ω s).1 ∧ 0 < (ω s).2} ≤
    (kernelIter (bdKernel (nsdTotalPopBDChain params)) t)
      (a + b) {x | 0 < x} := by
  have hbd_surv_one : ∀ t n, 0 < n →
      (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) n {x | 0 < x} = 1 := by
    intro t n hn
    have hstep_zero : ∀ x, 0 < x →
        (bdKernel (nsdTotalPopBDChain params) x) {0} = 0 := by
      intro x hx
      rw [bdKernel_apply_singleton]
      by_cases h1 : x = 1
      · subst h1
        simp [nsdTotalPopBDChain]
      · have h0x : ¬(0 = x) := by omega
        have h0xp1 : ¬(0 = x + 1) := by omega
        have h0xm1 : ¬(0 = x - 1) := by omega
        simp [h0x, h0xp1, h0xm1]
    have hzero_mass : ∀ t n, 0 < n →
        (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) n {0} = 0 := by
      intro t
      induction t with
      | zero =>
          intro n hn
          simp [kernelIter_zero, Kernel.id_apply, hn.ne']
      | succ t ih =>
          intro n hn
          rw [kernelIter_succ, Kernel.comp_apply' _ _ _ (measurableSet_singleton 0)]
          set μ := (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) n
          set g : ℕ → ℝ≥0∞ := fun x => (bdKernel (nsdTotalPopBDChain params) x) {0}
          have hμ0 : μ {0} = 0 := by
            simpa [μ] using ih n hn
          have h0part : ∫⁻ x in ({0} : Set ℕ), g x ∂μ = 0 := by
            exact setLIntegral_measure_zero _ _ hμ0
          have hpospart : ∫⁻ x in ({0} : Set ℕ)ᶜ, g x ∂μ = 0 := by
            apply le_antisymm _ zero_le
            calc
              ∫⁻ x in ({0} : Set ℕ)ᶜ, g x ∂μ
                  ≤ ∫⁻ _ in ({0} : Set ℕ)ᶜ, 0 ∂μ := by
                    apply lintegral_mono_ae
                    exact ae_restrict_of_forall_mem
                      (MeasurableSet.compl (measurableSet_singleton 0))
                      (fun x hx => by
                        have hx0 : x ≠ 0 := by
                          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
                        have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
                        exact le_of_eq (hstep_zero x hxpos))
              _ = 0 := by simp
          rw [← lintegral_add_compl _ (measurableSet_singleton 0), h0part, hpospart]
          simp
    have h0 : (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) n {0} = 0 :=
      hzero_mass t n hn
    haveI : IsProbabilityMeasure ((kernelIter (bdKernel (nsdTotalPopBDChain params)) t) n) :=
      (kernelIter_isMarkov (K := bdKernel (nsdTotalPopBDChain params)) t).isProbabilityMeasure n
    have hfin : (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) n {0} ≠ ⊤ :=
      measure_ne_top _ _
    have hset : ({x : ℕ | 0 < x} : Set ℕ) = ({0} : Set ℕ)ᶜ := by
      ext x
      simp [Nat.pos_iff_ne_zero]
    rw [hset, measure_compl (measurableSet_singleton 0) hfin, h0, tsub_zero, measure_univ]
  have hab : 0 < a + b := by omega
  have h_rhs_one :
      (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) (a + b) {x | 0 < x} = 1 :=
    hbd_surv_one t (a + b) hab
  set A : Set (ℕ → PopState) := {ω | ∀ s ≤ t, 0 < (ω s).1 ∧ 0 < (ω s).2}
  set B : Set (ℕ → PopState) := {ω | 0 < (ω t).1 ∧ 0 < (ω t).2}
  have hAB : A ⊆ B := by
    intro ω hω
    exact hω t le_rfl
  have hA_le_B :
      lvPathMeasure .nonSelfDestructive params (a, b) A ≤
        lvPathMeasure .nonSelfDestructive params (a, b) B :=
    measure_mono hAB
  haveI : IsProbabilityMeasure (lvPathMeasure .nonSelfDestructive params (a, b)) := by
    unfold lvPathMeasure homogeneousPathMeasure
    infer_instance
  calc
    lvPathMeasure .nonSelfDestructive params (a, b) A
        ≤ lvPathMeasure .nonSelfDestructive params (a, b) B := hA_le_B
    _ ≤ 1 := by simpa using
        (prob_le_one : lvPathMeasure .nonSelfDestructive params (a, b) B ≤ 1)
    _ = (kernelIter (bdKernel (nsdTotalPopBDChain params)) t) (a + b) {x | 0 < x} := by
      symm
      exact h_rhs_one

end LVConsensus
