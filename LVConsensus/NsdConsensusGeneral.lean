import LVConsensus.NsdConsensus

set_option autoImplicit false
set_option maxHeartbeats 3000000

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal BigOperators

namespace LVConsensus

private def nsdInterior (s : PopState) : Prop :=
  0 < s.1 ∧ 0 < s.2

private instance nsdInterior_decidable (s : PopState) :
    Decidable (nsdInterior s) := by
  unfold nsdInterior
  infer_instance

/-- The total population above one while both species are present, and zero
after consensus. -/
private def nsdInteriorLevel (s : PopState) : ℕ :=
  if nsdInterior s then s.1 + s.2 - 1 else 0

private noncomputable def cappedGeometricWeight
    (r : ℝ) (cutoff i : ℕ) : ℝ :=
  r ^ min i cutoff

private noncomputable def cappedGeometricPotential
    (r : ℝ) (cutoff n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, cappedGeometricWeight r cutoff i

private lemma cappedGeometricWeight_pos
    {r : ℝ} (hr : 0 < r) (cutoff i : ℕ) :
    0 < cappedGeometricWeight r cutoff i := by
  exact pow_pos hr _

private lemma cappedGeometricPotential_nonneg
    {r : ℝ} (hr : 0 < r) (cutoff n : ℕ) :
    0 ≤ cappedGeometricPotential r cutoff n := by
  exact Finset.sum_nonneg fun i _ =>
    (cappedGeometricWeight_pos hr cutoff i).le

private lemma cappedGeometricPotential_zero
    (r : ℝ) (cutoff : ℕ) :
    cappedGeometricPotential r cutoff 0 = 0 := by
  simp [cappedGeometricPotential]

private lemma cappedGeometricPotential_succ
    (r : ℝ) (cutoff n : ℕ) :
    cappedGeometricPotential r cutoff (n + 1) =
      cappedGeometricPotential r cutoff n +
        cappedGeometricWeight r cutoff n := by
  simp [cappedGeometricPotential, Finset.sum_range_succ]

private lemma cappedGeometricPotential_mono
    {r : ℝ} (hr : 0 < r) (cutoff : ℕ) :
    Monotone (cappedGeometricPotential r cutoff) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [cappedGeometricPotential_succ]
  exact le_add_of_nonneg_right
    (cappedGeometricWeight_pos hr cutoff n).le

/-- For an interior NSD state, this is the exact one-step integral formula
before imposing any harmonicity or drift inequality. -/
private lemma lvKernel_nsd_integral_eq_weighted_div
    (params : LVParams) (h : PopState → ℝ) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hφ : lvTotalPropensity params (a, b) ≠ 0) :
    ∫ x, h x ∂(lvKernel .nonSelfDestructive params) (a, b) =
      (params.beta * a * h (a + 1, b) +
        params.beta * b * h (a, b + 1) +
        (params.delta * a + params.alpha1 * a * b +
          params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) *
            h (a - 1, b) +
        (params.delta * b + params.alpha0 * a * b +
          params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) *
            h (a, b - 1)) /
        lvTotalPropensity params (a, b) := by
  let W : ℝ :=
    params.beta * a * h (a + 1, b) +
      params.beta * b * h (a, b + 1) +
      (params.delta * a + params.alpha1 * a * b +
        params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) *
          h (a - 1, b) +
      (params.delta * b + params.alpha0 * a * b +
        params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) *
          h (a, b - 1)
  let h' : PopState → ℝ :=
    fun s => if s = (a, b) then W / lvTotalPropensity params (a, b) else h s
  have hup0 : (a + 1, b) ≠ (a, b) := by
    intro heq
    have := congrArg Prod.fst heq
    simp at this
  have hup1 : (a, b + 1) ≠ (a, b) := by
    intro heq
    have := congrArg Prod.snd heq
    simp at this
  have hdown0 : (a - 1, b) ≠ (a, b) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only [Prod.fst] at this
    omega
  have hdown1 : (a, b - 1) ≠ (a, b) := by
    intro heq
    have := congrArg Prod.snd heq
    simp only [Prod.snd] at this
    omega
  have hHarm :
      params.beta * a * h' (a + 1, b) +
        params.beta * b * h' (a, b + 1) +
        (params.delta * a + params.alpha1 * a * b +
          params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2)) *
            h' (a - 1, b) +
        (params.delta * b + params.alpha0 * a * b +
          params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2)) *
            h' (a, b - 1) =
        lvTotalPropensity params (a, b) * h' (a, b) := by
    simp only [h', hup0, hup1, hdown0, hdown1, ↓reduceIte,
      if_pos rfl]
    dsimp only [W]
    field_simp
  have hIntegral :=
    lvKernel_nsd_harmonic_integral params h' a b ha hb hφ hHarm
  have hself :
      (lvKernel .nonSelfDestructive params) (a, b) ({(a, b)} : Set PopState) = 0 := by
    rw [lvKernel_nsd_apply params a b hφ, Measure.smul_apply]
    simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      hup0, hup1, hdown0, hdown1]
  have haene :
      ∀ᵐ x ∂(lvKernel .nonSelfDestructive params) (a, b),
        x ≠ (a, b) := by
    rw [ae_iff]
    have hset :
        {x : PopState | ¬x ≠ (a, b)} = ({(a, b)} : Set PopState) := by
      ext x
      simp
    rw [hset]
    exact hself
  calc
    ∫ x, h x ∂(lvKernel .nonSelfDestructive params) (a, b)
        = ∫ x, h' x ∂(lvKernel .nonSelfDestructive params) (a, b) := by
            apply integral_congr_ae
            filter_upwards [haene] with x hx
            simp [h', hx]
    _ = h' (a, b) := hIntegral
    _ = W / lvTotalPropensity params (a, b) := by simp [h']
    _ = _ := rfl

/-- A strict nonnegative Lyapunov inequality makes the occupation
probabilities of `I` summable. -/
private lemma kernel_occupation_tsum_le_of_lyapunov
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSingletonClass α] [Countable α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (I : Set α) (F : α → ℝ≥0∞)
    (hStep : ∀ x,
      Set.indicator I (fun _ => (1 : ℝ≥0∞)) x +
          ∫⁻ y, F y ∂K x ≤ F x)
    (s : α) :
    ∑' t : ℕ, (kernelIter K t) s I ≤ F s := by
  have hPartial :
      ∀ T : ℕ,
        (∑ t ∈ Finset.range T, (kernelIter K t) s I) +
            ∫⁻ x, F x ∂(kernelIter K T) s ≤ F s := by
    intro T
    induction T with
    | zero =>
        simp [kernelIter_zero, Kernel.id_apply]
    | succ T ih =>
        have hI : MeasurableSet I := (Set.to_countable I).measurableSet
        have hF : Measurable F := measurable_of_countable F
        have hInner :
            Measurable (fun x => ∫⁻ y, F y ∂K x) :=
          measurable_of_countable _
        have hOne :
            (kernelIter K T) s I +
                ∫⁻ y, F y ∂(kernelIter K (T + 1)) s ≤
              ∫⁻ x, F x ∂(kernelIter K T) s := by
          rw [kernelIter_lintegral_add K T 1 s F hF]
          have hK1 : kernelIter K 1 = K := by
            exact kernelIter_one_generic K
          simp_rw [hK1]
          calc
            (kernelIter K T) s I +
                  ∫⁻ x, (∫⁻ y, F y ∂K x) ∂(kernelIter K T) s
                =
              (∫⁻ x,
                  Set.indicator I (fun _ => (1 : ℝ≥0∞)) x
                ∂(kernelIter K T) s) +
                  ∫⁻ x, (∫⁻ y, F y ∂K x) ∂(kernelIter K T) s := by
                    congr 1
                    exact (lintegral_indicator_one hI).symm
            _ = ∫⁻ x,
                  (Set.indicator I (fun _ => (1 : ℝ≥0∞)) x +
                    ∫⁻ y, F y ∂K x)
                ∂(kernelIter K T) s := by
                  rw [lintegral_add_left
                    (measurable_const.indicator hI)
                    (fun x => ∫⁻ y, F y ∂K x)]
            _ ≤ ∫⁻ x, F x ∂(kernelIter K T) s :=
              lintegral_mono hStep
        rw [Finset.sum_range_succ]
        calc
          ((∑ t ∈ Finset.range T, (kernelIter K t) s I) +
                (kernelIter K T) s I) +
              ∫⁻ x, F x ∂(kernelIter K (T + 1)) s
              =
            (∑ t ∈ Finset.range T, (kernelIter K t) s I) +
              ((kernelIter K T) s I +
                ∫⁻ x, F x ∂(kernelIter K (T + 1)) s) := by
                  ac_rfl
          _ ≤ (∑ t ∈ Finset.range T, (kernelIter K t) s I) +
                ∫⁻ x, F x ∂(kernelIter K T) s :=
            add_le_add (le_refl _) hOne
          _ ≤ F s := ih
  apply ENNReal.tsum_le_of_sum_range_le
  intro T
  exact (le_add_right (le_refl _)).trans (hPartial T)

private lemma nsd_boundary_lintegral_zero
    (params : LVParams) (F : PopState → ℝ≥0∞)
    (hF : ∀ s, ¬nsdInterior s → F s = 0)
    (s : PopState) (hs : ¬nsdInterior s)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∫⁻ y, F y ∂(lvKernel .nonSelfDestructive params) s = 0 := by
  rcases not_and_or.mp hs with hs0 | hs1
  · have hs0' : s.1 = 0 := Nat.eq_zero_of_not_pos hs0
    have hdead :=
      nsd_kernel_species0_dead_absorbing params s hs0'
    apply le_antisymm _ zero_le
    calc
      ∫⁻ y, F y ∂(lvKernel .nonSelfDestructive params) s
          ≤ ∫⁻ y,
              Set.indicator {y : PopState | y.1 ≠ 0} F y
            ∂(lvKernel .nonSelfDestructive params) s := by
              apply lintegral_mono
              intro y
              by_cases hy : y.1 = 0
              · have : ¬nsdInterior y := by
                  simp [nsdInterior, hy]
                simp [Set.indicator, hy, hF y this]
              · simp [Set.indicator, hy]
      _ = 0 := by
        rw [lintegral_indicator
          ((Set.to_countable {y : PopState | y.1 ≠ 0}).measurableSet)]
        exact setLIntegral_measure_zero _ _ hdead
  · have hs1' : s.2 = 0 := Nat.eq_zero_of_not_pos hs1
    have hdead :=
      nsd_kernel_species1_dead_absorbing params s hs1'
    apply le_antisymm _ zero_le
    calc
      ∫⁻ y, F y ∂(lvKernel .nonSelfDestructive params) s
          ≤ ∫⁻ y,
              Set.indicator {y : PopState | y.2 ≠ 0} F y
            ∂(lvKernel .nonSelfDestructive params) s := by
              apply lintegral_mono
              intro y
              by_cases hy : y.2 = 0
              · have : ¬nsdInterior y := by
                  simp [nsdInterior, hy]
                simp [Set.indicator, hy, hF y this]
              · simp [Set.indicator, hy]
      _ = 0 := by
        rw [lintegral_indicator
          ((Set.to_countable {y : PopState | y.2 ≠ 0}).measurableSet)]
        exact setLIntegral_measure_zero _ _ hdead

/-- For symmetric NSD competition, every common intraspecific rate
`γ ≥ 2α > 0` gives almost-sure consensus, for arbitrary demographic rates. -/
theorem nsd_consensus_almost_sure_gamma_ge
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (hGe : 2 * params.alpha0 ≤ params.gamma0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | consensusReachedEvent ω} = 1 := by
  obtain ⟨cutoff, ε, hε, _hε1, hDrift⟩ :=
    nsdTotalPopBDChain_drift params hAlpha
  let δ₀ : ℝ :=
    params.alpha0 / (params.beta + params.delta + params.alpha0)
  have hden₀ : 0 < params.beta + params.delta + params.alpha0 := by
    linarith [params.beta_nonneg, params.delta_nonneg]
  have hδ₀ : 0 < δ₀ := div_pos hAlpha hden₀
  have hδ₀_le_one : δ₀ ≤ 1 := by
    dsimp [δ₀]
    rw [div_le_one hden₀]
    linarith [params.beta_nonneg, params.delta_nonneg]
  let r : ℝ := δ₀ / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr_le_one : r ≤ 1 := by
    dsimp [r]
    linarith
  let lowDrift : ℝ := (δ₀ / 2) * r ^ cutoff
  let highDrift : ℝ := ε * r ^ cutoff
  let κ : ℝ := min lowDrift highDrift
  have hlowDrift : 0 < lowDrift := by
    dsimp [lowDrift]
    positivity
  have hhighDrift : 0 < highDrift := by
    dsimp [highDrift]
    positivity
  have hκ : 0 < κ := by
    dsimp [κ]
    exact lt_min hlowDrift hhighDrift
  let V : ℕ → ℝ := cappedGeometricPotential r cutoff
  let H : PopState → ℝ := fun s => V (nsdInteriorLevel s)
  let G : PopState → ℝ := fun s => H s / κ
  let F : PopState → ℝ≥0∞ := fun s => ENNReal.ofReal (G s)
  have hVnonneg : ∀ n, 0 ≤ V n := fun n =>
    cappedGeometricPotential_nonneg hr cutoff n
  have hVmono : Monotone V :=
    cappedGeometricPotential_mono hr cutoff
  have hHnonneg : ∀ s, 0 ≤ H s := fun s => hVnonneg _
  have hGnonneg : ∀ s, 0 ≤ G s := fun s =>
    div_nonneg (hHnonneg s) hκ.le
  have hFboundary : ∀ s, ¬nsdInterior s → F s = 0 := by
    intro s hs
    simp [F, G, H, V, nsdInteriorLevel, hs,
      cappedGeometricPotential]
  have hStep :
      ∀ s,
        Set.indicator {s : PopState | nsdInterior s}
            (fun _ => (1 : ℝ≥0∞)) s +
            ∫⁻ y, F y ∂(lvKernel .nonSelfDestructive params) s ≤
          F s := by
    intro s
    by_cases hs : nsdInterior s
    · rcases s with ⟨a', b'⟩
      have ha' : 0 < a' := hs.1
      have hb' : 0 < b' := hs.2
      let m : ℕ := a' + b' - 1
      have hm : 0 < m := by
        dsimp [m]
        omega
      have hlevel : nsdInteriorLevel (a', b') = m := by
        simp [nsdInteriorLevel, nsdInterior, ha', hb', m]
      have hφpos : 0 < lvTotalPropensity params (a', b') := by
        unfold lvTotalPropensity
        have hinter :
            0 < params.alpha0 * (a' : ℝ) * b' := by
          positivity
        have haR1 : (1 : ℝ) ≤ a' := Nat.one_le_cast.mpr ha'
        have hbR1 : (1 : ℝ) ≤ b' := Nat.one_le_cast.mpr hb'
        have hga :
            0 ≤ params.gamma0 *
              ((a' : ℝ) * ((a' : ℝ) - 1) / 2) := by
          exact mul_nonneg params.gamma0_nonneg
            (div_nonneg
              (mul_nonneg (Nat.cast_nonneg a')
                (sub_nonneg.mpr haR1))
              (by norm_num))
        have hgb :
            0 ≤ params.gamma1 *
              ((b' : ℝ) * ((b' : ℝ) - 1) / 2) := by
          exact mul_nonneg params.gamma1_nonneg
            (div_nonneg
              (mul_nonneg (Nat.cast_nonneg b')
                (sub_nonneg.mpr hbR1))
              (by norm_num))
        nlinarith [mul_nonneg params.beta_nonneg (Nat.cast_nonneg a'),
          mul_nonneg params.beta_nonneg (Nat.cast_nonneg b'),
          mul_nonneg params.delta_nonneg (Nat.cast_nonneg a'),
          mul_nonneg params.delta_nonneg (Nat.cast_nonneg b'),
          mul_nonneg
            (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg a'))
            (Nat.cast_nonneg b')]
      have hφ : lvTotalPropensity params (a', b') ≠ 0 :=
        ne_of_gt hφpos
      let d : ℕ → ℝ := cappedGeometricWeight r cutoff
      have hdpos : ∀ i, 0 < d i := fun i =>
        cappedGeometricWeight_pos hr cutoff i
      have hVsucc : ∀ n, V (n + 1) = V n + d n := by
        intro n
        exact cappedGeometricPotential_succ r cutoff n
      have hBirth0 :
          H (a' + 1, b') = V (m + 1) := by
        simp only [H, nsdInteriorLevel]
        rw [if_pos (by exact ⟨by omega, hb'⟩)]
        congr 1
        dsimp [m]
        omega
      have hBirth1 :
          H (a', b' + 1) = V (m + 1) := by
        simp only [H, nsdInteriorLevel]
        rw [if_pos (by exact ⟨ha', by omega⟩)]
        congr 1
        dsimp [m]
        omega
      have hDeathLevel0 :
          nsdInteriorLevel (a' - 1, b') ≤ m - 1 := by
        simp only [nsdInteriorLevel]
        split_ifs <;> dsimp [m] <;> omega
      have hDeathLevel1 :
          nsdInteriorLevel (a', b' - 1) ≤ m - 1 := by
        simp only [nsdInteriorLevel]
        split_ifs <;> dsimp [m] <;> omega
      have hDeath0 :
          H (a' - 1, b') ≤ V (m - 1) := by
        exact hVmono hDeathLevel0
      have hDeath1 :
          H (a', b' - 1) ≤ V (m - 1) := by
        exact hVmono hDeathLevel1
      let c0 : ℝ :=
        params.delta * a' + params.alpha1 * a' * b' +
          params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2)
      let c1 : ℝ :=
        params.delta * b' + params.alpha0 * a' * b' +
          params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2)
      have hc0 : 0 ≤ c0 := by
        dsimp [c0]
        have haR : (1 : ℝ) ≤ a' := Nat.one_le_cast.mpr ha'
        have hγterm :
            0 ≤ params.gamma0 *
              ((a' : ℝ) * ((a' : ℝ) - 1) / 2) := by
          exact mul_nonneg params.gamma0_nonneg
            (div_nonneg
              (mul_nonneg (Nat.cast_nonneg a')
                (sub_nonneg.mpr haR))
              (by norm_num))
        nlinarith [mul_nonneg params.delta_nonneg (Nat.cast_nonneg a'),
          mul_nonneg
            (mul_nonneg params.alpha1_nonneg (Nat.cast_nonneg a'))
            (Nat.cast_nonneg b')]
      have hc1 : 0 ≤ c1 := by
        dsimp [c1]
        have hbR : (1 : ℝ) ≤ b' := Nat.one_le_cast.mpr hb'
        have hγterm :
            0 ≤ params.gamma1 *
              ((b' : ℝ) * ((b' : ℝ) - 1) / 2) := by
          exact mul_nonneg params.gamma1_nonneg
            (div_nonneg
              (mul_nonneg (Nat.cast_nonneg b')
                (sub_nonneg.mpr hbR))
              (by norm_num))
        nlinarith [mul_nonneg params.delta_nonneg (Nat.cast_nonneg b'),
          mul_nonneg
            (mul_nonneg params.alpha0_nonneg (Nat.cast_nonneg a'))
            (Nat.cast_nonneg b')]
      let W : ℝ :=
        params.beta * a' * H (a' + 1, b') +
          params.beta * b' * H (a', b' + 1) +
          c0 * H (a' - 1, b') +
          c1 * H (a', b' - 1)
      let B : ℝ := params.beta * (a' + b')
      let D : ℝ := c0 + c1
      have hB : 0 ≤ B := by
        dsimp [B]
        exact mul_nonneg params.beta_nonneg
          (add_nonneg (Nat.cast_nonneg a') (Nat.cast_nonneg b'))
      have hD : 0 ≤ D := add_nonneg hc0 hc1
      have hφBD :
          lvTotalPropensity params (a', b') = B + D := by
        dsimp [B, D, c0, c1]
        unfold lvTotalPropensity
        ring
      have hW :
          W ≤ B * V (m + 1) + D * V (m - 1) := by
        dsimp [W, B, D]
        rw [hBirth0, hBirth1]
        have h0 := mul_le_mul_of_nonneg_left hDeath0 hc0
        have h1 := mul_le_mul_of_nonneg_left hDeath1 hc1
        nlinarith
      let den : ℝ :=
        params.beta + params.delta + params.alpha0 * (m : ℝ)
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hden : 0 < den := by
        dsimp [den]
        exact add_pos_of_nonneg_of_pos
          (add_nonneg params.beta_nonneg params.delta_nonneg)
          (mul_pos hAlpha hmR)
      let p : ℝ := params.beta / den
      let q : ℝ :=
        (params.delta + params.alpha0 * (m : ℝ)) / den
      have hp : 0 ≤ p := div_nonneg params.beta_nonneg hden.le
      have hq : 0 ≤ q := by
        dsimp [q]
        exact div_nonneg
          (add_nonneg params.delta_nonneg
            (mul_nonneg params.alpha0_nonneg hmR.le))
          hden.le
      have hpq : p + q = 1 := by
        dsimp [p, q, den]
        rw [← add_div]
        convert div_self hden.ne' using 1 <;> ring
      have hp_le_one : p ≤ 1 := by linarith
      have hq_lower : δ₀ ≤ q := by
        dsimp [δ₀, q, den]
        rw [div_le_div_iff₀ hden₀ hden]
        have hm1R : (0 : ℝ) ≤ (m : ℝ) - 1 := by
          exact sub_nonneg.mpr (by exact_mod_cast hm)
        have h1 :
            0 ≤ params.delta * params.beta :=
          mul_nonneg params.delta_nonneg params.beta_nonneg
        have h2 :
            0 ≤ params.delta ^ 2 := sq_nonneg _
        have h3 :
            0 ≤ params.alpha0 * params.beta * ((m : ℝ) - 1) := by
          exact mul_nonneg
            (mul_nonneg params.alpha0_nonneg params.beta_nonneg) hm1R
        have h4 :
            0 ≤ params.alpha0 * params.delta * (m : ℝ) := by
          exact mul_nonneg
            (mul_nonneg params.alpha0_nonneg params.delta_nonneg) hmR.le
        nlinarith
      have hφLower :
          (a' + b' : ℝ) * den ≤
            lvTotalPropensity params (a', b') := by
        dsimp [den]
        have haR : (1 : ℝ) ≤ a' := Nat.one_le_cast.mpr ha'
        have hbR : (1 : ℝ) ≤ b' := Nat.one_le_cast.mpr hb'
        let Q : ℝ :=
          (a' : ℝ) * ((a' : ℝ) - 1) / 2 +
            (b' : ℝ) * ((b' : ℝ) - 1) / 2
        have hQ : 0 ≤ Q := by
          dsimp [Q]
          exact add_nonneg
            (div_nonneg
              (mul_nonneg (Nat.cast_nonneg a')
                (sub_nonneg.mpr haR))
              (by norm_num))
            (div_nonneg
              (mul_nonneg (Nat.cast_nonneg b')
                (sub_nonneg.mpr hbR))
              (by norm_num))
        have hextra :
            0 ≤ (params.gamma0 - 2 * params.alpha0) * Q := by
          exact mul_nonneg (sub_nonneg.mpr hGe) hQ
        have hid :
            lvTotalPropensity params (a', b') =
              ((a' : ℝ) + b') *
                  (params.beta + params.delta +
                    params.alpha0 * (((a' : ℝ) + b') - 1)) +
                (params.gamma0 - 2 * params.alpha0) * Q := by
          unfold lvTotalPropensity
          rw [← hNeutral, hGamma]
          dsimp [Q]
          ring
        rw [hid]
        have hmcast :
            (m : ℝ) = (a' : ℝ) + b' - 1 := by
          dsimp [m]
          rw [Nat.cast_sub (by omega : 1 ≤ a' + b'),
            Nat.cast_add, Nat.cast_one]
        rw [hmcast]
        linarith
      have hP_le :
          B / lvTotalPropensity params (a', b') ≤ p := by
        rw [show p = params.beta / den by rfl,
          div_le_div_iff₀ hφpos hden]
        simpa [B, mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left hφLower params.beta_nonneg
      have hVm :
          V m = V (m - 1) + d (m - 1) := by
        have : m = (m - 1) + 1 := by omega
        nth_rewrite 1 [this]
        exact hVsucc (m - 1)
      have hVup :
          V (m + 1) = V m + d m := hVsucc m
      have hd_lower :
          r ^ cutoff ≤ d (m - 1) := by
        dsimp [d, cappedGeometricWeight]
        exact pow_le_pow_of_le_one hr.le hr_le_one (Nat.min_le_right _ _)
      have hdmono : d m ≤ d (m - 1) := by
        dsimp [d, cappedGeometricWeight]
        apply pow_le_pow_of_le_one hr.le hr_le_one
        omega
      have hRefDrift :
          p * d m - q * d (m - 1) ≤ -κ := by
        by_cases hhigh : cutoff ≤ m
        · have hdm : d m = r ^ cutoff := by
            simp [d, cappedGeometricWeight, Nat.min_eq_right hhigh]
          have hbase :
              (nsdTotalPopBDChain params).p (m + 1) -
                  (nsdTotalPopBDChain params).q (m + 1) ≤ -ε :=
            hDrift (m + 1) (hhigh.trans (Nat.le_succ m)) (by omega)
          have hpbase :
              (nsdTotalPopBDChain params).p (m + 1) = p := by
            simp [nsdTotalPopBDChain, p, den, show ¬m + 1 ≤ 1 by omega]
          have hqbase :
              (nsdTotalPopBDChain params).q (m + 1) = q := by
            simp [nsdTotalPopBDChain, q, den, show ¬m + 1 ≤ 1 by omega]
          rw [hpbase, hqbase] at hbase
          have href :
              p * d m - q * d (m - 1) ≤
                (p - q) * d m := by
            nlinarith [mul_le_mul_of_nonneg_left hdmono hq]
          have hkHigh : κ ≤ highDrift := min_le_right _ _
          dsimp [highDrift] at hkHigh
          rw [hdm] at href
          nlinarith [mul_le_mul_of_nonneg_right hbase
            (pow_nonneg hr.le cutoff)]
        · have hmlow : m < cutoff := by omega
          have hdm :
              d m = r * d (m - 1) := by
            have hdm0 : d m = r ^ m := by
              simp [d, cappedGeometricWeight,
                Nat.min_eq_left hmlow.le]
            have hdpred : d (m - 1) = r ^ (m - 1) := by
              simp [d, cappedGeometricWeight,
                Nat.min_eq_left (by omega : m - 1 ≤ cutoff)]
            rw [hdm0, hdpred]
            calc
              r ^ m = r ^ ((m - 1) + 1) := by
                congr 1
                omega
              _ = r ^ (m - 1) * r := by rw [pow_succ]
              _ = r * r ^ (m - 1) := by ring
          have href :
              p * d m - q * d (m - 1) ≤
                -(δ₀ / 2) * d (m - 1) := by
            rw [hdm]
            have hpr : p * r ≤ r :=
              mul_le_of_le_one_left hr.le hp_le_one
            have hcoef :
                p * r - q ≤ -(δ₀ / 2) := by
              dsimp [r] at hpr ⊢
              linarith
            calc
              p * (r * d (m - 1)) - q * d (m - 1) =
                  (p * r - q) * d (m - 1) := by ring
              _ ≤ -(δ₀ / 2) * d (m - 1) :=
                mul_le_mul_of_nonneg_right hcoef
                  (hdpos (m - 1)).le
          have hkLow : κ ≤ lowDrift := min_le_left _ _
          dsimp [lowDrift] at hkLow
          nlinarith [mul_le_mul_of_nonneg_left hd_lower
            (show 0 ≤ δ₀ / 2 from by positivity)]
      have hPD :
          D / lvTotalPropensity params (a', b') =
            1 - B / lvTotalPropensity params (a', b') := by
        rw [hφBD]
        have hne : B + D ≠ 0 := by
          rw [← hφBD]
          exact hφ
        field_simp [hne]
        ring
      have hActualDrift :
          (B / lvTotalPropensity params (a', b')) * d m -
              (D / lvTotalPropensity params (a', b')) * d (m - 1) ≤
            -κ := by
        rw [hPD]
        have hcomp :
            (B / lvTotalPropensity params (a', b')) * d m -
                (1 - B / lvTotalPropensity params (a', b')) *
                    d (m - 1) ≤
              p * d m - q * d (m - 1) := by
          rw [show q = 1 - p by linarith [hpq]]
          nlinarith [mul_le_mul_of_nonneg_right hP_le
            (add_nonneg (hdpos m).le (hdpos (m - 1)).le)]
        exact hcomp.trans hRefDrift
      have hIntegralH :
          ∫ x, H x ∂(lvKernel .nonSelfDestructive params) (a', b') =
            W / lvTotalPropensity params (a', b') := by
        dsimp only [W, c0, c1]
        exact lvKernel_nsd_integral_eq_weighted_div
          params H a' b' ha' hb' hφ
      have hStrictH :
          κ + ∫ x, H x
              ∂(lvKernel .nonSelfDestructive params) (a', b') ≤
            H (a', b') := by
        have hHcur : H (a', b') = V m := by
          simp only [H, hlevel]
        rw [hIntegralH, hHcur]
        have hscaledW :
            W / lvTotalPropensity params (a', b') ≤
              B / lvTotalPropensity params (a', b') * V (m + 1) +
                D / lvTotalPropensity params (a', b') * V (m - 1) := by
          calc
            W / lvTotalPropensity params (a', b') ≤
                (B * V (m + 1) + D * V (m - 1)) /
                  lvTotalPropensity params (a', b') :=
              div_le_div_of_nonneg_right hW hφpos.le
            _ = B / lvTotalPropensity params (a', b') * V (m + 1) +
                  D / lvTotalPropensity params (a', b') * V (m - 1) := by
              field_simp
        have hrewrite :
            B / lvTotalPropensity params (a', b') * V (m + 1) +
                D / lvTotalPropensity params (a', b') * V (m - 1) =
              V m +
                (B / lvTotalPropensity params (a', b')) * d m -
                (D / lvTotalPropensity params (a', b')) * d (m - 1) := by
          rw [hVup, hVm, hPD]
          ring
        rw [hrewrite] at hscaledW
        linarith
      have hIntH :
          Integrable H
            ((lvKernel .nonSelfDestructive params) (a', b')) := by
        rw [lvKernel_nsd_apply params a' b' hφ]
        have isd := fun c s =>
          integrable_ofReal_smul_dirac H c (α := PopState) s
        have i1 := isd (params.beta * a') (a' + 1, b')
        have i2 := isd (params.beta * b') (a', b' + 1)
        have i3 := isd (params.delta * a') (a' - 1, b')
        have i4 := isd (params.delta * b') (a', b' - 1)
        have i5 := isd (params.alpha0 * a' * b') (a', b' - 1)
        have i6 := isd (params.alpha1 * a' * b') (a' - 1, b')
        have i7 := isd
          (params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2))
          (a' - 1, b')
        have i8 := isd
          (params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2))
          (a', b' - 1)
        exact
          (((((((i1.add_measure i2).add_measure i3).add_measure i4).add_measure
            i5).add_measure i6).add_measure i7).add_measure i8).smul_measure
              ENNReal.ofReal_ne_top
      have hIntG :
          Integrable G
            ((lvKernel .nonSelfDestructive params) (a', b')) := by
        exact hIntH.div_const κ
      have hIntegralG :
          ∫ x, G x
              ∂(lvKernel .nonSelfDestructive params) (a', b') =
            (∫ x, H x
              ∂(lvKernel .nonSelfDestructive params) (a', b')) / κ := by
        simp only [G]
        exact integral_div κ H
      have hStrictG :
          1 + ∫ x, G x
              ∂(lvKernel .nonSelfDestructive params) (a', b') ≤
            G (a', b') := by
        rw [hIntegralG]
        dsimp only [G]
        calc
          1 + (∫ x, H x
                ∂(lvKernel .nonSelfDestructive params) (a', b')) / κ =
              (κ + ∫ x, H x
                ∂(lvKernel .nonSelfDestructive params) (a', b')) / κ := by
                  field_simp
          _ ≤ H (a', b') / κ :=
            div_le_div_of_nonneg_right hStrictH hκ.le
      have hIntegralNonneg :
          0 ≤ ∫ x, G x
              ∂(lvKernel .nonSelfDestructive params) (a', b') :=
        integral_nonneg hGnonneg
      have hmem :
          (a', b') ∈ {s : PopState | nsdInterior s} := hs
      rw [Set.indicator_of_mem hmem]
      simp only [F]
      rw [← ofReal_integral_eq_lintegral_ofReal hIntG
        (Filter.Eventually.of_forall hGnonneg)]
      calc
        1 + ENNReal.ofReal
              (∫ x, G x
                ∂(lvKernel .nonSelfDestructive params) (a', b')) =
            ENNReal.ofReal
              (1 + ∫ x, G x
                ∂(lvKernel .nonSelfDestructive params) (a', b')) := by
                  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
                    hIntegralNonneg]
                  norm_num
        _ ≤ ENNReal.ofReal (G (a', b')) :=
          ENNReal.ofReal_le_ofReal hStrictG
    · have hnotmem :
          s ∉ {s : PopState | nsdInterior s} := hs
      rw [Set.indicator_of_notMem hnotmem, zero_add]
      rw [nsd_boundary_lintegral_zero params F hFboundary s hs]
      rw [hFboundary s hs]
  have hTsum :
      ∑' t : ℕ,
          (kernelIter (lvKernel .nonSelfDestructive params) t) (a, b)
            {s : PopState | nsdInterior s} ≤
        F (a, b) :=
    kernel_occupation_tsum_le_of_lyapunov
      (lvKernel .nonSelfDestructive params)
      {s : PopState | nsdInterior s} F hStep (a, b)
  have hFfinite : F (a, b) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hTsumFinite :
      (∑' t : ℕ,
          (kernelIter (lvKernel .nonSelfDestructive params) t) (a, b)
            {s : PopState | nsdInterior s}) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfinite hTsum
  have hlim :
      Filter.Tendsto
        (fun t =>
          (kernelIter (lvKernel .nonSelfDestructive params) t) (a, b)
            {s : PopState | nsdInterior s})
        Filter.atTop (nhds 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hTsumFinite
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let A : Set (ℕ → PopState) := {ω | ¬consensusReachedEvent ω}
  let C : Set (ℕ → PopState) := {ω | consensusReachedEvent ω}
  have hA_le :
      ∀ t,
        P A ≤
          (kernelIter (lvKernel .nonSelfDestructive params) t) (a, b)
            {s : PopState | nsdInterior s} := by
    intro t
    calc
      P A ≤ P {ω | nsdInterior (ω t)} := by
        apply measure_mono
        intro ω hω
        have hnreach : ¬reachedConsensus (ω t) := by
          intro hreach
          apply hω
          exact lt_of_le_of_lt
            (consensusTime_le_of_reached' ω t hreach)
            (WithTop.coe_lt_top t)
        simp only [reachedConsensus, not_or] at hnreach
        exact ⟨Nat.pos_of_ne_zero hnreach.1,
          Nat.pos_of_ne_zero hnreach.2⟩
      _ = (kernelIter (lvKernel .nonSelfDestructive params) t) (a, b)
            {s : PopState | nsdInterior s} := by
        dsimp [P, lvPathMeasure]
        rw [show ({ω : ℕ → PopState | nsdInterior (ω t)} :
              Set (ℕ → PopState)) =
            (fun ω : ℕ → PopState => ω t) ⁻¹'
              {s : PopState | nsdInterior s} from rfl,
          ← Measure.map_apply (measurable_pi_apply t)
            ((Set.to_countable _).measurableSet),
          homogeneousPathMeasure_dirac_marginal]
  have hAzero : P A = 0 := by
    apply le_antisymm
    · apply ge_of_tendsto' hlim
      exact hA_le
    · exact zero_le
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hCmeas : MeasurableSet C := by
    have hC_union :
        C = ⋃ t : ℕ, {ω : ℕ → PopState | consensusTime ω = ↑t} := by
      ext ω
      constructor
      · intro hω
        change consensusTime ω < ⊤ at hω
        rcases WithTop.ne_top_iff_exists.mp
            (WithTop.lt_top_iff_ne_top.mp hω) with ⟨t, ht⟩
        exact Set.mem_iUnion.mpr ⟨t, ht.symm⟩
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨t, ht⟩
        change consensusTime ω < ⊤
        rw [ht]
        exact WithTop.coe_lt_top t
    rw [hC_union]
    exact MeasurableSet.iUnion fun t =>
      measurableSet_consensusTime_eq_coe t
  have hcomp : Cᶜ = A := by
    ext ω
    simp [C, A]
  have hsum := measure_add_measure_compl hCmeas (μ := P)
  rw [hcomp, hAzero, add_zero, measure_univ] at hsum
  simpa [P, C] using hsum

end LVConsensus
