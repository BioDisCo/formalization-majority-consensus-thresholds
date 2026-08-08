import LVConsensus.SdConsensus

set_option autoImplicit false

namespace LVConsensus

open MeasureTheory ProbabilityTheory

/-! ### Per-individual rate identities for self-destructive competition

The two lemmas below are the self-destructive analogues of
`nsd_neutral_sp0_death_rate` and `nsd_neutral_sp1_death_rate`, which
`LineageAggregation.lean` uses to build the lineage-to-LV bridge in the
non-self-destructive case. They are currently unused, since `thm_sd_intra` is
proved by the `h_ratio_sd` route below rather than by a lineage argument; they
are kept because they are exactly the algebra an SD lineage development needs.
-/

/-- Under neutral SD, the total death+competition rate for species 0,
    `δ·a' + α·a'·b' + γ₀·a'·(a'-1)/2`, factors as `(δ + α₀·(N-1)) · a'`
    where N = a'+b'. This shows the per-individual death+competition rate
    is independent of the species split (a',b') and the species identifier. -/
lemma sd_neutral_sp0_death_rate (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0) (a' b' : ℕ) :
    params.delta * (a' : ℝ) + params.alpha0 * a' * b' +
      params.gamma0 * ((a' : ℝ) * ((a' : ℝ) - 1) / 2) =
    (params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) * a' := by
  rw [hEq0]; ring

/-- Under neutral SD, the total death+competition rate for species 1,
    `δ·b' + α·a'·b' + γ₁·b'·(b'-1)/2`, factors as `(δ + α₀·(N-1)) · b'`.
    Combined with `sd_neutral_sp0_death_rate`, both species have the SAME
    per-individual death+competition rate `δ + α₀·(N-1)`. -/
lemma sd_neutral_sp1_death_rate (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq1 : params.gamma1 = 2 * params.alpha1) (a' b' : ℕ) :
    params.delta * (b' : ℝ) + params.alpha0 * a' * b' +
      params.gamma1 * ((b' : ℝ) * ((b' : ℝ) - 1) / 2) =
    (params.delta + params.alpha0 * ((a' : ℝ) + b' - 1)) * b' := by
  rw [hEq1, hNeutral]; ring

/-- The consensus probability function h(a,b) = a/(a+b). -/
private noncomputable def h_ratio_sd : PopState → ℝ :=
  fun s => (s.1 : ℝ) / ((s.1 : ℝ) + (s.2 : ℝ))

private lemma h_ratio_sd_def (a b : ℕ) :
    h_ratio_sd (a, b) = (a : ℝ) / ((a : ℝ) + (b : ℝ)) := rfl

private lemma h_ratio_sd_bound (s : PopState) : 0 ≤ h_ratio_sd s ∧ h_ratio_sd s ≤ 1 := by
  have h1 : (0 : ℝ) ≤ s.1 := Nat.cast_nonneg s.1
  have h2 : (0 : ℝ) ≤ s.2 := Nat.cast_nonneg s.2
  constructor
  · exact div_nonneg h1 (by linarith)
  · by_cases hn : (s.1 : ℝ) + (s.2 : ℝ) = 0
    · simp [h_ratio_sd, hn]
    · have hpos : 0 < (s.1 : ℝ) + (s.2 : ℝ) :=
        lt_of_le_of_ne (by linarith) (Ne.symm hn)
      exact (div_le_one hpos).mpr (by linarith)

private lemma h_ratio_sd_bnd1 (a' : ℕ) (ha' : 0 < a') : h_ratio_sd (a', 0) = 1 := by
  simp [h_ratio_sd, Nat.cast_pos.mpr ha' |>.ne']

private lemma h_ratio_sd_bnd0 (b' : ℕ) : h_ratio_sd (0, b') = 0 := by
  simp [h_ratio_sd]

/-- The stopped-martingale value used in the corrected Part 1 statement:
    population proportion away from the draw, and value `1/2` at `(0,0)`. -/
private noncomputable def h_ratio_sd_draw : PopState → ℝ :=
  fun s => if s = (0, 0) then 1 / 2 else h_ratio_sd s

private lemma h_ratio_sd_draw_at_draw :
    h_ratio_sd_draw (0, 0) = 1 / 2 := by
  simp [h_ratio_sd_draw]

private lemma h_ratio_sd_draw_of_ne (s : PopState) (hs : s ≠ (0, 0)) :
    h_ratio_sd_draw s = h_ratio_sd s := by
  simp [h_ratio_sd_draw, hs]

private lemma pop_ne_zero_of_fst_pos (a b : ℕ) (ha : 0 < a) :
    (a, b) ≠ (0, 0) := by
  intro h
  exact (Nat.ne_of_gt ha) (Prod.mk.inj h).1

private lemma pop_ne_zero_of_snd_pos (a b : ℕ) (hb : 0 < b) :
    (a, b) ≠ (0, 0) := by
  intro h
  exact (Nat.ne_of_gt hb) (Prod.mk.inj h).2

private lemma h_ratio_sd_draw_bound (s : PopState) :
    0 ≤ h_ratio_sd_draw s ∧ h_ratio_sd_draw s ≤ 1 := by
  by_cases hs : s = (0, 0)
  · subst s
    norm_num [h_ratio_sd_draw]
  · simpa [h_ratio_sd_draw, hs] using h_ratio_sd_bound s

private lemma h_ratio_sd_draw_bnd1 (a' : ℕ) (ha' : 0 < a') :
    h_ratio_sd_draw (a', 0) = 1 := by
  rw [h_ratio_sd_draw_of_ne]
  · exact h_ratio_sd_bnd1 a' ha'
  · intro h
    exact (Nat.ne_of_gt ha') (Prod.mk.inj h).1

private lemma h_ratio_sd_draw_bnd0 (b' : ℕ) (hb' : 0 < b') :
    h_ratio_sd_draw (0, b') = 0 := by
  rw [h_ratio_sd_draw_of_ne]
  · exact h_ratio_sd_bnd0 b'
  · intro h
    exact (Nat.ne_of_gt hb') (Prod.mk.inj h).2

/-- Under neutral SD rates, the population proportion is superharmonic.
    The only strict case is `(1,1)`, where an interspecific reaction produces
    the draw `(0,0)`, to which `h_ratio_sd` assigns value zero. -/
private lemma h_ratio_sd_weighted_super
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    params.beta * a * h_ratio_sd (a + 1, b) +
        params.beta * b * h_ratio_sd (a, b + 1) +
        params.delta * a * h_ratio_sd (a - 1, b) +
        params.delta * b * h_ratio_sd (a, b - 1) +
        (params.alpha0 + params.alpha1) * a * b * h_ratio_sd (a - 1, b - 1) +
        params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) *
          h_ratio_sd (a - 2, b) +
        params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) *
          h_ratio_sd (a, b - 2) ≤
      lvTotalPropensity params (a, b) * h_ratio_sd (a, b) := by
  have hα : params.alpha1 = params.alpha0 := hNeutral.symm
  have hγ1 : params.gamma1 = 2 * params.alpha0 := by rw [hEq1, hNeutral]
  simp only [h_ratio_sd, hα, hEq0, hγ1, lvTotalPropensity]
  have ha1R : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb1R : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  simp only [Nat.cast_sub (show 1 ≤ a from ha), Nat.cast_sub (show 1 ≤ b from hb)]
  rcases (show (a = 1 ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b) ∨
      (2 ≤ a ∧ b = 1) ∨ (a = 1 ∧ 2 ≤ b) from by omega) with
    ⟨rfl, rfl⟩ | ⟨ha2, hb2⟩ | ⟨ha2, rfl⟩ | ⟨rfl, hb2⟩
  · norm_num
    nlinarith [params.beta_nonneg, params.delta_nonneg]
  · have ha2R : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
    simp only [Nat.cast_sub ha2, Nat.cast_sub hb2, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one]
    apply le_of_eq
    have hne_sum : (a : ℝ) + b ≠ 0 := by linarith
    have hne_p1 : (a : ℝ) + 1 + b ≠ 0 := by linarith
    have hne_p1' : (a : ℝ) + (b + 1) ≠ 0 := by linarith
    have hne_m1 : (a : ℝ) - 1 + b ≠ 0 := by linarith
    have hne_m1' : (a : ℝ) + (b - 1) ≠ 0 := by linarith
    have hne_m2 : (a : ℝ) - 1 + (b - 1) ≠ 0 := by linarith
    have hne_m2' : (a : ℝ) - 2 + b ≠ 0 := by linarith
    have hne_m2'' : (a : ℝ) + (b - 2) ≠ 0 := by linarith
    field_simp [hne_sum, hne_p1, hne_p1', hne_m1, hne_m1', hne_m2,
      hne_m2', hne_m2'']
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 800000 in
        ring_nf
  · have ha2R : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    simp only [Nat.cast_sub ha2, Nat.cast_add, Nat.cast_one]
    norm_num
    apply le_of_eq
    have hne_sum : (a : ℝ) + 1 ≠ 0 := by linarith
    have hne_p1 : (a : ℝ) + 2 ≠ 0 := by linarith
    have hne_m1 : (a : ℝ) - 1 ≠ 0 := by linarith
    have hne_m1' : (-1 : ℝ) + a ≠ 0 := by linarith
    field_simp [hne_sum, hne_p1, hne_m1, hne_m1']
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 800000 in
        ring_nf
    field_simp [hne_m1']
    ring
  · have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
    simp only [Nat.cast_sub hb2, Nat.cast_add, Nat.cast_one]
    norm_num
    apply le_of_eq
    have hne_sum : (1 : ℝ) + b ≠ 0 := by linarith
    have hne_p1 : (2 : ℝ) + b ≠ 0 := by linarith
    have hne_m1 : (b : ℝ) - 1 ≠ 0 := by linarith
    have hne_m1' : (-1 : ℝ) + b ≠ 0 := by linarith
    field_simp [hne_sum, hne_p1, hne_m1, hne_m1']
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 800000 in
        ring_nf
    field_simp [hne_m1']
    ring

/-- With the draw assigned value `1/2`, the neutral SD population proportion
    is exactly harmonic at every interior state. -/
private lemma h_ratio_sd_draw_weighted_harmonic
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    params.beta * a * h_ratio_sd_draw (a + 1, b) +
        params.beta * b * h_ratio_sd_draw (a, b + 1) +
        params.delta * a * h_ratio_sd_draw (a - 1, b) +
        params.delta * b * h_ratio_sd_draw (a, b - 1) +
        (params.alpha0 + params.alpha1) * a * b *
          h_ratio_sd_draw (a - 1, b - 1) +
        params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) *
          h_ratio_sd_draw (a - 2, b) +
        params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) *
          h_ratio_sd_draw (a, b - 2) =
      lvTotalPropensity params (a, b) * h_ratio_sd_draw (a, b) := by
  have hα : params.alpha1 = params.alpha0 := hNeutral.symm
  have hγ1 : params.gamma1 = 2 * params.alpha0 := by rw [hEq1, hNeutral]
  have ha1R : (1 : ℝ) ≤ (a : ℝ) := Nat.one_le_cast.mpr ha
  have hb1R : (1 : ℝ) ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  rcases (show (a = 1 ∧ b = 1) ∨ (2 ≤ a ∧ 2 ≤ b) ∨
      (2 ≤ a ∧ b = 1) ∨ (a = 1 ∧ 2 ≤ b) from by omega) with
    ⟨rfl, rfl⟩ | ⟨ha2, hb2⟩ | ⟨ha2, rfl⟩ | ⟨rfl, hb2⟩
  · norm_num [h_ratio_sd_draw, h_ratio_sd, hα, hEq0, hγ1,
      lvTotalPropensity]
    ring
  · have ha2R : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
    have hne_b0 : (a + 1, b) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ hb
    have hne_b1 : (a, b + 1) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    have hne_d0 : (a - 1, b) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ hb
    have hne_d1 : (a, b - 1) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    have hne_inter : (a - 1, b - 1) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ (by omega)
    have hne_i0 : (a - 2, b) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ hb
    have hne_i1 : (a, b - 2) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    have hne_cur : (a, b) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    rw [h_ratio_sd_draw_of_ne _ hne_b0, h_ratio_sd_draw_of_ne _ hne_b1,
      h_ratio_sd_draw_of_ne _ hne_d0, h_ratio_sd_draw_of_ne _ hne_d1,
      h_ratio_sd_draw_of_ne _ hne_inter, h_ratio_sd_draw_of_ne _ hne_i0,
      h_ratio_sd_draw_of_ne _ hne_i1, h_ratio_sd_draw_of_ne _ hne_cur]
    simp only [h_ratio_sd, hα, hEq0, hγ1, lvTotalPropensity,
      Nat.cast_sub (show 1 ≤ a from ha), Nat.cast_sub (show 1 ≤ b from hb),
      Nat.cast_sub ha2, Nat.cast_sub hb2, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one]
    have hne_sum : (a : ℝ) + b ≠ 0 := by linarith
    have hne_p1 : (a : ℝ) + 1 + b ≠ 0 := by linarith
    have hne_p1' : (a : ℝ) + (b + 1) ≠ 0 := by linarith
    have hne_m1 : (a : ℝ) - 1 + b ≠ 0 := by linarith
    have hne_m1' : (a : ℝ) + (b - 1) ≠ 0 := by linarith
    have hne_m2 : (a : ℝ) - 1 + (b - 1) ≠ 0 := by linarith
    have hne_m2' : (a : ℝ) - 2 + b ≠ 0 := by linarith
    have hne_m2'' : (a : ℝ) + (b - 2) ≠ 0 := by linarith
    field_simp [hne_sum, hne_p1, hne_p1', hne_m1, hne_m1', hne_m2,
      hne_m2', hne_m2'']
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 800000 in
        ring_nf
  · have ha2R : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    have hne_b0 : (a + 1, 1) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ one_pos
    have hne_b1 : (a, 2) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    have hne_d0 : (a - 1, 1) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ one_pos
    have hne_d1 : (a, 0) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    have hne_inter : (a - 1, 0) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ (by omega)
    have hne_i0 : (a - 2, 1) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ one_pos
    have hne_cur : (a, 1) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ ha
    rw [h_ratio_sd_draw_of_ne _ hne_b0, h_ratio_sd_draw_of_ne _ hne_b1,
      h_ratio_sd_draw_of_ne _ hne_d0, h_ratio_sd_draw_of_ne _ hne_d1,
      h_ratio_sd_draw_of_ne _ hne_inter, h_ratio_sd_draw_of_ne _ hne_i0,
      h_ratio_sd_draw_of_ne _ hne_cur]
    simp only [h_ratio_sd, hα, hEq0, hγ1, lvTotalPropensity,
      Nat.cast_sub (show 1 ≤ a from ha), Nat.cast_sub ha2, Nat.cast_add,
      Nat.cast_one]
    norm_num
    have hne_sum : (a : ℝ) + 1 ≠ 0 := by linarith
    have hne_p1 : (a : ℝ) + 2 ≠ 0 := by linarith
    have hne_m1 : (a : ℝ) - 1 ≠ 0 := by linarith
    have hne_m1' : (-1 : ℝ) + a ≠ 0 := by linarith
    field_simp [hne_sum, hne_p1, hne_m1, hne_m1']
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 800000 in
        ring_nf
    field_simp [hne_m1']
    ring
  · have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
    have hne_b0 : (2, b) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ hb
    have hne_b1 : (1, b + 1) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ one_pos
    have hne_d0 : (0, b) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ hb
    have hne_d1 : (1, b - 1) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ one_pos
    have hne_inter : (0, b - 1) ≠ (0, 0) :=
      pop_ne_zero_of_snd_pos _ _ (by omega)
    have hne_i1 : (1, b - 2) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ one_pos
    have hne_cur : (1, b) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos _ _ one_pos
    rw [h_ratio_sd_draw_of_ne _ hne_b0, h_ratio_sd_draw_of_ne _ hne_b1,
      h_ratio_sd_draw_of_ne _ hne_d0, h_ratio_sd_draw_of_ne _ hne_d1,
      h_ratio_sd_draw_of_ne _ hne_inter,
      h_ratio_sd_draw_of_ne _ hne_i1, h_ratio_sd_draw_of_ne _ hne_cur]
    simp only [h_ratio_sd, hα, hEq0, hγ1, lvTotalPropensity,
      Nat.cast_sub (show 1 ≤ b from hb), Nat.cast_sub hb2, Nat.cast_add,
      Nat.cast_one]
    norm_num
    have hne_sum : (1 : ℝ) + b ≠ 0 := by linarith
    have hne_p1 : (2 : ℝ) + b ≠ 0 := by linarith
    have hne_m1 : (b : ℝ) - 1 ≠ 0 := by linarith
    have hne_m1' : (-1 : ℝ) + b ≠ 0 := by linarith
    field_simp [hne_sum, hne_p1, hne_m1, hne_m1']
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 800000 in
        ring_nf
    field_simp [hne_m1']
    ring

/-- Integral form of the corrected one-step SD martingale calculation. -/
private lemma h_ratio_sd_draw_harmonic_interior
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    ∫ x, h_ratio_sd_draw x
        ∂(lvKernel .selfDestructive params) (a, b) =
      h_ratio_sd_draw (a, b) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have ha1R : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
  have hb1R : (1 : ℝ) ≤ b := Nat.one_le_cast.mpr hb
  have hφ : lvTotalPropensity params (a, b) ≠ 0 := by
    have hpos : 0 < params.alpha0 * (a : ℝ) * (b : ℝ) :=
      mul_pos (mul_pos hAlpha haR) hbR
    have hγ0 : 0 ≤ params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) :=
      mul_nonneg params.gamma0_nonneg
        (div_nonneg (mul_nonneg haR.le (by linarith)) (by norm_num))
    have hγ1 : 0 ≤ params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) :=
      mul_nonneg params.gamma1_nonneg
        (div_nonneg (mul_nonneg hbR.le (by linarith)) (by norm_num))
    have htotal : 0 < lvTotalPropensity params (a, b) := by
      simp only [lvTotalPropensity]
      nlinarith [mul_nonneg params.beta_nonneg haR.le,
        mul_nonneg params.beta_nonneg hbR.le,
        mul_nonneg params.delta_nonneg haR.le,
        mul_nonneg params.delta_nonneg hbR.le,
        mul_nonneg (mul_nonneg params.alpha1_nonneg haR.le) hbR.le]
    exact htotal.ne'
  exact lvKernel_sd_harmonic_integral params h_ratio_sd_draw a b ha hb hφ
    (h_ratio_sd_draw_weighted_harmonic
      params hAlpha hNeutral hEq0 hEq1 a b ha hb)

/-- The stopped kernel preserves the corrected SD proportion at every finite
    time. This is the bounded-martingale identity used by Part 1. -/
private lemma h_ratio_sd_draw_absorb_iter
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b N : ℕ)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    ∫ x, h_ratio_sd_draw x
        ∂(kernelIter (lvKernelAbsorb .selfDestructive params) N) (a, b) =
      h_ratio_sd_draw (a, b) := by
  have hAll : ∀ s : PopState,
      ∫ x, h_ratio_sd_draw x
          ∂(lvKernelAbsorb .selfDestructive params) s =
        h_ratio_sd_draw s := by
    rintro ⟨x, y⟩
    by_cases hx : x = 0
    · rw [lvKernelAbsorb_consensus .selfDestructive params (x, y) (Or.inl hx)]
      exact integral_dirac' h_ratio_sd_draw (x, y)
        (measurable_of_countable h_ratio_sd_draw).stronglyMeasurable
    · by_cases hy : y = 0
      · rw [lvKernelAbsorb_consensus .selfDestructive params (x, y) (Or.inr hy)]
        exact integral_dirac' h_ratio_sd_draw (x, y)
          (measurable_of_countable h_ratio_sd_draw).stronglyMeasurable
      · rw [lvKernelAbsorb_interior .selfDestructive params (x, y)
          (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy)]
        exact h_ratio_sd_draw_harmonic_interior params hAlpha hNeutral hEq0 hEq1
          x y (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy)
  apply kernelIter_harmonic_integral
    (lvKernelAbsorb .selfDestructive params) h_ratio_sd_draw (a, b) hAll
  intro n
  haveI : IsProbabilityMeasure
      ((kernelIter (lvKernelAbsorb .selfDestructive params) n) (a, b)) :=
    (kernelIter_isMarkov n).isProbabilityMeasure (a, b)
  apply Integrable.mono (integrable_const (1 : ℝ))
    (measurable_of_countable h_ratio_sd_draw).aestronglyMeasurable
  filter_upwards with s
  simp only [Real.norm_eq_abs, norm_one]
  exact abs_le.mpr
    ⟨by linarith [(h_ratio_sd_draw_bound s).1],
      (h_ratio_sd_draw_bound s).2⟩

/-- One-step superharmonicity of the population proportion for the neutral SD
    jump chain. -/
private lemma h_ratio_sd_superharmonic
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (s : PopState)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    ∫ x, h_ratio_sd x ∂(lvKernel .selfDestructive params) s ≤ h_ratio_sd s := by
  rcases s with ⟨a, b⟩
  have hInt : Integrable h_ratio_sd ((lvKernel .selfDestructive params) (a, b)) := by
    haveI : IsProbabilityMeasure ((lvKernel .selfDestructive params) (a, b)) :=
      by infer_instance
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h_ratio_sd).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(h_ratio_sd_bound x).1],
      (h_ratio_sd_bound x).2⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hnull := sd_kernel_species0_dead_absorbing_general params (0, b) rfl
    have hae : h_ratio_sd =ᵐ[(lvKernel .selfDestructive params) (0, b)] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      apply le_antisymm _ zero_le
      calc
        (lvKernel .selfDestructive params) (0, b)
              {x | h_ratio_sd x ≠ (0 : PopState → ℝ) x}
            ≤ (lvKernel .selfDestructive params) (0, b) {x | x.1 ≠ 0} := by
                apply measure_mono
                intro x hx hx0
                exact hx (by simp [h_ratio_sd, hx0])
        _ = 0 := hnull
    rw [integral_congr_ae hae]
    simp [h_ratio_sd]
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · haveI : IsProbabilityMeasure ((lvKernel .selfDestructive params) (a, 0)) :=
        by infer_instance
      calc
        ∫ x, h_ratio_sd x ∂(lvKernel .selfDestructive params) (a, 0)
            ≤ ∫ _x, (1 : ℝ) ∂(lvKernel .selfDestructive params) (a, 0) := by
                exact integral_mono hInt (integrable_const (1 : ℝ))
                  (fun x => (h_ratio_sd_bound x).2)
        _ = 1 := by simp
        _ = h_ratio_sd (a, 0) := (h_ratio_sd_bnd1 a ha).symm
    · have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
      have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
      have ha1R : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr ha
      have hb1R : (1 : ℝ) ≤ b := Nat.one_le_cast.mpr hb
      have hφ : lvTotalPropensity params (a, b) ≠ 0 := by
        have hpos : 0 < params.alpha0 * (a : ℝ) * (b : ℝ) :=
          mul_pos (mul_pos hAlpha haR) hbR
        have hγ0 : 0 ≤ params.gamma0 * ((a : ℝ) * ((a : ℝ) - 1) / 2) := by
          exact mul_nonneg params.gamma0_nonneg
            (div_nonneg (mul_nonneg haR.le (by linarith [ha1R])) (by norm_num))
        have hγ1 : 0 ≤ params.gamma1 * ((b : ℝ) * ((b : ℝ) - 1) / 2) := by
          exact mul_nonneg params.gamma1_nonneg
            (div_nonneg (mul_nonneg hbR.le (by linarith [hb1R])) (by norm_num))
        have htotal : 0 < lvTotalPropensity params (a, b) := by
          simp only [lvTotalPropensity]
          nlinarith [mul_nonneg params.beta_nonneg haR.le,
            mul_nonneg params.beta_nonneg hbR.le,
            mul_nonneg params.delta_nonneg haR.le,
            mul_nonneg params.delta_nonneg hbR.le,
            mul_nonneg (mul_nonneg params.alpha1_nonneg haR.le) hbR.le]
        exact htotal.ne'
      exact lvKernel_sd_superharmonic_integral params h_ratio_sd a b ha hb hφ
        (h_ratio_sd_weighted_super params hAlpha hNeutral hEq0 hEq1 a b ha hb)

/-- ENNReal form of `h_ratio_sd_superharmonic`, used by the finite-hitting
    optional-stopping bound. -/
private lemma h_ratio_sd_ennreal_superharmonic
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (s : PopState)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    ∫⁻ x, ENNReal.ofReal (h_ratio_sd x)
        ∂(lvKernel .selfDestructive params) s ≤
      ENNReal.ofReal (h_ratio_sd s) := by
  have hInt : Integrable h_ratio_sd ((lvKernel .selfDestructive params) s) := by
    haveI : IsProbabilityMeasure ((lvKernel .selfDestructive params) s) := by
      infer_instance
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h_ratio_sd).aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr ⟨by linarith [(h_ratio_sd_bound x).1],
      (h_ratio_sd_bound x).2⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun x => (h_ratio_sd_bound x).1)]
  exact ENNReal.ofReal_le_ofReal
    (h_ratio_sd_superharmonic params hAlpha hNeutral hEq0 hEq1 s)

/-- Paper `thm:sd-intra` (restricted unconditional subcase).
    Proves the STRONGER equality ρ = a/(a+b) under the restricted conditions
    β = δ = 0 and Odd(a+b).  With β=δ=0, SD events change population by ±2,
    so odd parity makes (0,0) unreachable; the chain always reaches single-species
    consensus and the harmonic function h(a,b) = a/(a+b) gives exact equality.
    The paper's corrected statement only claims ρ ≤ a/(a+b) for general β,δ
    (Part 2, see `thm_sd_intra_part1` below for Part 1 scaffold). -/
theorem thm_sd_intra
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hBeta : params.beta = 0)
    (hDelta : params.delta = 0)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    (hOdd : Odd (a + b))
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    majorityConsensusProb LVVariant.selfDestructive params (a, b) =
      ENNReal.ofReal ((a : Real) / (a + b)) := by
  rw [← h_ratio_sd_def]
  apply consensus_eq_harmonic_sd params h_ratio_sd a b hposA hposB hba hOdd
    hBeta hDelta
    (by rw [hEq0]; linarith)
    (by rw [hEq1, ← hNeutral]; linarith)
    (by linarith [params.alpha1_nonneg])
    h_ratio_sd_bound
  · -- Harmonicity: weighted sum = φ * h for SD with β=δ=0, γ=2α at odd-total states
    intro a' b' ha' hb' hodd
    simp only [h_ratio_sd]
    -- Substitute β=δ=0 to kill birth/death terms
    have hα : params.alpha1 = params.alpha0 := hNeutral.symm
    have hγ1 : params.gamma1 = 2 * params.alpha0 := by rw [hEq1, hNeutral]
    simp only [hBeta, hDelta, hα, hEq0, hγ1, lvTotalPropensity, zero_mul, zero_add,
      add_zero]
    -- With Odd(a'+b') and a',b'≥1: a'+b'≥3
    obtain ⟨k, hk⟩ := hodd
    have ha1R : (1 : ℝ) ≤ (a' : ℝ) := Nat.one_le_cast.mpr ha'
    have hb1R : (1 : ℝ) ≤ (b' : ℝ) := Nat.one_le_cast.mpr hb'
    -- Convert Nat subtractions for -1 (always valid since a',b'≥1)
    simp only [Nat.cast_sub (show 1 ≤ a' from ha'), Nat.cast_sub (show 1 ≤ b' from hb')]
    -- Case split on a'≥2 and b'≥2 (can't both be 1 since Odd(a'+b'))
    rcases (show (2 ≤ a' ∧ 2 ≤ b') ∨ (2 ≤ a' ∧ b' = 1) ∨ (a' = 1 ∧ 2 ≤ b') from by omega)
      with ⟨ha2, hb2⟩ | ⟨ha2, hb1⟩ | ⟨ha1, hb2⟩
    · -- a'≥2, b'≥2: all terms present, convert -2 casts
      have ha2R : (2 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha2
      have hb2R : (2 : ℝ) ≤ (b' : ℝ) := by exact_mod_cast hb2
      simp only [Nat.cast_sub ha2, Nat.cast_sub hb2, Nat.cast_ofNat, Nat.cast_one]
      -- Provide nonzero denominators in the exact form field_simp produces
      have hne_sum : (↑a' : ℝ) + ↑b' ≠ 0 := by linarith
      have hne_m2 : (-2 : ℝ) + ↑a' + ↑b' ≠ 0 := by linarith
      have hne1 : (↑a' : ℝ) - 1 + (↑b' - 1) ≠ 0 := by linarith
      have hne2 : (↑a' : ℝ) - 2 + ↑b' ≠ 0 := by linarith
      have hne3 : (↑a' : ℝ) + (↑b' - 2) ≠ 0 := by linarith
      field_simp [hne_sum, hne_m2, hne1, hne2, hne3]
      ring
    · -- a'≥2, b'=1: intra1 coeff b'*(b'-1)/2=0
      subst hb1
      have ha2R : (2 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha2
      simp only [Nat.cast_sub ha2, Nat.cast_one]
      norm_num
      have : (a' : ℝ) + 1 ≠ 0 := by linarith
      have : (a' : ℝ) - 1 ≠ 0 := by linarith
      have : (a' : ℝ) - 2 + 1 ≠ 0 := by linarith
      field_simp
      ring
    · -- a'=1, b'≥2: intra0 coeff a'*(a'-1)/2=0
      subst ha1
      have hb2R : (2 : ℝ) ≤ (b' : ℝ) := by exact_mod_cast hb2
      simp only [Nat.cast_sub hb2, Nat.cast_one]
      norm_num
      have : (1 : ℝ) + b' ≠ 0 := by linarith
      have : (b' : ℝ) - 1 ≠ 0 := by linarith
      have : (1 : ℝ) + (b' - 2) ≠ 0 := by linarith
      field_simp
      ring
  · exact h_ratio_sd_bnd1
  · intro b'; exact h_ratio_sd_bnd0 b'

-- ============================================================================
-- Helper lemmas for thm_sd_intra_part1
-- ============================================================================

/-- HELPER: When a > b, majorityConsensusEvent (a,b) (swapTraj ω) describes
    species 1 winning, which is equivalent to majorityConsensusEvent (b,a) ω
    since species 1 becomes the majority from state (b,a).

    PROOF IDEA:
    1. Unfold majorityConsensusEvent definition for both sides
    2. Note: species0Majority (a,b) = true and species0Majority (b,a) = false when a > b
    3. LHS simplifies to: consensusTime ω = t ∧ (ω t).2 > 0 ∧ (ω t).1 = 0 (species 1 wins)
    4. RHS simplifies to: consensusTime ω = t ∧ (ω t).2 > 0 ∧ (ω t).1 = 0 (species 1 wins)
    5. Both sides are identical! -/
private lemma majorityConsensusEvent_swap_equiv
    (a b : Nat) (hba : b < a) (ω : Nat → PopState) :
    majorityConsensusEvent (a, b) (swapTraj ω) ↔
    majorityConsensusEvent (b, a) ω := by
  -- Unfold definition of majorityConsensusEvent
  unfold majorityConsensusEvent
  -- Both sides use consensusTime; use consensusTime_swapTraj to unify
  rw [consensusTime_swapTraj]
  -- Now simplify the species0Majority checks
  unfold species0Majority
  simp only [swapTraj_apply, PopState.swap]
  -- Species `0` is the designated majority in `(a,b)`, but not in `(b,a)`.
  have hab : b ≤ a := Nat.le_of_lt hba
  have hnba : ¬a ≤ b := Nat.not_le_of_gt hba
  simp [hab, hnba]

/-- Event that one species wins (reaches consensus with a positive survivor).
    This is the event where consensusTime is finite AND the state at consensus
    is not the draw state (0,0), i.e., at least one species has positive count. -/
def oneSpeciesWinsEvent (ω : ℕ → PopState) : Prop :=
  match consensusTime ω with
  | ⊤ => False
  | (t : ℕ) => ((ω t).1 > 0 ∧ (ω t).2 = 0) ∨ ((ω t).1 = 0 ∧ (ω t).2 > 0)

/-- Event that the first consensus state is the draw `(0,0)`. -/
def drawAtConsensusEvent (ω : ℕ → PopState) : Prop :=
  match consensusTime ω with
  | ⊤ => False
  | (t : ℕ) => ω t = (0, 0)

/-- Once the stopped LV kernel is at consensus, every iterate remains the
    Dirac mass at that consensus state. -/
private lemma lvKernelAbsorb_iter_consensus
    (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)]
    (N : ℕ) (s : PopState) (hs : reachedConsensus s) :
    (kernelIter (lvKernelAbsorb v params) N) s = Measure.dirac s := by
  induction N with
  | zero =>
      simp [kernelIter_zero, Kernel.id_apply]
  | succ N ih =>
      simp only [kernelIter_succ]
      rw [Kernel.comp_apply, ih]
      simp only [Measure.dirac_bind (Kernel.measurable _)]
      exact lvKernelAbsorb_consensus v params s hs

/-- First consensus occurs by time `N` and its state lies in `A`. -/
private def consensusOutcomeBy
    (A : Set PopState) (N : ℕ) (ω : ℕ → PopState) : Prop :=
  match consensusTime ω with
  | ⊤ => False
  | (t : ℕ) => t ≤ N ∧ ω t ∈ A

/-- The first consensus state belongs to `A`. -/
private def consensusOutcome
    (A : Set PopState) (ω : ℕ → PopState) : Prop :=
  match consensusTime ω with
  | ⊤ => False
  | (t : ℕ) => ω t ∈ A

private lemma consensusOutcome_eq_iUnion
    (A : Set PopState) :
    {ω : ℕ → PopState | consensusOutcome A ω} =
      ⋃ N : ℕ, {ω | consensusOutcomeBy A N ω} := by
  ext ω
  constructor
  · intro h
    change consensusOutcome A ω at h
    cases hct : consensusTime ω with
    | top =>
        rw [consensusOutcome, hct] at h
        exact h.elim
    | coe t =>
        rw [consensusOutcome, hct] at h
        exact Set.mem_iUnion.mpr ⟨t, by
          simp only [Set.mem_setOf_eq, consensusOutcomeBy, hct]
          exact ⟨le_rfl, h⟩⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨N, hN⟩
    change consensusOutcomeBy A N ω at hN
    change consensusOutcome A ω
    cases hct : consensusTime ω with
    | top =>
        rw [consensusOutcomeBy, hct] at hN
        exact hN.elim
    | coe t =>
        rw [consensusOutcomeBy, hct] at hN
        rw [consensusOutcome, hct]
        exact hN.2

private lemma consensusOutcomeBy_monotone
    (A : Set PopState) :
    Monotone (fun N : ℕ => {ω : ℕ → PopState | consensusOutcomeBy A N ω}) := by
  intro N M hNM ω hω
  change consensusOutcomeBy A N ω at hω
  change consensusOutcomeBy A M ω
  cases hct : consensusTime ω with
  | top =>
      rw [consensusOutcomeBy, hct] at hω
      exact hω.elim
  | coe t =>
      rw [consensusOutcomeBy, hct] at hω
      rw [consensusOutcomeBy, hct]
      exact ⟨hω.1.trans hNM, hω.2⟩

/-- If the initial state is already at consensus, the bounded outcome event
    only records whether that initial state belongs to the requested outcome
    set. -/
private lemma consensusOutcomeBy_of_initial_consensus_iff
    (A : Set PopState) (N : ℕ) (s : PopState) (ω : ℕ → PopState)
    (hω0 : ω 0 = s) (hs : reachedConsensus s) :
    consensusOutcomeBy A N ω ↔ s ∈ A := by
  have hct : consensusTime ω = (0 : ℕ) := by
    rw [consensusTime_eq_coe_iff]
    constructor
    · simpa [hω0] using hs
    · intro j hj
      omega
  simp [consensusOutcomeBy, hct, hω0]

private lemma measurableSet_consensusOutcomeBy
    (A : Set PopState) (N : ℕ) :
    MeasurableSet {ω : ℕ → PopState | consensusOutcomeBy A N ω} := by
  have hEq :
      {ω : ℕ → PopState | consensusOutcomeBy A N ω} =
        ⋃ t ∈ Finset.range (N + 1),
          {ω : ℕ → PopState | consensusTime ω = ↑t} ∩
            (fun ω : ℕ → PopState => ω t) ⁻¹' A := by
    ext ω
    constructor
    · intro h
      change consensusOutcomeBy A N ω at h
      cases hct : consensusTime ω with
      | top =>
          rw [consensusOutcomeBy, hct] at h
          exact h.elim
      | coe t =>
          rw [consensusOutcomeBy, hct] at h
          have ht : t ≤ N := h.1
          refine Set.mem_iUnion₂.mpr ⟨t, Finset.mem_range.mpr (by omega), ?_⟩
          exact ⟨hct, h.2⟩
    · intro h
      rcases Set.mem_iUnion₂.mp h with ⟨t, ht, hct, hA⟩
      change consensusTime ω = ↑t at hct
      change ω t ∈ A at hA
      change consensusOutcomeBy A N ω
      unfold consensusOutcomeBy
      rw [hct]
      have ht' : t < N + 1 := Finset.mem_range.mp ht
      have htN : t ≤ N := by
        exact Nat.lt_succ_iff.mp (by simpa [Nat.succ_eq_add_one] using ht')
      exact ⟨htN, hA⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun t =>
    MeasurableSet.iUnion fun _ =>
      (measurableSet_consensusTime_eq_coe t).inter
        ((Set.to_countable A).measurableSet.preimage (measurable_pi_apply t))

private lemma measurableSet_consensusOutcome
    (A : Set PopState) :
    MeasurableSet {ω : ℕ → PopState | consensusOutcome A ω} := by
  rw [consensusOutcome_eq_iUnion A]
  exact MeasurableSet.iUnion fun N =>
    measurableSet_consensusOutcomeBy A N

private lemma consensusOutcomeBy_succ_shift_iff
    (A : Set PopState) (N : ℕ) (ω : ℕ → PopState)
    (h0 : ¬reachedConsensus (ω 0)) :
    consensusOutcomeBy A (N + 1) ω ↔
      consensusOutcomeBy A N (pathShift 1 ω) := by
  cases hct : consensusTime ω with
  | top =>
      have hs := consensusTime_pathShift_one_eq_top ω hct
      rw [consensusOutcomeBy, hct, consensusOutcomeBy, hs]
  | coe t =>
      cases t with
      | zero =>
          have hreach := reachedConsensus_at_consensusTime' ω 0 hct
          exact (h0 hreach).elim
      | succ t =>
          have hs := consensusTime_pathShift_one_eq_succ ω t hct
          simp only [consensusOutcomeBy, hct, hs]
          change
            (t + 1 ≤ N + 1 ∧ ω (t + 1) ∈ A) ↔
              (t ≤ N ∧ ω (1 + t) ∈ A)
          constructor
          · rintro ⟨ht, hA⟩
            exact ⟨by omega, by simpa [Nat.add_comm] using hA⟩
          · rintro ⟨ht, hA⟩
            exact ⟨by omega, by simpa [Nat.add_comm] using hA⟩

private lemma lvPath_initial_ae
    (v : LVVariant) (params : LVParams) (s : PopState)
    [IsMarkovKernel (lvKernel v params)] :
    ∀ᵐ ω ∂lvPathMeasure v params s, ω 0 = s := by
  rw [ae_iff]
  simpa [lvPathMeasure] using
    homogeneousPathMeasure_initial_ne_null (lvKernel v params) s

private lemma consensusOutcomeBy_measure_succ
    (v : LVVariant) (params : LVParams)
    (A : Set PopState) (N : ℕ) (s : PopState)
    (hs : ¬reachedConsensus s)
    [IsMarkovKernel (lvKernel v params)] :
    lvPathMeasure v params s
        {ω | consensusOutcomeBy A (N + 1) ω} =
      ∫⁻ x, lvPathMeasure v params x
          {ω | consensusOutcomeBy A N ω}
        ∂(lvKernel v params) s := by
  have hEvent :
      lvPathMeasure v params s
          {ω | consensusOutcomeBy A (N + 1) ω} =
        lvPathMeasure v params s
          ((pathShift 1) ⁻¹'
            {ω | consensusOutcomeBy A N ω}) := by
    apply measure_congr
    filter_upwards [lvPath_initial_ae v params s] with ω hω0
    apply propext
    change consensusOutcomeBy A (N + 1) ω ↔
      consensusOutcomeBy A N (pathShift 1 ω)
    exact consensusOutcomeBy_succ_shift_iff A N ω (hω0 ▸ hs)
  rw [hEvent]
  simpa [lvPathMeasure, kernelIter_one_generic] using
    homogeneousPathMeasure_shift_apply
      (lvKernel v params) s 1
      {ω | consensusOutcomeBy A N ω}
      (measurableSet_consensusOutcomeBy A N)

/-- The stopped `N`-step kernel and the original path law assign the same
    mass to every consensus outcome reached by time `N`. -/
private lemma lvKernelAbsorb_outcomeBy_eq
    (v : LVVariant) (params : LVParams)
    (A : Set PopState) (hA : MeasurableSet A)
    (hAbsorb : ∀ s ∈ A, reachedConsensus s)
    [IsMarkovKernel (lvKernel v params)] :
    ∀ (N : ℕ) (s : PopState),
      (kernelIter (lvKernelAbsorb v params) N) s A =
        lvPathMeasure v params s {ω | consensusOutcomeBy A N ω} := by
  intro N
  induction N with
  | zero =>
      intro s
      letI : IsProbabilityMeasure (lvPathMeasure v params s) := by
        dsimp [lvPathMeasure, homogeneousPathMeasure]
        infer_instance
      rw [kernelIter_zero, Kernel.id_apply, Measure.dirac_apply' _ hA]
      by_cases hsA : s ∈ A
      · simp only [Set.indicator_of_mem hsA]
        have hs : reachedConsensus s := hAbsorb s hsA
        calc
          1 = lvPathMeasure v params s Set.univ := by
            rw [measure_univ]
          _ = lvPathMeasure v params s
                {ω | consensusOutcomeBy A 0 ω} := by
            apply measure_congr
            filter_upwards [lvPath_initial_ae v params s] with ω hω0
            apply propext
            constructor
            · intro _
              exact (consensusOutcomeBy_of_initial_consensus_iff
                A 0 s ω hω0 hs).mpr hsA
            · intro _
              trivial
      · simp only [Set.indicator_of_notMem hsA]
        calc
          0 = lvPathMeasure v params s ∅ := by rw [measure_empty]
          _ = lvPathMeasure v params s
                {ω | consensusOutcomeBy A 0 ω} := by
            apply measure_congr
            filter_upwards [lvPath_initial_ae v params s] with ω hω0
            apply propext
            constructor
            · intro h
              exact h.elim
            · intro hout
              change consensusOutcomeBy A 0 ω at hout
              cases hct : consensusTime ω with
              | top =>
                  rw [consensusOutcomeBy, hct] at hout
                  exact hout.elim
              | coe t =>
                  rw [consensusOutcomeBy, hct] at hout
                  have ht : t = 0 := Nat.eq_zero_of_le_zero hout.1
                  subst t
                  exact hsA (by simpa [hω0] using hout.2)
  | succ N ih =>
      intro s
      letI : IsProbabilityMeasure (lvPathMeasure v params s) := by
        dsimp [lvPathMeasure, homogeneousPathMeasure]
        infer_instance
      by_cases hs : reachedConsensus s
      · rw [lvKernelAbsorb_iter_consensus v params (N + 1) s hs,
          Measure.dirac_apply' _ hA]
        by_cases hsA : s ∈ A
        · simp only [Set.indicator_of_mem hsA]
          calc
            1 = lvPathMeasure v params s Set.univ := by
              rw [measure_univ]
            _ = lvPathMeasure v params s
                  {ω | consensusOutcomeBy A (N + 1) ω} := by
              apply measure_congr
              filter_upwards [lvPath_initial_ae v params s] with ω hω0
              apply propext
              constructor
              · intro _
                exact (consensusOutcomeBy_of_initial_consensus_iff
                  A (N + 1) s ω hω0 hs).mpr hsA
              · intro _
                trivial
        · simp only [Set.indicator_of_notMem hsA]
          calc
            0 = lvPathMeasure v params s ∅ := by rw [measure_empty]
            _ = lvPathMeasure v params s
                  {ω | consensusOutcomeBy A (N + 1) ω} := by
              apply measure_congr
              filter_upwards [lvPath_initial_ae v params s] with ω hω0
              apply propext
              constructor
              · intro h
                exact h.elim
              · intro hout
                exact hsA
                  ((consensusOutcomeBy_of_initial_consensus_iff
                    A (N + 1) s ω hω0 hs).mp hout)
      · have hs1 : 0 < s.1 := by
          simp only [reachedConsensus, not_or] at hs
          exact Nat.pos_of_ne_zero hs.1
        have hs2 : 0 < s.2 := by
          simp only [reachedConsensus, not_or] at hs
          exact Nat.pos_of_ne_zero hs.2
        rw [kernelIter_succ_right, Kernel.comp_apply' _ _ _ hA,
          lvKernelAbsorb_interior v params s hs1 hs2,
          consensusOutcomeBy_measure_succ v params A N s hs]
        exact lintegral_congr fun x => ih x

/-- Finite-time optional stopping for the corrected SD boundary payoff:
    species 0 contributes `1`, the draw contributes `1/2`, and species 1
    contributes `0`. -/
private lemma sd_boundary_payoff_by_le
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b N : ℕ)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    lvPathMeasure .selfDestructive params (a, b)
          {ω | consensusOutcomeBy {s | 0 < s.1 ∧ s.2 = 0} N ω} +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure .selfDestructive params (a, b)
            {ω | consensusOutcomeBy ({(0, 0)} : Set PopState) N ω} ≤
      ENNReal.ofReal (h_ratio_sd_draw (a, b)) := by
  let A : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  let D : Set PopState := {(0, 0)}
  let μ : Measure PopState :=
    (kernelIter (lvKernelAbsorb .selfDestructive params) N) (a, b)
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have hD : MeasurableSet D := measurableSet_singleton _
  have hAcons : ∀ s ∈ A, reachedConsensus s := by
    intro s hs
    exact Or.inr hs.2
  have hDcons : ∀ s ∈ D, reachedConsensus s := by
    intro s hs
    subst s
    exact Or.inl rfl
  rw [show {s : PopState | 0 < s.1 ∧ s.2 = 0} = A from rfl,
    show ({(0, 0)} : Set PopState) = D from rfl,
    ← lvKernelAbsorb_outcomeBy_eq .selfDestructive params A hA hAcons N (a, b),
    ← lvKernelAbsorb_outcomeBy_eq .selfDestructive params D hD hDcons N (a, b)]
  haveI : IsProbabilityMeasure μ :=
    (kernelIter_isMarkov (K := lvKernelAbsorb .selfDestructive params) N)
      |>.isProbabilityMeasure (a, b)
  have hInt : Integrable h_ratio_sd_draw μ := by
    apply Integrable.mono (integrable_const (1 : ℝ))
      (measurable_of_countable h_ratio_sd_draw).aestronglyMeasurable
    filter_upwards with s
    simp only [Real.norm_eq_abs, norm_one]
    exact abs_le.mpr
      ⟨by linarith [(h_ratio_sd_draw_bound s).1],
        (h_ratio_sd_draw_bound s).2⟩
  have hPayoff :
      ∫⁻ s, ENNReal.ofReal (h_ratio_sd_draw s) ∂μ =
        ENNReal.ofReal (h_ratio_sd_draw (a, b)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun s => (h_ratio_sd_draw_bound s).1)]
    exact congrArg ENNReal.ofReal
      (h_ratio_sd_draw_absorb_iter params hAlpha hNeutral hEq0 hEq1 a b N)
  have hAm :
      Measurable (A.indicator (fun _ => (1 : ENNReal))) :=
    measurable_const.indicator hA
  calc
    μ A + ENNReal.ofReal (1 / 2) * μ D =
        (∫⁻ s, A.indicator (fun _ => (1 : ENNReal)) s ∂μ) +
          ∫⁻ s, D.indicator
            (fun _ => ENNReal.ofReal (1 / 2)) s ∂μ := by
      rw [lintegral_indicator_const hA, lintegral_indicator_const hD]
      simp
    _ = ∫⁻ s,
          A.indicator (fun _ => (1 : ENNReal)) s +
            D.indicator (fun _ => ENNReal.ofReal (1 / 2)) s ∂μ := by
      rw [lintegral_add_left hAm]
    _ ≤ ∫⁻ s, ENNReal.ofReal (h_ratio_sd_draw s) ∂μ := by
      apply lintegral_mono
      intro s
      by_cases hsA : s ∈ A
      · have hsD : s ∉ D := by
          intro hsD
          have hs0 : s = (0, 0) := hsD
          subst s
          exact (Nat.not_lt_zero 0) hsA.1
        rcases s with ⟨x, y⟩
        simp only [A, Set.mem_setOf_eq] at hsA
        rcases hsA with ⟨hx, rfl⟩
        have hxA : (x, 0) ∈ A := by
          exact ⟨hx, rfl⟩
        have hxD : (x, 0) ∉ D := hsD
        simp [Set.indicator_of_mem hxA, Set.indicator_of_notMem hxD,
          h_ratio_sd_draw, h_ratio_sd, hx.ne']
      · by_cases hsD : s ∈ D
        · have hs0 : s = (0, 0) := hsD
          subst s
          norm_num [A, D, h_ratio_sd_draw]
        · simp [Set.indicator_of_notMem hsA,
            Set.indicator_of_notMem hsD]
    _ = ENNReal.ofReal (h_ratio_sd_draw (a, b)) := hPayoff

/-- Infinite-time version of the stopped boundary-payoff inequality.  This
    does not assume that consensus occurs almost surely. -/
private lemma sd_boundary_payoff_le
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    lvPathMeasure .selfDestructive params (a, b)
          {ω | consensusOutcome {s | 0 < s.1 ∧ s.2 = 0} ω} +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure .selfDestructive params (a, b)
            {ω | consensusOutcome ({(0, 0)} : Set PopState) ω} ≤
      ENNReal.ofReal (h_ratio_sd_draw (a, b)) := by
  let P := lvPathMeasure .selfDestructive params (a, b)
  let A : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  let D : Set PopState := {(0, 0)}
  let EA : ℕ → Set (ℕ → PopState) :=
    fun N => {ω | consensusOutcomeBy A N ω}
  let ED : ℕ → Set (ℕ → PopState) :=
    fun N => {ω | consensusOutcomeBy D N ω}
  have hEA : Monotone EA := by
    simpa only [EA] using consensusOutcomeBy_monotone A
  have hED : Monotone ED := by
    simpa only [ED] using consensusOutcomeBy_monotone D
  have hf : Monotone (fun N => P (EA N)) :=
    fun _ _ hNM => measure_mono (hEA hNM)
  have hg : Monotone
      (fun N => ENNReal.ofReal (1 / 2) * P (ED N)) :=
    fun _ _ hNM => mul_le_mul_left' (measure_mono (hED hNM)) _
  rw [show {s : PopState | 0 < s.1 ∧ s.2 = 0} = A from rfl,
    show ({(0, 0)} : Set PopState) = D from rfl,
    consensusOutcome_eq_iUnion A, consensusOutcome_eq_iUnion D,
    show (⋃ N, {ω | consensusOutcomeBy A N ω}) = ⋃ N, EA N from rfl,
    show (⋃ N, {ω | consensusOutcomeBy D N ω}) = ⋃ N, ED N from rfl,
    hEA.measure_iUnion, hED.measure_iUnion, ENNReal.mul_iSup,
    ENNReal.iSup_add_iSup_of_monotone hf hg]
  apply iSup_le
  intro N
  simpa only [P, EA, ED, A, D] using
    sd_boundary_payoff_by_le params hAlpha hNeutral hEq0 hEq1 a b N

/-- The symmetric boundary-payoff inequality for a species-1 win. -/
private lemma sd_boundary_payoff_species1_le
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    lvPathMeasure .selfDestructive params (a, b)
          {ω | consensusOutcome {s | s.1 = 0 ∧ 0 < s.2} ω} +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure .selfDestructive params (a, b)
            {ω | consensusOutcome ({(0, 0)} : Set PopState) ω} ≤
      ENNReal.ofReal (h_ratio_sd_draw (b, a)) := by
  let P := lvPathMeasure .selfDestructive params (a, b)
  let Pswap := lvPathMeasure .selfDestructive params (b, a)
  let A0 : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  let A1 : Set PopState := {s | s.1 = 0 ∧ 0 < s.2}
  let D : Set PopState := {(0, 0)}
  let E0 : Set (ℕ → PopState) := {ω | consensusOutcome A0 ω}
  let E1 : Set (ℕ → PopState) := {ω | consensusOutcome A1 ω}
  let ED : Set (ℕ → PopState) := {ω | consensusOutcome D ω}
  have hGamma : params.gamma0 = params.gamma1 := by
    rw [hEq0, hEq1, hNeutral]
  have hswap : P.map swapTraj = Pswap := by
    simpa only [P, Pswap] using
      lvPathMeasure_swap .selfDestructive params hNeutral hGamma a b
  have hswapm : Measurable swapTraj := by
    rw [measurable_pi_iff]
    intro n
    exact (measurable_of_countable PopState.swap).comp
      (measurable_pi_apply n)
  have hE0m : MeasurableSet E0 := by
    simpa only [E0] using measurableSet_consensusOutcome A0
  have hEDm : MeasurableSet ED := by
    simpa only [ED] using measurableSet_consensusOutcome D
  have hpre0 : swapTraj ⁻¹' E0 = E1 := by
    ext ω
    simp only [Set.mem_preimage, E0, E1, Set.mem_setOf_eq]
    unfold consensusOutcome
    rw [consensusTime_swapTraj]
    cases hct : consensusTime ω with
    | top => simp
    | coe t =>
        simp only [A0, A1, swapTraj, PopState.swap, Set.mem_setOf_eq]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
  have hpreD : swapTraj ⁻¹' ED = ED := by
    ext ω
    simp only [Set.mem_preimage, ED, Set.mem_setOf_eq]
    unfold consensusOutcome
    rw [consensusTime_swapTraj]
    cases hct : consensusTime ω with
    | top => simp
    | coe t =>
        change PopState.swap (ω t) = (0, 0) ↔ ω t = (0, 0)
        constructor
        · intro h
          simpa using congrArg PopState.swap h
        · intro h
          simpa using congrArg PopState.swap h
  have hE0 : Pswap E0 = P E1 := by
    rw [← hswap, Measure.map_apply hswapm hE0m, hpre0]
  have hD : Pswap ED = P ED := by
    rw [← hswap, Measure.map_apply hswapm hEDm, hpreD]
  have hbound :=
    sd_boundary_payoff_le params hAlpha hNeutral hEq0 hEq1 b a
  simpa only [P, Pswap, A0, A1, D, E0, E1, ED, hE0, hD] using hbound

/-- Corrected SD Part 1 once almost-sure consensus is available.  The proof
    uses the paper's bounded stopped-martingale argument: the two symmetric
    boundary-payoff inequalities sum to one, hence both are equalities. -/
private lemma sd_part1_of_consensus
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hConsensus :
      lvPathMeasure .selfDestructive params (a, b)
        {ω | consensusReachedEvent ω} = 1)
    [IsMarkovKernel (lvKernel .selfDestructive params)] :
    majorityConsensusProb .selfDestructive params (a, b) +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure .selfDestructive params (a, b)
            {ω | drawAtConsensusEvent ω} =
      ENNReal.ofReal ((a : ℝ) / (a + b : ℝ)) := by
  let P := lvPathMeasure .selfDestructive params (a, b)
  let A0 : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
  let A1 : Set PopState := {s | s.1 = 0 ∧ 0 < s.2}
  let D : Set PopState := {(0, 0)}
  let E0 : Set (ℕ → PopState) := {ω | consensusOutcome A0 ω}
  let E1 : Set (ℕ → PopState) := {ω | consensusOutcome A1 ω}
  let ED : Set (ℕ → PopState) := {ω | consensusOutcome D ω}
  let C : Set (ℕ → PopState) := {ω | consensusReachedEvent ω}
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hE0m : MeasurableSet E0 := by
    simpa only [E0] using measurableSet_consensusOutcome A0
  have hE1m : MeasurableSet E1 := by
    simpa only [E1] using measurableSet_consensusOutcome A1
  have hEDm : MeasurableSet ED := by
    simpa only [ED] using measurableSet_consensusOutcome D
  have hdisj01 : Disjoint E0 E1 := by
    rw [Set.disjoint_left]
    intro ω h0 h1
    change consensusOutcome A0 ω at h0
    change consensusOutcome A1 ω at h1
    cases hct : consensusTime ω with
    | top =>
        rw [consensusOutcome, hct] at h0
        exact h0.elim
    | coe t =>
        rw [consensusOutcome, hct] at h0 h1
        simp only [A0, A1, Set.mem_setOf_eq] at h0 h1
        omega
  have hdisjD : Disjoint (E0 ∪ E1) ED := by
    rw [Set.disjoint_left]
    intro ω h01 hD
    rcases h01 with h0 | h1
    · change consensusOutcome A0 ω at h0
      change consensusOutcome D ω at hD
      cases hct : consensusTime ω with
      | top =>
          rw [consensusOutcome, hct] at h0
          exact h0.elim
      | coe t =>
          rw [consensusOutcome, hct] at h0 hD
          change ω t ∈ A0 at h0
          change ω t ∈ D at hD
          have hz : ω t = (0, 0) := by
            simpa only [D, Set.mem_singleton_iff] using hD
          rw [hz] at h0
          simp [A0] at h0
    · change consensusOutcome A1 ω at h1
      change consensusOutcome D ω at hD
      cases hct : consensusTime ω with
      | top =>
          rw [consensusOutcome, hct] at h1
          exact h1.elim
      | coe t =>
          rw [consensusOutcome, hct] at h1 hD
          change ω t ∈ A1 at h1
          change ω t ∈ D at hD
          have hz : ω t = (0, 0) := by
            simpa only [D, Set.mem_singleton_iff] using hD
          rw [hz] at h1
          simp [A1] at h1
  have hCeq : C = E0 ∪ E1 ∪ ED := by
    ext ω
    constructor
    · intro hC
      change consensusReachedEvent ω at hC
      cases hct : consensusTime ω with
      | top =>
          simp [consensusReachedEvent, hct] at hC
      | coe t =>
          have hreach :=
            reachedConsensus_at_consensusTime' ω t hct
          rcases hreach with hfst | hsnd
          · by_cases hsnd0 : (ω t).2 = 0
            · right
              change consensusOutcome D ω
              rw [consensusOutcome, hct]
              exact Prod.ext hfst hsnd0
            · left
              right
              change consensusOutcome A1 ω
              rw [consensusOutcome, hct]
              exact ⟨hfst, Nat.pos_of_ne_zero hsnd0⟩
          · by_cases hfst0 : (ω t).1 = 0
            · right
              change consensusOutcome D ω
              rw [consensusOutcome, hct]
              exact Prod.ext hfst0 hsnd
            · left
              left
              change consensusOutcome A0 ω
              rw [consensusOutcome, hct]
              exact ⟨Nat.pos_of_ne_zero hfst0, hsnd⟩
    · intro h
      rcases h with (h0 | h1) | hD
      · change consensusOutcome A0 ω at h0
        change consensusReachedEvent ω
        cases hct : consensusTime ω with
        | top =>
            rw [consensusOutcome, hct] at h0
            exact h0.elim
        | coe t =>
            simp [consensusReachedEvent, hct]
      · change consensusOutcome A1 ω at h1
        change consensusReachedEvent ω
        cases hct : consensusTime ω with
        | top =>
            rw [consensusOutcome, hct] at h1
            exact h1.elim
        | coe t =>
            simp [consensusReachedEvent, hct]
      · change consensusOutcome D ω at hD
        change consensusReachedEvent ω
        cases hct : consensusTime ω with
        | top =>
            rw [consensusOutcome, hct] at hD
            exact hD.elim
        | coe t =>
            simp [consensusReachedEvent, hct]
  have hsum : P E0 + P E1 + P ED = 1 := by
    rw [← measure_union hdisj01 hE1m,
      ← measure_union hdisjD hEDm, ← hCeq]
    simpa only [P, C] using hConsensus
  let c : ENNReal := ENNReal.ofReal (1 / 2)
  let r0 : ENNReal := ENNReal.ofReal ((a : ℝ) / (a + b : ℝ))
  let r1 : ENNReal := ENNReal.ofReal ((b : ℝ) / (b + a : ℝ))
  let u0 : ENNReal := P E0 + c * P ED
  let u1 : ENNReal := P E1 + c * P ED
  have hc : c + c = 1 := by
    norm_num [c, ← ENNReal.ofReal_add]
  have huSum : u0 + u1 = 1 := by
    dsimp [u0, u1]
    calc
      P E0 + c * P ED + (P E1 + c * P ED)
          = P E0 + P E1 + (c + c) * P ED := by
            ring
      _ = P E0 + P E1 + P ED := by rw [hc, one_mul]
      _ = 1 := hsum
  have hrSum : r0 + r1 = 1 := by
    have hden : (a : ℝ) + b ≠ 0 := by positivity
    dsimp [r0, r1]
    rw [← ENNReal.ofReal_add
      (div_nonneg (Nat.cast_nonneg _)
        (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (div_nonneg (Nat.cast_nonneg _)
        (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))]
    have hreal :
        (a : ℝ) / ((a : ℝ) + b) +
            (b : ℝ) / ((b : ℝ) + a) = 1 := by
      field_simp [hden]
      ring
    rw [hreal]
    simp
  have hu0le : u0 ≤ r0 := by
    have h :=
      sd_boundary_payoff_le params hAlpha hNeutral hEq0 hEq1 a b
    have hne : (a, b) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos a b ha
    dsimp [u0, r0, c]
    simpa only [P, E0, ED, A0, D,
      h_ratio_sd_draw_of_ne (a, b) hne, h_ratio_sd] using h
  have hu1le : u1 ≤ r1 := by
    have h :=
      sd_boundary_payoff_species1_le
        params hAlpha hNeutral hEq0 hEq1 a b
    have hne : (b, a) ≠ (0, 0) :=
      pop_ne_zero_of_fst_pos b a hb
    dsimp [u1, r1, c]
    simpa only [P, E1, ED, A1, D,
      h_ratio_sd_draw_of_ne (b, a) hne, h_ratio_sd] using h
  have hr0ne : r0 ≠ ⊤ := by
    dsimp [r0]
    exact ENNReal.ofReal_ne_top
  have hr1ne : r1 ≠ ⊤ := by
    dsimp [r1]
    exact ENNReal.ofReal_ne_top
  have hu0ne : u0 ≠ ⊤ :=
    ne_top_of_le_ne_top hr0ne hu0le
  have hu1ne : u1 ≠ ⊤ :=
    ne_top_of_le_ne_top hr1ne hu1le
  have hr0le : r0 ≤ u0 := by
    apply ENNReal.le_of_add_le_add_right hu1ne
    calc
      r0 + u1 ≤ r0 + r1 := by
        simpa [add_comm] using add_le_add_left hu1le r0
      _ = 1 := hrSum
      _ = u0 + u1 := huSum.symm
  have hr1le : r1 ≤ u1 := by
    apply ENNReal.le_of_add_le_add_left hu0ne
    calc
      u0 + r1 ≤ r0 + r1 := by
        simpa [add_comm] using add_le_add_right hu0le r1
      _ = 1 := hrSum
      _ = u0 + u1 := huSum.symm
  have hu0 : u0 = r0 := le_antisymm hu0le hr0le
  have hu1 : u1 = r1 := le_antisymm hu1le hr1le
  have hDraw : {ω | drawAtConsensusEvent ω} = ED := by
    ext ω
    change drawAtConsensusEvent ω ↔ consensusOutcome D ω
    unfold drawAtConsensusEvent consensusOutcome
    cases hct : consensusTime ω with
    | top => simp
    | coe t => simp [D]
  unfold majorityConsensusProb
  rcases Nat.eq_or_lt_of_le hba with hab | hlt
  · subst b
    have hMaj : {ω | majorityConsensusEvent (a, a) ω} = E0 := by
      ext ω
      change majorityConsensusEvent (a, a) ω ↔ consensusOutcome A0 ω
      rw [majorityConsensusEvent_diag_iff]
      unfold consensusOutcome
      cases hct : consensusTime ω with
      | top => simp
      | coe t => simp [A0]
    simpa only [P, hMaj, hDraw, c, r0] using hu0
  · have hMaj : {ω | majorityConsensusEvent (a, b) ω} = E0 := by
      ext ω
      change majorityConsensusEvent (a, b) ω ↔ consensusOutcome A0 ω
      unfold majorityConsensusEvent consensusOutcome
      cases hct : consensusTime ω with
      | top => simp
      | coe t =>
          have hmajor : species0Majority (a, b) := by
            exact Nat.le_of_lt hlt
          simp [hmajor, A0]
    simpa only [P, hMaj, hDraw, c, r0] using hu0

/-- Corrected Part 1 of paper `thm:sd-intra`.

    The proportion martingale assigns value `1/2` to the draw state, giving
      Pr[majority wins] + (1/2) Pr[draw] = a/(a+b).

    The paper's conditional identity is false: with `β=δ=0` and initial
    state `(3,1)`, majority win and draw each have probability `1/2`. -/
theorem thm_sd_intra_part1
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    (hab3 : 3 ≤ a + b)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    majorityConsensusProb LVVariant.selfDestructive params (a, b) +
        ENNReal.ofReal (1 / 2) *
          lvPathMeasure LVVariant.selfDestructive params (a, b)
            {ω | drawAtConsensusEvent ω} =
      ENNReal.ofReal ((a : ℝ) / (a + b : ℝ)) := by
  exact sd_part1_of_consensus params hAlpha hNeutral hEq0 hEq1
    a b hposA hposB hba
    (sd_consensus_almost_sure params a b hposA hposB
      hAlpha hNeutral hEq0 hEq1)

-- THEOREM 7.5 PART 2: Probability bound ρ(S) ≤ a/(a+b)
-- ============================================================================
-- This completes Theorem 7.5 in the paper by proving the second inequality.
-- Part 1 (thm_sd_intra_part1) proved the exact probability conditioned on one species winning.
-- Part 2 proves an unconditional upper bound on majority consensus probability.

/-- THEOREM 7.5 PART 2: Self-destructive competition, probability bound.

    Let S be a neutral Lotka-Volterra chain with self-destructive competition
    and initial configuration S₀ = (a,b), where a ≥ b > 0, a+b ≥ 3, α = γ/2 ≥ 0,
    and β, δ ≥ 0.

    If α > 0, then the probability that the majority species wins (reaches the state
    where it has positive population and the minority has zero) is bounded by:

        ρ(S) ≤ a/(a+b)

    This bound follows from Part 1 and the fact that consensus probability can be
    decomposed as:

        ρ(S) = Pr[majority | one species wins] · Pr[one species wins]
             = (a/(a+b)) · Pr[one species wins]
             ≤ a/(a+b)

    The bound is tight when one species almost surely wins (e.g., when β = δ = 0
    and α > 0), in which case ρ(S) = a/(a+b).
-/
theorem thm_sd_intra_part2
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat)
    (hposA : 0 < a)
    (hposB : 0 < b)
    (hba : b ≤ a)
    (hab3 : 3 ≤ a + b)
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    majorityConsensusProb LVVariant.selfDestructive params (a, b) ≤
      ENNReal.ofReal ((a : ℝ) / (a + b : ℝ)) := by
  rcases Nat.eq_or_lt_of_le hba with hEq | hlt
  · subst b
    have hGamma : params.gamma0 = params.gamma1 := by
      calc
        params.gamma0 = 2 * params.alpha0 := hEq0
        _ = 2 * params.alpha1 := by rw [hNeutral]
        _ = params.gamma1 := hEq1.symm
    have hdiag := mc_any_from_diagonal_le_half .selfDestructive params
      (a, a) a hNeutral hGamma
    calc
      majorityConsensusProb .selfDestructive params (a, a)
          ≤ ENNReal.ofReal (1 / 2) := by
            simpa [majorityConsensusProb] using hdiag
      _ = ENNReal.ofReal ((a : ℝ) / (a + a : ℝ)) := by
            congr 1
            field_simp [show (a : ℝ) ≠ 0 by exact_mod_cast hposA.ne']
            ring
  · let A : Set PopState := {s | 0 < s.1 ∧ s.2 = 0}
    let f : PopState → ENNReal := fun s => ENNReal.ofReal (h_ratio_sd s)
    let P := lvPathMeasure .selfDestructive params (a, b)
    have hA : ∀ s ∈ A, 1 ≤ f s := by
      rintro ⟨x, y⟩ hs
      change 0 < x ∧ y = 0 at hs
      obtain ⟨hx, hy⟩ := hs
      subst y
      simp [f, h_ratio_sd_bnd1 x hx]
    have hSuper : ∀ s, ∫⁻ x, f x
        ∂(lvKernel .selfDestructive params) s ≤ f s := by
      intro s
      exact h_ratio_sd_ennreal_superharmonic params hAlpha hNeutral hEq0 hEq1 s
    have hHit : ∀ N, P (pathHitsBy A N) ≤ f (a, b) := by
      intro N
      exact homogeneousPathMeasure_hitBy_le
        (lvKernel .selfDestructive params) f A hA hSuper (a, b) N
    have hMono : Monotone (pathHitsBy A) := by
      intro n m hnm ω hω
      obtain ⟨t, ht, hAt⟩ := hω
      exact ⟨t, ht.trans hnm, hAt⟩
    have hMaj : species0Majority (a, b) := by
      simp [species0Majority]
      omega
    have hMCEsub :
        {ω | majorityConsensusEvent (a, b) ω} ⊆
          ⋃ N, pathHitsBy A N := by
      intro ω hmc
      simp only [Set.mem_setOf_eq] at hmc
      unfold majorityConsensusEvent at hmc
      split at hmc
      · exact hmc.elim
      · rename_i t hct
        rcases hmc with ⟨_, htpos, htzero⟩ | ⟨hnMaj, _⟩
        · refine Set.mem_iUnion.mpr ⟨t, t, le_rfl, ?_⟩
          exact ⟨htpos, htzero⟩
        · exact absurd hMaj hnMaj
    unfold majorityConsensusProb
    change P {ω | majorityConsensusEvent (a, b) ω} ≤ _
    calc
      P {ω | majorityConsensusEvent (a, b) ω}
          ≤ P (⋃ N, pathHitsBy A N) := measure_mono hMCEsub
      _ = ⨆ N, P (pathHitsBy A N) := hMono.measure_iUnion
      _ ≤ f (a, b) := iSup_le hHit
      _ = ENNReal.ofReal ((a : ℝ) / (a + b : ℝ)) := rfl

end LVConsensus
