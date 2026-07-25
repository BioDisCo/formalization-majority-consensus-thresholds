import LVConsensus.BDAlmostSure

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal

namespace LVConsensus

noncomputable def shiftBDOne (N : BirthDeathChain) : BirthDeathChain where
  p := fun m => if m = 0 then 0 else N.p (m + 1)
  q := fun m => if m = 0 then 0 else N.q (m + 1)
  p_nonneg := by
    intro m
    split_ifs
    · exact le_rfl
    · exact N.p_nonneg _
  q_nonneg := by
    intro m
    split_ifs
    · exact le_rfl
    · exact N.q_nonneg _
  pq_le_one := by
    intro m
    split_ifs
    · norm_num
    · exact N.pq_le_one _
  absorb_zero := by simp

def popExcessOne (s : PopState) : ℕ := s.1 + s.2 - 1

lemma nsd_kernel_map_popExcessOne
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((lvKernel .nonSelfDestructive params) (a, b)).map popExcessOne =
      bdKernel (shiftBDOne (nsdTotalPopBDChain params)) (popExcessOne (a, b)) := by
  apply Measure.ext_of_singleton
  intro m
  rw [Measure.map_apply (measurable_of_countable popExcessOne)
    (measurableSet_singleton m)]
  let n := a + b
  let e := n - 1
  let U : Set PopState := {s | s.1 + s.2 = n + 1}
  let D : Set PopState := {s | s.1 + s.2 + 1 = n}
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hepos : 0 < e := by dsimp [e, n]; omega
  have hMarg := nsd_kernel_totalPop_marginal params hNeutral hEq0 hEq1
    hAlpha a b ha hb
  dsimp at hMarg
  have hexcess : popExcessOne (a, b) = e := by
    dsimp [popExcessOne, e, n]
  have hpq :
      (nsdTotalPopBDChain params).p n +
          (nsdTotalPopBDChain params).q n = 1 := by
    simp only [nsdTotalPopBDChain, show ¬n ≤ 1 by omega, ↓reduceIte]
    have hden :
        0 < params.beta + params.delta +
          params.alpha0 * ((n : ℝ) - 1) := by
      have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
        have hn1' : (1 : ℝ) < (n : ℝ) := by
          exact_mod_cast (show 1 < n by omega)
        linarith
      nlinarith [params.beta_nonneg, params.delta_nonneg,
        mul_pos hAlpha hn1]
    rw [← add_div]
    convert div_self hden.ne' using 1 <;> ring
  have hUdisjD : Disjoint U D := by
    apply Set.disjoint_left.2
    intro s hsU hsD
    dsimp [U, D, n] at hsU hsD
    omega
  have hmass :
      (lvKernel .nonSelfDestructive params (a, b)) (U ∪ D) = 1 := by
    rw [measure_union hUdisjD (Set.to_countable D).measurableSet]
    change
      (lvKernel .nonSelfDestructive params (a, b))
          {s | s.1 + s.2 = a + b + 1} +
        (lvKernel .nonSelfDestructive params (a, b))
          {s | s.1 + s.2 + 1 = a + b} = 1
    rw [hMarg.1, hMarg.2, ← ENNReal.ofReal_add
      ((nsdTotalPopBDChain params).p_nonneg n)
      ((nsdTotalPopBDChain params).q_nonneg n), hpq]
    simp
  have hsupport_zero :
      (lvKernel .nonSelfDestructive params (a, b)) (U ∪ D)ᶜ = 0 := by
    haveI : IsProbabilityMeasure
        (lvKernel .nonSelfDestructive params (a, b)) := by infer_instance
    rw [measure_compl (Set.to_countable _).measurableSet
      (measure_ne_top _ _), hmass, measure_univ, tsub_self]
  have hmeasure_on_support :
      ∀ (P Q : Set PopState), Q ⊆ U ∪ D → P ∩ (U ∪ D) = Q →
        (lvKernel .nonSelfDestructive params (a, b)) P =
          (lvKernel .nonSelfDestructive params (a, b)) Q := by
    intro P Q hQ hPQ
    apply le_antisymm
    · calc
        (lvKernel .nonSelfDestructive params (a, b)) P
            ≤ (lvKernel .nonSelfDestructive params (a, b))
                (Q ∪ (U ∪ D)ᶜ) := by
              apply measure_mono
              intro s hs
              by_cases hsS : s ∈ U ∪ D
              · left
                have : s ∈ P ∩ (U ∪ D) := ⟨hs, hsS⟩
                simpa [hPQ] using this
              · exact Or.inr hsS
        _ ≤ (lvKernel .nonSelfDestructive params (a, b)) Q +
              (lvKernel .nonSelfDestructive params (a, b)) (U ∪ D)ᶜ :=
            measure_union_le _ _
        _ = (lvKernel .nonSelfDestructive params (a, b)) Q := by
              rw [hsupport_zero, add_zero]
    · apply measure_mono
      intro s hs
      have hsS : s ∈ U ∪ D := hQ hs
      have : s ∈ P ∩ (U ∪ D) := by simpa [hPQ] using hs
      exact this.1
  rw [bdKernel_apply_singleton]
  by_cases hmU : m = e + 1
  · subst m
    have hpre : (popExcessOne ⁻¹' {e + 1}) ∩ (U ∪ D) = U := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.mem_union, popExcessOne]
      dsimp [U, e, n]
      omega
    rw [hmeasure_on_support _ U (by exact Set.subset_union_left) hpre]
    have hne0 : e ≠ 0 := hepos.ne'
    rw [hexcess]
    simp only [shiftBDOne, hne0, ↓reduceIte]
    have hidx : e + 1 = n := by dsimp [e]; omega
    rw [hidx]
    have hnotq : ¬(n = e - 1) := by omega
    have hnoth : ¬(n = e) := by omega
    rw [if_neg hnotq, if_neg hnoth]
    simpa [U, n] using hMarg.1
  · by_cases hmD : m = e - 1
    · subst m
      have hpre : (popExcessOne ⁻¹' {e - 1}) ∩ (U ∪ D) = D := by
        ext s
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_union, popExcessOne]
        constructor
        · intro hs
          rcases hs with ⟨_, hsU | hsD⟩
          · dsimp [U, D, e, n] at *
            omega
          · exact hsD
        · intro hsD
          refine ⟨?_, Or.inr hsD⟩
          dsimp [D, e, n] at *
          omega
      rw [hmeasure_on_support _ D (by exact Set.subset_union_right) hpre]
      have hne0 : e ≠ 0 := hepos.ne'
      rw [hexcess]
      simp only [shiftBDOne, hne0, ↓reduceIte]
      have hidx : e + 1 = n := by dsimp [e]; omega
      rw [hidx]
      have hnotp : ¬(e - 1 = n + 1) := by omega
      have hnoth : ¬(e - 1 = n) := by omega
      rw [if_neg hnoth, if_neg (by omega)]
      simpa [D, n] using hMarg.2
    · have hpre_disj :
          Disjoint (popExcessOne ⁻¹' {m}) (U ∪ D) := by
        apply Set.disjoint_left.2
        intro s hs hUD
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs
        rcases hUD with hU | hD
        · apply hmU
          dsimp [popExcessOne, U, e, n] at hs hU ⊢
          omega
        · apply hmD
          dsimp [popExcessOne, D, e, n] at hs hD ⊢
          omega
      have hzero :
          (lvKernel .nonSelfDestructive params (a, b))
            (popExcessOne ⁻¹' {m}) = 0 := by
        haveI : IsProbabilityMeasure
            (lvKernel .nonSelfDestructive params (a, b)) := by infer_instance
        have hcomp :
            (lvKernel .nonSelfDestructive params (a, b)) (U ∪ D)ᶜ = 0 := by
          rw [measure_compl (Set.to_countable _).measurableSet
            (measure_ne_top _ _), hmass, measure_univ, tsub_self]
        apply measure_mono_null _ hcomp
        exact Set.disjoint_left.1 hpre_disj
      rw [hzero]
      have hne0 : e ≠ 0 := hepos.ne'
      rw [hexcess]
      simp only [shiftBDOne, hne0, ↓reduceIte]
      have hidx : e + 1 = n := by dsimp [e]; omega
      rw [hidx]
      have hmN : ¬m = n := by simpa [hidx] using hmU
      rw [if_neg hmN, if_neg hmD]
      have hhold : holdProb (shiftBDOne (nsdTotalPopBDChain params)) e = 0 := by
        simp only [holdProb, shiftBDOne, hne0, ↓reduceIte, hidx]
        linarith [hpq]
      split_ifs
      · change 0 = 0 + 0 +
          ENNReal.ofReal (holdProb (shiftBDOne (nsdTotalPopBDChain params)) e)
        rw [hhold]
        simp
      · simp

lemma nsd_kernelIter_interior_le_shift
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    ∀ (t : ℕ) (s : PopState),
      (kernelIter (lvKernel .nonSelfDestructive params) t) s
          {x | 0 < x.1 ∧ 0 < x.2} ≤
        (kernelIter
          (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
          (popExcessOne s) {m | 0 < m} := by
  intro t
  induction t with
  | zero =>
      intro s
      simp only [kernelIter_zero, Kernel.id_apply]
      rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      by_cases hsI : 0 < s.1 ∧ 0 < s.2
      · have hsE : 0 < popExcessOne s := by
          dsimp [popExcessOne]
          omega
        simp [hsI, hsE]
      · simp [hsI]
  | succ t ih =>
      intro s
      by_cases hs0 : s.1 = 0
      · have hdead :=
          nsd_kernelIter_species0_dead_absorbing params s hs0 (t + 1)
        have hle :
            (kernelIter (lvKernel .nonSelfDestructive params) (t + 1)) s
                {x | 0 < x.1 ∧ 0 < x.2} ≤
              (kernelIter (lvKernel .nonSelfDestructive params) (t + 1)) s
                {x | x.1 ≠ 0} := by
          apply measure_mono
          intro x hx
          exact Nat.ne_of_gt hx.1
        exact le_trans (hle.trans_eq hdead) zero_le
      · by_cases hs1 : s.2 = 0
        · have hdead :=
            nsd_kernelIter_species1_dead_absorbing params s hs1 (t + 1)
          have hle :
              (kernelIter (lvKernel .nonSelfDestructive params) (t + 1)) s
                  {x | 0 < x.1 ∧ 0 < x.2} ≤
                (kernelIter (lvKernel .nonSelfDestructive params) (t + 1)) s
                  {x | x.2 ≠ 0} := by
            apply measure_mono
            intro x hx
            exact Nat.ne_of_gt hx.2
          exact le_trans (hle.trans_eq hdead) zero_le
        · have hs0p : 0 < s.1 := Nat.pos_of_ne_zero hs0
          have hs1p : 0 < s.2 := Nat.pos_of_ne_zero hs1
          rw [kernelIter_succ_right, kernelIter_succ_right,
            Kernel.comp_apply' _ _ _
              (Set.to_countable {x : PopState | 0 < x.1 ∧ 0 < x.2}).measurableSet,
            Kernel.comp_apply' _ _ _
              (Set.to_countable {m : ℕ | 0 < m}).measurableSet]
          calc
            ∫⁻ y, (kernelIter (lvKernel .nonSelfDestructive params) t) y
                  {x | 0 < x.1 ∧ 0 < x.2}
                ∂(lvKernel .nonSelfDestructive params) s
                ≤ ∫⁻ y, (kernelIter
                    (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
                    (popExcessOne y) {m | 0 < m}
                  ∂(lvKernel .nonSelfDestructive params) s := by
                    exact lintegral_mono ih
            _ = ∫⁻ m, (kernelIter
                    (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
                    m {m | 0 < m}
                  ∂((lvKernel .nonSelfDestructive params) s).map popExcessOne := by
                    rw [MeasureTheory.lintegral_map
                      (Kernel.measurable_coe
                        (kernelIter
                          (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
                        (Set.to_countable {m : ℕ | 0 < m}).measurableSet)
                      (measurable_of_countable popExcessOne)]
            _ = ∫⁻ m, (kernelIter
                    (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
                    m {m | 0 < m}
                  ∂bdKernel (shiftBDOne (nsdTotalPopBDChain params))
                    (popExcessOne s) := by
                    rw [nsd_kernel_map_popExcessOne params hNeutral hEq0 hEq1
                      hAlpha s.1 s.2 hs0p hs1p]

lemma nsd_path_stay_interior_le_shift
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (hAlpha : 0 < params.alpha0)
    (a b t : ℕ)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
        {ω | ∀ u ≤ t, 0 < (ω u).1 ∧ 0 < (ω u).2} ≤
      (kernelIter
        (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
        (popExcessOne (a, b)) {m | 0 < m} := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let F : Set (ℕ → PopState) :=
    {ω | ∀ u ≤ t, 0 < (ω u).1 ∧ 0 < (ω u).2}
  let E : Set (ℕ → PopState) := {ω | 0 < (ω t).1 ∧ 0 < (ω t).2}
  calc
    P F ≤ P E := by
      apply measure_mono
      intro ω hω
      exact hω t le_rfl
    _ = (kernelIter (lvKernel .nonSelfDestructive params) t) (a, b)
        {s | 0 < s.1 ∧ 0 < s.2} := by
      dsimp [P, E]
      unfold lvPathMeasure
      rw [show ({ω : ℕ → PopState | 0 < (ω t).1 ∧ 0 < (ω t).2} :
            Set (ℕ → PopState)) =
          (fun ω : ℕ → PopState => ω t) ⁻¹'
            ({s : PopState | 0 < s.1 ∧ 0 < s.2}) from rfl,
        ← Measure.map_apply (measurable_pi_apply t) (by measurability),
        homogeneousPathMeasure_dirac_marginal]
    _ ≤ (kernelIter
          (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
          (popExcessOne (a, b)) {m | 0 < m} :=
      nsd_kernelIter_interior_le_shift params hNeutral hEq0 hEq1 hAlpha t (a, b)

lemma shifted_nsd_survival_iInf_eq_zero
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (k : ℕ) :
    (⨅ t : ℕ,
      (kernelIter
        (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
        k {m | 0 < m}) = 0 := by
  let N := shiftBDOne (nsdTotalPopBDChain params)
  by_cases hBeta : params.beta = 0
  · have hq : ∀ m : ℕ, 0 < m → N.q m = 1 := by
      intro m hm
      have hm0 : m ≠ 0 := hm.ne'
      have hm2 : ¬m + 1 ≤ 1 := by omega
      dsimp [N, shiftBDOne]
      simp only [hm0, ↓reduceIte, nsdTotalPopBDChain, hm2, hBeta, zero_add]
      have hmcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by
        push_cast
        ring
      rw [hmcast]
      have hden :
          params.delta + params.alpha0 * (m : ℝ) ≠ 0 := by
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have : 0 < params.alpha0 * (m : ℝ) := mul_pos hAlpha hmR
        linarith [params.delta_nonneg]
      exact div_self hden
    by_cases hk : k = 0
    · subst k
      apply le_antisymm
      · exact le_trans (iInf_le _ 0) (by
          simp [kernelIter_zero, Kernel.id_apply])
      · exact zero_le
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hmass_ge :
          1 ≤ (kernelIter (bdKernel N) k) k {0} := by
        simpa using
          bd_consecutive_deaths N 1 one_pos
            (fun m hm => by rw [hq m hm]) k hkpos
      haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) k) k) :=
        (kernelIter_isMarkov (K := bdKernel N) k).isProbabilityMeasure k
      have hmass : (kernelIter (bdKernel N) k) k {0} = 1 :=
        le_antisymm prob_le_one hmass_ge
      have hsurv : (kernelIter (bdKernel N) k) k {m | 0 < m} = 0 := by
        have hset : ({m : ℕ | 0 < m} : Set ℕ) = ({0} : Set ℕ)ᶜ := by
          ext m
          simp [Nat.pos_iff_ne_zero]
        rw [hset, measure_compl (measurableSet_singleton 0)
          (measure_ne_top _ _), hmass, measure_univ, tsub_self]
      apply le_antisymm
      · calc
          (⨅ t : ℕ,
              (kernelIter (bdKernel N) t) k {m | 0 < m})
              ≤ (kernelIter (bdKernel N) k) k {m | 0 < m} := iInf_le _ k
          _ = 0 := hsurv
      · exact zero_le
  · have hBetaPos : 0 < params.beta :=
      lt_of_le_of_ne params.beta_nonneg (Ne.symm hBeta)
    obtain ⟨n₀, ε, hε, _, hDrift⟩ :=
      nsdTotalPopBDChain_drift params hAlpha
    let δ₀ : ℝ :=
      params.alpha0 / (params.beta + params.delta + params.alpha0)
    have hden0 : 0 < params.beta + params.delta + params.alpha0 := by
      linarith [params.delta_nonneg]
    have hδ₀ : 0 < δ₀ := div_pos hAlpha hden0
    have hBirth : ∀ m : ℕ, 0 < m → 0 < N.p m := by
      intro m hm
      have hm0 : m ≠ 0 := hm.ne'
      have hm2 : ¬m + 1 ≤ 1 := by omega
      dsimp [N, shiftBDOne]
      simp only [hm0, ↓reduceIte, nsdTotalPopBDChain, hm2]
      apply div_pos hBetaPos
      have hmR : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) - 1 := by
        have : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < m + 1)
        linarith
      nlinarith [params.delta_nonneg, mul_pos hAlpha hmR]
    have hDeath : ∀ m : ℕ, 0 < m → δ₀ ≤ N.q m := by
      intro m hm
      have hm0 : m ≠ 0 := hm.ne'
      have hm2 : ¬m + 1 ≤ 1 := by omega
      dsimp [N, shiftBDOne]
      simp only [hm0, ↓reduceIte, nsdTotalPopBDChain, hm2]
      have hmR : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) - 1 := by
        have : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m + 1)
        linarith
      have hx : params.alpha0 ≤
          params.delta + params.alpha0 * (((m + 1 : ℕ) : ℝ) - 1) := by
        nlinarith [params.delta_nonneg,
          mul_le_mul_of_nonneg_left hmR hAlpha.le]
      have hden :
          0 < params.beta + params.delta +
            params.alpha0 * (((m + 1 : ℕ) : ℝ) - 1) := by
        linarith
      dsimp [δ₀]
      rw [div_le_div_iff₀ hden0 hden]
      nlinarith [params.beta_nonneg, params.delta_nonneg,
        mul_nonneg params.delta_nonneg
          (add_nonneg params.delta_nonneg
            (mul_nonneg hAlpha.le
              (by linarith : 0 ≤ (((m + 1 : ℕ) : ℝ) - 1))))]
    have hShiftDrift :
        ∀ m, n₀ ≤ m → 0 < m → N.p m - N.q m ≤ -ε := by
      intro m hm0 hm
      have hmne : m ≠ 0 := hm.ne'
      have hm2 : ¬m + 1 ≤ 1 := by omega
      dsimp [N, shiftBDOne]
      simp only [hmne, ↓reduceIte]
      exact hDrift (m + 1) (hm0.trans (Nat.le_succ m)) (by omega)
    simpa only [N] using
      bd_survival_iInf_eq_zero_of_eventual_negative_drift N
        hBirth δ₀ ε hδ₀ hε hDeath n₀ hShiftDrift k

lemma nsd_consensus_almost_sure_via_shift
    (params : LVParams)
    (_hGamma0 : 0 < params.gamma0) (_hGamma1 : 0 < params.gamma1)
    (_hAlphaSum : 0 < params.alpha0 + params.alpha1)
    (a b : Nat)
    (hposA : 0 < a) (hposB : 0 < b)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    [IsMarkovKernel (lvKernel .nonSelfDestructive params)] :
    lvPathMeasure .nonSelfDestructive params (a, b)
      {ω | consensusReachedEvent ω} = 1 := by
  let P := lvPathMeasure .nonSelfDestructive params (a, b)
  let C : Set (ℕ → PopState) := {ω | consensusReachedEvent ω}
  let A : Set (ℕ → PopState) := {ω | ¬consensusReachedEvent ω}
  haveI : IsProbabilityMeasure P := by
    dsimp [P, lvPathMeasure, homogeneousPathMeasure]
    infer_instance
  have hA_le : ∀ t : ℕ,
      P A ≤
        (kernelIter
          (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
          (popExcessOne (a, b)) {m | 0 < m} := by
    intro t
    calc
      P A ≤ P {ω | ∀ u ≤ t, 0 < (ω u).1 ∧ 0 < (ω u).2} := by
        apply measure_mono
        intro ω hω u hu
        have hnreach : ¬reachedConsensus (ω u) := by
          intro hreach
          apply hω
          exact lt_of_le_of_lt
            (consensusTime_le_of_reached' ω u hreach)
            (WithTop.coe_lt_top u)
        simp only [reachedConsensus, not_or] at hnreach
        exact ⟨Nat.pos_of_ne_zero hnreach.1,
          Nat.pos_of_ne_zero hnreach.2⟩
      _ ≤ (kernelIter
          (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
          (popExcessOne (a, b)) {m | 0 < m} :=
        nsd_path_stay_interior_le_shift params hNeutral hEq0 hEq1 hAlpha a b t
  have hA_zero : P A = 0 := by
    apply le_antisymm
    · calc
        P A ≤ ⨅ t : ℕ,
            (kernelIter
              (bdKernel (shiftBDOne (nsdTotalPopBDChain params))) t)
              (popExcessOne (a, b)) {m | 0 < m} := le_iInf hA_le
        _ = 0 :=
          shifted_nsd_survival_iInf_eq_zero params hAlpha
            (popExcessOne (a, b))
    · exact zero_le
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
  have hC_meas : MeasurableSet C := by
    rw [hC_union]
    exact MeasurableSet.iUnion fun t =>
      measurableSet_consensusTime_eq_coe t
  have hcomp : Cᶜ = A := by
    ext ω
    simp [C, A]
  have hsum := measure_add_measure_compl hC_meas (μ := P)
  rw [hcomp, hA_zero, add_zero, measure_univ] at hsum
  simpa [P, C] using hsum

end LVConsensus
