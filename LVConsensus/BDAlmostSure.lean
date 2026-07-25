import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal

namespace LVConsensus

private noncomputable def survR (N : BirthDeathChain) (n t : ℕ) : ℝ :=
  ((kernelIter (bdKernel N) t) n {x | 0 < x}).toReal

private lemma survR_nonneg (N : BirthDeathChain) (n t : ℕ) :
    0 ≤ survR N n t := ENNReal.toReal_nonneg

private lemma survR_le_one (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n t : ℕ) :
    survR N n t ≤ 1 := by
  rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
  exact ENNReal.toReal_mono (by simp) (by
    haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n) :=
      (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure n
    exact prob_le_one)

private lemma survR_antitone (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    Antitone (survR N n) := by
  intro t u htu
  haveI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n) :=
    (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure n
  apply ENNReal.toReal_mono
  · exact measure_ne_top _ _
  · -- survival decreases because zero is absorbing
    rw [show u = t + (u - t) by omega, kernelIter_add,
      Kernel.comp_apply' _ _ _ ((Set.to_countable _).measurableSet)]
    calc
      ∫⁻ y, (kernelIter (bdKernel N) (u - t)) y {x | 0 < x}
          ∂(kernelIter (bdKernel N) t) n
          ≤ ∫⁻ y, Set.indicator {x | 0 < x} (fun _ => 1) y
              ∂(kernelIter (bdKernel N) t) n := by
            apply lintegral_mono
            intro y
            by_cases hy : 0 < y
            · simp only [Set.indicator_apply, Set.mem_setOf_eq, hy, ↓reduceIte,
                Pi.one_apply]
              haveI : IsProbabilityMeasure
                  ((kernelIter (bdKernel N) (u - t)) y) :=
                (kernelIter_isMarkov (K := bdKernel N) (u - t))
                  |>.isProbabilityMeasure y
              exact prob_le_one
            · have hy0 : y = 0 := by omega
              subst y
              simp [kernelIter_bdKernel_zero, Measure.dirac_apply]
      _ = (kernelIter (bdKernel N) t) n {x | 0 < x} := by
            rw [lintegral_indicator ((Set.to_countable _).measurableSet)]
            simp

private noncomputable def survLimit (N : BirthDeathChain) (n : ℕ) : ℝ :=
  ⨅ t : ℕ, survR N n t

private lemma survR_tendsto (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    Filter.Tendsto (survR N n) Filter.atTop
      (nhds (survLimit N n)) := by
  exact tendsto_atTop_ciInf (survR_antitone N n)
    ⟨0, fun x hx => by rcases hx with ⟨t, rfl⟩; exact survR_nonneg N n t⟩

private lemma survLimit_nonneg (N : BirthDeathChain) (n : ℕ) :
    0 ≤ survLimit N n := by
  exact le_ciInf (fun t => survR_nonneg N n t)

private lemma survLimit_le_one (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    survLimit N n ≤ 1 := by
  exact ciInf_le_of_le (by
    exact ⟨0, fun x hx => by
      rcases hx with ⟨t, rfl⟩
      exact survR_nonneg N n t⟩) 0 (survR_le_one N n 0)

private lemma survR_succ (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n t : ℕ) :
    survR N n (t + 1) =
      N.p n * survR N (n + 1) t +
      N.q n * survR N (n - 1) t +
      holdProb N n * survR N n t := by
  unfold survR
  rw [kernelIter_succ_right,
    Kernel.comp_apply' _ _ _ ((Set.to_countable _).measurableSet),
    bdKernel_apply,
    lintegral_add_measure, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure,
    lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, lintegral_dirac]
  simp only [smul_eq_mul]
  have hpTop :
      ENNReal.ofReal (N.p n) *
          (kernelIter (bdKernel N) t) (n + 1) {x | 0 < x} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      letI : IsProbabilityMeasure
          ((kernelIter (bdKernel N) t) (n + 1)) :=
        (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure _
      exact measure_ne_top _ _)
  have hqTop :
      ENNReal.ofReal (N.q n) *
          (kernelIter (bdKernel N) t) (n - 1) {x | 0 < x} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      letI : IsProbabilityMeasure
          ((kernelIter (bdKernel N) t) (n - 1)) :=
        (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure _
      exact measure_ne_top _ _)
  have hhTop :
      ENNReal.ofReal (holdProb N n) *
          (kernelIter (bdKernel N) t) n {x | 0 < x} ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      letI : IsProbabilityMeasure
          ((kernelIter (bdKernel N) t) n) :=
        (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure _
      exact measure_ne_top _ _)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hpTop, hqTop⟩) hhTop,
    ENNReal.toReal_add hpTop hqTop,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofReal (N.p_nonneg n),
      ENNReal.toReal_ofReal (N.q_nonneg n)]
  have hhold : 0 ≤ holdProb N n := by
    show 0 ≤ 1 - N.p n - N.q n
    linarith [N.pq_le_one n]
  rw [ENNReal.toReal_ofReal hhold]

private lemma survLimit_harmonic (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    survLimit N n =
      N.p n * survLimit N (n + 1) +
      N.q n * survLimit N (n - 1) +
      holdProb N n * survLimit N n := by
  have hshift :
      Filter.Tendsto (fun t => survR N n (t + 1)) Filter.atTop
        (nhds (survLimit N n)) := by
    exact (survR_tendsto N n).comp (Filter.tendsto_add_atTop_nat 1)
  have hp := (tendsto_const_nhds (x := N.p n)).mul (survR_tendsto N (n + 1))
  have hq := (tendsto_const_nhds (x := N.q n)).mul (survR_tendsto N (n - 1))
  have hh := (tendsto_const_nhds (x := holdProb N n)).mul (survR_tendsto N n)
  have hr :
      Filter.Tendsto
        (fun t =>
          N.p n * survR N (n + 1) t +
          N.q n * survR N (n - 1) t +
          holdProb N n * survR N n t)
        Filter.atTop
        (nhds
          (N.p n * survLimit N (n + 1) +
          N.q n * survLimit N (n - 1) +
          holdProb N n * survLimit N n)) :=
    (hp.add hq).add hh
  exact tendsto_nhds_unique hshift
    (by simpa only [survR_succ N] using hr)

private lemma survLimit_zero (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] :
    survLimit N 0 = 0 := by
  apply le_antisymm
  · have hbdd : BddBelow (Set.range (survR N 0)) :=
      ⟨0, fun x hx => by
        rcases hx with ⟨t, rfl⟩
        exact survR_nonneg N 0 t⟩
    exact le_trans (ciInf_le hbdd 0) (by
      simp [survR, kernelIter_zero, Kernel.id_apply, Measure.dirac_apply])
  · exact survLimit_nonneg N 0

private lemma increment_relation (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)] (n : ℕ) :
    N.p n * (survLimit N (n + 1) - survLimit N n) =
      N.q n * (survLimit N n - survLimit N (n - 1)) := by
  have h := survLimit_harmonic N n
  simp only [holdProb] at h
  linarith

private lemma survLimit_mono (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (hBirth : ∀ n, 0 < n → 0 < N.p n)
    (δ : ℝ) (hδ : 0 < δ)
    (hDeath : ∀ n, 0 < n → δ ≤ N.q n) :
    Monotone (survLimit N) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n using Nat.case_strong_induction_on with
  | hz =>
      rw [survLimit_zero N]
      exact survLimit_nonneg N 1
  | hi n ih =>
      have hn : 0 < n + 1 := by omega
      have hq : 0 < N.q (n + 1) :=
        lt_of_lt_of_le hδ (hDeath (n + 1) hn)
      have hp : 0 < N.p (n + 1) := hBirth (n + 1) hn
      have hrel := increment_relation N (n + 1)
      have hprev : 0 ≤
          survLimit N (n + 1) - survLimit N ((n + 1) - 1) := by
        have hle : survLimit N n ≤ survLimit N (n + 1) := ih n le_rfl
        simpa using sub_nonneg.mpr hle
      nlinarith

private lemma survLimit_eq_zero (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (hBirth : ∀ n, 0 < n → 0 < N.p n)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε) :
    ∀ n, survLimit N n = 0 := by
  have hmono := survLimit_mono N hBirth δ hδ hDeath
  have hu0 := survLimit_zero N
  have hu1 : survLimit N 1 = 0 := by
    by_contra hne
    have hu1pos : 0 < survLimit N 1 := by
      have := survLimit_nonneg N 1
      exact lt_of_le_of_ne this (Ne.symm hne)
    let d : ℕ → ℝ := fun n => survLimit N (n + 1) - survLimit N n
    have hd0 : 0 < d 0 := by
      simp only [d, zero_add]
      rw [hu0]
      simpa using hu1pos
    have hdpos : ∀ n, 0 < d n := by
      intro n
      induction n with
      | zero => exact hd0
      | succ n ih =>
          have hn1 : 0 < n + 1 := by omega
          have hp : 0 < N.p (n + 1) := hBirth (n + 1) hn1
          have hq : 0 < N.q (n + 1) :=
            lt_of_lt_of_le hδ (hDeath (n + 1) hn1)
          have hrel := increment_relation N (n + 1)
          simp only [d]
          have hrel' :
              N.p (n + 1) * d (n + 1) =
                N.q (n + 1) * d n := by
            simpa [d, Nat.add_assoc] using hrel
          nlinarith
    set L : ℕ := max n₀ 1
    have hLpos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hLge : n₀ ≤ L := le_max_left _ _
    have hstep : ∀ n, L ≤ n →
        (1 + ε) * d (n - 1) ≤ d n := by
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le hLpos hn
      have hp : 0 < N.p n := hBirth n hnpos
      have hq : 0 < N.q n := lt_of_lt_of_le hδ (hDeath n hnpos)
      have hp1 : N.p n ≤ 1 := by
        nlinarith [N.pq_le_one n, N.q_nonneg n]
      have hdrift := hDrift n (hLge.trans hn) hnpos
      have hrel := increment_relation N n
      have hnm : n - 1 + 1 = n :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnpos.ne')
      have hrel' : N.p n * d n = N.q n * d (n - 1) := by
        simpa [d, hnm] using hrel
      have hdprev : 0 < d (n - 1) := hdpos _
      have hdiff : 0 ≤ d n - d (n - 1) := by
        nlinarith
      have hscaled :
          N.p n * (d n - d (n - 1)) ≤ d n - d (n - 1) := by
        nlinarith [N.p_nonneg n]
      have hgain :
          ε * d (n - 1) ≤ N.p n * (d n - d (n - 1)) := by
        nlinarith
      nlinarith
    set base : ℕ := L - 1
    have hbase_succ : base + 1 = L := by
      dsimp [base]
      omega
    have hgrow : ∀ k : ℕ,
        (1 + ε) ^ k * d base ≤ d (base + k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have hfac : 0 ≤ 1 + ε := by linarith
          calc
            (1 + ε) ^ (k + 1) * d base
                = (1 + ε) * ((1 + ε) ^ k * d base) := by
                    rw [pow_succ]
                    ring
            _ ≤ (1 + ε) * d (base + k) :=
              mul_le_mul_of_nonneg_left ih hfac
            _ ≤ d (base + (k + 1)) := by
              have hs := hstep (base + k + 1) (by omega)
              simpa [Nat.add_assoc] using hs
    have hbasepos : 0 < d base := hdpos base
    obtain ⟨k, hk⟩ :=
      pow_unbounded_of_one_lt (1 / d base) (by linarith : 1 < 1 + ε)
    have hk' : 1 < (1 + ε) ^ k * d base := by
      exact (div_lt_iff₀ hbasepos).mp (by simpa [one_div] using hk)
    have hdupper : d (base + k) ≤ 1 := by
      have hnn := survLimit_nonneg N (base + k)
      have htop := survLimit_le_one N (base + k + 1)
      dsimp [d]
      linarith
    linarith [hk', hgrow k, hdupper]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | k
      · exact hu0
      · exact hu1
      · have hcur : survLimit N (k + 1) = 0 := ih (k + 1) (by omega)
        have hprev : survLimit N k = 0 := ih k (by omega)
        have hp : 0 < N.p (k + 1) := hBirth (k + 1) (by omega)
        have hrel := increment_relation N (k + 1)
        simp only [hcur, hprev, sub_zero, zero_sub, mul_zero, add_eq_zero,
          Nat.add_sub_cancel] at hrel
        nlinarith [survLimit_nonneg N (k + 2)]

theorem bd_survival_iInf_eq_zero_of_eventual_negative_drift
    (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (hBirth : ∀ n, 0 < n → 0 < N.p n)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (n : ℕ) :
    (⨅ t : ℕ, (kernelIter (bdKernel N) t) n {x | 0 < x}) = 0 := by
  let S : ℝ≥0∞ :=
    ⨅ t : ℕ, (kernelIter (bdKernel N) t) n {x | 0 < x}
  have hS_le_one : S ≤ 1 := by
    calc
      S ≤ (kernelIter (bdKernel N) 0) n {x | 0 < x} := iInf_le _ 0
      _ ≤ 1 := by
        letI : IsProbabilityMeasure
            ((kernelIter (bdKernel N) 0) n) :=
          (kernelIter_isMarkov (K := bdKernel N) 0).isProbabilityMeasure n
        exact prob_le_one
  have hS_ne : S ≠ ⊤ := ne_top_of_le_ne_top (by simp) hS_le_one
  have hreal : S.toReal = 0 := by
    apply le_antisymm
    · rw [← survLimit_eq_zero N hBirth δ ε hδ hε hDeath n₀ hDrift n]
      apply le_ciInf
      intro t
      have hR_ne :
          (kernelIter (bdKernel N) t) n {x | 0 < x} ≠ ⊤ := by
        letI : IsProbabilityMeasure
            ((kernelIter (bdKernel N) t) n) :=
          (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure n
        exact measure_ne_top _ _
      exact ENNReal.toReal_mono hR_ne (iInf_le _ t)
    · exact ENNReal.toReal_nonneg
  have hS_zero : S = 0 :=
    (ENNReal.toReal_eq_zero_iff S).mp hreal |>.resolve_right hS_ne
  simpa only [S] using hS_zero

theorem bd_nonextinction_zero_of_eventual_negative_drift
    (N : BirthDeathChain)
    [IsMarkovKernel (bdKernel N)]
    (hBirth : ∀ n, 0 < n → 0 < N.p n)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hDeath : ∀ n, 0 < n → δ ≤ N.q n)
    (n₀ : ℕ)
    (hDrift : ∀ n, n₀ ≤ n → 0 < n → N.p n - N.q n ≤ -ε)
    (n : ℕ) :
    bdPathMeasure N n {ω | extinctionTime ω = ⊤} = 0 := by
  let μ := bdPathMeasure N n
  let A : Set (ℕ → ℕ) := {ω | extinctionTime ω = ⊤}
  have hle : ∀ t : ℕ,
      μ A ≤ (kernelIter (bdKernel N) t) n {x | 0 < x} := by
    intro t
    calc
      μ A ≤ extinctionTail N n (t + 1) := by
        apply measure_mono
        intro ω hω
        simp only [A, Set.mem_setOf_eq] at hω
        simp only [extinctionTail, Set.mem_setOf_eq]
        rw [hω]
        exact le_top
      _ ≤ (kernelIter (bdKernel N) t) n {x | 0 < x} :=
        extinctionTail_le_marginal N n t
  have hμA_ne : μ A ≠ ⊤ := by
    haveI : IsProbabilityMeasure μ := by
      dsimp [μ, bdPathMeasure, homogeneousPathMeasure]
      infer_instance
    exact measure_ne_top _ _
  have hreal : (μ A).toReal = 0 := by
    apply le_antisymm
    · rw [← survLimit_eq_zero N hBirth δ ε hδ hε hDeath n₀ hDrift n]
      apply le_ciInf
      intro t
      have hRne :
          (kernelIter (bdKernel N) t) n {x | 0 < x} ≠ ⊤ := by
        letI : IsProbabilityMeasure ((kernelIter (bdKernel N) t) n) :=
          (kernelIter_isMarkov (K := bdKernel N) t).isProbabilityMeasure n
        exact measure_ne_top _ _
      exact ENNReal.toReal_mono hRne (hle t)
    · exact ENNReal.toReal_nonneg
  exact (ENNReal.toReal_eq_zero_iff (μ A)).mp hreal |>.resolve_right hμA_ne

end LVConsensus
