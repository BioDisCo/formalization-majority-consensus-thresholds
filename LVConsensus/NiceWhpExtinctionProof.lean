import LVConsensus.NiceWhpBirths
import LVConsensus.Preliminaries
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

private noncomputable def biasedCoin (d : ℝ) : Measure Bool :=
  ENNReal.ofReal d • Measure.dirac true +
    ENNReal.ofReal (1 - d) • Measure.dirac false

private lemma biasedCoin_isProbability (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    IsProbabilityMeasure (biasedCoin d) := by
  refine ⟨?_⟩
  simp [biasedCoin]
  rw [← ENNReal.ofReal_add hd0]
  norm_num
  linarith

private lemma biasedCoin_true (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    biasedCoin d {true} = ENNReal.ofReal d := by
  simp [biasedCoin, Measure.smul_apply, hd0, hd1]

private noncomputable def biasedCoins (d : ℝ) :
    Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => biasedCoin d

private lemma biasedCoins_isProbability (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    IsProbabilityMeasure (biasedCoins d) := by
  letI : IsProbabilityMeasure (biasedCoin d) :=
    biasedCoin_isProbability d hd0 hd1
  unfold biasedCoins
  infer_instance

private def coinStep (i : ℕ) (ω : ℕ → Bool) : Bool :=
  ω i

private lemma coinStep_measurable (i : ℕ) :
    Measurable (coinStep i) :=
  measurable_pi_apply i

private lemma coinStep_indep (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    iIndepFun coinStep (biasedCoins d) := by
  letI hcoin : IsProbabilityMeasure (biasedCoin d) :=
    biasedCoin_isProbability d hd0 hd1
  letI : ∀ i : ℕ,
      IsProbabilityMeasure ((fun _ : ℕ => biasedCoin d) i) :=
    fun _ => hcoin
  have h := iIndepFun_infinitePi
    (P := fun _ : ℕ => biasedCoin d)
    (X := fun _ : ℕ => id)
    (fun _ => measurable_id)
  change iIndepFun (fun i ω => ω i)
    (Measure.infinitePi fun _ : ℕ => biasedCoin d)
  exact h

private lemma biasedCoins_coin_true (d : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (i : ℕ) :
    biasedCoins d {ω | coinStep i ω = true} =
      ENNReal.ofReal d := by
  letI hcoin : IsProbabilityMeasure (biasedCoin d) :=
    biasedCoin_isProbability d hd0 hd1
  letI : ∀ i : ℕ,
      IsProbabilityMeasure ((fun _ : ℕ => biasedCoin d) i) :=
    fun _ => hcoin
  change biasedCoins d
    ((fun ω : ℕ → Bool => ω i) ⁻¹' {true}) =
      ENNReal.ofReal d
  rw [← Measure.map_apply (measurable_pi_apply i)
    (measurableSet_singleton true)]
  unfold biasedCoins
  rw [Measure.infinitePi_map_eval]
  exact biasedCoin_true d hd0 hd1

/-- A progress step is either a death while the chain is alive or any step
after state zero has already been reached. -/
private def progressStep (i : ℕ) (ω : ℕ → ℕ) : Bool :=
  decide (ω i = 0 ∨ ω (i + 1) + 1 = ω i)

private lemma progressStep_measurable (i : ℕ) :
    Measurable (progressStep i) := by
  unfold progressStep
  apply Measurable.ite
  · have hp : Measurable
        (fun ω : ℕ → ℕ =>
          (ω i, ω (i + 1))) :=
      (measurable_pi_apply i).prodMk
        (measurable_pi_apply (i + 1))
    exact hp ((Set.to_countable
      {z : ℕ × ℕ | z.1 = 0 ∨ z.2 + 1 = z.1}).measurableSet)
  · exact measurable_const
  · exact measurable_const

private def progressFailure : Set (ℕ → ℕ) :=
  {ω | ω 0 ≠ 0 ∧ ω 1 + 1 ≠ ω 0}

private lemma measurableSet_progressFailure :
    MeasurableSet progressFailure := by
  unfold progressFailure
  measurability

private lemma progressFailure_shift (i : ℕ) :
    (pathShift i) ⁻¹' progressFailure =
      {ω | progressStep i ω = false} := by
  ext ω
  simp [progressFailure, progressStep, pathShift]

private lemma bdKernel_failure_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (D : ℝ) (hD0 : 0 < D)
    (hq : ∀ x, 0 < x → D ≤ N.q x)
    (x : ℕ) :
    bdPathMeasure N x progressFailure ≤
      ENNReal.ofReal (1 - D) := by
  have hD1 : D ≤ 1 := by
    have hq1 := hq 1 Nat.one_pos
    have hpq := N.pq_le_one 1
    have hp0 := N.p_nonneg 1
    linarith
  rcases x.eq_zero_or_pos with rfl | hx
  · calc
      bdPathMeasure N 0 progressFailure
          ≤ bdPathMeasure N 0 {ω | ω 0 ≠ 0} := by
            apply measure_mono
            intro ω hω
            exact hω.1
      _ = 0 := bdPathMeasure_initial_ne N 0
      _ ≤ ENNReal.ofReal (1 - D) := by positivity
  · let S : Set ℕ := {y | y + 1 ≠ x}
    have hsubset :
        progressFailure ⊆
          {ω | ω 0 ≠ x} ∪ {ω | ω 1 ∈ S} := by
      intro ω hω
      by_cases h0 : ω 0 = x
      · right
        simpa [S, h0] using hω.2
      · exact Or.inl h0
    have hS :
        S = ({x - 1} : Set ℕ)ᶜ := by
      ext y
      simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      omega
    calc
      bdPathMeasure N x progressFailure
          ≤ bdPathMeasure N x
              ({ω | ω 0 ≠ x} ∪ {ω | ω 1 ∈ S}) :=
            measure_mono hsubset
      _ ≤ bdPathMeasure N x {ω | ω 0 ≠ x} +
            bdPathMeasure N x {ω | ω 1 ∈ S} :=
          measure_union_le _ _
      _ = bdPathMeasure N x {ω | ω 1 ∈ S} := by
          rw [bdPathMeasure_initial_ne N x]
          simp
      _ = (bdKernel N x) S := by
          rw [bdPathMeasure_coord_eq N x 1 S
            ((Set.to_countable S).measurableSet),
            kernelIter_one]
      _ = 1 - ENNReal.ofReal (N.q x) := by
          rw [hS, measure_compl (measurableSet_singleton _)]
          · haveI : IsProbabilityMeasure (bdKernel N x) :=
              (inferInstance :
                IsMarkovKernel (bdKernel N)).isProbabilityMeasure x
            rw [measure_univ,
              bdKernel_down_singleton N x hx]
          · exact measure_ne_top _ _
      _ = ENNReal.ofReal (1 - N.q x) := by
          simpa using
            (ENNReal.ofReal_sub 1 (N.q_nonneg x)).symm
      _ ≤ ENNReal.ofReal (1 - D) := by
          exact ENNReal.ofReal_le_ofReal (by
            have := hq x hx
            linarith)

private lemma progressPast_cylinder
    (R : ℕ) (i : Fin R) (A : Set (ℕ → ℕ))
    (hA : MeasurableSet[
      bernoulliPastSpace
        (fun j : Fin R => progressStep j) i] A) :
    MeasurableSet A ∧ isCylinderUpTo i A := by
  let F : (ℕ → ℕ) → (∀ j : Finset.Iic i.val, ℕ) :=
    @frestrictLe ℕ _ (fun _ : ℕ => ℕ) _ i.val
  have hPastLe :
      bernoulliPastSpace
          (fun j : Fin R => progressStep j) i ≤
        MeasurableSpace.comap F ⊤ := by
    unfold bernoulliPastSpace
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    have hji : j.val < i.val := by
      simpa using hj
    let G :
        (∀ u : Finset.Iic i.val, ℕ) → Bool :=
      fun p => decide
        (p ⟨j.val, Finset.mem_Iic.mpr
            (Nat.le_of_lt hj)⟩ = 0 ∨
          p ⟨j.val + 1, Finset.mem_Iic.mpr
            (Nat.succ_le_iff.mpr hji)⟩ + 1 =
          p ⟨j.val, Finset.mem_Iic.mpr
            (Nat.le_of_lt hj)⟩)
    have heq :
        progressStep j = G ∘ F := by
      funext ω
      simp [progressStep, G, F, frestrictLe_apply]
      rfl
    change MeasurableSpace.comap (progressStep j.val) ⊤ ≤
      MeasurableSpace.comap F ⊤
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono le_top
  have hA' :
      MeasurableSet[MeasurableSpace.comap F ⊤] A :=
    hPastLe A hA
  obtain ⟨B, hB, hAB⟩ :=
    MeasurableSpace.measurableSet_comap.mp hA'
  constructor
  · rw [← hAB]
    exact (Set.to_countable B).measurableSet.preimage (by
      simpa [F] using
        (measurable_frestrictLe
          (X := fun _ : ℕ => ℕ) i.val))
  · intro ω η heq hω
    rw [← hAB] at hω ⊢
    have hprefix : F ω = F η := by
      funext j
      exact heq j (Finset.mem_Iic.mp j.2)
    simpa [hprefix] using hω

private lemma progress_conditionally_ge
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hq : ∀ x, 0 < x → D ≤ N.q x)
    (n R : ℕ) :
    BernoulliConditionallyGECross
      (bdPathMeasure N n) (biasedCoins D)
      (fun i : Fin R => progressStep i)
      (fun i : Fin R => coinStep i) := by
  letI : IsProbabilityMeasure (bdPathMeasure N n) := by
    unfold bdPathMeasure homogeneousPathMeasure
    infer_instance
  intro i A hA
  obtain ⟨hAmeas, hAcyl⟩ :=
    progressPast_cylinder R i A hA
  let L : Set (ℕ → ℕ) :=
    {ω | progressStep i ω = true}
  let F : Set (ℕ → ℕ) :=
    {ω | progressStep i ω = false}
  have hLmeas : MeasurableSet L :=
    (progressStep_measurable i)
      (measurableSet_singleton true)
  have hFmeas : MeasurableSet F :=
    (progressStep_measurable i)
      (measurableSet_singleton false)
  have hmarkov :
      bdPathMeasure N n (A ∩ F) ≤
        ENNReal.ofReal (1 - D) *
          bdPathMeasure N n A := by
    rw [show F = (pathShift i.val) ⁻¹'
        progressFailure by
      exact (progressFailure_shift i.val).symm]
    exact homogeneousPathMeasure_markov_bound
      (bdKernel N) n i.val
      (ENNReal.ofReal (1 - D)) A progressFailure
      hAmeas measurableSet_progressFailure hAcyl
      (by
        intro ω _hω
        simpa [bdPathMeasure] using
          bdKernel_failure_le N D hD0 hq (ω i.val))
  have hfail :
      (bdPathMeasure N n).real (A ∩ F) ≤
        (1 - D) * (bdPathMeasure N n).real A := by
    have hreal := (ENNReal.toReal_le_toReal
      (measure_ne_top (bdPathMeasure N n) (A ∩ F))
      (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top
        (measure_ne_top (bdPathMeasure N n) A))).mpr
      hmarkov
    simpa [measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - D)]
      using hreal
  have hdisj : Disjoint (A ∩ L) (A ∩ F) := by
    rw [Set.disjoint_left]
    intro ω hωL hωF
    simp only [Set.mem_inter_iff, L, F,
      Set.mem_setOf_eq] at hωL hωF
    simp [hωL.2] at hωF
  have hunion : (A ∩ L) ∪ (A ∩ F) = A := by
    ext ω
    simp only [Set.mem_union, Set.mem_inter_iff,
      L, F, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hω
      by_cases h : progressStep i ω = true
      · exact Or.inl ⟨hω, h⟩
      · right
        exact ⟨hω, Bool.eq_false_of_not_eq_true h⟩
  have hsplit :
      (bdPathMeasure N n).real A =
        (bdPathMeasure N n).real (A ∩ L) +
          (bdPathMeasure N n).real (A ∩ F) := by
    calc
      (bdPathMeasure N n).real A =
          (bdPathMeasure N n).real
            ((A ∩ L) ∪ (A ∩ F)) := by rw [hunion]
      _ = (bdPathMeasure N n).real (A ∩ L) +
          (bdPathMeasure N n).real (A ∩ F) :=
        measureReal_union (μ := bdPathMeasure N n) hdisj
          (hAmeas.inter hFmeas)
  have hcoin :
      (biasedCoins D).real
          {ω | coinStep i ω = true} = D := by
    rw [measureReal_def,
      biasedCoins_coin_true D hD0.le hD1 i]
    exact ENNReal.toReal_ofReal hD0.le
  change
    (bdPathMeasure N n).real A *
        (biasedCoins D).real
          {ω | coinStep i ω = true} ≤
      (bdPathMeasure N n).real
        (A ∩ {ω | progressStep i ω = true})
  rw [hcoin]
  change
    (bdPathMeasure N n).real A * D ≤
      (bdPathMeasure N n).real (A ∩ L)
  nlinarith

private def boolCount
    {Ω : Type*} {R : ℕ}
    (X : Fin R → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ i : Fin R, if X i ω then 1 else 0

private lemma boolCount_measurable
    {Ω : Type*} [MeasurableSpace Ω] {R : ℕ}
    (X : Fin R → Ω → Bool)
    (hX : ∀ i, Measurable (X i)) :
    Measurable (boolCount X) := by
  unfold boolCount
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_of_finite
      (fun b : Bool => if b then (1 : ℕ) else 0)).comp
    (hX i)

private lemma iid_progress_domination
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hq : ∀ x, 0 < x → D ≤ N.q x)
    (n R r : ℕ) :
    biasedCoins D
        {ω | r ≤ boolCount
          (fun i : Fin R => coinStep i) ω} ≤
      bdPathMeasure N n
        {ω | r ≤ boolCount
          (fun i : Fin R => progressStep i) ω} := by
  letI : IsProbabilityMeasure (bdPathMeasure N n) := by
    unfold bdPathMeasure homogeneousPathMeasure
    infer_instance
  letI : IsProbabilityMeasure (biasedCoins D) :=
    biasedCoins_isProbability D hD0.le hD1
  simpa only [boolCount] using
    bernoulli_sum_domination_lower_cross
      (bdPathMeasure N n) (biasedCoins D) R
      (fun i : Fin R => progressStep i)
      (fun i : Fin R => coinStep i)
      (fun i => progressStep_measurable i)
      (fun i => coinStep_measurable i)
      ((coinStep_indep D hD0.le hD1).precomp
        Fin.val_injective)
      (progress_conditionally_ge N D hD0 hD1 hq n R)
      r

private lemma progress_lower_tail_le
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hq : ∀ x, 0 < x → D ≤ N.q x)
    (n R r : ℕ) :
    bdPathMeasure N n
        {ω | boolCount
          (fun i : Fin R => progressStep i) ω < r} ≤
      biasedCoins D
        {ω | boolCount
          (fun i : Fin R => coinStep i) ω < r} := by
  letI : IsProbabilityMeasure (bdPathMeasure N n) := by
    unfold bdPathMeasure homogeneousPathMeasure
    infer_instance
  letI : IsProbabilityMeasure (biasedCoins D) :=
    biasedCoins_isProbability D hD0.le hD1
  let A : Set (ℕ → ℕ) :=
    {ω | r ≤ boolCount
      (fun i : Fin R => progressStep i) ω}
  let B : Set (ℕ → Bool) :=
    {ω | r ≤ boolCount
      (fun i : Fin R => coinStep i) ω}
  have hAmeas : MeasurableSet A :=
    (boolCount_measurable
      (fun i : Fin R => progressStep i)
      (fun i => progressStep_measurable i))
      measurableSet_Ici
  have hBmeas : MeasurableSet B :=
    (boolCount_measurable
      (fun i : Fin R => coinStep i)
      (fun i => coinStep_measurable i))
      measurableSet_Ici
  have hdom :
      biasedCoins D B ≤ bdPathMeasure N n A :=
    iid_progress_domination N D hD0 hD1 hq n R r
  have hAc :
      Aᶜ =
        {ω | boolCount
          (fun i : Fin R => progressStep i) ω < r} := by
    ext ω
    simp [A]
  have hBc :
      Bᶜ =
        {ω | boolCount
          (fun i : Fin R => coinStep i) ω < r} := by
    ext ω
    simp [B]
  rw [← hAc, ← hBc,
    measure_compl hAmeas
      (measure_ne_top (bdPathMeasure N n) A),
    measure_compl hBmeas
      (measure_ne_top (biasedCoins D) B)]
  simpa only [measure_univ] using
    (tsub_le_tsub_left hdom 1)

private def coinCountReal (R : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ i : Fin R, if coinStep i ω then 1 else 0

private lemma coinCountReal_rep (R : ℕ) (ω : ℕ → Bool) :
    coinCountReal R ω =
      ∑ i : Fin R,
        if coinStep i ω then (1 : ℝ) else 0 := rfl

private lemma coin_indicator_integral
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (i : ℕ) :
    ∫ ω, (if coinStep i ω then (1 : ℝ) else 0)
        ∂biasedCoins D = D := by
  let L : Set (ℕ → Bool) :=
    {ω | coinStep i ω = true}
  have hL : MeasurableSet L :=
    (coinStep_measurable i)
      (measurableSet_singleton true)
  have hfun :
      (fun ω : ℕ → Bool =>
          if coinStep i ω then (1 : ℝ) else 0) =
        L.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : coinStep i ω = true
    · simp [L, h]
    · have hf := Bool.eq_false_of_not_eq_true h
      simp [L, h, hf]
  rw [hfun]
  calc
    ∫ ω, L.indicator (fun _ => (1 : ℝ)) ω
        ∂biasedCoins D =
        (biasedCoins D).real L := by
          change (∫ ω, L.indicator
            (1 : (ℕ → Bool) → ℝ) ω ∂biasedCoins D) =
              (biasedCoins D).real L
          exact integral_indicator_one
            (μ := biasedCoins D) hL
    _ = D := by
      rw [measureReal_def,
        biasedCoins_coin_true D hD0.le hD1 i]
      exact ENNReal.toReal_ofReal hD0.le

private lemma coinCountReal_integral
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (R : ℕ) :
    ∫ ω, coinCountReal R ω ∂biasedCoins D =
      D * R := by
  letI : IsProbabilityMeasure (biasedCoins D) :=
    biasedCoins_isProbability D hD0.le hD1
  unfold coinCountReal
  rw [integral_finset_sum]
  · simp_rw [coin_indicator_integral D hD0 hD1]
    simp [mul_comm]
  · intro i _hi
    have hmeas :
        Measurable (fun ω : ℕ → Bool =>
          if coinStep i ω then (1 : ℝ) else 0) :=
      (measurable_of_finite
        (fun b : Bool => if b then (1 : ℝ) else 0)).comp
          (coinStep_measurable i)
    exact Integrable.of_mem_Icc 0 1 hmeas.aemeasurable
      (ae_of_all _ (by
        intro ω
        cases coinStep i ω <;> simp))

private lemma biasedCoins_lower_tail
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (R : ℕ) :
    biasedCoins D
        {ω | boolCount
          (fun i : Fin R => coinStep i) ω <
            Nat.ceil (D * R / 2)} ≤
      ENNReal.ofReal
        (Real.exp (-(D * R) / 8)) := by
  letI : IsProbabilityMeasure (biasedCoins D) :=
    biasedCoins_isProbability D hD0.le hD1
  have hchernoff :=
    lemma_chernoff_lower
      (biasedCoins D) R
      (fun i : Fin R => coinStep i)
      (coinCountReal R)
      (coinCountReal_rep R)
      (fun i => coinStep_measurable i)
      ((coinStep_indep D hD0.le hD1).precomp
        Fin.val_injective)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
  rw [coinCountReal_integral D hD0 hD1 R] at hchernoff
  calc
    biasedCoins D
        {ω | boolCount
          (fun i : Fin R => coinStep i) ω <
            Nat.ceil (D * R / 2)}
        ≤ biasedCoins D
            {ω | coinCountReal R ω ≤
              (1 - (1 / 2 : ℝ)) * (D * R)} := by
          apply measure_mono
          intro ω hω
          have hlt :
              (boolCount
                (fun i : Fin R => coinStep i) ω : ℝ) <
                D * R / 2 :=
            Nat.lt_ceil.mp hω
          change coinCountReal R ω ≤
            (1 - (1 / 2 : ℝ)) * (D * R)
          have heq :
              coinCountReal R ω =
                (boolCount
                  (fun i : Fin R => coinStep i) ω : ℕ) := by
            simp [coinCountReal, boolCount]
          rw [heq]
          linarith
    _ ≤ ENNReal.ofReal
          (Real.exp
            (-(D * R) * (1 / 2 : ℝ) ^ (2 : ℕ) / 2)) :=
      hchernoff
    _ = ENNReal.ofReal
          (Real.exp (-(D * R) / 8)) := by
      congr 2
      ring

private def downCount (R : ℕ) (ω : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range R,
    if ω (i + 1) + 1 = ω i then 1 else 0

private lemma downCount_succ (R : ℕ) (ω : ℕ → ℕ) :
    downCount (R + 1) ω =
      downCount R ω +
        if ω (R + 1) + 1 = ω R then 1 else 0 := by
  unfold downCount
  rw [Finset.sum_range_succ]

private lemma birthsUpTo_succ_ext (R : ℕ) (ω : ℕ → ℕ) :
    birthsUpTo ω (R + 1) =
      birthsUpTo ω R +
        if ω (R + 1) = ω R + 1 then 1 else 0 := by
  unfold birthsUpTo
  rw [Finset.sum_range_succ]

private lemma birth_death_balance
    (n : ℕ) (ω : ℕ → ℕ)
    (h0 : ω 0 = n) (hvalid : validBdPath ω) :
    ∀ R, ω R + downCount R ω =
      n + birthsUpTo ω R := by
  intro R
  induction R with
  | zero =>
      simp [downCount, birthsUpTo, h0]
  | succ R ih =>
      rw [downCount_succ, birthsUpTo_succ_ext]
      rcases hvalid R with hup | hdown | hhold
      · rw [hup]
        rw [if_neg (by omega), if_pos rfl]
        omega
      · rw [hdown]
        by_cases hz : ω R = 0
        · rw [hz]
          simp
          simpa [hz] using ih
        · have hp : 0 < ω R := Nat.pos_of_ne_zero hz
          have hnup : ω R - 1 ≠ ω R + 1 := by omega
          rw [if_neg hnup, if_pos (by omega)]
          omega
      · rw [hhold]
        rw [if_neg (by omega), if_neg (by omega)]
        exact ih

private lemma progress_eq_down_of_alive
    (R : ℕ) (ω : ℕ → ℕ)
    (halive : ∀ i, i < R → ω i ≠ 0) :
    boolCount (fun i : Fin R => progressStep i) ω =
      downCount R ω := by
  unfold boolCount downCount
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i < R := by
    simpa using hi
  have hnz := halive i hir
  simp [progressStep, hnz]

private lemma birthsUpTo_mono
    (ω : ℕ → ℕ) {R T : ℕ} (hRT : R ≤ T) :
    birthsUpTo ω R ≤ birthsUpTo ω T := by
  unfold birthsUpTo
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono hRT

private lemma extinction_event_subset
    (n R B : ℕ) :
    {ω : ℕ → ℕ | extinctionTime ω ≥ R} ⊆
      ({ω | extinctionTime ω = ⊤} ∪
      ({ω | B + 1 ≤ birthsBeforeExtinction ω} ∪
      ({ω | boolCount
        (fun i : Fin R => progressStep i) ω <
          n + B + 1} ∪
      ({ω | ω 0 ≠ n} ∪
      {ω | ¬validBdPath ω})))) := by
  intro ω hsurv
  by_cases htop : extinctionTime ω = ⊤
  · exact Or.inl htop
  by_cases hbirth : B + 1 ≤ birthsBeforeExtinction ω
  · exact Or.inr (Or.inl hbirth)
  by_cases h0 : ω 0 = n
  · by_cases hvalid : validBdPath ω
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      lift extinctionTime ω to ℕ using htop with T hT
      have hRT : R ≤ T := by
        change (R : WithTop ℕ) ≤ extinctionTime ω at hsurv
        rw [← hT] at hsurv
        exact WithTop.coe_le_coe.mp hsurv
      have halive : ∀ i, i < R → ω i ≠ 0 := by
        intro i hi
        apply ext_time_gt_imp_nonzero
        rw [← hT]
        exact WithTop.coe_lt_coe.mpr
          (lt_of_lt_of_le hi hRT)
      have hprog :
          boolCount
              (fun i : Fin R => progressStep i) ω =
            downCount R ω :=
        progress_eq_down_of_alive R ω halive
      have hbirthR :
          birthsUpTo ω R ≤ B := by
        have hmono :
            birthsUpTo ω R ≤
              birthsBeforeExtinction ω := by
          rw [birthsBeforeExtinction, ← hT]
          exact birthsUpTo_mono ω hRT
        omega
      have hbalance :=
        birth_death_balance n ω h0 hvalid R
      change boolCount
        (fun i : Fin R => progressStep i) ω <
          n + B + 1
      rw [hprog]
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr hvalid)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h0)))

private lemma extinction_tail_le_birth_add_progress
    (N : BirthDeathChain) [IsMarkovKernel (bdKernel N)]
    (D : ℝ) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hq : ∀ x, 0 < x → D ≤ N.q x)
    (hExt : ∀ n, bdPathMeasure N n
      {ω | extinctionTime ω = ⊤} = 0)
    (n R B : ℕ)
    (hscale : (n + B + 1 : ℕ) ≤ D * R / 2) :
    extinctionTail N n R ≤
      birthTail N n (B + 1) +
        ENNReal.ofReal (Real.exp (-(D * R) / 8)) := by
  have hsubset :=
    extinction_event_subset n R B
  have hprog :
      bdPathMeasure N n
          {ω | boolCount
            (fun i : Fin R => progressStep i) ω <
              n + B + 1} ≤
        ENNReal.ofReal (Real.exp (-(D * R) / 8)) := by
    calc
      bdPathMeasure N n
          {ω | boolCount
            (fun i : Fin R => progressStep i) ω <
              n + B + 1}
          ≤ bdPathMeasure N n
              {ω | boolCount
                (fun i : Fin R => progressStep i) ω <
                  Nat.ceil (D * R / 2)} := by
            apply measure_mono
            intro ω hω
            exact lt_of_lt_of_le hω
              (by
                have hceil :
                    (n + B + 1 : ℝ) ≤
                      (Nat.ceil (D * R / 2) : ℝ) :=
                  by
                    simpa only [Nat.cast_add, Nat.cast_one] using
                      hscale.trans
                        (Nat.le_ceil (D * R / 2))
                exact_mod_cast hceil)
      _ ≤ biasedCoins D
            {ω | boolCount
              (fun i : Fin R => coinStep i) ω <
                Nat.ceil (D * R / 2)} :=
          progress_lower_tail_le N D hD0 hD1 hq
            n R (Nat.ceil (D * R / 2))
      _ ≤ ENNReal.ofReal
            (Real.exp (-(D * R) / 8)) :=
          biasedCoins_lower_tail D hD0 hD1 R
  unfold extinctionTail birthTail
  calc
    bdPathMeasure N n
        {ω | extinctionTime ω ≥ ↑R}
        ≤ bdPathMeasure N n
            ({ω | extinctionTime ω = ⊤} ∪
            ({ω | B + 1 ≤ birthsBeforeExtinction ω} ∪
            ({ω | boolCount
              (fun i : Fin R => progressStep i) ω <
                n + B + 1} ∪
            ({ω | ω 0 ≠ n} ∪
            {ω | ¬validBdPath ω})))) :=
          measure_mono hsubset
    _ ≤ bdPathMeasure N n
            {ω | extinctionTime ω = ⊤} +
          bdPathMeasure N n
            {ω | B + 1 ≤ birthsBeforeExtinction ω} +
          bdPathMeasure N n
            {ω | boolCount
              (fun i : Fin R => progressStep i) ω <
                n + B + 1} +
          bdPathMeasure N n {ω | ω 0 ≠ n} +
          bdPathMeasure N n {ω | ¬validBdPath ω} := by
        calc
          _ ≤ bdPathMeasure N n
                {ω | extinctionTime ω = ⊤} +
              bdPathMeasure N n
                ({ω | B + 1 ≤ birthsBeforeExtinction ω} ∪
                ({ω | boolCount
                  (fun i : Fin R => progressStep i) ω <
                    n + B + 1} ∪
                ({ω | ω 0 ≠ n} ∪
                {ω | ¬validBdPath ω}))) :=
              measure_union_le _ _
          _ ≤ bdPathMeasure N n
                {ω | extinctionTime ω = ⊤} +
              (bdPathMeasure N n
                {ω | B + 1 ≤ birthsBeforeExtinction ω} +
              bdPathMeasure N n
                ({ω | boolCount
                  (fun i : Fin R => progressStep i) ω <
                    n + B + 1} ∪
                ({ω | ω 0 ≠ n} ∪
                {ω | ¬validBdPath ω}))) := by
              exact add_le_add (le_refl _)
                (measure_union_le _ _)
          _ ≤ bdPathMeasure N n
                {ω | extinctionTime ω = ⊤} +
              (bdPathMeasure N n
                {ω | B + 1 ≤ birthsBeforeExtinction ω} +
              (bdPathMeasure N n
                {ω | boolCount
                  (fun i : Fin R => progressStep i) ω <
                    n + B + 1} +
              bdPathMeasure N n
                ({ω | ω 0 ≠ n} ∪
                {ω | ¬validBdPath ω}))) := by
              gcongr
              exact measure_union_le _ _
          _ ≤ bdPathMeasure N n
                {ω | extinctionTime ω = ⊤} +
              (bdPathMeasure N n
                {ω | B + 1 ≤ birthsBeforeExtinction ω} +
              (bdPathMeasure N n
                {ω | boolCount
                  (fun i : Fin R => progressStep i) ω <
                    n + B + 1} +
              (bdPathMeasure N n {ω | ω 0 ≠ n} +
              bdPathMeasure N n
                {ω | ¬validBdPath ω}))) := by
              gcongr
              exact measure_union_le _ _
          _ = _ := by
              ac_rfl
    _ = bdPathMeasure N n
            {ω | B + 1 ≤ birthsBeforeExtinction ω} +
          bdPathMeasure N n
            {ω | boolCount
              (fun i : Fin R => progressStep i) ω <
                n + B + 1} := by
        rw [hExt n, bdPathMeasure_initial_ne N n,
          bdPathMeasure_invalid_path N n]
        simp
    _ ≤ bdPathMeasure N n
            {ω | B + 1 ≤ birthsBeforeExtinction ω} +
          ENNReal.ofReal
            (Real.exp (-(D * R) / 8)) :=
      add_le_add (le_refl _) hprog

private lemma log_sq_isLittleO_id :
    (fun x : ℝ => (Real.log x) ^ 2) =o[Filter.atTop]
      (fun x : ℝ => x) := by
  have hlog :=
    isLittleO_log_rpow_atTop
      (r := (1 / 2 : ℝ)) (by norm_num)
  have hmul := hlog.mul hlog
  refine hmul.congr'
    (Filter.Eventually.of_forall (by
      intro x
      simp only [pow_two]))
    ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  calc
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) =
        x ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
          rw [Real.rpow_add hx]
    _ = x := by norm_num

set_option maxHeartbeats 800000 in
private lemma mul_logSqScaleNat_le_self
    (C : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      C * logSqScaleNat n ≤ n := by
  rcases C.eq_zero_or_pos with rfl | hC
  · exact ⟨0, by simp⟩
  have htend :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1
      tendsto_natCast_atTop_atTop
  have hnat :
      (fun n : ℕ =>
          (Real.log ((n : ℝ) + 1)) ^ 2) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ) + 1) :=
    log_sq_isLittleO_id.comp_tendsto htend
  let c : ℝ := 1 / (4 * C)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hev :=
    (hnat.forall_isBigOWith hc).bound
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n₁, hn₁⟩ := hev
  refine ⟨max n₁ (max (2 * C) 1), ?_⟩
  intro n hn
  have hn1 : n₁ ≤ n := le_trans
    (le_max_left _ _) hn
  have hnC : 2 * C ≤ n := le_trans
    (le_max_of_le_right (le_max_left _ _)) hn
  have hnpos : 1 ≤ n := le_trans
    (le_max_of_le_right (le_max_right _ _)) hn
  have hraw := hn₁ n hn1
  have hlognonneg :
      0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hsqnonneg :
      0 ≤ (Real.log ((n : ℝ) + 1)) ^ 2 :=
    sq_nonneg _
  have hnreal : 0 ≤ (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hsqnonneg,
    Real.norm_eq_abs, abs_of_nonneg hnreal] at hraw
  have hsq :
      (Real.log ((n : ℝ) + 1)) ^ 2 ≤
        (n : ℝ) / (2 * C) := by
    dsimp [c] at hraw
    have hnplus : (n : ℝ) + 1 ≤ 2 * n := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    have hden : (0 : ℝ) < 4 * C := by positivity
    calc
      _ ≤ 1 / (4 * C) * ((n : ℝ) + 1) := hraw
      _ ≤ 1 / (4 * C) * (2 * n) :=
        mul_le_mul_of_nonneg_left hnplus (by positivity)
      _ = (n : ℝ) / (2 * C) := by
        field_simp
        <;> ring
  have hM :
      (logSqScaleNat n : ℝ) ≤
        (Real.log ((n : ℝ) + 1)) ^ 2 + 1 := by
    unfold logSqScaleNat logSqScale logScale
    have hnonneg :
        0 ≤ Int.ceil
          ((Real.log ((n : ℝ) + 1)) ^ 2) :=
      Int.ceil_nonneg (sq_nonneg _)
    rw [show
        (Int.toNat
          (Int.ceil
            ((Real.log ((n : ℝ) + 1)) ^ 2)) : ℝ) =
          (Int.ceil
            ((Real.log ((n : ℝ) + 1)) ^ 2) : ℝ) by
      exact_mod_cast
        (Int.toNat_of_nonneg hnonneg)]
    exact
      (Int.ceil_lt_add_one
        ((Real.log ((n : ℝ) + 1)) ^ 2)).le
  have hCreal :
      (C : ℝ) *
          (logSqScaleNat n : ℝ) ≤ n := by
    have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
    have hnC' : (2 * C : ℝ) ≤ n := by exact_mod_cast hnC
    have hmain :
        (C : ℝ) *
            ((Real.log ((n : ℝ) + 1)) ^ 2) ≤
          (n : ℝ) / 2 := by
      calc
        _ ≤ (C : ℝ) * ((n : ℝ) / (2 * C)) :=
          mul_le_mul_of_nonneg_left hsq hCpos.le
        _ = (n : ℝ) / 2 := by
          field_simp
    calc
      _ ≤ (C : ℝ) *
          ((Real.log ((n : ℝ) + 1)) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hM hCpos.le
      _ = (C : ℝ) *
          (Real.log ((n : ℝ) + 1)) ^ 2 + C := by ring
      _ ≤ (n : ℝ) / 2 + C :=
        add_le_add hmain (le_refl (C : ℝ))
      _ ≤ n := by linarith
  exact_mod_cast hCreal

private lemma twice_poly_inv_succ_le
    (n k : ℕ) (hn : 1 ≤ n) :
    ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ ≤
      ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ := by
  let a : ℝ≥0∞ := n + 1
  have ha0 : a ≠ 0 := by
    simp [a]
  have hatop : a ≠ ⊤ := by
    simp [a]
  have htwo : (2 : ℝ≥0∞) ≤ a := by
    dsimp [a]
    exact_mod_cast (show 2 ≤ n + 1 by omega)
  have haeq : a = (↑(n + 1) : ℝ≥0∞) := by
    simp [a]
  rw [← haeq]
  calc
    (a ^ (k + 1))⁻¹ + (a ^ (k + 1))⁻¹ =
        2 * (a ^ (k + 1))⁻¹ := by ring
    _ ≤ a * (a ^ (k + 1))⁻¹ :=
      mul_le_mul_right' htwo _
    _ = a * a⁻¹ ^ (k + 1) := by
      rw [ENNReal.inv_pow]
    _ = a * (a⁻¹ ^ k * a⁻¹) := by
      rw [pow_succ]
    _ = a⁻¹ ^ k * (a * a⁻¹) := by
      ac_rfl
    _ = a⁻¹ ^ k := by
      rw [ENNReal.mul_inv_cancel ha0 hatop, mul_one]
    _ = (a ^ k)⁻¹ := by
      rw [ENNReal.inv_pow]

/-- Uniform form of the corrected extinction proof: the same linear time
threshold works for every initial state `x ≤ n`. -/
theorem nice_whp_extinction_linear_uniform_unconditional
    (N : NiceChain)
    [IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    ∀ k : ℕ, ∃ C n₀ : ℕ, 0 < C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ x : ℕ, x ≤ n →
        extinctionTail N.toBirthDeathChain x (C * n) ≤
          ((n + 1 : ℝ≥0∞) ^ k)⁻¹ := by
  let bd := N.toBirthDeathChain
  have hD1 : N.D ≤ 1 := by
    have hq := N.q_ge 1 Nat.one_pos
    have hpq := bd.pq_le_one 1
    have hp0 := bd.p_nonneg 1
    dsimp [bd] at hpq hp0
    linarith
  obtain ⟨nDrift, hDrift⟩ := nice_drift_neg N
  have hExt :
      ∀ x, bdPathMeasure bd x
        {ω | extinctionTime ω = ⊤} = 0 := by
    intro x
    have hDrift' :
        ∀ m, nDrift ≤ m → 0 < m →
          bd.p m - bd.q m ≤ -(N.D / 2) := by
      intro m hm hmp
      have h := hDrift m hm hmp
      linarith
    exact bd_extinction_almost_sure bd
      (N.D / 2) (half_pos N.D_pos) nDrift
      hDrift' N.D N.D_pos N.q_ge x
  have hBirth :=
    nice_whp_births_logsq_uniform_unconditional N
  intro k
  obtain ⟨Cb, nb, hCb, hbirth⟩ :=
    hBirth (k + 1)
  obtain ⟨nlin, hlin⟩ :=
    mul_logSqScaleNat_le_self Cb
  let Θ : ℕ := Nat.ceil (6 / N.D)
  have hΘpos : 0 < Θ := by
    dsimp [Θ]
    rw [Nat.ceil_pos]
    exact div_pos (by norm_num) N.D_pos
  have hΘreal :
      6 / N.D ≤ (Θ : ℝ) := by
    dsimp [Θ]
    exact Nat.le_ceil _
  have hDΘ : (6 : ℝ) ≤ N.D * Θ := by
    have := (div_le_iff₀ N.D_pos).mp hΘreal
    nlinarith
  let r : ℝ :=
    Real.exp (-(N.D * Θ) / 8)
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    have hΘrealpos : (0 : ℝ) < Θ := by
      exact_mod_cast hΘpos
    have hprod : 0 < N.D * (Θ : ℝ) :=
      mul_pos N.D_pos hΘrealpos
    linarith
  obtain ⟨nexp, hexp⟩ :=
    exp_decay_le_poly_inv r hr0 hr1 (k + 1)
  refine ⟨Θ, max nb (max nlin (max nexp 1)),
    hΘpos, ?_⟩
  intro n hn
  intro x hx
  have hnb : nb ≤ n := le_trans
    (le_max_left _ _) hn
  have hnlin : nlin ≤ n := le_trans
    (le_max_of_le_right (le_max_left _ _)) hn
  have hnexp : nexp ≤ n := le_trans
    (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))) hn
  have hn1 : 1 ≤ n := le_trans
    (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))) hn
  let B := Cb * logSqScaleNat n
  have hBn : B ≤ n :=
    hlin n hnlin
  have hscale :
      (n + B + 1 : ℕ) ≤
        N.D * (Θ * n) / 2 := by
    have hleft :
        (n + B + 1 : ℕ) ≤ 3 * n := by
      omega
    have hfactor :
        (3 : ℝ) ≤ N.D * Θ / 2 := by
      nlinarith
    exact_mod_cast
      (calc
        (n + B + 1 : ℝ) ≤ 3 * n := by
          exact_mod_cast hleft
        _ ≤ N.D * (Θ * n) / 2 := by
          have hn0 : (0 : ℝ) ≤ n := by positivity
          nlinarith)
  have hscale_x :
      (x + B + 1 : ℕ) ≤
        N.D * (Θ * n) / 2 := by
    have hxnNat : x + B + 1 ≤ n + B + 1 := by
      calc
        x + B + 1 = x + (B + 1) := by omega
        _ ≤ n + (B + 1) := Nat.add_le_add_right hx _
        _ = n + B + 1 := by omega
    have hxnReal : ((x + B + 1 : ℕ) : ℝ) ≤
        ((n + B + 1 : ℕ) : ℝ) := by
      exact_mod_cast hxnNat
    exact hxnReal.trans hscale
  have hcore :=
    extinction_tail_le_birth_add_progress
      bd N.D N.D_pos hD1 N.q_ge hExt
      x (Θ * n) B (by
        simpa only [Nat.cast_mul] using hscale_x)
  have hb :
      birthTail bd x (B + 1) ≤
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ := by
    calc
      birthTail bd x (B + 1) ≤
          birthTail bd x B := by
        unfold birthTail
        apply measure_mono
        intro ω hω
        exact (by omega : B ≤ B + 1).trans hω
      _ ≤ ((↑(n + 1) : ℝ≥0∞) ^
          (k + 1))⁻¹ := by
        simpa only [bd, B, Nat.cast_add,
          Nat.cast_one] using hbirth n hnb x hx
  have hexpeq :
      Real.exp
          (-(N.D * (↑(Θ * n) : ℝ)) / 8) =
        r ^ n := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he :
      ENNReal.ofReal
          (Real.exp
            (-(N.D * (↑(Θ * n) : ℝ)) / 8)) ≤
        ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ := by
    rw [hexpeq]
    exact hexp n hnexp
  calc
    extinctionTail bd x (Θ * n) ≤
        birthTail bd x (B + 1) +
          ENNReal.ofReal
            (Real.exp
              (-(N.D * (↑(Θ * n) : ℝ)) / 8)) :=
      hcore
    _ ≤ ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ +
          ((↑(n + 1) : ℝ≥0∞) ^ (k + 1))⁻¹ :=
      add_le_add hb he
    _ ≤ ((↑(n + 1) : ℝ≥0∞) ^ k)⁻¹ :=
      twice_poly_inv_succ_le n k hn1
    _ = ((↑n + 1 : ℝ≥0∞) ^ k)⁻¹ := by
      push_cast
      ring_nf

/-- Corrected proof of paper `lemma:nice-whp-extinction`, using the paper's
birth bound and an adapted-Bernoulli progress coupling. -/
theorem nice_whp_extinction_linear_unconditional
    (N : NiceChain)
    [IsMarkovKernel (bdKernel N.toBirthDeathChain)] :
    WhpTailBound
      (fun n t =>
        extinctionTail N.toBirthDeathChain n t)
      (fun n => n) := by
  intro k
  obtain ⟨C, n₀, hC, h⟩ :=
    nice_whp_extinction_linear_uniform_unconditional N k
  exact ⟨C, n₀, hC, fun n hn => h n hn n le_rfl⟩

end LVConsensus
