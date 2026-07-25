import LVConsensus.Definitions
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
/-!
# Markov Property Bound

Full proof of the Markov property bound for homogeneous path measures.
This file is separate from Definitions.lean (which cannot import MarkovLib)
so that SwapInvariance.lean can use the proved version without creating
a circular import cycle.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal BigOperators

namespace LVConsensus

-- -----------------------------------------------------------------------
-- Private helpers for the Markov shift proof
-- -----------------------------------------------------------------------

instance homogeneousHistoryKernel_isMarkov
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (homogeneousHistoryKernel K n) := by
  unfold homogeneousHistoryKernel; infer_instance

private def lastElem' (n : ℕ) (α : Type*) :
    (∀ i : Finset.Iic n, α) → α :=
  fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

private lemma lastElem'_frestrictLe {α : Type*}
    (n : ℕ) (ω : ℕ → α) :
    lastElem' n α (frestrictLe n ω) = ω n := by
  simp [lastElem', frestrictLe_apply]

private lemma histKernel_eq_K_lastElem'
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K] (n : ℕ)
    (h : ∀ i : Finset.Iic n, α) :
    homogeneousHistoryKernel K n h =
      K (lastElem' n α h) := by
  unfold homogeneousHistoryKernel lastElem'
  rw [Kernel.comp_apply,
      Kernel.deterministic_apply (by fun_prop)]
  exact Measure.dirac_bind (Kernel.measurable K) _

/-- Project path coordinates from Iic (k+n) to Iic n by shifting. -/
private def projKn' {α : Type*} (k n : ℕ) (h : ∀ i : Finset.Iic (k + n), α) :
    ∀ i : Finset.Iic n, α :=
  fun i => h ⟨k + i.val, Finset.mem_Iic.mpr (by have := Finset.mem_Iic.mp i.2; omega)⟩

private lemma measurable_projKn' {α : Type*} [MeasurableSpace α] (k n : ℕ) :
    Measurable (projKn' (α := α) k n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Reindex the singleton interval Ioc(k+n)(k+n+1) → Ioc n (n+1). -/
private def singletonReindex' {α : Type*} (k n : ℕ)
    (y : ∀ i : Finset.Ioc (k + n) (k + n + 1), α) : ∀ i : Finset.Ioc n (n + 1), α :=
  fun _ => y ⟨k + n + 1, Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩⟩

private lemma measurable_singletonReindex' {α : Type*} [MeasurableSpace α] (k n : ℕ) :
    Measurable (singletonReindex' (α := α) k n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

private lemma projKn_comp_IicProdIoc' {α : Type*} (k n : ℕ) :
    (projKn' (α := α) k (n + 1)) ∘
      (show (∀ i : Finset.Iic (k + n), α) × (∀ i : Finset.Ioc (k + n) (k + n + 1), α) →
        ∀ i : Finset.Iic (k + (n + 1)), α from
        (IicProdIoc (X := fun _ => α) (k + n) (k + n + 1) ·)) =
    (IicProdIoc (X := fun _ => α) n (n + 1)) ∘ Prod.map (projKn' k n) (singletonReindex' k n) := by
  funext ⟨x, y⟩ ⟨i, hi⟩
  simp only [Function.comp, Prod.map, projKn', singletonReindex', IicProdIoc,
    Finset.mem_Ioc, Finset.mem_Iic]
  by_cases h1 : k + i ≤ k + n
  · have h2 : i ≤ n := by omega
    simp [h1, h2]
  · have h2 : ¬ (i ≤ n) := by omega
    have h3 : i = n + 1 := by have := Finset.mem_Iic.mp hi; omega
    subst h3
    simp only [dif_neg (show ¬ k + (n + 1) ≤ k + n by omega),
               dif_neg (show ¬ n + 1 ≤ n by omega), singletonReindex']
    exact congrArg y (Subtype.ext rfl)

private lemma singletonReindex_comp_piSingleton' {α : Type*} [MeasurableSpace α] (k n : ℕ) :
    (singletonReindex' (α := α) k n) ∘
      (MeasurableEquiv.piSingleton (X := fun _ => α) (k + n) : α → _) =
    (MeasurableEquiv.piSingleton (X := fun _ => α) n : α → _) := by
  funext a _
  simp [Function.comp, singletonReindex', MeasurableEquiv.piSingleton]

private lemma hHK_projKn_eq' {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (k n : ℕ) (h : ∀ i : Finset.Iic (k + n), α) :
    homogeneousHistoryKernel K (k + n) h =
    homogeneousHistoryKernel K n (projKn' k n h) := by
  rw [histKernel_eq_K_lastElem', histKernel_eq_K_lastElem']
  simp [lastElem', projKn']

/-- Key shift lemma: the partial trajectory from k shifted by k equals the fresh partial
    trajectory from 0. Proved by induction on n. -/
private lemma partialTraj_shift_eq''
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (k : ℕ) (p : ∀ i : Finset.Iic k, α) (n : ℕ) :
    let X : ℕ → Type _ := fun _ => α
    let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
      fun t => homogeneousHistoryKernel K t
    let q₀ : ∀ _ : Finset.Iic 0, X 0 := fun _ => p ⟨k, Finset.mem_Iic.mpr le_rfl⟩
    (partialTraj (X := X) κ k (k + n) p).map (projKn' k n) =
    partialTraj (X := X) κ 0 n q₀ := by
  intro X κ q₀
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]; infer_instance
  induction n with
  | zero =>
    simp only [Nat.add_zero]
    rw [partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_projKn' k 0),
        partialTraj_self, Kernel.id_apply]
    congr 1
    funext ⟨i, hi⟩
    simp [projKn', Nat.le_zero.mp (Finset.mem_Iic.mp hi), q₀]
  | succ n ih =>
    show (partialTraj (X := X) κ k (k + n + 1) p).map (projKn' k (n + 1)) =
        partialTraj (X := X) κ 0 (n + 1) q₀
    rw [partialTraj_succ_of_le (Nat.le_add_right k n)]
    rw [Kernel.map_apply _ measurable_IicProdIoc, Kernel.comp_apply]
    have hProdMeas : Measurable
        (Prod.map (projKn' (α := α) k n) (singletonReindex' (α := α) k n)) :=
      Measurable.prodMap (measurable_projKn' k n) (measurable_singletonReindex' k n)
    have hIicMeas : Measurable
        (IicProdIoc (X := fun _ => α) n (n + 1)) :=
      measurable_IicProdIoc
    rw [Measure.map_map (measurable_projKn' k (n + 1)) measurable_IicProdIoc,
        projKn_comp_IicProdIoc' k n,
        ← Measure.map_map hIicMeas hProdMeas]
    rw [← Measure.compProd_eq_comp_prod]
    suffices hcompProd :
        ((partialTraj (X := X) κ k (k + n) p) ⊗ₘ
          (κ (k + n)).map (MeasurableEquiv.piSingleton (X := fun _ => α) (k + n))).map
          (Prod.map (projKn' k n) (singletonReindex' k n)) =
        (partialTraj (X := X) κ 0 n q₀) ⊗ₘ
          (κ n).map (MeasurableEquiv.piSingleton (X := fun _ => α) n) by
      rw [hcompProd, Measure.compProd_eq_comp_prod,
          ← Kernel.comp_apply,
          ← Kernel.map_apply _ hIicMeas]
      exact congrArg
        (fun L : Kernel (∀ i : Finset.Iic 0, X i)
            (∀ i : Finset.Iic (n + 1), X i) => L q₀)
        (partialTraj_succ_of_le (X := X) (κ := κ) (Nat.zero_le n)).symm
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (Measurable.prodMap (measurable_projKn' k n) (measurable_singletonReindex' k n)) hs,
        Measure.compProd_apply (hs.preimage (Measurable.prodMap (measurable_projKn' k n) (measurable_singletonReindex' k n))),
        Measure.compProd_apply hs, ← ih,
        MeasureTheory.lintegral_map (Kernel.measurable_kernel_prodMk_left hs)
          (measurable_projKn' k n)]
    congr 1; ext h
    rw [show Prod.mk h ⁻¹' (Prod.map (projKn' k n) (singletonReindex' k n) ⁻¹' s) =
              (fun b => (projKn' k n h, singletonReindex' k n b)) ⁻¹' s from rfl,
        Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ => α) (k + n)).measurable _
          (hs.preimage (Measurable.prodMk measurable_const (measurable_singletonReindex' k n))),
        Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ => α) n).measurable _
          (hs.preimage measurable_prodMk_left),
        hHK_projKn_eq' K k n h]
    congr 1; ext a
    simp only [Set.mem_preimage]
    constructor <;> intro ha <;>
      rwa [← Function.comp_apply (f := singletonReindex' k n)
                (g := ⇑(MeasurableEquiv.piSingleton (X := fun _ => α) (k + n))),
           congrFun (singletonReindex_comp_piSingleton' k n) a] at *

/-- Markov property for homogeneous chains: shifting the trajectory by k steps gives the same
    distribution as a fresh chain started at the state at time k. -/
lemma traj_map_pathShift_eq_homogeneousPathMeasure'
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (k : ℕ) (p : ∀ i : Finset.Iic k, α) :
    let X : ℕ → Type _ := fun _ => α
    let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
      fun t => homogeneousHistoryKernel K t
    (traj (X := X) κ k p).map (pathShift k) =
    homogeneousPathMeasure (Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K := by
  intro X κ
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]; infer_instance
  let q₀ : ∀ _ : Finset.Iic 0, X 0 := fun _ => p ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  have hRHS : (homogeneousPathMeasure (Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K) =
      (traj (X := X) κ 0) ∘ₘ
        ((Measure.dirac (p ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map
          (MeasurableEquiv.piUnique _).symm) := by
    simp only [homogeneousPathMeasure, trajMeasure, X, κ]
  have hshift_meas : Measurable (pathShift (α := α) k) :=
    measurable_pi_lambda _ fun n => measurable_pi_apply _
  have hshift : IsProjectiveLimit ((traj (X := X) κ k p).map (pathShift k))
      (inducedFamily (fun n => partialTraj (X := X) κ 0 n q₀)) := by
    rw [isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj κ q₀)]
    intro n
    rw [inducedFamily_Iic,
        Measure.map_map (measurable_frestrictLe n) hshift_meas,
        show frestrictLe n ∘ pathShift k = projKn' k n ∘ frestrictLe (k + n) from by
          funext ω ⟨i, hi⟩
          simp [frestrictLe_apply, pathShift, projKn'],
        ← Measure.map_map (measurable_projKn' k n) (measurable_frestrictLe (k + n))]
    have htraj : (traj (X := X) κ k p).map (frestrictLe (k + n)) =
        (partialTraj (X := X) κ k (k + n)) p := by
      rw [← Kernel.map_apply _ (measurable_frestrictLe (k + n)),
          traj_map_frestrictLe (X := X)]
    rw [htraj]
    exact partialTraj_shift_eq'' K k p n
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

/-- Markov property bound at fixed time k for homogeneous chains.

    If B is a cylinder event up to time k, C is a measurable event on paths, and
    from every state ω(k) reachable via B the shifted chain satisfies P_{ω(k)}(C) ≤ c,
    then P(B ∩ (pathShift k)⁻¹' C) ≤ c · P(B). -/
lemma homogeneousPathMeasure_markov_bound
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : ProbabilityTheory.Kernel α α) [ProbabilityTheory.IsMarkovKernel K]
    (s₀ : α) (k : ℕ) (c : ℝ≥0∞)
    (B : Set (ℕ → α)) (C : Set (ℕ → α))
    (_hBmeas : MeasurableSet B) (_hCmeas : MeasurableSet C)
    (_hBcyl : isCylinderUpTo k B)
    (_hBound : ∀ ω : ℕ → α, ω ∈ B →
      homogeneousPathMeasure (Measure.dirac (ω k)) K C ≤ c) :
    homogeneousPathMeasure (Measure.dirac s₀) K
      (B ∩ (pathShift k) ⁻¹' C) ≤
    c * homogeneousPathMeasure (Measure.dirac s₀) K B := by
  let X : ℕ → Type _ := fun _ => α
  let κ : (t : ℕ) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]; infer_instance
  let u₀ : ∀ i : Finset.Iic 0, X i := fun _ => s₀
  set P := homogeneousPathMeasure (Measure.dirac s₀) K with hP_def
  haveI hPprob : IsProbabilityMeasure P := by
    simp only [hP_def, P, homogeneousPathMeasure]; infer_instance
  have hPeq : P = traj κ 0 u₀ := by
    have hdef : P = (traj κ 0) ∘ₘ
        (Measure.dirac s₀).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm :=
      rfl
    rw [hdef, Measure.map_dirac' (MeasurableEquiv.measurable _),
        show (traj κ 0) ∘ₘ Measure.dirac
            ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm s₀) =
          (Measure.dirac _).bind (traj κ 0) from rfl,
        Measure.dirac_bind (Kernel.measurable _)]
    congr 1
  set μ := P.map (frestrictLe k) with hμ_def
  haveI hμprob : IsProbabilityMeasure μ := by
    constructor
    simp [hμ_def, Measure.map_apply (measurable_frestrictLe k)]
  have hμ_eq : μ = partialTraj κ 0 k u₀ := by
    rw [hμ_def, hPeq]
    have : (traj κ 0 u₀).map (frestrictLe k) = ((traj κ 0).map (frestrictLe k)) u₀ :=
      (Kernel.map_apply (traj κ 0) (measurable_frestrictLe k) u₀).symm
    rw [this, traj_map_frestrictLe (κ := κ) 0 k]
  have hCP : μ ⊗ₘ (traj κ k) = P.map (fun x => (frestrictLe k x, x)) := by
    rw [hμ_eq, hPeq, partialTraj_compProd_traj (Nat.zero_le k) u₀]
  have hshift_meas : Measurable (pathShift k : (ℕ → α) → ℕ → α) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  have hBC_meas : MeasurableSet (B ∩ (pathShift k) ⁻¹' C) :=
    _hBmeas.inter (_hCmeas.preimage hshift_meas)
  have hPair_meas : Measurable (fun x : ℕ → α => (frestrictLe k x, x)) :=
    Measurable.prod (measurable_frestrictLe k) measurable_id
  have hFmeas : Measurable (fun p : (∀ i : Finset.Iic k, α) × (ℕ → α) =>
      B.indicator (fun _ => (1:ℝ≥0∞)) p.2 *
      (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) p.2) := by
    apply Measurable.mul
    · exact (Measurable.indicator measurable_const _hBmeas).comp measurable_snd
    · exact (Measurable.indicator measurable_const
        (_hCmeas.preimage hshift_meas)).comp measurable_snd
  have hLHS : ∫⁻ ω, (B ∩ pathShift k ⁻¹' C).indicator (1 : (ℕ → α) → ℝ≥0∞) ω ∂P =
      ∫⁻ p, ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y *
        (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y ∂traj κ k p ∂μ := by
    have hind : ∀ ω : ℕ → α, (B ∩ pathShift k ⁻¹' C).indicator (1 : (ℕ → α) → ℝ≥0∞) ω =
        B.indicator (fun _ => (1:ℝ≥0∞)) ω *
        (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) ω := by
      intro ω
      simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage]
      by_cases hB : ω ∈ B <;> by_cases hC : pathShift k ω ∈ C <;> simp [hB, hC]
    simp_rw [hind]
    rw [show ∫⁻ ω, B.indicator (fun _ => (1:ℝ≥0∞)) ω *
        (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) ω ∂P =
        ∫⁻ x, B.indicator (fun _ => (1:ℝ≥0∞)) x.2 *
        (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) x.2
        ∂(P.map (fun x => (frestrictLe k x, x))) from
      (lintegral_map hFmeas hPair_meas).symm,
      ← hCP, Measure.lintegral_compProd hFmeas]
  rw [← lintegral_indicator_one hBC_meas, hLHS]
  have hGmeas : Measurable (fun p : ∀ i : Finset.Iic k, α =>
      ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y *
        (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y ∂traj (X := X) κ k p) :=
    Measurable.lintegral_kernel_prod_right' hFmeas
  rw [hμ_def, MeasureTheory.lintegral_map hGmeas (measurable_frestrictLe k)]
  have hbound_inner : ∀ ω : ℕ → α,
      ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y *
        (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y ∂traj κ k (frestrictLe k ω) ≤
      c * B.indicator (fun _ => (1:ℝ≥0∞)) ω := by
    intro ω
    have htraj_frest : (traj (X := X) κ k (frestrictLe k ω)).map (frestrictLe k) =
        Measure.dirac (frestrictLe k ω) := by
      rw [← Kernel.map_apply (traj (X := X) κ k) (measurable_frestrictLe k),
          traj_map_frestrictLe (X := X), partialTraj_self, Kernel.id_apply]
    have hae : ∀ᵐ y ∂(traj (X := X) κ k (frestrictLe k ω)), frestrictLe k y = frestrictLe k ω := by
      rw [ae_iff]
      have hset : {y | ¬ frestrictLe k y = frestrictLe k ω} =
          frestrictLe k ⁻¹' ({frestrictLe k ω}ᶜ : Set (∀ i : Finset.Iic k, X ↑i)) := by
        ext; simp [frestrictLe_apply]
      haveI : Countable (Finset.Iic k) := inferInstance
      haveI : MeasurableSingletonClass (∀ i : Finset.Iic k, X ↑i) :=
        Pi.instMeasurableSingletonClass
      rw [hset,
          ← Measure.map_apply (measurable_frestrictLe k)
            ((MeasurableSet.singleton (frestrictLe k ω : ∀ i : Finset.Iic k, X ↑i)).compl),
          htraj_frest, dirac_eq_zero_iff_not_mem (MeasurableSet.singleton _).compl]
      simp
    by_cases hωB : ω ∈ B
    · simp only [Set.indicator_of_mem hωB, mul_one]
      have hle : ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y *
          (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y
          ∂traj (X := X) κ k (frestrictLe k ω) ≤
          ∫⁻ y, (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y
          ∂traj (X := X) κ k (frestrictLe k ω) := by
        apply lintegral_mono
        intro y
        simp only [Set.indicator]
        split_ifs <;> simp
      calc ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y *
              (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y
              ∂traj (X := X) κ k (frestrictLe k ω)
          ≤ ∫⁻ y, (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y
              ∂traj (X := X) κ k (frestrictLe k ω) := hle
        _ = (traj (X := X) κ k (frestrictLe k ω)) (pathShift k ⁻¹' C) := by
              rw [show ∫⁻ y, (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y
                    ∂traj (X := X) κ k (frestrictLe k ω) =
                  ∫⁻ y, (pathShift k ⁻¹' C).indicator 1 y
                    ∂traj (X := X) κ k (frestrictLe k ω) from rfl,
                  lintegral_indicator_one (_hCmeas.preimage hshift_meas)]
        _ = ((traj (X := X) κ k (frestrictLe k ω)).map (pathShift k)) C := by
              rw [Measure.map_apply hshift_meas _hCmeas]
        _ = homogeneousPathMeasure
              (Measure.dirac ((frestrictLe k ω) ⟨k, Finset.mem_Iic.mpr le_rfl⟩)) K C := by
              congr 1
              exact traj_map_pathShift_eq_homogeneousPathMeasure' K k (frestrictLe k ω)
        _ = homogeneousPathMeasure (Measure.dirac (ω k)) K C := by
              simp [frestrictLe_apply]
        _ ≤ c := _hBound ω hωB
    · simp only [Set.indicator_of_notMem hωB, mul_zero, le_refl, nonpos_iff_eq_zero]
      apply (lintegral_eq_zero_iff
        (Measurable.mul (Measurable.indicator measurable_const _hBmeas)
          (Measurable.indicator measurable_const (_hCmeas.preimage hshift_meas)))).2
      filter_upwards [hae] with y hy
      simp only [Pi.zero_apply, Set.indicator, Set.mem_inter_iff, Set.mem_preimage]
      by_cases hyB : y ∈ B
      · exfalso
        apply hωB
        apply _hBcyl y ω _ hyB
        intro i hi
        have := congr_fun hy ⟨i, Finset.mem_Iic.mpr hi⟩
        simp [frestrictLe_apply] at this
        exact this
      · simp [hyB]
  calc ∫⁻ ω, ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y *
          (pathShift k ⁻¹' C).indicator (fun _ => (1:ℝ≥0∞)) y
          ∂traj (X := X) κ k (frestrictLe k ω) ∂P
      ≤ ∫⁻ ω, c * B.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P :=
          lintegral_mono hbound_inner
    _ = c * ∫⁻ ω, B.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P := by
          rw [lintegral_const_mul c
            ((Measurable.indicator measurable_const _hBmeas))]
    _ = c * P B := by
          have : ∫⁻ ω, B.indicator (fun _ => (1:ℝ≥0∞)) ω ∂P = P B := by
            rw [show (fun ω => B.indicator (fun _ => (1:ℝ≥0∞)) ω) = B.indicator 1 from by
              ext; rfl, lintegral_indicator_one _hBmeas]
          rw [this]

/-- Countable stopping-time decomposition of the fixed-time Markov bound.

    The sets `B t x` can describe the event that a stopping rule fires at time `t`
    in state `x`.  Decomposing over those countably many possibilities and applying
    `homogeneousPathMeasure_markov_bound` to every cylinder gives the strong-Markov
    inequality needed by restart arguments.  Disjointness and coverage are left to
    each application, so this lemma is also useful for upper bounds by a subfamily. -/
lemma homogeneousPathMeasure_markov_bound_countable
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : ProbabilityTheory.Kernel α α) [ProbabilityTheory.IsMarkovKernel K]
    (s₀ : α)
    (B : ℕ → α → Set (ℕ → α))
    (C : ℕ → α → Set (ℕ → α))
    (c : ℕ → α → ℝ≥0∞)
    (hBmeas : ∀ t x, MeasurableSet (B t x))
    (hCmeas : ∀ t x, MeasurableSet (C t x))
    (hBcyl : ∀ t x, isCylinderUpTo t (B t x))
    (hBound : ∀ t x (ω : ℕ → α), ω ∈ B t x →
      homogeneousPathMeasure (Measure.dirac (ω t)) K (C t x) ≤ c t x) :
    homogeneousPathMeasure (Measure.dirac s₀) K
        (⋃ t, ⋃ x, B t x ∩ (pathShift t) ⁻¹' C t x) ≤
      ∑' t, ∑' x, c t x *
        homogeneousPathMeasure (Measure.dirac s₀) K (B t x) := by
  calc
    homogeneousPathMeasure (Measure.dirac s₀) K
        (⋃ t, ⋃ x, B t x ∩ (pathShift t) ⁻¹' C t x)
        ≤ ∑' t, homogeneousPathMeasure (Measure.dirac s₀) K
            (⋃ x, B t x ∩ (pathShift t) ⁻¹' C t x) :=
          measure_iUnion_le _
    _ ≤ ∑' t, ∑' x, homogeneousPathMeasure (Measure.dirac s₀) K
            (B t x ∩ (pathShift t) ⁻¹' C t x) := by
          apply ENNReal.tsum_le_tsum
          intro t
          exact measure_iUnion_le _
    _ ≤ ∑' t, ∑' x, c t x *
          homogeneousPathMeasure (Measure.dirac s₀) K (B t x) := by
          apply ENNReal.tsum_le_tsum
          intro t
          apply ENNReal.tsum_le_tsum
          intro x
          exact homogeneousPathMeasure_markov_bound K s₀ t (c t x)
            (B t x) (C t x) (hBmeas t x) (hCmeas t x)
            (hBcyl t x) (hBound t x)

/-- A natural number is the sum of the indicators of its strict lower levels. -/
private lemma ennreal_nat_eq_tsum_lt (n : ℕ) :
    (n : ℝ≥0∞) = ∑' j : ℕ, if j < n then 1 else 0 := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · calc
      (n : ℝ≥0∞) = ∑ _j ∈ Finset.range n, (1 : ℝ≥0∞) := by simp
      _ = ∑ j ∈ Finset.range n, if j < n then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos (Finset.mem_range.mp hj)]
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp [hj]

/-- Strong-Markov restart inequality for an integer-valued path functional.

    On a cylinder `B` ending at time `k` in the fixed state `x`, the expected
    value of `F` on the shifted future is at most the fresh expectation from `x`
    times `P(B)`.  The proof applies the fixed-time Markov bound to every tail
    event `{j < F}` and uses the tail-sum formula. -/
lemma homogeneousPathMeasure_markov_lintegral_nat
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : ProbabilityTheory.Kernel α α) [ProbabilityTheory.IsMarkovKernel K]
    (s₀ x : α) (k : ℕ)
    (B : Set (ℕ → α)) (F : (ℕ → α) → ℕ)
    (hBmeas : MeasurableSet B) (hBcyl : isCylinderUpTo k B)
    (hFmeas : Measurable F)
    (hState : ∀ ω : ℕ → α, ω ∈ B → ω k = x) :
    ∫⁻ ω in B, (F (pathShift k ω) : ℝ≥0∞)
        ∂homogeneousPathMeasure (Measure.dirac s₀) K ≤
      (∫⁻ η, (F η : ℝ≥0∞)
          ∂homogeneousPathMeasure (Measure.dirac x) K) *
        homogeneousPathMeasure (Measure.dirac s₀) K B := by
  let P := homogeneousPathMeasure (Measure.dirac s₀) K
  let Px := homogeneousPathMeasure (Measure.dirac x) K
  have hshift : Measurable (pathShift k : (ℕ → α) → ℕ → α) :=
    measurable_pi_lambda _ fun n => measurable_pi_apply _
  let C : ℕ → Set (ℕ → α) := fun j => {η | j < F η}
  have hCmeas : ∀ j, MeasurableSet (C j) := by
    intro j
    exact hFmeas measurableSet_Ioi
  have hrepr : ∀ ω : ℕ → α,
      B.indicator (fun ω => (F (pathShift k ω) : ℝ≥0∞)) ω =
        ∑' j : ℕ, (B ∩ (pathShift k) ⁻¹' C j).indicator
          (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, ennreal_nat_eq_tsum_lt]
      apply tsum_congr
      intro j
      simp [Set.indicator, C, hω]
    · rw [Set.indicator_of_notMem hω]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro j
      rw [Set.indicator_of_notMem]
      exact fun hj => hω hj.1
  have hfresh :
      (∫⁻ η, (F η : ℝ≥0∞) ∂Px) = ∑' j, Px (C j) := by
    calc
      (∫⁻ η, (F η : ℝ≥0∞) ∂Px)
          = ∫⁻ η, ∑' j : ℕ, (C j).indicator (fun _ => (1 : ℝ≥0∞)) η ∂Px := by
              congr 1
              funext η
              simp only [Set.indicator_apply, C, Set.mem_setOf_eq]
              rw [ennreal_nat_eq_tsum_lt]
      _ = ∑' j, ∫⁻ η, (C j).indicator (fun _ => (1 : ℝ≥0∞)) η ∂Px := by
              rw [lintegral_tsum]
              intro j
              exact (measurable_const.indicator (hCmeas j)).aemeasurable
      _ = ∑' j, Px (C j) := by
              apply tsum_congr
              intro j
              exact lintegral_indicator_one (hCmeas j)
  rw [← lintegral_indicator hBmeas]
  simp_rw [hrepr]
  rw [lintegral_tsum]
  · calc
      ∑' j, ∫⁻ ω, (B ∩ (pathShift k) ⁻¹' C j).indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂P
          = ∑' j, P (B ∩ (pathShift k) ⁻¹' C j) := by
              apply tsum_congr
              intro j
              exact lintegral_indicator_one
                (hBmeas.inter ((hCmeas j).preimage hshift))
      _ ≤ ∑' j, Px (C j) * P B := by
              apply ENNReal.tsum_le_tsum
              intro j
              apply homogeneousPathMeasure_markov_bound K s₀ k (Px (C j))
                B (C j) hBmeas (hCmeas j) hBcyl
              intro ω hω
              rw [hState ω hω]
      _ = (∑' j, Px (C j)) * P B := by rw [ENNReal.tsum_mul_right]
      _ = (∫⁻ η, (F η : ℝ≥0∞) ∂Px) * P B := by rw [hfresh]
  · intro j
    exact (measurable_const.indicator
      (hBmeas.inter ((hCmeas j).preimage hshift))).aemeasurable

end LVConsensus
