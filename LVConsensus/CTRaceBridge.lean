import LVConsensus.UniformIntraspecific
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal

namespace LVConsensus

/-- First-step Markov decomposition retaining the next state and shifting
the remaining infinite path. -/
lemma homogeneousPathMeasure_first_shift_lintegral
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s₀ : α)
    (F : α × (Nat → α) → ENNReal) (hF : Measurable F) :
    ∫⁻ ω, F (ω 1, pathShift 1 ω)
        ∂homogeneousPathMeasure (Measure.dirac s₀) K =
      ∫⁻ x, ∫⁻ η, F (x, η)
          ∂homogeneousPathMeasure (Measure.dirac x) K ∂K s₀ := by
  let X : Nat → Type _ := fun _ => α
  let κ : (t : Nat) → Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  haveI : ∀ t, IsMarkovKernel (κ t) := fun t => by
    simp only [κ, X, homogeneousHistoryKernel]
    infer_instance
  let u₀ : ∀ i : Finset.Iic 0, X i := fun _ => s₀
  let P := homogeneousPathMeasure (Measure.dirac s₀) K
  haveI : IsProbabilityMeasure P := by
    simp only [P, homogeneousPathMeasure]
    infer_instance
  have hPeq : P = traj κ 0 u₀ := by
    have hdef : P = (traj κ 0) ∘ₘ
        (Measure.dirac s₀).map
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => α)).symm := rfl
    rw [hdef, Measure.map_dirac' (MeasurableEquiv.measurable _),
        show (traj κ 0) ∘ₘ Measure.dirac
            ((MeasurableEquiv.piUnique
              (fun _ : Finset.Iic 0 => α)).symm s₀) =
          (Measure.dirac _).bind (traj κ 0) from rfl,
        Measure.dirac_bind (Kernel.measurable _) _]
    congr 1
  let μ := P.map (frestrictLe 1)
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [show μ Set.univ =
        P ((frestrictLe 1) ⁻¹' Set.univ) by
          exact Measure.map_apply (measurable_frestrictLe 1)
            MeasurableSet.univ]
    simp
  have hμ_eq : μ = partialTraj κ 0 1 u₀ := by
    rw [show μ = P.map (frestrictLe 1) from rfl, hPeq]
    have hm :
        (traj κ 0 u₀).map (frestrictLe 1) =
          ((traj κ 0).map (frestrictLe 1)) u₀ :=
      (Kernel.map_apply (traj κ 0) (measurable_frestrictLe 1) u₀).symm
    rw [hm, traj_map_frestrictLe (κ := κ) 0 1]
  have hCP : μ ⊗ₘ (traj κ 1) =
      P.map (fun x => (frestrictLe 1 x, x)) := by
    rw [hμ_eq, hPeq]
    exact partialTraj_compProd_traj (κ := κ) (Nat.zero_le 1) u₀
  let last : (∀ i : Finset.Iic 1, α) → α :=
    fun p => p ⟨1, Finset.mem_Iic.mpr le_rfl⟩
  have hlast : Measurable last := measurable_pi_apply _
  have hpair : Measurable
      (fun ω : Nat → α => (frestrictLe 1 ω, ω)) :=
    (measurable_frestrictLe 1).prod measurable_id
  have hG : Measurable
      (fun q : (∀ i : Finset.Iic 1, α) × (Nat → α) =>
        F (last q.1, pathShift 1 q.2)) := by
    have hshiftMeas :
        Measurable
          (fun q : (∀ i : Finset.Iic 1, α) × (Nat → α) =>
            pathShift 1 q.2) := by
      rw [measurable_pi_iff]
      intro n
      exact (measurable_pi_apply (1 + n)).comp measurable_snd
    apply hF.comp
    exact (hlast.comp measurable_fst).prod hshiftMeas
  calc
    ∫⁻ ω, F (ω 1, pathShift 1 ω) ∂P =
        ∫⁻ q, F (last q.1, pathShift 1 q.2)
          ∂(P.map (fun ω => (frestrictLe 1 ω, ω))) := by
            rw [lintegral_map hG hpair]
            rfl
    _ = ∫⁻ q, F (last q.1, pathShift 1 q.2)
          ∂(μ ⊗ₘ (traj κ 1)) := by rw [hCP]
    _ = ∫⁻ p, ∫⁻ y, F (last p, pathShift 1 y)
          ∂traj κ 1 p ∂μ := by
            rw [Measure.lintegral_compProd hG]
    _ = ∫⁻ p, ∫⁻ η, F (last p, η)
          ∂homogeneousPathMeasure (Measure.dirac (last p)) K ∂μ := by
            congr 1
            funext p
            have hshift :
                (traj κ 1 p).map (pathShift 1) =
                  homogeneousPathMeasure (Measure.dirac (last p)) K := by
              simpa only [last, X, κ] using
                traj_map_pathShift_eq_homogeneousPathMeasure K 1 p
            rw [← hshift]
            rw [MeasureTheory.lintegral_map]
            · exact hF.comp
                ((measurable_const :
                    Measurable (fun _ : Nat → α => last p)).prod
                  measurable_id)
            · exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
    _ = ∫⁻ x, ∫⁻ η, F (x, η)
          ∂homogeneousPathMeasure (Measure.dirac x) K
          ∂(μ.map last) := by
            let init : α → (∀ i : Finset.Iic 0, α) :=
              fun x _ => x
            have hinit : Measurable init := by
              rw [measurable_pi_iff]
              intro i
              exact measurable_id
            let fresh : Kernel α (Nat → α) :=
              (traj κ 0).comap init hinit
            have hFreshEq :
                ∀ x, fresh x =
                  homogeneousPathMeasure (Measure.dirac x) K := by
              intro x
              dsimp only [fresh]
              rw [Kernel.comap_apply]
              let ux : ∀ i : Finset.Iic 0, X i := fun _ => x
              change traj κ 0 ux =
                homogeneousPathMeasure (Measure.dirac x) K
              symm
              have hdef :
                  homogeneousPathMeasure (Measure.dirac x) K =
                    (traj κ 0) ∘ₘ
                      (Measure.dirac x).map
                        (MeasurableEquiv.piUnique
                          (fun _ : Finset.Iic 0 => α)).symm := rfl
              rw [hdef, Measure.map_dirac'
                    (MeasurableEquiv.measurable _),
                  show (traj κ 0) ∘ₘ Measure.dirac
                      ((MeasurableEquiv.piUnique
                        (fun _ : Finset.Iic 0 => α)).symm x) =
                    (Measure.dirac _).bind (traj κ 0) from rfl,
                  Measure.dirac_bind (Kernel.measurable _) _]
              congr 1
            have hFreshMeas :
                Measurable (fun x =>
                  ∫⁻ η, F (x, η)
                    ∂homogeneousPathMeasure (Measure.dirac x) K) := by
              simpa only [← hFreshEq] using
                (Measurable.lintegral_kernel_prod_right'
                  (κ := fresh) hF)
            rw [MeasureTheory.lintegral_map hFreshMeas hlast]
    _ = ∫⁻ x, ∫⁻ η, F (x, η)
          ∂homogeneousPathMeasure (Measure.dirac x) K ∂K s₀ := by
            have hmap : μ.map last = K s₀ := by
              rw [show μ = P.map (frestrictLe 1) from rfl,
                Measure.map_map hlast (measurable_frestrictLe 1)]
              change P.map (fun ω => ω 1) = K s₀
              rw [show P =
                homogeneousPathMeasure (Measure.dirac s₀) K from rfl,
                homogeneousPathMeasure_dirac_marginal K s₀ 1,
                show kernelIter K 1 = K from kernelIter_one_generic K]
            rw [hmap]

/-- Kernel sending a state to the law of a fresh homogeneous path from
that state. -/
noncomputable def homogeneousPathKernel
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K] :
    Kernel α (Nat → α) := by
  let X : Nat → Type _ := fun _ => α
  let κ : (t : Nat) →
      Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  let init : α → (∀ i : Finset.Iic 0, α) :=
    fun x _ => x
  exact (traj κ 0).comap init (by
    rw [measurable_pi_iff]
    intro i
    exact measurable_id)

lemma homogeneousPathKernel_apply
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K] (x : α) :
    homogeneousPathKernel K x =
      homogeneousPathMeasure (Measure.dirac x) K := by
  let X : Nat → Type _ := fun _ => α
  let κ : (t : Nat) →
      Kernel (∀ i : Finset.Iic t, X i) (X (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  let init : α → (∀ i : Finset.Iic 0, α) :=
    fun y _ => y
  rw [homogeneousPathKernel]
  change ((traj κ 0).comap init (by
      rw [measurable_pi_iff]
      intro i
      exact measurable_id) : Kernel α (Nat → α)) x =
    homogeneousPathMeasure (Measure.dirac x) K
  rw [Kernel.comap_apply]
  let ux : ∀ i : Finset.Iic 0, X i := fun _ => x
  change traj κ 0 ux =
    homogeneousPathMeasure (Measure.dirac x) K
  symm
  have hdef :
      homogeneousPathMeasure (Measure.dirac x) K =
        (traj κ 0) ∘ₘ
          (Measure.dirac x).map
            (MeasurableEquiv.piUnique
              (fun _ : Finset.Iic 0 => α)).symm := rfl
  rw [hdef, Measure.map_dirac'
        (MeasurableEquiv.measurable _),
      show (traj κ 0) ∘ₘ Measure.dirac
          ((MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 => α)).symm x) =
        (Measure.dirac _).bind (traj κ 0) from rfl,
      Measure.dirac_bind (Kernel.measurable _) _]
  congr 1

instance homogeneousPathKernel_isMarkov
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [Nonempty α]
    (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (homogeneousPathKernel K) := by
  refine ⟨fun x => ?_⟩
  rw [homogeneousPathKernel_apply]
  simp only [homogeneousPathMeasure]
  infer_instance

@[fun_prop] lemma measurable_pathShift (k : Nat) {α : Type*}
    [MeasurableSpace α] :
    Measurable (pathShift k : (Nat → α) → Nat → α) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply (k + n)

/-- First-step decomposition for two independent homogeneous paths. -/
lemma homogeneousPathMeasure_prod_first_shift_lintegral
    {α₀ α₁ : Type*}
    [MeasurableSpace α₀] [StandardBorelSpace α₀] [Nonempty α₀]
    [MeasurableSpace α₁] [StandardBorelSpace α₁] [Nonempty α₁]
    (K₀ : Kernel α₀ α₀) [IsMarkovKernel K₀]
    (K₁ : Kernel α₁ α₁) [IsMarkovKernel K₁]
    (s₀ : α₀) (s₁ : α₁)
    (F : (α₀ × α₁) ×
        ((Nat → α₀) × (Nat → α₁)) → ENNReal)
    (hF : Measurable F) :
    ∫⁻ z,
        F ((z.1 1, z.2 1),
          (pathShift 1 z.1, pathShift 1 z.2))
      ∂(homogeneousPathMeasure (Measure.dirac s₀) K₀).prod
        (homogeneousPathMeasure (Measure.dirac s₁) K₁) =
    ∫⁻ x₀, ∫⁻ η₀, ∫⁻ x₁, ∫⁻ η₁,
        F ((x₀, x₁), (η₀, η₁))
          ∂homogeneousPathMeasure (Measure.dirac x₁) K₁
          ∂K₁ s₁
          ∂homogeneousPathMeasure (Measure.dirac x₀) K₀
          ∂K₀ s₀ := by
  let P₀ := homogeneousPathMeasure (Measure.dirac s₀) K₀
  let P₁ := homogeneousPathMeasure (Measure.dirac s₁) K₁
  haveI : IsProbabilityMeasure P₀ := by
    simp only [P₀, homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure P₁ := by
    simp only [P₁, homogeneousPathMeasure]
    infer_instance
  have hOuter :
      Measurable
        (fun ω₀ : Nat → α₀ =>
          ∫⁻ ω₁,
            F ((ω₀ 1, ω₁ 1),
              (pathShift 1 ω₀, pathShift 1 ω₁)) ∂P₁) := by
    apply Measurable.lintegral_prod_right
    apply hF.comp
    fun_prop
  change (∫⁻ z,
      F ((z.1 1, z.2 1),
        (pathShift 1 z.1, pathShift 1 z.2)) ∂P₀.prod P₁) = _
  rw [MeasureTheory.lintegral_prod _ (by
    apply Measurable.aemeasurable
    apply hF.comp
    exact
      (((measurable_pi_apply 1).comp measurable_fst).prod
        ((measurable_pi_apply 1).comp measurable_snd)).prod
      (((measurable_pathShift 1).comp measurable_fst).prod
        ((measurable_pathShift 1).comp measurable_snd)) : AEMeasurable
      (fun z : (Nat → α₀) × (Nat → α₁) =>
        F ((z.1 1, z.2 1),
          (pathShift 1 z.1, pathShift 1 z.2)))
      (P₀.prod P₁))]
  have hInner :
      ∀ ω₀ : Nat → α₀,
        (∫⁻ ω₁,
            F ((ω₀ 1, ω₁ 1),
              (pathShift 1 ω₀, pathShift 1 ω₁)) ∂P₁) =
          ∫⁻ x₁, ∫⁻ η₁,
            F ((ω₀ 1, x₁), (pathShift 1 ω₀, η₁))
              ∂homogeneousPathMeasure (Measure.dirac x₁) K₁
              ∂K₁ s₁ := by
    intro ω₀
    let G : α₁ × (Nat → α₁) → ENNReal :=
      fun q => F ((ω₀ 1, q.1), (pathShift 1 ω₀, q.2))
    have hG : Measurable G := by
      apply hF.comp
      fun_prop
    simpa only [P₁, G] using
      homogeneousPathMeasure_first_shift_lintegral
        K₁ s₁ G hG
  simp_rw [hInner]
  let H : α₀ × (Nat → α₀) → ENNReal :=
    fun q => ∫⁻ x₁, ∫⁻ η₁,
      F ((q.1, x₁), (q.2, η₁))
        ∂homogeneousPathMeasure (Measure.dirac x₁) K₁
        ∂K₁ s₁
  have hH : Measurable H := by
    let D := (α₀ × (Nat → α₀)) × α₁
    let tail₁ : Kernel D (Nat → α₁) :=
      (homogeneousPathKernel K₁).comap
        (fun d => d.2) measurable_snd
    let J : D → ENNReal := fun d =>
      ∫⁻ η₁, F ((d.1.1, d.2), (d.1.2, η₁)) ∂tail₁ d
    have hJ : Measurable J := by
      let fJ :
          (((α₀ × (Nat → α₀)) × α₁) ×
            (Nat → α₁)) → ENNReal :=
        fun p => F ((p.1.1.1, p.1.2), (p.1.1.2, p.2))
      have hfJ : Measurable fJ := by
        apply hF.comp
        fun_prop
      dsimp only [J]
      change Measurable
        (fun d : D =>
          ∫⁻ η₁, fJ (d, η₁) ∂tail₁ d)
      exact Measurable.lintegral_kernel_prod_right'
        (κ := tail₁) hfJ
    have hJeq :
        ∀ d : D, J d =
          ∫⁻ η₁, F ((d.1.1, d.2), (d.1.2, η₁))
            ∂homogeneousPathMeasure (Measure.dirac d.2) K₁ := by
      intro d
      dsimp only [J, tail₁]
      rw [Kernel.comap_apply]
      rw [homogeneousPathKernel_apply]
    have hJtarget :
        Measurable
          (fun d : D =>
            ∫⁻ η₁, F ((d.1.1, d.2), (d.1.2, η₁))
              ∂homogeneousPathMeasure
                (Measure.dirac d.2) K₁) := by
      convert hJ using 1
      funext d
      exact (hJeq d).symm
    change Measurable
      (fun q : α₀ × (Nat → α₀) =>
        ∫⁻ x₁, ∫⁻ η₁,
          F ((q.1, x₁), (q.2, η₁))
            ∂homogeneousPathMeasure (Measure.dirac x₁) K₁
            ∂K₁ s₁)
    exact Measurable.lintegral_prod_right'
      (ν := K₁ s₁) hJtarget
  let G₀ : α₀ × (Nat → α₀) → ENNReal := H
  have hFirst₀ :=
    homogeneousPathMeasure_first_shift_lintegral
      K₀ s₀ G₀ hH
  simpa only [P₀, H, G₀] using hFirst₀

/-- Calendar extinction time splits into the first holding time and the
extinction time of the shifted timed path. -/
lemma timedExtinctionTime_eq_first_add_shift
    (ω : Nat → Nat × Real) :
    timedExtinctionTime ω =
      timedStateHolding (ω 1) +
        timedExtinctionTime (pathShift 1 ω) := by
  let q : Nat → ENNReal := fun k => timedHoldingContribution ω k
  let r : Nat → ENNReal :=
    fun k => timedHoldingContribution (pathShift 1 ω) k
  have hq :
      q 0 + q 1 + ∑' k : Nat, q (k + 2) =
        ∑' k : Nat, q k := by
    have h :=
      ENNReal.summable.sum_add_tsum_nat_add'
        (f := q) (k := 2)
    simpa [Finset.sum_range_succ, add_assoc] using h
  have hr :
      r 0 + ∑' k : Nat, r (k + 1) =
        ∑' k : Nat, r k := by
    have h :=
      ENNReal.summable.sum_add_tsum_nat_add'
        (f := r) (k := 1)
    simpa using h
  have htail :
      ∑' k : Nat, r (k + 1) =
        ∑' k : Nat, q (k + 2) := by
    congr 1
    funext k
    simp only [q, r, timedHoldingContribution, Nat.add_eq_zero,
      one_ne_zero, and_false, ↓reduceIte, pathShift,
      timedStateHolding]
    rw [show 1 + (k + 1) = k + 2 by omega]
    simp
  simp only [timedExtinctionTime]
  change (∑' k : Nat, q k) =
    timedStateHolding (ω 1) + ∑' k : Nat, r k
  rw [← hq, ← hr, htail]
  simp [q, r, timedHoldingContribution]

lemma expMeasure_singleton_zero
    (r x : Real) :
    expMeasure r {x} = 0 := by
  rw [expMeasure, gammaMeasure]
  change (volume.withDensity (gammaPDF 1 r)) {x} = 0
  calc
    (volume.withDensity (gammaPDF 1 r)) {x} =
        ∫⁻ y in ({x} : Set Real), gammaPDF 1 r y ∂volume :=
      withDensity_apply (gammaPDF 1 r)
        (measurableSet_singleton x)
    _ = 0 :=
      setLIntegral_measure_zero _ _ (measure_singleton x)

lemma expMeasure_Iio
    {r t : Real} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Set.Iio t) =
      ENNReal.ofReal (1 - Real.exp (-(r * t))) := by
  have hsplit :
      Set.Iic t = Set.Iio t ∪ {t} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio,
      Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (Set.Iio t) ({t} : Set Real) := by
    exact Set.disjoint_left.2 fun x hx hxt =>
      (ne_of_lt (show x < t from hx)) (show x = t from hxt)
  have hIic :
      expMeasure r (Set.Iic t) =
        ENNReal.ofReal (1 - Real.exp (-(r * t))) := by
    letI : IsProbabilityMeasure (expMeasure r) :=
      isProbabilityMeasure_expMeasure hr
    have hfinite : expMeasure r (Set.Iic t) ≠ ⊤ :=
      measure_ne_top _ _
    calc
      expMeasure r (Set.Iic t) =
          ENNReal.ofReal ((expMeasure r (Set.Iic t)).toReal) :=
            (ENNReal.ofReal_toReal hfinite).symm
      _ = ENNReal.ofReal (cdf (expMeasure r) t) := by
            rw [cdf_eq_real, measureReal_def]
      _ = ENNReal.ofReal
          (1 - Real.exp (-(r * t))) := by
            rw [cdf_expMeasure_eq hr, if_pos ht]
  rw [hsplit, measure_union hdisj (measurableSet_singleton t),
    expMeasure_singleton_zero, add_zero] at hIic
  exact hIic

lemma expMeasure_lt_shift
    {r a b : Real} (hr : 0 < r) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a < b) :
    expMeasure r {x | x + a < b} =
      ENNReal.ofReal
        (1 - Real.exp (-(r * (b - a)))) := by
  have hset : {x : Real | x + a < b} = Set.Iio (b - a) := by
    ext x
    change (x + a < b) ↔ (x < b - a)
    constructor <;> intro hx <;> linarith
  rw [hset]
  exact expMeasure_Iio hr (sub_nonneg.mpr hab.le)

lemma expMeasure_offset_gt
    {r a b : Real} (hr : 0 < r) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hba : b ≤ a) :
    expMeasure r {x | a < x + b} =
      ENNReal.ofReal
        (Real.exp (-(r * (a - b)))) := by
  have hset : {x : Real | a < x + b} =
      Set.Ioi (a - b) := by
    ext x
    change (a < x + b) ↔ (a - b < x)
    constructor <;> intro hx <;> linarith
  rw [hset]
  exact expMeasure_Ioi hr (sub_nonneg.mpr hba)

lemma expRace_offset_ge
    {r₀ r₁ a b : Real}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) :
    (expMeasure r₀).prod (expMeasure r₁)
        {z | z.1 + a < z.2 + b} =
      ENNReal.ofReal (r₀ / (r₀ + r₁)) *
        ENNReal.ofReal
          (Real.exp (-(r₁ * (a - b)))) := by
  letI : IsProbabilityMeasure (expMeasure r₀) :=
    isProbabilityMeasure_expMeasure hr₀
  letI : IsProbabilityMeasure (expMeasure r₁) :=
    isProbabilityMeasure_expMeasure hr₁
  have hE : MeasurableSet
      {z : Real × Real | z.1 + a < z.2 + b} := by
    measurability
  rw [Measure.prod_apply hE]
  have hae :
      ∀ᵐ x ∂expMeasure r₀,
        expMeasure r₁
            (Prod.mk x ⁻¹'
              {z : Real × Real | z.1 + a < z.2 + b}) =
          ENNReal.ofReal
            (Real.exp (-(r₁ * (a - b)))) *
              ENNReal.ofReal
                (Real.exp (-(r₁ * x))) := by
    filter_upwards [expMeasure_ae_nonneg hr₀] with x hx
    have hx' : 0 ≤ x := by simpa using hx
    have hthreshold : 0 ≤ x + a - b := by linarith
    have hset :
        Prod.mk x ⁻¹'
            {z : Real × Real | z.1 + a < z.2 + b} =
          Set.Ioi (x + a - b) := by
      ext y
      change (x + a < y + b) ↔ (x + a - b < y)
      constructor <;> intro h <;> linarith
    rw [hset, expMeasure_Ioi hr₁ hthreshold]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [show -(r₁ * (x + a - b)) =
        -(r₁ * (a - b)) + -(r₁ * x) by ring,
      Real.exp_add]
  rw [lintegral_congr_ae hae]
  rw [lintegral_const_mul _ (by fun_prop)]
  rw [expMeasure_laplace hr₀ hr₁.le]
  rw [mul_comm]

lemma expRace_offset_eq_zero
    {r₀ r₁ a b : Real}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    (expMeasure r₀).prod (expMeasure r₁)
        {z | z.1 + a = z.2 + b} = 0 := by
  letI : IsProbabilityMeasure (expMeasure r₀) :=
    isProbabilityMeasure_expMeasure hr₀
  letI : IsProbabilityMeasure (expMeasure r₁) :=
    isProbabilityMeasure_expMeasure hr₁
  have hE : MeasurableSet
      {z : Real × Real | z.1 + a = z.2 + b} := by
    measurability
  rw [Measure.prod_apply hE]
  have hzero :
      ∀ x : Real,
        expMeasure r₁
            (Prod.mk x ⁻¹'
              {z : Real × Real | z.1 + a = z.2 + b}) = 0 := by
    intro x
    have hset :
        Prod.mk x ⁻¹'
            {z : Real × Real | z.1 + a = z.2 + b} =
          {x + a - b} := by
      ext y
      change (x + a = y + b) ↔ y = x + a - b
      constructor <;> intro h <;> linarith
    rw [hset, expMeasure_singleton_zero]
  simp_rw [hzero]
  exact lintegral_zero

/-- One-step race identity for two independent exponential clocks with
nonnegative future-time offsets.  This is the memoryless-clock
calculation behind superposition of the two isolated continuous-time
chains. -/
lemma expRace_offset_identity
    {r₀ r₁ a b : Real}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (expMeasure r₀).prod (expMeasure r₁)
        {z | z.1 + a < z.2 + b} =
      ENNReal.ofReal (r₀ / (r₀ + r₁)) *
          expMeasure r₁ {x | a < x + b} +
        ENNReal.ofReal (r₁ / (r₀ + r₁)) *
          expMeasure r₀ {x | x + a < b} := by
  letI : IsProbabilityMeasure (expMeasure r₀) :=
    isProbabilityMeasure_expMeasure hr₀
  letI : IsProbabilityMeasure (expMeasure r₁) :=
    isProbabilityMeasure_expMeasure hr₁
  have hrs : 0 < r₀ + r₁ := add_pos hr₀ hr₁
  have hp0 : 0 ≤ r₀ / (r₀ + r₁) := div_nonneg hr₀.le hrs.le
  have hp1 : 0 ≤ r₁ / (r₀ + r₁) := div_nonneg hr₁.le hrs.le
  have hpSum :
      ENNReal.ofReal (r₀ / (r₀ + r₁)) +
          ENNReal.ofReal (r₁ / (r₀ + r₁)) = 1 := by
    rw [← ENNReal.ofReal_add hp0 hp1]
    have hreal :
        r₀ / (r₀ + r₁) + r₁ / (r₀ + r₁) = 1 := by
      field_simp
    rw [hreal]
    norm_num
  rcases le_total b a with hba | hab
  · rw [expRace_offset_ge hr₀ hr₁ ha hb hba,
      expMeasure_offset_gt hr₁ ha hb hba]
    have hzero :
        expMeasure r₀ {x | x + a < b} = 0 := by
      have hsub : {x : Real | x + a < b} ⊆ Set.Iio 0 := by
        intro x hx
        change x + a < b at hx
        change x < 0
        linarith
      have hIio0 : expMeasure r₀ (Set.Iio 0) = 0 := by
        simpa using expMeasure_Iio hr₀ (le_refl 0)
      exact measure_mono_null hsub hIio0
    rw [hzero, mul_zero, add_zero]
  · by_cases heq : a = b
    · subst b
      exact (expRace_offset_ge hr₀ hr₁ ha hb le_rfl).trans (by
        rw [expMeasure_offset_gt hr₁ ha hb le_rfl]
        have hzero :
            expMeasure r₀ {x | x + a < a} = 0 := by
          have hsub : {x : Real | x + a < a} ⊆ Set.Iio 0 := by
            intro x hx
            change x + a < a at hx
            change x < 0
            linarith
          have hIio0 : expMeasure r₀ (Set.Iio 0) = 0 := by
            simpa using expMeasure_Iio hr₀ (le_refl 0)
          exact measure_mono_null hsub hIio0
        rw [hzero, mul_zero, add_zero])
    · have hab' : a < b := lt_of_le_of_ne hab heq
      let μ := (expMeasure r₀).prod (expMeasure r₁)
      let E : Set (Real × Real) :=
        {z | z.1 + a < z.2 + b}
      let F : Set (Real × Real) :=
        {z | z.2 + b < z.1 + a}
      let T : Set (Real × Real) :=
        {z | z.1 + a = z.2 + b}
      have hE : MeasurableSet E := by
        dsimp only [E]
        measurability
      have hF : MeasurableSet F := by
        dsimp only [F]
        measurability
      have hT : MeasurableSet T := by
        dsimp only [T]
        measurability
      have hcomp : Eᶜ = F ∪ T := by
        ext z
        simp only [E, F, T, Set.mem_compl_iff, Set.mem_setOf_eq,
          Set.mem_union]
        constructor
        · intro hn
          have hle : z.2 + b ≤ z.1 + a := le_of_not_gt hn
          rcases hle.lt_or_eq with hlt | heq'
          · exact Or.inl hlt
          · exact Or.inr heq'.symm
        · rintro (hlt | heq')
          · exact not_lt_of_ge hlt.le
          · exact fun hlt => (ne_of_lt hlt) heq'
      have hdisj : Disjoint F T := by
        exact Set.disjoint_left.2 fun z hzF hzT =>
          (ne_of_lt hzF) hzT.symm
      have hTzero : μ T = 0 := by
        exact expRace_offset_eq_zero hr₀ hr₁
      have hFval :
          μ F =
            ENNReal.ofReal (r₁ / (r₀ + r₁)) *
              ENNReal.ofReal
                (Real.exp (-(r₀ * (b - a)))) := by
        have hswap :
            μ F =
              (expMeasure r₁).prod (expMeasure r₀)
                {z | z.1 + b < z.2 + a} := by
          rw [show μ F =
              μ.map Prod.swap
                {z | z.1 + b < z.2 + a} by
            rw [Measure.map_apply (by fun_prop) (by measurability)]
            rfl]
          rw [Measure.prod_swap]
        rw [hswap]
        simpa only [add_comm r₁ r₀] using
          expRace_offset_ge hr₁ hr₀ hb ha hab
      have hEval :
          μ E =
            1 -
              ENNReal.ofReal (r₁ / (r₀ + r₁)) *
                ENNReal.ofReal
                  (Real.exp (-(r₀ * (b - a)))) := by
        have hFcomp : Fᶜ = E ∪ T := by
          ext z
          simp only [E, F, T, Set.mem_compl_iff, Set.mem_setOf_eq,
            Set.mem_union]
          constructor
          · intro hn
            have hle : z.1 + a ≤ z.2 + b := le_of_not_gt hn
            rcases hle.lt_or_eq with hlt | heq'
            · exact Or.inl hlt
            · exact Or.inr heq'
          · rintro (hlt | heq')
            · exact not_lt_of_ge hlt.le
            · exact fun hlt => (ne_of_lt hlt) heq'.symm
        have hdisjET : Disjoint E T := by
          exact Set.disjoint_left.2 fun z hzE hzT =>
            (ne_of_lt hzE) hzT
        calc
          μ E = μ (E ∪ T) := by
            rw [measure_union hdisjET hT, hTzero, add_zero]
          _ = μ Fᶜ := by rw [hFcomp]
          _ = μ Set.univ - μ F :=
            measure_compl hF (measure_ne_top μ F)
          _ = 1 -
              ENNReal.ofReal (r₁ / (r₀ + r₁)) *
                ENNReal.ofReal
                  (Real.exp (-(r₀ * (b - a)))) := by
            rw [hFval, measure_univ]
      rw [show expMeasure r₁ {x | a < x + b} = 1 by
        have hfull :
            ∀ᵐ x ∂expMeasure r₁, a < x + b := by
          filter_upwards [expMeasure_ae_nonneg hr₁] with x hx
          have hx' : 0 ≤ x := by simpa using hx
          linarith
        have hcompZero :
            expMeasure r₁ {x | ¬a < x + b} = 0 :=
          ae_iff.mp hfull
        have hSmeas :
            MeasurableSet {x : Real | a < x + b} := by
          measurability
        calc
          expMeasure r₁ {x | a < x + b} =
              expMeasure r₁ Set.univ -
                expMeasure r₁ {x | ¬a < x + b} := by
            rw [show {x : Real | a < x + b} =
                ({x : Real | ¬a < x + b})ᶜ by ext x; simp]
            exact measure_compl hSmeas.compl
              (measure_ne_top _ _)
          _ = 1 := by rw [hcompZero, measure_univ, tsub_zero],
        expMeasure_lt_shift hr₀ ha hb hab', mul_one]
      rw [hEval]
      let p₀ := ENNReal.ofReal (r₀ / (r₀ + r₁))
      let p₁ := ENNReal.ofReal (r₁ / (r₀ + r₁))
      let e := ENNReal.ofReal (Real.exp (-(r₀ * (b - a))))
      have hp1e : p₁ * e ≤ 1 := by
        calc
          p₁ * e ≤ p₁ * 1 := by
            gcongr
            exact ENNReal.ofReal_le_one.mpr
              (by
                rw [Real.exp_le_one_iff]
                have : 0 < r₀ * (b - a) :=
                  mul_pos hr₀ (sub_pos.mpr hab')
                linarith)
          _ = p₁ := by rw [mul_one]
          _ ≤ p₀ + p₁ := le_add_left le_rfl
          _ = 1 := hpSum
      have hp1e' : p₁ * e ≤ p₁ := by
        calc
          p₁ * e ≤ p₁ * 1 := by
            gcongr
            exact ENNReal.ofReal_le_one.mpr
              (by
                rw [Real.exp_le_one_iff]
                have : 0 < r₀ * (b - a) :=
                  mul_pos hr₀ (sub_pos.mpr hab')
                linarith)
          _ = p₁ := by rw [mul_one]
      have hOneSub :
          ENNReal.ofReal
              (1 - Real.exp (-(r₀ * (b - a)))) =
            1 - e := by
        rw [ENNReal.ofReal_sub 1 (Real.exp_nonneg _),
          ENNReal.ofReal_one]
      change 1 - p₁ * e = p₀ + p₁ *
        ENNReal.ofReal
          (1 - Real.exp (-(r₀ * (b - a))))
      rw [hOneSub]
      have hp0top : p₀ ≠ ⊤ := ENNReal.ofReal_ne_top
      have hp1top : p₁ ≠ ⊤ := ENNReal.ofReal_ne_top
      have heOne : e ≤ 1 := by
        exact ENNReal.ofReal_le_one.mpr
          (by
            rw [Real.exp_le_one_iff]
            have : 0 < r₀ * (b - a) :=
              mul_pos hr₀ (sub_pos.mpr hab')
            linarith)
      have hrhsTop : p₀ + p₁ * (1 - e) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr
          ⟨hp0top, ENNReal.mul_ne_top hp1top
            (ENNReal.sub_ne_top ENNReal.one_ne_top)⟩
      apply (ENNReal.toReal_eq_toReal_iff'
        (ENNReal.sub_ne_top ENNReal.one_ne_top) hrhsTop).mp
      rw [ENNReal.toReal_sub_of_le hp1e ENNReal.one_ne_top,
        ENNReal.toReal_add hp0top
          (ENNReal.mul_ne_top hp1top
            (ENNReal.sub_ne_top ENNReal.one_ne_top))]
      simp only [ENNReal.toReal_mul]
      rw [ENNReal.toReal_sub_of_le heOne ENNReal.one_ne_top]
      have hpSumReal : p₀.toReal + p₁.toReal = 1 := by
        rw [← ENNReal.toReal_add hp0top hp1top, hpSum]
        norm_num
      norm_num only [ENNReal.toReal_one]
      linarith

/-! ## Extinction-race probability -/

/-- Probability that isolated species `0` becomes extinct strictly before
isolated species `1`. -/
noncomputable def independentExtinctionRaceProb
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (a b : Nat) : ENNReal :=
  (singleSpeciesTimedPathMeasure
        v params false hDelta a).prod
    (singleSpeciesTimedPathMeasure
        v params true hDelta b)
      {z | timedExtinctionTime z.1 <
        timedExtinctionTime z.2}

lemma measurableSet_timedExtinctionRace :
    MeasurableSet
      {z : (Nat → Nat × Real) × (Nat → Nat × Real) |
        timedExtinctionTime z.1 < timedExtinctionTime z.2} := by
  exact measurableSet_lt
    (measurable_timedExtinctionTime.comp measurable_fst)
    (measurable_timedExtinctionTime.comp measurable_snd)

lemma independentExtinctionRaceProb_le_one
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (a b : Nat) :
    independentExtinctionRaceProb v params hDelta a b ≤ 1 := by
  letI : IsMarkovKernel
      (singleSpeciesTimedKernel v params false) :=
    singleSpeciesTimedKernel_isMarkov v params false hDelta
  letI : IsMarkovKernel
      (singleSpeciesTimedKernel v params true) :=
    singleSpeciesTimedKernel_isMarkov v params true hDelta
  haveI hP0 : IsProbabilityMeasure
      (singleSpeciesTimedPathMeasure
        v params false hDelta a) := by
    simp only [singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI hP1 : IsProbabilityMeasure
      (singleSpeciesTimedPathMeasure
        v params true hDelta b) := by
    simp only [singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  let μ :=
    (singleSpeciesTimedPathMeasure
        v params false hDelta a).prod
      (singleSpeciesTimedPathMeasure
        v params true hDelta b)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  calc
    independentExtinctionRaceProb v params hDelta a b =
        μ {z | timedExtinctionTime z.1 <
          timedExtinctionTime z.2} := rfl
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem singleSpecies_timedExtinctionTime_ne_top_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params i hDelta))
    (hmono : Monotone cert.V) (m : Nat) :
    ∀ᵐ ω ∂singleSpeciesTimedPathMeasure
        v params i hDelta m,
      timedExtinctionTime ω ≠ ⊤ := by
  have hInt :
      (∫⁻ ω, timedExtinctionTime ω
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta m) ≠ ⊤ :=
    ne_top_of_le_ne_top cert.bound_ne_top
      (singleSpecies_timedExtinctionTime_lintegral_le
        v params i hDelta cert hmono m)
  filter_upwards [
    ae_lt_top measurable_timedExtinctionTime hInt] with ω hω
  exact hω.ne

theorem singleSpecies_timedExtinctionTime_ne_top_ae_of_gamma
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) (m : Nat) :
    ∀ᵐ ω ∂singleSpeciesTimedPathMeasure
        v params i hDelta m,
      timedExtinctionTime ω ≠ ⊤ := by
  obtain ⟨cert, hmono⟩ :=
    exists_singleSpecies_monotone_certificate
      params i hDelta hGamma
  exact singleSpecies_timedExtinctionTime_ne_top_ae
    v params i hDelta cert hmono m

theorem singleSpecies_timedExtinctionTime_zero_ae_of_gamma
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) :
    ∀ᵐ ω ∂singleSpeciesTimedPathMeasure
        v params i hDelta 0,
      timedExtinctionTime ω = 0 := by
  obtain ⟨cert, hmono⟩ :=
    exists_singleSpecies_monotone_certificate
      params i hDelta hGamma
  have hle :
      ∫⁻ ω, timedExtinctionTime ω
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta 0 ≤ 0 := by
    simpa [cert.zero] using
      singleSpecies_timedExtinctionTime_lintegral_le_value
        v params i hDelta cert hmono 0
  have hzero :
      ∫⁻ ω, timedExtinctionTime ω
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta 0 = 0 :=
    le_antisymm hle bot_le
  exact (lintegral_eq_zero_iff
    measurable_timedExtinctionTime).mp hzero

lemma expMeasure_ae_pos {r : Real} (hr : 0 < r) :
    ∀ᵐ x ∂expMeasure r, 0 < x := by
  rw [ae_iff]
  have hbad :
      {x : Real | ¬0 < x} = Set.Iic 0 := by
    ext x
    simp
  rw [hbad]
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  have hfinite : expMeasure r (Set.Iic 0) ≠ ⊤ :=
    measure_ne_top _ _
  calc
    expMeasure r (Set.Iic 0) =
        ENNReal.ofReal ((expMeasure r (Set.Iic 0)).toReal) :=
          (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal (cdf (expMeasure r) 0) := by
          rw [cdf_eq_real, measureReal_def]
    _ = 0 := by simp [cdf_expMeasure_eq hr]

lemma singleSpeciesTimedStep_holding_pos_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) (hm : 0 < m) :
    ∀ᵐ z ∂singleSpeciesTimedStep v params i m,
      0 < z.2 := by
  have hRate :
      0 < singleSpeciesTotalRate params i m :=
    singleSpeciesTotalRate_pos params i hDelta m hm
  let J := singleSpeciesJumpMeasure v params i m
  let E := expMeasure (singleSpeciesTotalRate params i m)
  haveI : IsProbabilityMeasure J :=
    singleSpeciesJumpMeasure_isProbability v params i m
  haveI : IsProbabilityMeasure E :=
    isProbabilityMeasure_expMeasure hRate
  have hEpos : E (Set.Ioi 0) = 1 := by
    have hbad :
        E {x : Real | ¬0 < x} = 0 :=
      ae_iff.mp (expMeasure_ae_pos hRate)
    have hIoi : MeasurableSet (Set.Ioi (0 : Real)) :=
      measurableSet_Ioi
    calc
      E (Set.Ioi 0) =
          E Set.univ - E (Set.Ioi 0)ᶜ := by
            simpa only [compl_compl] using
              (measure_compl hIoi.compl
                (measure_ne_top E (Set.Ioi 0)ᶜ))
      _ = 1 := by
        rw [show (Set.Ioi (0 : Real))ᶜ =
            {x : Real | ¬0 < x} by ext x; simp,
          hbad, measure_univ, tsub_zero]
  rw [ae_iff]
  have hset :
      {z : Nat × Real | ¬0 < z.2} =
        Set.univ ×ˢ (Set.Ioi (0 : Real))ᶜ := by
    ext z
    simp
  simp only [singleSpeciesTimedStep, hm.ne', ↓reduceIte]
  rw [hset, Measure.prod_prod, measure_univ, one_mul]
  rw [measure_compl measurableSet_Ioi (measure_ne_top _ _),
    hEpos, measure_univ, tsub_self]

lemma singleSpeciesTimedPath_first_holding_pos_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) (hm : 0 < m) :
    ∀ᵐ ω ∂singleSpeciesTimedPathMeasure
        v params i hDelta m,
      0 < (ω 1).2 := by
  let K := singleSpeciesTimedKernel v params i
  let P := singleSpeciesTimedPathMeasure
    v params i hDelta m
  haveI : IsMarkovKernel K :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  have hmap :
      P.map (fun ω => ω 1) =
        singleSpeciesTimedStep v params i m := by
    change
      (homogeneousPathMeasure (Measure.dirac (m, 0)) K).map
          (fun ω => ω 1) =
        singleSpeciesTimedStep v params i m
    rw [homogeneousPathMeasure_dirac_marginal,
      kernelIter_one_generic]
    rfl
  have hpos :=
    singleSpeciesTimedStep_holding_pos_ae
      v params i hDelta m hm
  rw [← hmap] at hpos
  exact ae_of_ae_map (measurable_pi_apply 1).aemeasurable hpos

lemma singleSpecies_timedExtinctionTime_pos_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) (hm : 0 < m) :
    ∀ᵐ ω ∂singleSpeciesTimedPathMeasure
        v params i hDelta m,
      0 < timedExtinctionTime ω := by
  filter_upwards [
    singleSpeciesTimedPath_first_holding_pos_ae
      v params i hDelta m hm] with ω hω
  have hhold :
      0 < timedHoldingContribution ω 1 := by
    simpa [timedHoldingContribution, timedStateHolding,
      ENNReal.ofReal_pos] using hω
  exact lt_of_lt_of_le hhold
    (ENNReal.le_tsum 1)

lemma independentExtinctionRaceProb_zero_left
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma0 : 0 < speciesGamma params false)
    (b : Nat) (hb : 0 < b) :
    independentExtinctionRaceProb
        v params hDelta 0 b = 1 := by
  let μ0 :=
    singleSpeciesTimedPathMeasure
      v params false hDelta 0
  let μ1 :=
    singleSpeciesTimedPathMeasure
      v params true hDelta b
  haveI : IsProbabilityMeasure μ0 := by
    simp only [μ0, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ1 := by
    simp only [μ1, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  have h0 :
      ∀ᵐ ω ∂μ0, timedExtinctionTime ω = 0 := by
    simpa only [μ0] using
      singleSpecies_timedExtinctionTime_zero_ae_of_gamma
        v params false hDelta hGamma0
  have h1 :
      ∀ᵐ ω ∂μ1, 0 < timedExtinctionTime ω := by
    simpa only [μ1] using
      singleSpecies_timedExtinctionTime_pos_ae
        v params true hDelta b hb
  have hae :
      ∀ᵐ z ∂μ0.prod μ1,
        timedExtinctionTime z.1 <
          timedExtinctionTime z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      measurableSet_timedExtinctionRace).2
    filter_upwards [h0] with ω0 hω0
    filter_upwards [h1] with ω1 hω1
    simpa [hω0] using hω1
  exact (mem_ae_iff_prob_eq_one
    measurableSet_timedExtinctionRace).mp hae

lemma independentExtinctionRaceProb_zero_right
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma1 : 0 < speciesGamma params true)
    (a : Nat) :
    independentExtinctionRaceProb
        v params hDelta a 0 = 0 := by
  let μ0 :=
    singleSpeciesTimedPathMeasure
      v params false hDelta a
  let μ1 :=
    singleSpeciesTimedPathMeasure
      v params true hDelta 0
  haveI : IsProbabilityMeasure μ0 := by
    simp only [μ0, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ1 := by
    simp only [μ1, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  have h1 :
      ∀ᵐ ω ∂μ1, timedExtinctionTime ω = 0 := by
    simpa only [μ1] using
      singleSpecies_timedExtinctionTime_zero_ae_of_gamma
        v params true hDelta hGamma1
  change μ0.prod μ1
      {z | timedExtinctionTime z.1 <
        timedExtinctionTime z.2} = 0
  have hnot :
      ∀ᵐ z ∂μ0.prod μ1,
        ¬timedExtinctionTime z.1 <
          timedExtinctionTime z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      measurableSet_timedExtinctionRace.compl).2
    filter_upwards with ω0
    filter_upwards [h1] with ω1 hω1
    simp only [Set.mem_setOf_eq, not_lt]
    rw [hω1]
    exact bot_le
  simpa only [not_not] using ae_iff.mp hnot

/-! ## First-step law of the isolated timed chain -/

/-- Timed single-species path law with an arbitrary, unused holding
coordinate in its initial state. -/
noncomputable def singleSpeciesTimedPathMeasureFrom
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (n : Nat) (h : Real) :
    Measure (Nat → Nat × Real) := by
  letI := singleSpeciesTimedKernel_isMarkov
    v params i hDelta
  exact homogeneousPathMeasure
    (Measure.dirac (n, h))
    (singleSpeciesTimedKernel v params i)

/-- The extinction-time law of a fresh timed path depends on the
initial count, but not on the unused holding-time coordinate at index
zero. -/
lemma singleSpeciesTimedPath_lintegral_extinction_initial_irrel
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (n : Nat) (h : Real)
    (G : ENNReal → ENNReal) (hG : Measurable G) :
    ∫⁻ η, G (timedExtinctionTime η)
        ∂singleSpeciesTimedPathMeasureFrom
          v params i hDelta n h =
      ∫⁻ η, G (timedExtinctionTime η)
        ∂singleSpeciesTimedPathMeasure
          v params i hDelta n := by
  let K := singleSpeciesTimedKernel v params i
  haveI : IsMarkovKernel K :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  let F :
      (Nat × Real) × (Nat → Nat × Real) → ENNReal :=
    fun q => G
      (timedStateHolding q.1 +
        timedExtinctionTime q.2)
  have hF : Measurable F := by
    apply hG.comp
    exact measurable_timedStateHolding.comp measurable_fst
      |>.add
        (measurable_timedExtinctionTime.comp measurable_snd)
  have hKh :
      K (n, h) = K (n, 0) := by
    simp only [K, singleSpeciesTimedKernel,
      Kernel.comap_apply]
  have hLeft :=
    homogeneousPathMeasure_first_shift_lintegral
      K (n, h) F hF
  have hRight :=
    homogeneousPathMeasure_first_shift_lintegral
      K (n, 0) F hF
  calc
    ∫⁻ η, G (timedExtinctionTime η)
        ∂singleSpeciesTimedPathMeasureFrom
          v params i hDelta n h =
      ∫⁻ η, F (η 1, pathShift 1 η)
        ∂homogeneousPathMeasure (Measure.dirac (n, h)) K := by
          change
            (∫⁻ η, G (timedExtinctionTime η)
              ∂homogeneousPathMeasure
                (Measure.dirac (n, h)) K) = _
          congr 1
          funext η
          simp only [F]
          rw [timedExtinctionTime_eq_first_add_shift]
    _ = ∫⁻ x, ∫⁻ η, F (x, η)
          ∂homogeneousPathMeasure (Measure.dirac x) K
          ∂K (n, h) := hLeft
    _ = ∫⁻ x, ∫⁻ η, F (x, η)
          ∂homogeneousPathMeasure (Measure.dirac x) K
          ∂K (n, 0) := by rw [hKh]
    _ = ∫⁻ η, F (η 1, pathShift 1 η)
          ∂homogeneousPathMeasure
            (Measure.dirac (n, 0)) K := hRight.symm
    _ = ∫⁻ η, G (timedExtinctionTime η)
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta n := by
          change
            (∫⁻ η, F (η 1, pathShift 1 η)
              ∂homogeneousPathMeasure
                (Measure.dirac (n, 0)) K) =
              ∫⁻ η, G (timedExtinctionTime η)
                ∂homogeneousPathMeasure
                  (Measure.dirac (n, 0)) K
          congr 1
          funext η
          simp only [F]
          exact congrArg G
            (timedExtinctionTime_eq_first_add_shift η).symm

/-- First-step decomposition with the sampled holding time placed
inside the integral, after the extinction time of the fresh tail. -/
lemma singleSpeciesTimedPath_first_extinction_lintegral
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (m : Nat) (hm : 0 < m)
    (G : Real × ENNReal → ENNReal) (hG : Measurable G) :
    ∫⁻ ω,
        G ((ω 1).2,
          timedExtinctionTime (pathShift 1 ω))
      ∂singleSpeciesTimedPathMeasure
        v params i hDelta m =
      ∫⁻ n, ∫⁻ η, ∫⁻ h,
        G (h, timedExtinctionTime η)
          ∂expMeasure (singleSpeciesTotalRate params i m)
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta n
          ∂singleSpeciesJumpMeasure v params i m := by
  let K := singleSpeciesTimedKernel v params i
  haveI : IsMarkovKernel K :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  have hInitialRate :
      0 < singleSpeciesTotalRate params i m :=
    singleSpeciesTotalRate_pos params i hDelta m hm
  letI : IsProbabilityMeasure
      (expMeasure (singleSpeciesTotalRate params i m)) :=
    isProbabilityMeasure_expMeasure hInitialRate
  let F :
      (Nat × Real) × (Nat → Nat × Real) → ENNReal :=
    fun q => G (q.1.2, timedExtinctionTime q.2)
  have hF : Measurable F := by
    apply hG.comp
    exact (measurable_snd.comp measurable_fst).prod
      (measurable_timedExtinctionTime.comp measurable_snd)
  have hfirst :=
    homogeneousPathMeasure_first_shift_lintegral
      K (m, 0) F hF
  have hirrel :
      ∀ z : Nat × Real,
        (∫⁻ η, F (z, η)
          ∂homogeneousPathMeasure (Measure.dirac z) K) =
        ∫⁻ η, F (z, η)
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta z.1 := by
    intro z
    let Gz : ENNReal → ENNReal :=
      fun t => G (z.2, t)
    have hGz : Measurable Gz := by
      apply hG.comp
      exact
        (show Measurable
            (fun t : ENNReal => (z.2, t)) from
          measurable_const.prodMk measurable_id)
    simpa only [F, Gz,
      singleSpeciesTimedPathMeasureFrom] using
      singleSpeciesTimedPath_lintegral_extinction_initial_irrel
        v params i hDelta z.1 z.2 Gz hGz
  calc
    ∫⁻ ω,
        G ((ω 1).2,
          timedExtinctionTime (pathShift 1 ω))
      ∂singleSpeciesTimedPathMeasure
        v params i hDelta m =
      ∫⁻ ω, F (ω 1, pathShift 1 ω)
        ∂homogeneousPathMeasure
          (Measure.dirac (m, 0)) K := by rfl
    _ = ∫⁻ z, ∫⁻ η, F (z, η)
          ∂homogeneousPathMeasure (Measure.dirac z) K
          ∂K (m, 0) := hfirst
    _ = ∫⁻ z, ∫⁻ η, F (z, η)
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta z.1
          ∂K (m, 0) := by
          congr 1
          funext z
          exact hirrel z
    _ = ∫⁻ z, ∫⁻ η, F (z, η)
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta z.1
          ∂singleSpeciesTimedStep v params i m := by
          rw [show K (m, 0) =
            singleSpeciesTimedStep v params i m by rfl]
    _ = ∫⁻ z, ∫⁻ η, F (z, η)
          ∂singleSpeciesTimedPathMeasure
            v params i hDelta z.1
          ∂(singleSpeciesJumpMeasure v params i m).prod
            (expMeasure
              (singleSpeciesTotalRate params i m)) := by
          rw [singleSpeciesTimedStep, if_neg hm.ne']
    _ = ∫⁻ n, ∫⁻ h, ∫⁻ η,
          G (h, timedExtinctionTime η)
            ∂singleSpeciesTimedPathMeasure
              v params i hDelta n
            ∂expMeasure
              (singleSpeciesTotalRate params i m)
            ∂singleSpeciesJumpMeasure v params i m := by
          let H : Nat × Real → ENNReal :=
            fun z => ∫⁻ η,
              G (z.2, timedExtinctionTime η)
                ∂singleSpeciesTimedPathMeasure
                  v params i hDelta z.1
          have hH : Measurable H := by
            apply measurable_from_prod_countable_right
            intro n
            haveI : IsProbabilityMeasure
                (singleSpeciesTimedPathMeasure
                  v params i hDelta n) := by
              simp only [singleSpeciesTimedPathMeasure,
                homogeneousPathMeasure]
              infer_instance
            change Measurable
              (fun h : Real => ∫⁻ η,
                G (h, timedExtinctionTime η)
                  ∂singleSpeciesTimedPathMeasure
                    v params i hDelta n)
            apply Measurable.lintegral_prod_right
            apply hG.comp
            exact
              (show Measurable
                  (fun q :
                    Real × (Nat → Nat × Real) =>
                      (q.1, timedExtinctionTime q.2)) from
                measurable_fst.prodMk
                  (measurable_timedExtinctionTime.comp
                    measurable_snd))
          rw [MeasureTheory.lintegral_prod H hH.aemeasurable]
    _ = ∫⁻ n, ∫⁻ η, ∫⁻ h,
          G (h, timedExtinctionTime η)
            ∂expMeasure
              (singleSpeciesTotalRate params i m)
            ∂singleSpeciesTimedPathMeasure
              v params i hDelta n
            ∂singleSpeciesJumpMeasure v params i m := by
          congr 1
          funext n
          let E :=
            expMeasure
              (singleSpeciesTotalRate params i m)
          let P :=
            singleSpeciesTimedPathMeasure
              v params i hDelta n
          have hRate :
              0 < singleSpeciesTotalRate params i m :=
            singleSpeciesTotalRate_pos
              params i hDelta m hm
          haveI : IsProbabilityMeasure E :=
            isProbabilityMeasure_expMeasure hRate
          haveI : IsProbabilityMeasure P := by
            simp only [P, singleSpeciesTimedPathMeasure,
              homogeneousPathMeasure]
            infer_instance
          let Q : Real × (Nat → Nat × Real) → ENNReal :=
            fun q => G (q.1, timedExtinctionTime q.2)
          have hQ : Measurable Q := by
            apply hG.comp
            exact
              (show Measurable
                  (fun q :
                    Real × (Nat → Nat × Real) =>
                      (q.1, timedExtinctionTime q.2)) from
                measurable_fst.prodMk
                  (measurable_timedExtinctionTime.comp
                    measurable_snd))
          calc
            (∫⁻ h, ∫⁻ η,
                G (h, timedExtinctionTime η) ∂P ∂E) =
              ∫⁻ q, Q q ∂E.prod P := by
                rw [MeasureTheory.lintegral_prod Q
                  hQ.aemeasurable]
            _ = ∫⁻ η, ∫⁻ h,
                G (h, timedExtinctionTime η) ∂E ∂P := by
                exact MeasureTheory.lintegral_prod_symm'
                  Q hQ

/-! ## Extinction-time convolution law -/

/-- Kernel of fresh timed paths indexed only by the current count. -/
noncomputable def singleSpeciesTimedPathKernel
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    Kernel Nat (Nat → Nat × Real) := by
  letI := singleSpeciesTimedKernel_isMarkov
    v params i hDelta
  exact (homogeneousPathKernel
      (singleSpeciesTimedKernel v params i)).comap
    (fun n => (n, 0))
    (measurable_id.prodMk measurable_const)

lemma singleSpeciesTimedPathKernel_apply
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) :
    singleSpeciesTimedPathKernel
        v params i hDelta n =
      singleSpeciesTimedPathMeasure
        v params i hDelta n := by
  letI := singleSpeciesTimedKernel_isMarkov
    v params i hDelta
  rw [singleSpeciesTimedPathKernel, Kernel.comap_apply,
    homogeneousPathKernel_apply]
  rfl

instance singleSpeciesTimedPathKernel_isMarkov
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    IsMarkovKernel
      (singleSpeciesTimedPathKernel
        v params i hDelta) := by
  refine ⟨fun n => ?_⟩
  rw [singleSpeciesTimedPathKernel_apply]
  simp only [singleSpeciesTimedPathMeasure,
    homogeneousPathMeasure]
  infer_instance

/-- Extinction-time distribution of one isolated species. -/
noncomputable def singleSpeciesExtinctionTimeKernel
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    Kernel Nat ENNReal :=
  (singleSpeciesTimedPathKernel
      v params i hDelta).map
    timedExtinctionTime

instance singleSpeciesExtinctionTimeKernel_isMarkov
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    IsMarkovKernel
      (singleSpeciesExtinctionTimeKernel
        v params i hDelta) := by
  refine ⟨fun n => ?_⟩
  rw [singleSpeciesExtinctionTimeKernel,
    Kernel.map_apply _ measurable_timedExtinctionTime]
  exact Measure.isProbabilityMeasure_map
    measurable_timedExtinctionTime.aemeasurable

lemma singleSpeciesExtinctionTimeKernel_apply
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) :
    singleSpeciesExtinctionTimeKernel
        v params i hDelta n =
      (singleSpeciesTimedPathMeasure
        v params i hDelta n).map
          timedExtinctionTime := by
  rw [singleSpeciesExtinctionTimeKernel,
    Kernel.map_apply _ measurable_timedExtinctionTime,
    singleSpeciesTimedPathKernel_apply]

/-- Distribution of the extinction time after sampling the next
embedded count, but before adding the current exponential holding
time. -/
noncomputable def singleSpeciesContinuationTimeMeasure
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) :
    Measure ENNReal :=
  (singleSpeciesJumpMeasure v params i m).bind
    (singleSpeciesExtinctionTimeKernel
      v params i hDelta)

instance singleSpeciesContinuationTimeMeasure_isProbability
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) :
    IsProbabilityMeasure
      (singleSpeciesContinuationTimeMeasure
        v params i hDelta m) := by
  constructor
  rw [singleSpeciesContinuationTimeMeasure,
    Measure.bind_apply MeasurableSet.univ
      (Kernel.measurable _).aemeasurable]
  simp

/-- At a positive count, the extinction-time distribution is the
convolution of the current exponential holding time with the
continuation-time distribution. -/
theorem singleSpecies_extinctionTime_convolution
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (m : Nat) (hm : 0 < m) :
    (singleSpeciesTimedPathMeasure
        v params i hDelta m).map
          timedExtinctionTime =
      ((expMeasure
          (singleSpeciesTotalRate params i m)).prod
        (singleSpeciesContinuationTimeMeasure
          v params i hDelta m)).map
        (fun q => ENNReal.ofReal q.1 + q.2) := by
  let P :=
    singleSpeciesTimedPathMeasure
      v params i hDelta m
  let E :=
    expMeasure
      (singleSpeciesTotalRate params i m)
  let C :=
    singleSpeciesContinuationTimeMeasure
      v params i hDelta m
  have hRate :
      0 < singleSpeciesTotalRate params i m :=
    singleSpeciesTotalRate_pos
      params i hDelta m hm
  haveI : IsProbabilityMeasure E :=
    isProbabilityMeasure_expMeasure hRate
  haveI : IsProbabilityMeasure C :=
    singleSpeciesContinuationTimeMeasure_isProbability
      v params i hDelta m
  have hsum :
      Measurable
        (fun q : Real × ENNReal =>
          ENNReal.ofReal q.1 + q.2) := by
    exact (ENNReal.measurable_ofReal.comp measurable_fst).add
      measurable_snd
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply measurable_timedExtinctionTime hS,
    Measure.map_apply hsum hS]
  let I : ENNReal → ENNReal :=
    Set.indicator S (fun _ => 1)
  have hI : Measurable I :=
    measurable_const.indicator hS
  have hleft :
      P (timedExtinctionTime ⁻¹' S) =
        ∫⁻ ω, I (timedExtinctionTime ω) ∂P := by
    rw [← lintegral_indicator_one
      (hS.preimage measurable_timedExtinctionTime)]
    congr 1
  have hright :
      E.prod C
          ((fun q : Real × ENNReal =>
            ENNReal.ofReal q.1 + q.2) ⁻¹' S) =
        ∫⁻ t, ∫⁻ h,
          I (ENNReal.ofReal h + t) ∂E ∂C := by
    rw [← lintegral_indicator_one
      (hS.preimage hsum)]
    rw [MeasureTheory.lintegral_prod_symm]
    · congr 1
    · exact (measurable_const.indicator
        (hS.preimage hsum)).aemeasurable
  rw [hleft, hright]
  have hsplit :
      ∀ ω : Nat → Nat × Real,
        I (timedExtinctionTime ω) =
          I (ENNReal.ofReal (ω 1).2 +
            timedExtinctionTime (pathShift 1 ω)) := by
    intro ω
    rw [timedExtinctionTime_eq_first_add_shift]
    rfl
  rw [lintegral_congr hsplit]
  let G : Real × ENNReal → ENNReal :=
    fun q => I (ENNReal.ofReal q.1 + q.2)
  have hG : Measurable G := by
    apply hI.comp
    exact (ENNReal.measurable_ofReal.comp measurable_fst).add
      measurable_snd
  rw [singleSpeciesTimedPath_first_extinction_lintegral
    v params i hDelta m hm G hG]
  simp only [G]
  dsimp only [C, singleSpeciesContinuationTimeMeasure]
  rw [Measure.lintegral_bind
    (Kernel.measurable _).aemeasurable (by
      apply Measurable.aemeasurable
      apply Measurable.lintegral_prod_left
      apply hI.comp
      exact (ENNReal.measurable_ofReal.comp measurable_fst).add
        measurable_snd)]
  congr 1
  funext n
  rw [singleSpeciesExtinctionTimeKernel_apply]
  rw [MeasureTheory.lintegral_map]
  · apply Measurable.lintegral_prod_left
    apply hI.comp
    exact (ENNReal.measurable_ofReal.comp measurable_fst).add
      measurable_snd
  · exact measurable_timedExtinctionTime

lemma expRace_ennreal_offset_identity
    {r₀ r₁ : Real} {a b : ENNReal}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (expMeasure r₀).prod (expMeasure r₁)
        {z | ENNReal.ofReal z.1 + a <
          ENNReal.ofReal z.2 + b} =
      ENNReal.ofReal (r₀ / (r₀ + r₁)) *
          expMeasure r₁
            {x | a < ENNReal.ofReal x + b} +
        ENNReal.ofReal (r₁ / (r₀ + r₁)) *
          expMeasure r₀
            {x | ENNReal.ofReal x + a < b} := by
  letI : IsProbabilityMeasure (expMeasure r₀) :=
    isProbabilityMeasure_expMeasure hr₀
  letI : IsProbabilityMeasure (expMeasure r₁) :=
    isProbabilityMeasure_expMeasure hr₁
  have hleft :
      (expMeasure r₀).prod (expMeasure r₁)
          {z | ENNReal.ofReal z.1 + a <
            ENNReal.ofReal z.2 + b} =
        (expMeasure r₀).prod (expMeasure r₁)
          {z | z.1 + a.toReal <
            z.2 + b.toReal} := by
    apply measure_congr
    have hp : MeasurableSet
        {z : Real × Real |
          ((ENNReal.ofReal z.1 + a <
              ENNReal.ofReal z.2 + b) ↔
            (z.1 + a.toReal <
              z.2 + b.toReal))} := by
      measurability
    have hiff :
        ∀ᵐ z ∂(expMeasure r₀).prod (expMeasure r₁),
          ((ENNReal.ofReal z.1 + a <
              ENNReal.ofReal z.2 + b) ↔
            (z.1 + a.toReal <
              z.2 + b.toReal)) := by
      apply (Measure.ae_prod_iff_ae_ae hp).2
      filter_upwards [expMeasure_ae_nonneg hr₀] with x hx
      have hx' : 0 ≤ x := by simpa using hx
      filter_upwards [expMeasure_ae_nonneg hr₁] with y hy
      have hy' : 0 ≤ y := by simpa using hy
      rw [← ENNReal.toReal_lt_toReal
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.ofReal_ne_top, ha⟩)
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.ofReal_ne_top, hb⟩),
        ENNReal.toReal_add ENNReal.ofReal_ne_top ha,
        ENNReal.toReal_add ENNReal.ofReal_ne_top hb,
        ENNReal.toReal_ofReal hx',
        ENNReal.toReal_ofReal hy']
    filter_upwards [hiff] with z hz
    exact propext hz
  have hright1 :
      expMeasure r₁
          {x | a < ENNReal.ofReal x + b} =
        expMeasure r₁
          {x | a.toReal < x + b.toReal} := by
    apply measure_congr
    filter_upwards [expMeasure_ae_nonneg hr₁] with x hx
    have hx' : 0 ≤ x := by simpa using hx
    have hiff :
        (a < ENNReal.ofReal x + b) ↔
          a.toReal < x + b.toReal := by
      rw [← ENNReal.toReal_lt_toReal ha
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.ofReal_ne_top, hb⟩),
        ENNReal.toReal_add ENNReal.ofReal_ne_top hb,
        ENNReal.toReal_ofReal hx']
    exact propext hiff
  have hright0 :
      expMeasure r₀
          {x | ENNReal.ofReal x + a < b} =
        expMeasure r₀
          {x | x + a.toReal < b.toReal} := by
    apply measure_congr
    filter_upwards [expMeasure_ae_nonneg hr₀] with x hx
    have hx' : 0 ≤ x := by simpa using hx
    have hiff :
        (ENNReal.ofReal x + a < b) ↔
          x + a.toReal < b.toReal := by
      rw [← ENNReal.toReal_lt_toReal
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.ofReal_ne_top, ha⟩) hb,
        ENNReal.toReal_add ENNReal.ofReal_ne_top ha,
        ENNReal.toReal_ofReal hx']
    exact propext hiff
  rw [hleft, hright1, hright0]
  exact expRace_offset_identity hr₀ hr₁
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma singleSpeciesExtinctionTimeKernel_top
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i)
    (n : Nat) :
    singleSpeciesExtinctionTimeKernel
        v params i hDelta n {⊤} = 0 := by
  rw [singleSpeciesExtinctionTimeKernel_apply,
    Measure.map_apply measurable_timedExtinctionTime
      (measurableSet_singleton ⊤)]
  have hae :=
    singleSpecies_timedExtinctionTime_ne_top_ae_of_gamma
      v params i hDelta hGamma n
  have hzero := ae_iff.mp hae
  rw [show timedExtinctionTime ⁻¹' ({⊤} : Set ENNReal) =
      {ω | timedExtinctionTime ω = ⊤} by ext ω; simp]
  simpa only [not_ne_iff] using hzero

lemma singleSpeciesContinuationTime_ne_top_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i)
    (m : Nat) :
    ∀ᵐ t ∂singleSpeciesContinuationTimeMeasure
        v params i hDelta m,
      t ≠ ⊤ := by
  rw [ae_iff]
  have hset :
      {t : ENNReal | ¬t ≠ ⊤} = {⊤} := by
    ext t
    simp
  rw [hset, singleSpeciesContinuationTimeMeasure,
    Measure.bind_apply (measurableSet_singleton ⊤)
      (Kernel.measurable _).aemeasurable]
  simp_rw [singleSpeciesExtinctionTimeKernel_top
    v params i hDelta hGamma]
  exact lintegral_zero

lemma lintegral_swap
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (F : α × β → ENNReal) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ) =
      ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂ν := by
  calc
    (∫⁻ x, ∫⁻ y, F (x, y) ∂ν ∂μ) =
        ∫⁻ z, F z ∂μ.prod ν := by
          rw [MeasureTheory.lintegral_prod F hF.aemeasurable]
    _ = ∫⁻ y, ∫⁻ x, F (x, y) ∂μ ∂ν :=
      MeasureTheory.lintegral_prod_symm' F hF

lemma lintegral_four_reorder
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μα : Measure α) (μβ : Measure β)
    (μγ : Measure γ) (μδ : Measure δ)
    [SFinite μα] [SFinite μβ]
    [SFinite μγ] [SFinite μδ]
    (F : (α × β) × (γ × δ) → ENNReal)
    (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, ∫⁻ w,
        F ((x, y), (z, w)) ∂μδ ∂μγ ∂μβ ∂μα) =
      ∫⁻ y, ∫⁻ w, ∫⁻ x, ∫⁻ z,
        F ((x, y), (z, w)) ∂μγ ∂μα ∂μδ ∂μβ := by
  have hSwapZW :
      ∀ x y,
        (∫⁻ z, ∫⁻ w,
            F ((x, y), (z, w)) ∂μδ ∂μγ) =
          ∫⁻ w, ∫⁻ z,
            F ((x, y), (z, w)) ∂μγ ∂μδ := by
    intro x y
    exact lintegral_swap μγ μδ
      (fun q => F ((x, y), (q.1, q.2)))
      (hF.comp (by fun_prop))
  let H : α × β → ENNReal :=
    fun q => ∫⁻ w, ∫⁻ z,
      F ((q.1, q.2), (z, w)) ∂μγ ∂μδ
  have hH : Measurable H := by
    apply Measurable.lintegral_prod_right
    apply Measurable.lintegral_prod_right
    exact hF.comp (by fun_prop)
  have hSwapXY :
      (∫⁻ x, ∫⁻ y, H (x, y) ∂μβ ∂μα) =
        ∫⁻ y, ∫⁻ x, H (x, y) ∂μα ∂μβ :=
    lintegral_swap μα μβ H hH
  have hSwapXW :
      ∀ y,
        (∫⁻ x, ∫⁻ w, ∫⁻ z,
            F ((x, y), (z, w)) ∂μγ ∂μδ ∂μα) =
          ∫⁻ w, ∫⁻ x, ∫⁻ z,
            F ((x, y), (z, w)) ∂μγ ∂μα ∂μδ := by
    intro y
    let Q : α × δ → ENNReal :=
      fun q => ∫⁻ z,
        F ((q.1, y), (z, q.2)) ∂μγ
    have hQ : Measurable Q := by
      apply Measurable.lintegral_prod_right
      exact hF.comp (by fun_prop)
    exact lintegral_swap μα μδ Q hQ
  calc
    (∫⁻ x, ∫⁻ y, ∫⁻ z, ∫⁻ w,
        F ((x, y), (z, w)) ∂μδ ∂μγ ∂μβ ∂μα) =
      ∫⁻ x, ∫⁻ y, ∫⁻ w, ∫⁻ z,
        F ((x, y), (z, w)) ∂μγ ∂μδ ∂μβ ∂μα := by
          congr 1
          funext x
          congr 1
          funext y
          exact hSwapZW x y
    _ = ∫⁻ y, ∫⁻ x, ∫⁻ w, ∫⁻ z,
        F ((x, y), (z, w)) ∂μγ ∂μδ ∂μα ∂μβ := by
          simpa only [H] using hSwapXY
    _ = ∫⁻ y, ∫⁻ w, ∫⁻ x, ∫⁻ z,
        F ((x, y), (z, w)) ∂μγ ∂μα ∂μδ ∂μβ := by
          congr 1
          funext y
          exact hSwapXW y

/-! ## Superposition of two extinction-time laws -/

/-- Indicator of the event that the first time is strictly smaller
than the second. -/
noncomputable def ennrealRaceIndicator
    (q : ENNReal × ENNReal) : ENNReal :=
  Set.indicator {z : ENNReal × ENNReal | z.1 < z.2}
    (fun _ => 1) q

lemma measurable_ennrealRaceIndicator :
    Measurable ennrealRaceIndicator := by
  exact measurable_const.indicator (by measurability)

lemma raceMeasure_eq_lintegral
    (μ ν : Measure ENNReal) [SFinite μ] [SFinite ν] :
    μ.prod ν {q | q.1 < q.2} =
      ∫⁻ x, ∫⁻ y, ennrealRaceIndicator (x, y) ∂ν ∂μ := by
  rw [← MeasureTheory.lintegral_indicator_one
    (show MeasurableSet
      {q : ENNReal × ENNReal | q.1 < q.2} by measurability)]
  change (∫⁻ q, ennrealRaceIndicator q ∂μ.prod ν) = _
  rw [MeasureTheory.lintegral_prod
    ennrealRaceIndicator
    measurable_ennrealRaceIndicator.aemeasurable]

/-- Add a real exponential holding time to an `ENNReal` continuation
time. -/
noncomputable def addHoldingTime
    (q : Real × ENNReal) : ENNReal :=
  ENNReal.ofReal q.1 + q.2

lemma measurable_addHoldingTime :
    Measurable addHoldingTime := by
  exact (ENNReal.measurable_ofReal.comp measurable_fst).add
    measurable_snd

/-- Race against a time obtained by adding an exponential holding time
to an independent continuation time. -/
lemma continuation_convolution_race_right
    (C₀ : Measure ENNReal) (E₁ : Measure Real)
    (C₁ : Measure ENNReal)
    [SFinite C₀] [SFinite E₁] [SFinite C₁] :
    C₀.prod ((E₁.prod C₁).map addHoldingTime)
        {q | q.1 < q.2} =
      ∫⁻ a, ∫⁻ b,
        E₁ {h | a < ENNReal.ofReal h + b} ∂C₁ ∂C₀ := by
  rw [raceMeasure_eq_lintegral]
  congr 1
  funext a
  have hIa :
      Measurable
        (fun y : ENNReal =>
          ennrealRaceIndicator (a, y)) := by
    exact measurable_ennrealRaceIndicator.comp
      (measurable_const.prodMk measurable_id)
  rw [MeasureTheory.lintegral_map hIa
    measurable_addHoldingTime]
  rw [MeasureTheory.lintegral_prod
      (fun q : Real × ENNReal =>
        ennrealRaceIndicator (a, addHoldingTime q))
      (measurable_ennrealRaceIndicator.comp
        (measurable_const.prodMk measurable_addHoldingTime)).aemeasurable]
  change (∫⁻ h, ∫⁻ b,
      ennrealRaceIndicator
        (a, ENNReal.ofReal h + b) ∂C₁ ∂E₁) = _
  rw [lintegral_swap E₁ C₁
    (fun q : Real × ENNReal =>
      ennrealRaceIndicator
        (a, ENNReal.ofReal q.1 + q.2))
    (measurable_ennrealRaceIndicator.comp (by fun_prop))]
  congr 1
  funext b
  rw [← MeasureTheory.lintegral_indicator_one
    (show MeasurableSet
      {h : Real | a < ENNReal.ofReal h + b} by
        measurability)]
  rfl

/-- A time obtained by adding an exponential holding time to a
continuation time races against a second continuation time. -/
lemma convolution_continuation_race_left
    (E₀ : Measure Real) (C₀ : Measure ENNReal)
    (C₁ : Measure ENNReal)
    [SFinite E₀] [SFinite C₀] [SFinite C₁] :
    ((E₀.prod C₀).map addHoldingTime).prod C₁
        {q | q.1 < q.2} =
      ∫⁻ a, ∫⁻ b,
        E₀ {h | ENNReal.ofReal h + a < b} ∂C₁ ∂C₀ := by
  rw [raceMeasure_eq_lintegral]
  have hOuter :
      Measurable
        (fun x : ENNReal =>
          ∫⁻ y,
            ennrealRaceIndicator (x, y) ∂C₁) := by
    apply Measurable.lintegral_prod_right
    exact measurable_ennrealRaceIndicator
  rw [MeasureTheory.lintegral_map hOuter
    measurable_addHoldingTime]
  have hInnerOuter :
      Measurable
        (fun q : Real × ENNReal =>
          ∫⁻ b,
            ennrealRaceIndicator
              (addHoldingTime q, b) ∂C₁) := by
    apply Measurable.lintegral_prod_right
    exact measurable_ennrealRaceIndicator.comp
      ((measurable_addHoldingTime.comp measurable_fst).prodMk
        measurable_snd)
  rw [MeasureTheory.lintegral_prod
    (fun q : Real × ENNReal =>
      ∫⁻ b,
        ennrealRaceIndicator
          (addHoldingTime q, b) ∂C₁)
    hInnerOuter.aemeasurable]
  change (∫⁻ h, ∫⁻ a, ∫⁻ b,
      ennrealRaceIndicator
        (ENNReal.ofReal h + a, b) ∂C₁ ∂C₀ ∂E₀) = _
  let H : Real × ENNReal → ENNReal :=
    fun q => ∫⁻ b,
      ennrealRaceIndicator
        (ENNReal.ofReal q.1 + q.2, b) ∂C₁
  have hH : Measurable H := by
    apply Measurable.lintegral_prod_right
    exact measurable_ennrealRaceIndicator.comp (by fun_prop)
  rw [lintegral_swap E₀ C₀ H hH]
  congr 1
  funext a
  rw [lintegral_swap E₀ C₁
    (fun q : Real × ENNReal =>
      ennrealRaceIndicator
        (ENNReal.ofReal q.1 + a, q.2))
    (measurable_ennrealRaceIndicator.comp (by fun_prop))]
  congr 1
  funext b
  rw [← MeasureTheory.lintegral_indicator_one
    (show MeasurableSet
      {h : Real | ENNReal.ofReal h + a < b} by
        measurability)]
  rfl

/-- Expand a race between two exponential-plus-continuation times into
the four independent integrations used by the memoryless-clock
calculation. -/
lemma convolution_convolution_race_lintegral
    (E₀ E₁ : Measure Real) (C₀ C₁ : Measure ENNReal)
    [SFinite E₀] [SFinite E₁]
    [SFinite C₀] [SFinite C₁] :
    ((E₀.prod C₀).map addHoldingTime).prod
        ((E₁.prod C₁).map addHoldingTime)
        {q | q.1 < q.2} =
      ∫⁻ h₀, ∫⁻ a, ∫⁻ h₁, ∫⁻ b,
        ennrealRaceIndicator
          (ENNReal.ofReal h₀ + a,
            ENNReal.ofReal h₁ + b)
          ∂C₁ ∂E₁ ∂C₀ ∂E₀ := by
  rw [raceMeasure_eq_lintegral]
  have hInner :
      Measurable
        (fun x : ENNReal =>
          ∫⁻ y, ennrealRaceIndicator (x, y)
            ∂(E₁.prod C₁).map addHoldingTime) := by
    apply Measurable.lintegral_prod_right
    exact measurable_ennrealRaceIndicator
  rw [MeasureTheory.lintegral_map hInner
    measurable_addHoldingTime]
  have hInnerMap :
      ∀ q₀ : Real × ENNReal,
        (∫⁻ y, ennrealRaceIndicator
            (addHoldingTime q₀, y)
            ∂(E₁.prod C₁).map addHoldingTime) =
          ∫⁻ q₁, ennrealRaceIndicator
            (addHoldingTime q₀, addHoldingTime q₁)
            ∂E₁.prod C₁ := by
    intro q₀
    have hI :
        Measurable
          (fun y : ENNReal =>
            ennrealRaceIndicator
              (addHoldingTime q₀, y)) := by
      exact measurable_ennrealRaceIndicator.comp
        (measurable_const.prodMk measurable_id)
    exact MeasureTheory.lintegral_map hI
      measurable_addHoldingTime
  simp_rw [hInnerMap]
  have hOuterProd :
      Measurable
        (fun q₀ : Real × ENNReal =>
          ∫⁻ q₁, ennrealRaceIndicator
            (addHoldingTime q₀, addHoldingTime q₁)
            ∂E₁.prod C₁) := by
    apply Measurable.lintegral_prod_right
    exact measurable_ennrealRaceIndicator.comp
      ((measurable_addHoldingTime.comp measurable_fst).prodMk
        (measurable_addHoldingTime.comp measurable_snd))
  rw [MeasureTheory.lintegral_prod _ hOuterProd.aemeasurable]
  congr 1
  funext h₀
  congr 1
  funext a
  rw [MeasureTheory.lintegral_prod
    (fun q₁ : Real × ENNReal =>
      ennrealRaceIndicator
        (addHoldingTime (h₀, a),
          addHoldingTime q₁))
    (measurable_ennrealRaceIndicator.comp
      (measurable_const.prodMk
        measurable_addHoldingTime)).aemeasurable]
  rfl

/-- Memoryless superposition identity for two independent
exponential-plus-continuation extinction times. -/
theorem exponential_convolution_race_identity
    {r₀ r₁ : Real} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (C₀ C₁ : Measure ENNReal)
    [IsProbabilityMeasure C₀] [IsProbabilityMeasure C₁]
    (hC₀ : ∀ᵐ a ∂C₀, a ≠ ⊤)
    (hC₁ : ∀ᵐ b ∂C₁, b ≠ ⊤) :
    (((expMeasure r₀).prod C₀).map addHoldingTime).prod
        (((expMeasure r₁).prod C₁).map addHoldingTime)
        {q | q.1 < q.2} =
      ENNReal.ofReal (r₀ / (r₀ + r₁)) *
          C₀.prod
            (((expMeasure r₁).prod C₁).map addHoldingTime)
            {q | q.1 < q.2} +
        ENNReal.ofReal (r₁ / (r₀ + r₁)) *
          (((expMeasure r₀).prod C₀).map addHoldingTime).prod
            C₁ {q | q.1 < q.2} := by
  let E₀ := expMeasure r₀
  let E₁ := expMeasure r₁
  let p₀ := ENNReal.ofReal (r₀ / (r₀ + r₁))
  let p₁ := ENNReal.ofReal (r₁ / (r₀ + r₁))
  haveI : IsProbabilityMeasure E₀ :=
    isProbabilityMeasure_expMeasure hr₀
  haveI : IsProbabilityMeasure E₁ :=
    isProbabilityMeasure_expMeasure hr₁
  let F : (Real × ENNReal) × (Real × ENNReal) → ENNReal :=
    fun q => ennrealRaceIndicator
      (ENNReal.ofReal q.1.1 + q.1.2,
        ENNReal.ofReal q.2.1 + q.2.2)
  have hF : Measurable F := by
    exact measurable_ennrealRaceIndicator.comp (by fun_prop)
  have hClock :
      ∀ᵐ a ∂C₀, ∀ᵐ b ∂C₁,
        (∫⁻ h₀, ∫⁻ h₁,
          ennrealRaceIndicator
            (ENNReal.ofReal h₀ + a,
              ENNReal.ofReal h₁ + b)
            ∂E₁ ∂E₀) =
          p₀ * E₁
              {h | a < ENNReal.ofReal h + b} +
            p₁ * E₀
              {h | ENNReal.ofReal h + a < b} := by
    filter_upwards [hC₀] with a ha
    filter_upwards [hC₁] with b hb
    calc
      (∫⁻ h₀, ∫⁻ h₁,
          ennrealRaceIndicator
            (ENNReal.ofReal h₀ + a,
              ENNReal.ofReal h₁ + b)
            ∂E₁ ∂E₀) =
        E₀.prod E₁
          {z | ENNReal.ofReal z.1 + a <
            ENNReal.ofReal z.2 + b} := by
              rw [← MeasureTheory.lintegral_indicator_one
                (show MeasurableSet
                  {z : Real × Real |
                    ENNReal.ofReal z.1 + a <
                      ENNReal.ofReal z.2 + b} by
                    measurability)]
              rw [MeasureTheory.lintegral_prod _ (by
                apply Measurable.aemeasurable
                exact measurable_const.indicator (by
                  measurability))]
              rfl
      _ = p₀ * E₁
              {h | a < ENNReal.ofReal h + b} +
            p₁ * E₀
              {h | ENNReal.ofReal h + a < b} := by
          simpa only [E₀, E₁, p₀, p₁] using
            expRace_ennreal_offset_identity
              hr₀ hr₁ ha hb
  let f : ENNReal × ENNReal → ENNReal :=
    fun q => E₁
      {h | q.1 < ENNReal.ofReal h + q.2}
  let g : ENNReal × ENNReal → ENNReal :=
    fun q => E₀
      {h | ENNReal.ofReal h + q.1 < q.2}
  have hf : Measurable f := by
    let S : Set ((ENNReal × ENNReal) × Real) :=
      {z | z.1.1 < ENNReal.ofReal z.2 + z.1.2}
    have hS : MeasurableSet S := by
      dsimp only [S]
      measurability
    change Measurable
      (fun q : ENNReal × ENNReal =>
        E₁ (Prod.mk q ⁻¹' S))
    exact measurable_measure_prodMk_left hS
  have hg : Measurable g := by
    let S : Set ((ENNReal × ENNReal) × Real) :=
      {z | ENNReal.ofReal z.2 + z.1.1 < z.1.2}
    have hS : MeasurableSet S := by
      dsimp only [S]
      measurability
    change Measurable
      (fun q : ENNReal × ENNReal =>
        E₀ (Prod.mk q ⁻¹' S))
    exact measurable_measure_prodMk_left hS
  calc
    (((expMeasure r₀).prod C₀).map addHoldingTime).prod
          (((expMeasure r₁).prod C₁).map addHoldingTime)
          {q | q.1 < q.2} =
        ∫⁻ h₀, ∫⁻ a, ∫⁻ h₁, ∫⁻ b,
          F ((h₀, a), (h₁, b))
            ∂C₁ ∂E₁ ∂C₀ ∂E₀ := by
              simpa only [E₀, E₁, F] using
                convolution_convolution_race_lintegral
                  (expMeasure r₀) (expMeasure r₁) C₀ C₁
    _ = ∫⁻ a, ∫⁻ b, ∫⁻ h₀, ∫⁻ h₁,
          F ((h₀, a), (h₁, b))
            ∂E₁ ∂E₀ ∂C₁ ∂C₀ := by
              exact lintegral_four_reorder
                E₀ C₀ E₁ C₁ F hF
    _ = ∫⁻ a, ∫⁻ b,
          (p₀ * f (a, b) + p₁ * g (a, b))
          ∂C₁ ∂C₀ := by
              apply lintegral_congr_ae
              filter_upwards [hClock] with a ha
              apply lintegral_congr_ae
              filter_upwards [ha] with b hb
              simpa only [F, f, g] using hb
    _ = p₀ * (∫⁻ a, ∫⁻ b, f (a, b) ∂C₁ ∂C₀) +
          p₁ * (∫⁻ a, ∫⁻ b, g (a, b) ∂C₁ ∂C₀) := by
              have hfInner :
                  Measurable
                    (fun a => ∫⁻ b, f (a, b) ∂C₁) :=
                Measurable.lintegral_prod_right hf
              have hgInner :
                  Measurable
                    (fun a => ∫⁻ b, g (a, b) ∂C₁) :=
                Measurable.lintegral_prod_right hg
              have hInner :
                  ∀ a,
                    (∫⁻ b,
                      (p₀ * f (a, b) +
                        p₁ * g (a, b)) ∂C₁) =
                      p₀ * (∫⁻ b, f (a, b) ∂C₁) +
                        p₁ * (∫⁻ b, g (a, b) ∂C₁) := by
                intro a
                have hfa :
                    Measurable
                      (fun b => f (a, b)) := by
                  exact hf.comp
                    (measurable_const.prodMk measurable_id)
                have hga :
                    Measurable
                      (fun b => g (a, b)) := by
                  exact hg.comp
                    (measurable_const.prodMk measurable_id)
                rw [MeasureTheory.lintegral_add_left
                  (hfa.const_mul p₀)
                  _]
                rw [MeasureTheory.lintegral_const_mul
                  p₀ hfa]
                rw [MeasureTheory.lintegral_const_mul
                  p₁ hga]
              simp_rw [hInner]
              rw [MeasureTheory.lintegral_add_left
                (hfInner.const_mul p₀) _]
              rw [MeasureTheory.lintegral_const_mul p₀ hfInner]
              rw [MeasureTheory.lintegral_const_mul p₁ hgInner]
    _ = p₀ *
          C₀.prod
            ((E₁.prod C₁).map addHoldingTime)
              {q | q.1 < q.2} +
        p₁ *
          ((E₀.prod C₀).map addHoldingTime).prod
            C₁ {q | q.1 < q.2} := by
              rw [continuation_convolution_race_right
                C₀ E₁ C₁,
                convolution_continuation_race_left
                  E₀ C₀ C₁]
    _ = ENNReal.ofReal (r₀ / (r₀ + r₁)) *
          C₀.prod
            (((expMeasure r₁).prod C₁).map addHoldingTime)
            {q | q.1 < q.2} +
        ENNReal.ofReal (r₁ / (r₀ + r₁)) *
          (((expMeasure r₀).prod C₀).map addHoldingTime).prod
            C₁ {q | q.1 < q.2} := by
              rfl

lemma independentExtinctionRaceProb_eq_time_laws
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (a b : Nat) :
    independentExtinctionRaceProb v params hDelta a b =
      ((singleSpeciesTimedPathMeasure
          v params false hDelta a).map
            timedExtinctionTime).prod
        ((singleSpeciesTimedPathMeasure
          v params true hDelta b).map
            timedExtinctionTime)
        {q | q.1 < q.2} := by
  let P₀ :=
    singleSpeciesTimedPathMeasure
      v params false hDelta a
  let P₁ :=
    singleSpeciesTimedPathMeasure
      v params true hDelta b
  haveI : IsProbabilityMeasure P₀ := by
    simp only [P₀, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure P₁ := by
    simp only [P₁, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  have hT : Measurable timedExtinctionTime :=
    measurable_timedExtinctionTime
  have hR :
      MeasurableSet
        {q : ENNReal × ENNReal | q.1 < q.2} := by
    measurability
  rw [show (P₀.map timedExtinctionTime).prod
        (P₁.map timedExtinctionTime) =
      (P₀.prod P₁).map
        (Prod.map timedExtinctionTime
          timedExtinctionTime) by
      exact Measure.map_prod_map P₀ P₁ hT hT]
  rw [Measure.map_apply
    (hT.prodMap hT) hR]
  rfl

/-- If species `0` makes the first jump, integration over its
continuation law is integration of the fresh extinction-race
probability over its embedded next-count law. -/
lemma continuation_race_species0_eq_lintegral
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (a b : Nat) :
    (singleSpeciesContinuationTimeMeasure
        v params false hDelta a).prod
      ((singleSpeciesTimedPathMeasure
        v params true hDelta b).map
          timedExtinctionTime)
      {q | q.1 < q.2} =
    ∫⁻ n,
      independentExtinctionRaceProb
        v params hDelta n b
      ∂singleSpeciesJumpMeasure
        v params false a := by
  let J :=
    singleSpeciesJumpMeasure
      v params false a
  let K :=
    singleSpeciesExtinctionTimeKernel
      v params false hDelta
  let M :=
    (singleSpeciesTimedPathMeasure
      v params true hDelta b).map
        timedExtinctionTime
  haveI : IsProbabilityMeasure J := by
    dsimp only [J]
    infer_instance
  haveI : IsMarkovKernel K := by
    dsimp only [K]
    infer_instance
  haveI : IsMarkovKernel
      (singleSpeciesTimedKernel
        v params true) :=
    singleSpeciesTimedKernel_isMarkov
      v params true hDelta
  haveI : IsProbabilityMeasure
      (singleSpeciesTimedPathMeasure
        v params true hDelta b) := by
    simp only [singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure M := by
    dsimp only [M]
    exact Measure.isProbabilityMeasure_map
      measurable_timedExtinctionTime.aemeasurable
  have hH :
      Measurable
        (fun t₀ : ENNReal =>
          ∫⁻ t₁,
            ennrealRaceIndicator (t₀, t₁) ∂M) := by
    apply Measurable.lintegral_prod_right
    exact measurable_ennrealRaceIndicator
  rw [show singleSpeciesContinuationTimeMeasure
      v params false hDelta a = J.bind K by rfl]
  rw [raceMeasure_eq_lintegral]
  rw [Measure.lintegral_bind
    (Kernel.measurable K).aemeasurable
    hH.aemeasurable]
  congr 1
  funext n
  rw [← raceMeasure_eq_lintegral]
  rw [show K n =
      (singleSpeciesTimedPathMeasure
        v params false hDelta n).map
          timedExtinctionTime by
    exact singleSpeciesExtinctionTimeKernel_apply
      v params false hDelta n]
  exact
    (independentExtinctionRaceProb_eq_time_laws
      v params hDelta n b).symm

/-- If species `1` makes the first jump, integration over its
continuation law is integration of the fresh extinction-race
probability over its embedded next-count law. -/
lemma race_continuation_species1_eq_lintegral
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (a b : Nat) :
    ((singleSpeciesTimedPathMeasure
        v params false hDelta a).map
          timedExtinctionTime).prod
      (singleSpeciesContinuationTimeMeasure
        v params true hDelta b)
      {q | q.1 < q.2} =
    ∫⁻ n,
      independentExtinctionRaceProb
        v params hDelta a n
      ∂singleSpeciesJumpMeasure
        v params true b := by
  let J :=
    singleSpeciesJumpMeasure
      v params true b
  let K :=
    singleSpeciesExtinctionTimeKernel
      v params true hDelta
  let M :=
    (singleSpeciesTimedPathMeasure
      v params false hDelta a).map
        timedExtinctionTime
  haveI : IsProbabilityMeasure J := by
    dsimp only [J]
    infer_instance
  haveI : IsMarkovKernel K := by
    dsimp only [K]
    infer_instance
  haveI : IsMarkovKernel
      (singleSpeciesTimedKernel
        v params false) :=
    singleSpeciesTimedKernel_isMarkov
      v params false hDelta
  haveI : IsProbabilityMeasure
      (singleSpeciesTimedPathMeasure
        v params false hDelta a) := by
    simp only [singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure M := by
    dsimp only [M]
    exact Measure.isProbabilityMeasure_map
      measurable_timedExtinctionTime.aemeasurable
  rw [show singleSpeciesContinuationTimeMeasure
      v params true hDelta b = J.bind K by rfl]
  rw [raceMeasure_eq_lintegral]
  have hInner :
      ∀ t₀ : ENNReal,
        (∫⁻ t₁,
            ennrealRaceIndicator (t₀, t₁)
            ∂J.bind K) =
          ∫⁻ n, ∫⁻ t₁,
            ennrealRaceIndicator (t₀, t₁)
            ∂K n ∂J := by
    intro t₀
    have hI :
        Measurable
          (fun t₁ : ENNReal =>
            ennrealRaceIndicator (t₀, t₁)) := by
      exact measurable_ennrealRaceIndicator.comp
        (measurable_const.prodMk measurable_id)
    exact Measure.lintegral_bind
      (Kernel.measurable K).aemeasurable
      hI.aemeasurable
  simp_rw [hInner]
  let K' : Kernel (ENNReal × Nat) ENNReal :=
    K.comap (fun q => q.2) measurable_snd
  let Q : ENNReal × Nat → ENNReal :=
    fun q => ∫⁻ t₁,
      ennrealRaceIndicator (q.1, t₁)
      ∂K' q
  have hQ : Measurable Q := by
    let H : (ENNReal × Nat) × ENNReal → ENNReal :=
      fun z => ennrealRaceIndicator
        (z.1.1, z.2)
    have hH : Measurable H :=
      measurable_ennrealRaceIndicator.comp (by fun_prop)
    exact Measurable.lintegral_kernel_prod_right'
      (κ := K') hH
  change (∫⁻ t₀, ∫⁻ n,
      Q (t₀, n) ∂J ∂M) = _
  rw [lintegral_swap M J Q hQ]
  congr 1
  funext n
  have hK' :
      ∀ x : ENNReal, K' (x, n) = K n := by
    intro x
    dsimp only [K']
    rw [Kernel.comap_apply]
  dsimp only [Q]
  simp_rw [hK']
  rw [← raceMeasure_eq_lintegral]
  rw [show K n =
      (singleSpeciesTimedPathMeasure
        v params true hDelta n).map
          timedExtinctionTime by
    exact singleSpeciesExtinctionTimeKernel_apply
      v params true hDelta n]
  exact
    (independentExtinctionRaceProb_eq_time_laws
      v params hDelta a n).symm

/-- First-step equation for the race of the two isolated extinction
times.  The coefficients are the probabilities that the corresponding
species supplies the next clock ring. -/
theorem independentExtinctionRaceProb_first_step
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    independentExtinctionRaceProb
        v params hDelta a b =
      ENNReal.ofReal
          (singleSpeciesTotalRate params false a /
            (singleSpeciesTotalRate params false a +
              singleSpeciesTotalRate params true b)) *
        (∫⁻ n,
          independentExtinctionRaceProb
            v params hDelta n b
          ∂singleSpeciesJumpMeasure
            v params false a) +
      ENNReal.ofReal
          (singleSpeciesTotalRate params true b /
            (singleSpeciesTotalRate params false a +
              singleSpeciesTotalRate params true b)) *
        (∫⁻ n,
          independentExtinctionRaceProb
            v params hDelta a n
          ∂singleSpeciesJumpMeasure
            v params true b) := by
  let r₀ := singleSpeciesTotalRate params false a
  let r₁ := singleSpeciesTotalRate params true b
  let C₀ :=
    singleSpeciesContinuationTimeMeasure
      v params false hDelta a
  let C₁ :=
    singleSpeciesContinuationTimeMeasure
      v params true hDelta b
  have hr₀ : 0 < r₀ :=
    singleSpeciesTotalRate_pos
      params false hDelta a ha
  have hr₁ : 0 < r₁ :=
    singleSpeciesTotalRate_pos
      params true hDelta b hb
  haveI : IsProbabilityMeasure C₀ := by
    dsimp only [C₀]
    infer_instance
  haveI : IsProbabilityMeasure C₁ := by
    dsimp only [C₁]
    infer_instance
  have hC₀ : ∀ᵐ t ∂C₀, t ≠ ⊤ := by
    simpa only [C₀, speciesGamma] using
      singleSpeciesContinuationTime_ne_top_ae
        v params false hDelta hGamma0 a
  have hC₁ : ∀ᵐ t ∂C₁, t ≠ ⊤ := by
    simpa only [C₁, speciesGamma] using
      singleSpeciesContinuationTime_ne_top_ae
        v params true hDelta hGamma1 b
  rw [independentExtinctionRaceProb_eq_time_laws]
  rw [singleSpecies_extinctionTime_convolution
      v params false hDelta a ha,
    singleSpecies_extinctionTime_convolution
      v params true hDelta b hb]
  change
    (((expMeasure r₀).prod C₀).map
        (fun q => ENNReal.ofReal q.1 + q.2)).prod
      (((expMeasure r₁).prod C₁).map
        (fun q => ENNReal.ofReal q.1 + q.2))
      {q | q.1 < q.2} = _
  rw [show (fun q : Real × ENNReal =>
      ENNReal.ofReal q.1 + q.2) = addHoldingTime from rfl]
  rw [exponential_convolution_race_identity
    hr₀ hr₁ C₀ C₁ hC₀ hC₁]
  rw [show C₀.prod
        (((expMeasure r₁).prod C₁).map addHoldingTime)
        {q | q.1 < q.2} =
      ∫⁻ n,
        independentExtinctionRaceProb
          v params hDelta n b
        ∂singleSpeciesJumpMeasure
          v params false a by
    rw [show ((expMeasure r₁).prod C₁).map
        addHoldingTime =
      (singleSpeciesTimedPathMeasure
          v params true hDelta b).map
        timedExtinctionTime by
      rw [singleSpecies_extinctionTime_convolution
        v params true hDelta b hb]
      rfl]
    exact continuation_race_species0_eq_lintegral
      v params hDelta a b]
  rw [show
      (((expMeasure r₀).prod C₀).map addHoldingTime).prod
          C₁ {q | q.1 < q.2} =
        ∫⁻ n,
          independentExtinctionRaceProb
            v params hDelta a n
          ∂singleSpeciesJumpMeasure
            v params true b by
    rw [show ((expMeasure r₀).prod C₀).map
        addHoldingTime =
      (singleSpeciesTimedPathMeasure
          v params false hDelta a).map
        timedExtinctionTime by
      rw [singleSpecies_extinctionTime_convolution
        v params false hDelta a ha]
      rfl]
    exact race_continuation_species1_eq_lintegral
      v params hDelta a b]

/-- With no interspecific reactions, the two-species embedded kernel
is obtained by superposing the two isolated jump chains. -/
theorem lvKernel_eq_independent_species_mixture
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    lvKernel v params (a, b) =
      ENNReal.ofReal
          (singleSpeciesTotalRate params false a /
            (singleSpeciesTotalRate params false a +
              singleSpeciesTotalRate params true b)) •
        (singleSpeciesJumpMeasure
          v params false a).map (fun n => (n, b)) +
      ENNReal.ofReal
          (singleSpeciesTotalRate params true b /
            (singleSpeciesTotalRate params false a +
              singleSpeciesTotalRate params true b)) •
        (singleSpeciesJumpMeasure
          v params true b).map (fun n => (a, n)) := by
  have hr₀ :
      0 < singleSpeciesTotalRate params false a :=
    singleSpeciesTotalRate_pos
      params false hDelta a ha
  have hr₁ :
      0 < singleSpeciesTotalRate params true b :=
    singleSpeciesTotalRate_pos
      params true hDelta b hb
  have hTotal :
      lvTotalPropensity params (a, b) =
        singleSpeciesTotalRate params false a +
          singleSpeciesTotalRate params true b := by
    simp [singleSpeciesTotalRate, speciesState,
      lvTotalPropensity, hAlpha0, hAlpha1]
    ring
  have hPhi :
      lvTotalPropensity params (a, b) ≠ 0 := by
    rw [hTotal]
    positivity
  let r₀ := singleSpeciesTotalRate params false a
  let r₁ := singleSpeciesTotalRate params true b
  let W₀ : Measure Nat :=
    ENNReal.ofReal (singleSpeciesBirthRate params a) •
        Measure.dirac (a + 1) +
      ENNReal.ofReal
          (singleSpeciesIndividualDeathRate params a) •
        Measure.dirac (a - 1) +
      ENNReal.ofReal (singleSpeciesIntraRate params false a) •
        Measure.dirac (singleSpeciesIntraTarget v a)
  let W₁ : Measure Nat :=
    ENNReal.ofReal (singleSpeciesBirthRate params b) •
        Measure.dirac (b + 1) +
      ENNReal.ofReal
          (singleSpeciesIndividualDeathRate params b) •
        Measure.dirac (b - 1) +
      ENNReal.ofReal (singleSpeciesIntraRate params true b) •
        Measure.dirac (singleSpeciesIntraTarget v b)
  have hCancel₀ :
      ENNReal.ofReal (r₀ / (r₀ + r₁)) *
          ENNReal.ofReal (1 / r₀) =
        ENNReal.ofReal (1 / (r₀ + r₁)) := by
    rw [← ENNReal.ofReal_mul
      (div_nonneg hr₀.le (add_pos hr₀ hr₁).le)]
    congr 1
    dsimp only [r₀, r₁]
    field_simp [hr₀.ne', hr₁.ne',
      (add_pos hr₀ hr₁).ne']
  have hCancel₁ :
      ENNReal.ofReal (r₁ / (r₀ + r₁)) *
          ENNReal.ofReal (1 / r₁) =
        ENNReal.ofReal (1 / (r₀ + r₁)) := by
    rw [← ENNReal.ofReal_mul
      (div_nonneg hr₁.le (add_pos hr₀ hr₁).le)]
    congr 1
    dsimp only [r₀, r₁]
    field_simp [hr₀.ne', hr₁.ne',
      (add_pos hr₀ hr₁).ne']
  have hMix₀ :
      ENNReal.ofReal (r₀ / (r₀ + r₁)) •
          (singleSpeciesJumpMeasure
            v params false a).map (fun n => (n, b)) =
        ENNReal.ofReal (1 / (r₀ + r₁)) •
          W₀.map (fun n => (n, b)) := by
    rw [singleSpeciesJumpMeasure_eq
      v params false hDelta a ha]
    change
      ENNReal.ofReal (r₀ / (r₀ + r₁)) •
          (ENNReal.ofReal (1 / r₀) • W₀).map
            (fun n => (n, b)) = _
    rw [Measure.map_smul]
    rw [smul_smul, hCancel₀]
  have hMix₁ :
      ENNReal.ofReal (r₁ / (r₀ + r₁)) •
          (singleSpeciesJumpMeasure
            v params true b).map (fun n => (a, n)) =
        ENNReal.ofReal (1 / (r₀ + r₁)) •
          W₁.map (fun n => (a, n)) := by
    rw [singleSpeciesJumpMeasure_eq
      v params true hDelta b hb]
    change
      ENNReal.ofReal (r₁ / (r₀ + r₁)) •
          (ENNReal.ofReal (1 / r₁) • W₁).map
            (fun n => (a, n)) = _
    rw [Measure.map_smul]
    rw [smul_smul, hCancel₁]
  change lvKernel v params (a, b) =
    ENNReal.ofReal (r₀ / (r₀ + r₁)) •
        (singleSpeciesJumpMeasure
          v params false a).map (fun n => (n, b)) +
      ENNReal.ofReal (r₁ / (r₀ + r₁)) •
        (singleSpeciesJumpMeasure
          v params true b).map (fun n => (a, n))
  rw [hMix₀, hMix₁, ← smul_add]
  cases v
  · rw [lvKernel_sd_apply params a b hPhi, hTotal]
    change
      ENNReal.ofReal (1 / (r₀ + r₁)) • _ =
        ENNReal.ofReal (1 / (r₀ + r₁)) • _
    congr 1
    simp [Measure.map_smul, Measure.map_add,
      Measure.map_dirac', measurable_of_countable,
      singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate,
      singleSpeciesIntraRate, speciesGamma,
      singleSpeciesIntraTarget,
      singleSpeciesTotalRate, speciesState,
      lvTotalPropensity, hAlpha0, hAlpha1,
      W₀, W₁, r₀, r₁]
    ac_rfl
  · rw [lvKernel_nsd_apply params a b hPhi, hTotal]
    change
      ENNReal.ofReal (1 / (r₀ + r₁)) • _ =
        ENNReal.ofReal (1 / (r₀ + r₁)) • _
    congr 1
    simp [Measure.map_smul, Measure.map_add,
      Measure.map_dirac', measurable_of_countable,
      singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate,
      singleSpeciesIntraRate, speciesGamma,
      singleSpeciesIntraTarget,
      singleSpeciesTotalRate, speciesState,
      lvTotalPropensity, hAlpha0, hAlpha1,
      W₀, W₁, r₀, r₁]
    ac_rfl

/-- The independent extinction-race probability is harmonic for the
embedded two-species chain when the interspecific rates vanish. -/
theorem independentExtinctionRaceProb_lintegral_lvKernel
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (∫⁻ s,
      independentExtinctionRaceProb
        v params hDelta s.1 s.2
      ∂lvKernel v params (a, b)) =
      independentExtinctionRaceProb
        v params hDelta a b := by
  let H : PopState → ENNReal :=
    fun s => independentExtinctionRaceProb
      v params hDelta s.1 s.2
  have hH : Measurable H :=
    measurable_of_countable H
  rw [lvKernel_eq_independent_species_mixture
    v params hAlpha0 hAlpha1 hDelta a b ha hb]
  rw [MeasureTheory.lintegral_add_measure]
  rw [MeasureTheory.lintegral_smul_measure,
    MeasureTheory.lintegral_smul_measure]
  rw [MeasureTheory.lintegral_map hH
    (measurable_of_countable
      (fun n : Nat => (n, b)))]
  rw [MeasureTheory.lintegral_map hH
    (measurable_of_countable
      (fun n : Nat => (a, n)))]
  change
    ENNReal.ofReal
        (singleSpeciesTotalRate params false a /
          (singleSpeciesTotalRate params false a +
            singleSpeciesTotalRate params true b)) *
        (∫⁻ n,
          independentExtinctionRaceProb
            v params hDelta n b
          ∂singleSpeciesJumpMeasure
            v params false a) +
      ENNReal.ofReal
        (singleSpeciesTotalRate params true b /
          (singleSpeciesTotalRate params false a +
            singleSpeciesTotalRate params true b)) *
        (∫⁻ n,
          independentExtinctionRaceProb
            v params hDelta a n
          ∂singleSpeciesJumpMeasure
            v params true b) =
      independentExtinctionRaceProb
        v params hDelta a b
  exact (independentExtinctionRaceProb_first_step
    v params hDelta hGamma0 hGamma1
    a b ha hb).symm

/-! ## Almost-sure absorption of the embedded superposition -/

/-- Sum of the two isolated birth-count potentials, stopped when either
species is extinct. -/
noncomputable def intraspecificBirthPotential
    (cutoff₀ : Nat) (ratio₀ : Real)
    (cutoff₁ : Nat) (ratio₁ : Real)
    (s : PopState) : ENNReal :=
  if 0 < s.1 ∧ 0 < s.2 then
    ENNReal.ofReal
        (birthCountPotential cutoff₀ ratio₀ s.1) +
      ENNReal.ofReal
        (birthCountPotential cutoff₁ ratio₁ s.2)
  else 0

/-- One-step probability of a birth, stopped when either species is
extinct, written using the two isolated clocks. -/
noncomputable def intraspecificBirthCost
    (params : LVParams) (s : PopState) : ENNReal :=
  if 0 < s.1 ∧ 0 < s.2 then
    let r₀ := singleSpeciesTotalRate params false s.1
    let r₁ := singleSpeciesTotalRate params true s.2
    ENNReal.ofReal (r₀ / (r₀ + r₁)) *
        singleSpeciesBirthCost params false s.1 +
      ENNReal.ofReal (r₁ / (r₀ + r₁)) *
        singleSpeciesBirthCost params true s.2
  else 0

lemma measurable_intraspecificBirthPotential
    (cutoff₀ : Nat) (ratio₀ : Real)
    (cutoff₁ : Nat) (ratio₁ : Real) :
    Measurable
      (intraspecificBirthPotential
        cutoff₀ ratio₀ cutoff₁ ratio₁) :=
  measurable_of_countable _

lemma measurable_intraspecificBirthCost
    (params : LVParams) :
    Measurable (intraspecificBirthCost params) :=
  measurable_of_countable _

lemma ofReal_rate_ratios_add_one
    {r₀ r₁ : Real} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    ENNReal.ofReal (r₀ / (r₀ + r₁)) +
      ENNReal.ofReal (r₁ / (r₀ + r₁)) = 1 := by
  have hsum : 0 < r₀ + r₁ := add_pos hr₀ hr₁
  rw [← ENNReal.ofReal_add
    (div_nonneg hr₀.le hsum.le)
    (div_nonneg hr₁.le hsum.le)]
  have :
      r₀ / (r₀ + r₁) +
          r₁ / (r₀ + r₁) = 1 := by
    field_simp
  rw [this]
  norm_num

/-- Interior Foster inequality controlling the number of births in the
superposed embedded chain. -/
lemma intraspecific_birth_drift_interior
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (cutoff₀ : Nat) (ratio₀ : Real) (hratio₀ : 1 ≤ ratio₀)
    (cutoff₁ : Nat) (ratio₁ : Real) (hratio₁ : 1 ≤ ratio₁)
    (hDrift₀ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₀ ratio₀ (n + 1) ≤
        (singleSpeciesReferenceCT params false hDelta).deathRate n *
          birthCountIncrement cutoff₀ ratio₀ n)
    (hDrift₁ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₁ ratio₁ (n + 1) ≤
        (singleSpeciesReferenceCT params true hDelta).deathRate n *
          birthCountIncrement cutoff₁ ratio₁ n)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    intraspecificBirthCost params (a, b) +
        ∫⁻ s,
          intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁ s
          ∂lvKernel v params (a, b) ≤
      intraspecificBirthPotential
        cutoff₀ ratio₀ cutoff₁ ratio₁ (a, b) := by
  let r₀ := singleSpeciesTotalRate params false a
  let r₁ := singleSpeciesTotalRate params true b
  let p₀ := ENNReal.ofReal (r₀ / (r₀ + r₁))
  let p₁ := ENNReal.ofReal (r₁ / (r₀ + r₁))
  let V₀ : Nat → ENNReal :=
    fun n => ENNReal.ofReal
      (birthCountPotential cutoff₀ ratio₀ n)
  let V₁ : Nat → ENNReal :=
    fun n => ENNReal.ofReal
      (birthCountPotential cutoff₁ ratio₁ n)
  let U : PopState → ENNReal :=
    fun s => V₀ s.1 + V₁ s.2
  let c₀ := singleSpeciesBirthCost params false a
  let c₁ := singleSpeciesBirthCost params true b
  let I₀ := ∫⁻ n, V₀ n ∂
    singleSpeciesJumpMeasure v params false a
  let I₁ := ∫⁻ n, V₁ n ∂
    singleSpeciesJumpMeasure v params true b
  have hr₀ : 0 < r₀ :=
    singleSpeciesTotalRate_pos
      params false hDelta a ha
  have hr₁ : 0 < r₁ :=
    singleSpeciesTotalRate_pos
      params true hDelta b hb
  have hpSum : p₀ + p₁ = 1 :=
    ofReal_rate_ratios_add_one hr₀ hr₁
  have hV₀ : Measurable V₀ := measurable_of_countable _
  have hV₁ : Measurable V₁ := measurable_of_countable _
  have hU : Measurable U := measurable_of_countable _
  have hDriftIso₀ : c₀ + I₀ ≤ V₀ a := by
    exact singleSpecies_birthCost_potential_drift
      v params false hDelta cutoff₀ ratio₀ hratio₀
      hDrift₀ a ha
  have hDriftIso₁ : c₁ + I₁ ≤ V₁ b := by
    exact singleSpecies_birthCost_potential_drift
      v params true hDelta cutoff₁ ratio₁ hratio₁
      hDrift₁ b hb
  have hStoppedLe :
      ∀ s : PopState,
        intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁ s ≤
          U s := by
    intro s
    simp only [intraspecificBirthPotential]
    split_ifs
    · rfl
    · exact bot_le
  have hIntegralLe :
      (∫⁻ s,
          intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁ s
          ∂lvKernel v params (a, b)) ≤
        p₀ * (I₀ + V₁ b) +
          p₁ * (V₀ a + I₁) := by
    calc
      (∫⁻ s,
          intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁ s
          ∂lvKernel v params (a, b)) ≤
          ∫⁻ s, U s ∂lvKernel v params (a, b) :=
        lintegral_mono hStoppedLe
      _ = ∫⁻ s, U s ∂
          (p₀ •
              (singleSpeciesJumpMeasure
                v params false a).map
                (fun n => (n, b)) +
            p₁ •
              (singleSpeciesJumpMeasure
                v params true b).map
                (fun n => (a, n))) := by
            rw [lvKernel_eq_independent_species_mixture
              v params hAlpha0 hAlpha1 hDelta a b ha hb]
      _ = p₀ * (I₀ + V₁ b) +
          p₁ * (V₀ a + I₁) := by
            rw [MeasureTheory.lintegral_add_measure,
              MeasureTheory.lintegral_smul_measure,
              MeasureTheory.lintegral_smul_measure]
            rw [MeasureTheory.lintegral_map hU
              (measurable_of_countable
                (fun n : Nat => (n, b)))]
            rw [MeasureTheory.lintegral_map hU
              (measurable_of_countable
                (fun n : Nat => (a, n)))]
            haveI : IsProbabilityMeasure
                (singleSpeciesJumpMeasure
                  v params false a) := by infer_instance
            haveI : IsProbabilityMeasure
                (singleSpeciesJumpMeasure
                  v params true b) := by infer_instance
            change
              p₀ * (∫⁻ n, V₀ n + V₁ b
                ∂singleSpeciesJumpMeasure
                  v params false a) +
              p₁ * (∫⁻ n, V₀ a + V₁ n
                ∂singleSpeciesJumpMeasure
                  v params true b) =
              p₀ * (I₀ + V₁ b) +
                p₁ * (V₀ a + I₁)
            rw [MeasureTheory.lintegral_add_left
              hV₀ (fun _ => V₁ b),
              MeasureTheory.lintegral_add_right
                (fun _ => V₀ a) hV₁]
            simp only [MeasureTheory.lintegral_const,
              measure_univ, mul_one]
            rfl
  simp only [intraspecificBirthCost, ha, hb,
    and_self, ↓reduceIte,
    intraspecificBirthPotential]
  change
    p₀ * c₀ + p₁ * c₁ +
        (∫⁻ s,
          intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁ s
          ∂lvKernel v params (a, b)) ≤
      V₀ a + V₁ b
  calc
    p₀ * c₀ + p₁ * c₁ +
        (∫⁻ s,
          intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁ s
          ∂lvKernel v params (a, b))
      ≤ p₀ * c₀ + p₁ * c₁ +
          (p₀ * (I₀ + V₁ b) +
            p₁ * (V₀ a + I₁)) := by
        gcongr
    _ = p₀ * (c₀ + I₀ + V₁ b) +
        p₁ * (V₀ a + c₁ + I₁) := by
      ring
    _ ≤ p₀ * (V₀ a + V₁ b) +
        p₁ * (V₀ a + V₁ b) := by
      apply add_le_add
      · have h₀ :
            c₀ + I₀ + V₁ b ≤ V₀ a + V₁ b := by
          simpa only [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hDriftIso₀ (V₁ b)
        exact mul_le_mul_left' h₀ p₀
      · have h₁ :
            V₀ a + c₁ + I₁ ≤ V₀ a + V₁ b := by
          simpa only [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hDriftIso₁ (V₀ a)
        exact mul_le_mul_left' h₁ p₁
    _ = V₀ a + V₁ b := by
      rw [← add_mul, hpSum, one_mul]

lemma lvKernel_species0_dead_ae
    (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)]
    (s : PopState) (hs : s.1 = 0) :
    ∀ᵐ y ∂lvKernel v params s, y.1 = 0 := by
  rw [ae_iff]
  have hzero :
      lvKernel v params s
        {y : PopState | y.1 ≠ 0} = 0 := by
    cases v
    · exact sd_kernel_species0_dead_absorbing_general
        params s hs
    · exact nsd_kernel_species0_dead_absorbing
        params s hs
  simpa only [not_not] using hzero

lemma lvKernel_species1_dead_ae
    (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)]
    (s : PopState) (hs : s.2 = 0) :
    ∀ᵐ y ∂lvKernel v params s, y.2 = 0 := by
  rw [ae_iff]
  have hzero :
      lvKernel v params s
        {y : PopState | y.2 ≠ 0} = 0 := by
    cases v
    · exact sd_kernel_species1_dead_absorbing_general
        params s hs
    · exact nsd_kernel_species1_dead_absorbing
        params s hs
  simpa only [not_not] using hzero

lemma intraspecific_birth_drift
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (cutoff₀ : Nat) (ratio₀ : Real) (hratio₀ : 1 ≤ ratio₀)
    (cutoff₁ : Nat) (ratio₁ : Real) (hratio₁ : 1 ≤ ratio₁)
    (hDrift₀ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₀ ratio₀ (n + 1) ≤
        (singleSpeciesReferenceCT params false hDelta).deathRate n *
          birthCountIncrement cutoff₀ ratio₀ n)
    (hDrift₁ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₁ ratio₁ (n + 1) ≤
        (singleSpeciesReferenceCT params true hDelta).deathRate n *
          birthCountIncrement cutoff₁ ratio₁ n)
    [IsMarkovKernel (lvKernel v params)] :
    ∀ s : PopState,
      intraspecificBirthCost params s +
          ∫⁻ y,
            intraspecificBirthPotential
              cutoff₀ ratio₀ cutoff₁ ratio₁ y
            ∂lvKernel v params s ≤
        intraspecificBirthPotential
          cutoff₀ ratio₀ cutoff₁ ratio₁ s := by
  intro ⟨a, b⟩
  by_cases ha : a = 0
  · have hzero :
        (∫⁻ y,
            intraspecificBirthPotential
              cutoff₀ ratio₀ cutoff₁ ratio₁ y
            ∂lvKernel v params (a, b)) = 0 := by
      apply (lintegral_eq_zero_iff
        (measurable_intraspecificBirthPotential
          cutoff₀ ratio₀ cutoff₁ ratio₁)).2
      filter_upwards [
        lvKernel_species0_dead_ae
          v params (a, b) ha] with y hy
      simp [intraspecificBirthPotential, hy]
    rw [hzero]
    simp [intraspecificBirthCost,
      intraspecificBirthPotential, ha]
  · by_cases hb : b = 0
    · have hzero :
          (∫⁻ y,
              intraspecificBirthPotential
                cutoff₀ ratio₀ cutoff₁ ratio₁ y
              ∂lvKernel v params (a, b)) = 0 := by
        apply (lintegral_eq_zero_iff
          (measurable_intraspecificBirthPotential
            cutoff₀ ratio₀ cutoff₁ ratio₁)).2
        filter_upwards [
          lvKernel_species1_dead_ae
            v params (a, b) hb] with y hy
        simp [intraspecificBirthPotential, hy]
      rw [hzero]
      simp [intraspecificBirthCost,
        intraspecificBirthPotential, hb]
    · exact intraspecific_birth_drift_interior
        v params hAlpha0 hAlpha1 hDelta
        cutoff₀ ratio₀ hratio₀
        cutoff₁ ratio₁ hratio₁
        hDrift₀ hDrift₁ a b
        (Nat.pos_of_ne_zero ha)
        (Nat.pos_of_ne_zero hb)

/-- The clock formula `intraspecificBirthCost` is exactly the
one-step probability of an interior birth in the LV kernel. -/
lemma lvKernel_interior_birth
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (s : PopState) :
    lvKernel v params s
        {y | (0 < s.1 ∧ 0 < s.2) ∧
          y.1 + y.2 = s.1 + s.2 + 1} =
      intraspecificBirthCost params s := by
  rcases s with ⟨a, b⟩
  by_cases ha : a = 0
  · simp [intraspecificBirthCost, ha]
  · by_cases hb : b = 0
    · simp [intraspecificBirthCost, hb]
    · have haPos : 0 < a := Nat.pos_of_ne_zero ha
      have hbPos : 0 < b := Nat.pos_of_ne_zero hb
      let r₀ := singleSpeciesTotalRate params false a
      let r₁ := singleSpeciesTotalRate params true b
      let p₀ := ENNReal.ofReal (r₀ / (r₀ + r₁))
      let p₁ := ENNReal.ofReal (r₁ / (r₀ + r₁))
      let A : Set PopState :=
        {y | (0 < a ∧ 0 < b) ∧
          y.1 + y.2 = a + b + 1}
      have hA : MeasurableSet A := by
        dsimp only [A]
        measurability
      have hPre₀ :
          (fun n : Nat => (n, b)) ⁻¹' A = {a + 1} := by
        ext n
        simp only [A, Set.mem_preimage,
          Set.mem_setOf_eq, Set.mem_singleton_iff,
          Prod.fst, Prod.snd,
          haPos, hbPos, and_self]
        constructor
        · intro h
          have h' : n + b = (a + 1) + b := by
            omega
          exact Nat.add_right_cancel h'
        · intro h
          subst n
          simp [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]
      have hPre₁ :
          (fun n : Nat => (a, n)) ⁻¹' A = {b + 1} := by
        ext n
        simp only [A, Set.mem_preimage,
          Set.mem_setOf_eq, Set.mem_singleton_iff,
          Prod.fst, Prod.snd,
          haPos, hbPos, and_self]
        constructor
        · intro h
          have h' : a + n = a + (b + 1) := by
            omega
          exact Nat.add_left_cancel h'
        · intro h
          subst n
          simp [Nat.add_assoc]
      rw [lvKernel_eq_independent_species_mixture
        v params hAlpha0 hAlpha1 hDelta
        a b haPos hbPos]
      change
        (p₀ •
            (singleSpeciesJumpMeasure
              v params false a).map
              (fun n => (n, b)) +
          p₁ •
            (singleSpeciesJumpMeasure
              v params true b).map
              (fun n => (a, n))) A =
        intraspecificBirthCost params (a, b)
      rw [Measure.add_apply, Measure.smul_apply,
        Measure.smul_apply]
      rw [Measure.map_apply
          (measurable_of_countable
            (fun n : Nat => (n, b))) hA,
        Measure.map_apply
          (measurable_of_countable
            (fun n : Nat => (a, n))) hA]
      rw [hPre₀, hPre₁,
        singleSpeciesJumpMeasure_birth
          v params false hDelta a,
        singleSpeciesJumpMeasure_birth
          v params true hDelta b]
      simp only [intraspecificBirthCost,
        haPos, hbPos, and_self, ↓reduceIte]
      rfl

/-- Expected number of interior births during the first `t` embedded
jumps, in first-step form. -/
noncomputable def intraspecificBirthReward
    (v : LVVariant) (params : LVParams) :
    Nat → PopState → ENNReal
  | 0, _ => 0
  | t + 1, s =>
      intraspecificBirthCost params s +
        ∫⁻ y, intraspecificBirthReward v params t y
          ∂lvKernel v params s

lemma intraspecificBirthReward_le_potential
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (cutoff₀ : Nat) (ratio₀ : Real) (hratio₀ : 1 ≤ ratio₀)
    (cutoff₁ : Nat) (ratio₁ : Real) (hratio₁ : 1 ≤ ratio₁)
    (hDrift₀ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₀ ratio₀ (n + 1) ≤
        (singleSpeciesReferenceCT params false hDelta).deathRate n *
          birthCountIncrement cutoff₀ ratio₀ n)
    (hDrift₁ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₁ ratio₁ (n + 1) ≤
        (singleSpeciesReferenceCT params true hDelta).deathRate n *
          birthCountIncrement cutoff₁ ratio₁ n)
    [IsMarkovKernel (lvKernel v params)] :
    ∀ t s,
      intraspecificBirthReward v params t s ≤
        intraspecificBirthPotential
          cutoff₀ ratio₀ cutoff₁ ratio₁ s := by
  intro t
  induction t with
  | zero =>
      intro s
      simp [intraspecificBirthReward]
  | succ t ih =>
      intro s
      simp only [intraspecificBirthReward]
      calc
        intraspecificBirthCost params s +
              ∫⁻ y,
                intraspecificBirthReward
                  v params t y
                ∂lvKernel v params s
            ≤ intraspecificBirthCost params s +
              ∫⁻ y,
                intraspecificBirthPotential
                  cutoff₀ ratio₀ cutoff₁ ratio₁ y
                ∂lvKernel v params s := by
                gcongr with y
                exact ih y
        _ ≤ intraspecificBirthPotential
              cutoff₀ ratio₀ cutoff₁ ratio₁ s :=
          intraspecific_birth_drift
            v params hAlpha0 hAlpha1 hDelta
            cutoff₀ ratio₀ hratio₀
            cutoff₁ ratio₁ hratio₁
            hDrift₀ hDrift₁ s

lemma intraspecificBirthReward_eq_sum
    (v : LVVariant) (params : LVParams)
    [IsMarkovKernel (lvKernel v params)]
    (t : Nat) (s : PopState) :
    intraspecificBirthReward v params t s =
      ∑ k ∈ Finset.range t,
        ∫⁻ x, intraspecificBirthCost params x
          ∂kernelIter (lvKernel v params) k s := by
  induction t generalizing s with
  | zero =>
      simp [intraspecificBirthReward]
  | succ t ih =>
      have hshift (k : Nat) :
          ∫⁻ x, (∫⁻ y,
              intraspecificBirthCost params y
              ∂kernelIter (lvKernel v params) k x)
            ∂lvKernel v params s =
          ∫⁻ y,
            intraspecificBirthCost params y
            ∂kernelIter (lvKernel v params) (k + 1) s := by
        rw [show k + 1 = 1 + k by omega]
        rw [kernelIter_lintegral_add
          (lvKernel v params) 1 k s
          (intraspecificBirthCost params)
          (measurable_intraspecificBirthCost params)]
        rw [kernelIter_one_generic]
      simp only [intraspecificBirthReward]
      simp_rw [ih]
      rw [lintegral_finsetSum (Finset.range t)
        (fun _ _ => Measurable.lintegral_kernel
          (measurable_intraspecificBirthCost params))]
      simp_rw [hshift]
      rw [Finset.sum_range_succ']
      simp [kernelIter_zero, Kernel.id_apply,
        lintegral_dirac]
      ac_rfl

theorem intraspecific_expected_birth_sum_le
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (cutoff₀ : Nat) (ratio₀ : Real) (hratio₀ : 1 ≤ ratio₀)
    (cutoff₁ : Nat) (ratio₁ : Real) (hratio₁ : 1 ≤ ratio₁)
    (hDrift₀ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₀ ratio₀ (n + 1) ≤
        (singleSpeciesReferenceCT params false hDelta).deathRate n *
          birthCountIncrement cutoff₀ ratio₀ n)
    (hDrift₁ : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff₁ ratio₁ (n + 1) ≤
        (singleSpeciesReferenceCT params true hDelta).deathRate n *
          birthCountIncrement cutoff₁ ratio₁ n)
    [IsMarkovKernel (lvKernel v params)]
    (s : PopState) :
    ∑' k : Nat,
        ∫⁻ x, intraspecificBirthCost params x
          ∂kernelIter (lvKernel v params) k s ≤
      intraspecificBirthPotential
        cutoff₀ ratio₀ cutoff₁ ratio₁ s := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun t => ?_
  rw [← intraspecificBirthReward_eq_sum
    v params t s]
  exact intraspecificBirthReward_le_potential
    v params hAlpha0 hAlpha1 hDelta
    cutoff₀ ratio₀ hratio₀
    cutoff₁ ratio₁ hratio₁
    hDrift₀ hDrift₁ t s

/-- An embedded transition is an interior birth when it starts before
consensus and raises the total population by one. -/
def IsInteriorBirthStep (x y : PopState) : Prop :=
  0 < x.1 ∧ 0 < x.2 ∧
    y.1 + y.2 = x.1 + x.2 + 1

def lvInteriorBirthEvent (k : Nat) :
    Set (Nat → PopState) :=
  {ω | IsInteriorBirthStep (ω k) (ω (k + 1))}

lemma measurableSet_lvInteriorBirthEvent (k : Nat) :
    MeasurableSet (lvInteriorBirthEvent k) := by
  have hpair : Measurable (fun ω : Nat → PopState =>
      (ω k, ω (k + 1))) :=
    (measurable_pi_apply k).prod
      (measurable_pi_apply (k + 1))
  have hstep : MeasurableSet
      {p : PopState × PopState |
        IsInteriorBirthStep p.1 p.2} :=
    (Set.to_countable _).measurableSet
  exact hpair hstep

lemma lvPathMeasure_interiorBirthEvent
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)]
    (s₀ : PopState) (k : Nat) :
    lvPathMeasure v params s₀
        (lvInteriorBirthEvent k) =
      ∫⁻ x, intraspecificBirthCost params x
        ∂kernelIter (lvKernel v params) k s₀ := by
  classical
  let K := lvKernel v params
  let P := homogeneousPathMeasure (Measure.dirac s₀) K
  let A : PopState → Set (Nat → PopState) :=
    fun x => {ω | ω k = x ∧
      IsInteriorBirthStep x (ω (k + 1))}
  have hUnion :
      lvInteriorBirthEvent k = ⋃ x : PopState, A x := by
    ext ω
    simp only [lvInteriorBirthEvent, Set.mem_setOf_eq,
      Set.mem_iUnion, A]
    constructor
    · intro h
      exact ⟨ω k, rfl, h⟩
    · rintro ⟨x, hx, hstep⟩
      simpa [hx] using hstep
  have hPair :
      Pairwise (fun x y => Disjoint (A x) (A y)) := by
    intro x y hxy
    apply Set.disjoint_left.2
    intro ω hx hy
    exact hxy (hx.1.symm.trans hy.1)
  have hMeas : ∀ x, MeasurableSet (A x) := by
    intro x
    have hcur : MeasurableSet
        {ω : Nat → PopState | ω k = x} := by
      measurability
    have hnext : MeasurableSet
        {ω : Nat → PopState |
          IsInteriorBirthStep x (ω (k + 1))} := by
      have hpred : MeasurableSet
          {y : PopState | IsInteriorBirthStep x y} :=
        (Set.to_countable _).measurableSet
      exact hpred.preimage (measurable_pi_apply (k + 1))
    exact hcur.inter hnext
  have hPiece :
      ∀ x : PopState,
        P (A x) =
          intraspecificBirthCost params x *
            (kernelIter K k) s₀ {x} := by
    intro x
    let g : PopState → ENNReal :=
      fun z => if z = x then 1 else 0
    let φ : PopState → ENNReal :=
      fun y => if IsInteriorBirthStep x y then 1 else 0
    have hg : Measurable g := measurable_of_countable _
    have hφ : Measurable φ := measurable_of_countable _
    have hIndicator :
        ∀ ω : Nat → PopState,
          (A x).indicator
              (1 : (Nat → PopState) → ENNReal) ω =
            g (ω k) * φ (ω (k + 1)) := by
      intro ω
      by_cases hcur : ω k = x
      · by_cases hnext :
          IsInteriorBirthStep x (ω (k + 1))
        <;> simp [A, g, φ, Set.indicator,
          hcur, hnext]
      · simp [A, g, Set.indicator, hcur]
    rw [← lintegral_indicator_one (hMeas x)]
    rw [show
      (∫⁻ ω, (A x).indicator
          (1 : (Nat → PopState) → ENNReal) ω ∂P) =
        ∫⁻ ω, g (ω k) * φ (ω (k + 1)) ∂P by
          congr 1
          funext ω
          exact hIndicator ω]
    rw [homogeneousPathMeasure_joint_lintegral
      K s₀ k g φ hg hφ]
    have hInner :
        ∀ z : PopState,
          g z * ∫⁻ y, φ y ∂K z =
            if z = x then
              intraspecificBirthCost params x
            else 0 := by
      intro z
      by_cases hz : z = x
      · subst z
        simp only [g, φ, ↓reduceIte, one_mul]
        rw [show
          (∫⁻ y,
              (if IsInteriorBirthStep x y
                then 1 else 0) ∂K x) =
            K x {y | IsInteriorBirthStep x y} by
              rw [← lintegral_indicator_one
                ((Set.to_countable
                  {y | IsInteriorBirthStep x y}).measurableSet)]
              congr 1
              ]
        simpa only [K, IsInteriorBirthStep,
          and_assoc] using
          lvKernel_interior_birth
            v params hAlpha0 hAlpha1 hDelta x
      · simp [g, hz]
    simp_rw [hInner]
    rw [lintegral_countable']
    simp only [ite_mul, zero_mul]
    rw [tsum_eq_single x]
    · simp
    · intro z hzx
      simp [hzx]
  change P (lvInteriorBirthEvent k) =
    ∫⁻ x, intraspecificBirthCost params x
      ∂kernelIter K k s₀
  rw [hUnion, measure_iUnion hPair hMeas]
  simp_rw [hPiece]
  rw [lintegral_countable']

theorem lvInteriorBirthEvents_tsum_ne_top
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)]
    (s₀ : PopState) :
    ∑' k : Nat,
        lvPathMeasure v params s₀
          (lvInteriorBirthEvent k) ≠ ⊤ := by
  obtain ⟨cutoff₀, ratio₀, hratio₀, hDrift₀⟩ :=
    exists_birthCount_increments
      params false hDelta (by
        simpa [speciesGamma] using hGamma0)
  obtain ⟨cutoff₁, ratio₁, hratio₁, hDrift₁⟩ :=
    exists_birthCount_increments
      params true hDelta (by
        simpa [speciesGamma] using hGamma1)
  simp_rw [lvPathMeasure_interiorBirthEvent
    v params hAlpha0 hAlpha1 hDelta s₀]
  apply ne_top_of_le_ne_top
    (b := intraspecificBirthPotential
      cutoff₀ ratio₀ cutoff₁ ratio₁ s₀)
  · rw [intraspecificBirthPotential]
    split_ifs
    · exact ENNReal.add_ne_top.2
        ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    · exact ENNReal.zero_ne_top
  · exact intraspecific_expected_birth_sum_le
      v params hAlpha0 hAlpha1 hDelta
      cutoff₀ ratio₀ hratio₀
      cutoff₁ ratio₁ hratio₁
      hDrift₀ hDrift₁ s₀

/-- Before consensus, every embedded jump is either a birth or lowers
the total population. -/
def IntraspecificInteriorStep (x y : PopState) : Prop :=
  0 < x.1 ∧ 0 < x.2 →
    IsInteriorBirthStep x y ∨
      y.1 + y.2 < x.1 + x.2

lemma lvKernel_intraspecificInteriorStep_ae
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta) :
    ∀ x : PopState, ∀ᵐ y ∂lvKernel v params x,
      IntraspecificInteriorStep x y := by
  intro x
  rcases x with ⟨a, b⟩
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · rw [lvKernel_eq_independent_species_mixture
        v params hAlpha0 hAlpha1 hDelta a b ha hb]
      apply ae_add_measure_iff.2
      constructor
      · apply Measure.ae_smul_measure
        apply (MeasureTheory.ae_map_iff
          (μ := singleSpeciesJumpMeasure
            v params false a)
          (f := fun n : Nat => (n, b))
          (by fun_prop)
          (Set.to_countable _).measurableSet).2
        filter_upwards [
          singleSpeciesJumpMeasure_step_ae
            v params false hDelta a] with n hn
        intro _
        rcases hn with hzero | ⟨_, hup | hdown⟩
        · exact (ha.ne' hzero.1).elim
        · left
          exact ⟨ha, hb, by omega⟩
        · right
          omega
      · apply Measure.ae_smul_measure
        apply (MeasureTheory.ae_map_iff
          (μ := singleSpeciesJumpMeasure
            v params true b)
          (f := fun n : Nat => (a, n))
          (by fun_prop)
          (Set.to_countable _).measurableSet).2
        filter_upwards [
          singleSpeciesJumpMeasure_step_ae
            v params true hDelta b] with n hn
        intro _
        rcases hn with hzero | ⟨_, hup | hdown⟩
        · exact (hb.ne' hzero.1).elim
        · left
          exact ⟨ha, hb, by omega⟩
        · right
          omega
    · filter_upwards
      exact fun _ hInterior =>
        (hb hInterior.2).elim
  · filter_upwards
    exact fun _ hInterior =>
      (ha hInterior.1).elim

lemma path_hits_consensus_of_eventually_no_interior_birth
    (ω : Nat → PopState)
    (hstep : ∀ k,
      IntraspecificInteriorStep
        (ω k) (ω (k + 1)))
    (hbirth : ∀ᶠ k in Filter.atTop,
      ω ∉ lvInteriorBirthEvent k) :
    ∃ t, (ω t).1 = 0 ∨ (ω t).2 = 0 := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 hbirth
  by_contra hnever
  push_neg at hnever
  have hdec : ∀ k, N ≤ k →
      (ω (k + 1)).1 + (ω (k + 1)).2 <
        (ω k).1 + (ω k).2 := by
    intro k hk
    have hinterior :
        0 < (ω k).1 ∧ 0 < (ω k).2 :=
      ⟨Nat.pos_of_ne_zero (hnever k).1,
        Nat.pos_of_ne_zero (hnever k).2⟩
    rcases hstep k hinterior with hUp | hDown
    · exact (hN k hk hUp).elim
    · exact hDown
  have hbound : ∀ j : Nat,
      (ω (N + j)).1 + (ω (N + j)).2 + j ≤
        (ω N).1 + (ω N).2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hd :=
          hdec (N + j) (Nat.le_add_right N j)
        have hindex :
            N + (j + 1) = (N + j) + 1 := by
          omega
        rw [hindex]
        omega
  have := hbound ((ω N).1 + (ω N).2 + 1)
  omega

set_option maxHeartbeats 800000 in
theorem lvPath_eventually_consensus_ae
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)]
    (s₀ : PopState) :
    ∀ᵐ ω ∂lvPathMeasure v params s₀,
      ∃ t, (ω t).1 = 0 ∨ (ω t).2 = 0 := by
  have hsteps :
      ∀ᵐ ω ∂lvPathMeasure v params s₀,
        ∀ k, IntraspecificInteriorStep
          (ω k) (ω (k + 1)) := by
    change
      ∀ᵐ ω ∂homogeneousPathMeasure
          (Measure.dirac s₀) (lvKernel v params),
        ∀ k, IntraspecificInteriorStep
          (ω k) (ω (k + 1))
    exact homogeneousPathMeasure_transition_ae
      (lvKernel v params) s₀
      IntraspecificInteriorStep
      (lvKernel_intraspecificInteriorStep_ae
        v params hAlpha0 hAlpha1 hDelta)
  have hnobirth :
      ∀ᵐ ω ∂lvPathMeasure v params s₀,
        ∀ᶠ k in Filter.atTop,
          ω ∉ lvInteriorBirthEvent k :=
    ae_eventually_notMem
      (lvInteriorBirthEvents_tsum_ne_top
        v params hAlpha0 hAlpha1
        hGamma0 hGamma1 hDelta s₀)
  filter_upwards [hsteps, hnobirth] with
      ω hωstep hωbirth
  exact
    path_hits_consensus_of_eventually_no_interior_birth
      ω hωstep hωbirth

/-! ## The extinction race bounds majority consensus -/

/-- The real-valued probability that isolated species `0` becomes
extinct before isolated species `1`. -/
noncomputable def independentExtinctionRaceReal
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (s : PopState) : Real :=
  (independentExtinctionRaceProb
    v params hDelta s.1 s.2).toReal

lemma independentExtinctionRaceReal_bounds
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (s : PopState) :
    0 ≤ independentExtinctionRaceReal
        v params hDelta s ∧
      independentExtinctionRaceReal
        v params hDelta s ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · exact ENNReal.toReal_mono ENNReal.one_ne_top
      (independentExtinctionRaceProb_le_one
        v params hDelta s.1 s.2)

lemma independentExtinctionRaceReal_integral_lvKernel
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)]
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (∫ s,
      independentExtinctionRaceReal
        v params hDelta s
      ∂lvKernel v params (a, b)) =
      independentExtinctionRaceReal
        v params hDelta (a, b) := by
  let H : PopState → ENNReal :=
    fun s => independentExtinctionRaceProb
      v params hDelta s.1 s.2
  have hH : Measurable H := measurable_of_countable H
  have hfinite : ∀ᵐ s ∂lvKernel v params (a, b),
      H s < ⊤ := by
    filter_upwards with s
    exact lt_of_le_of_lt
      (independentExtinctionRaceProb_le_one
        v params hDelta s.1 s.2)
      ENNReal.one_lt_top
  change (∫ s, (H s).toReal
      ∂lvKernel v params (a, b)) =
    (H (a, b)).toReal
  rw [MeasureTheory.integral_toReal
    hH.aemeasurable hfinite]
  rw [independentExtinctionRaceProb_lintegral_lvKernel
    v params hAlpha0 hAlpha1 hGamma0 hGamma1
    hDelta a b ha hb]

/-- Complement of the isolated extinction-race probability, with the
correct stopped values on the two consensus boundaries. -/
noncomputable def intraspecificMajorityRaceBound
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (s : PopState) : ENNReal :=
  if s.1 = 0 then 0
  else if s.2 = 0 then 1
  else ENNReal.ofReal
    (1 - independentExtinctionRaceReal
      v params hDelta s)

lemma intraspecificMajorityRaceBound_le_one
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta) (s : PopState) :
    intraspecificMajorityRaceBound
      v params hDelta s ≤ 1 := by
  by_cases hs0 : s.1 = 0
  · simp [intraspecificMajorityRaceBound, hs0]
  · by_cases hs1 : s.2 = 0
    · simp [intraspecificMajorityRaceBound,
        hs0, hs1]
    · simp only [intraspecificMajorityRaceBound,
        hs0, hs1, ↓reduceIte]
      rw [ENNReal.ofReal_le_one]
      linarith [
        (independentExtinctionRaceReal_bounds
          v params hDelta s).1]

lemma intraspecificMajorityRaceBound_eq_complement
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (s : PopState) (hdraw : s ≠ (0, 0)) :
    intraspecificMajorityRaceBound
        v params hDelta s =
      ENNReal.ofReal
        (1 - independentExtinctionRaceReal
          v params hDelta s) := by
  rcases s with ⟨a, b⟩
  by_cases ha : a = 0
  · subst a
    have hb : 0 < b := by
      have hb0 : b ≠ 0 := by
        intro hb0
        exact hdraw (by simp [hb0])
      exact Nat.pos_of_ne_zero hb0
    have hRace :
        independentExtinctionRaceReal
            v params hDelta (0, b) = 1 := by
      simp only [independentExtinctionRaceReal,
        Prod.fst, Prod.snd]
      rw [independentExtinctionRaceProb_zero_left
        v params hDelta (by
          simpa [speciesGamma] using hGamma0)
        b hb]
      simp
    simp [intraspecificMajorityRaceBound,
      hRace]
  · by_cases hb : b = 0
    · subst b
      have hRace :
          independentExtinctionRaceReal
              v params hDelta (a, 0) = 0 := by
        simp only [independentExtinctionRaceReal,
          Prod.fst, Prod.snd]
        rw [independentExtinctionRaceProb_zero_right
          v params hDelta (by
            simpa [speciesGamma] using hGamma1) a]
        simp
      simp [intraspecificMajorityRaceBound,
        ha, hRace]
    · simp [intraspecificMajorityRaceBound,
        ha, hb]

lemma lvKernel_interior_draw_null
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hDelta : 0 < params.delta)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    lvKernel v params (a, b) {(0, 0)} = 0 := by
  rw [lvKernel_eq_independent_species_mixture
    v params hAlpha0 hAlpha1 hDelta
    a b ha hb]
  have hA : MeasurableSet ({(0, 0)} : Set PopState) :=
    measurableSet_singleton _
  have hPre₀ :
      (fun n : Nat => (n, b)) ⁻¹'
        ({(0, 0)} : Set PopState) = ∅ := by
    ext n
    simp [hb.ne']
  have hPre₁ :
      (fun n : Nat => (a, n)) ⁻¹'
        ({(0, 0)} : Set PopState) = ∅ := by
    ext n
    simp [ha.ne']
  rw [Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  rw [Measure.map_apply
      (measurable_of_countable
        (fun n : Nat => (n, b))) hA,
    Measure.map_apply
      (measurable_of_countable
        (fun n : Nat => (a, n))) hA]
  rw [hPre₀, hPre₁]
  simp

lemma intraspecificMajorityRaceBound_lintegral_lvKernel
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)]
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (∫⁻ s,
      intraspecificMajorityRaceBound
        v params hDelta s
      ∂lvKernel v params (a, b)) =
      intraspecificMajorityRaceBound
        v params hDelta (a, b) := by
  let R : PopState → Real :=
    independentExtinctionRaceReal v params hDelta
  let q : PopState → ENNReal :=
    intraspecificMajorityRaceBound v params hDelta
  have hRmeas : Measurable R := measurable_of_countable R
  have hqmeas : Measurable q := measurable_of_countable q
  have hRint : Integrable R
      (lvKernel v params (a, b)) := by
    haveI : IsProbabilityMeasure
        (lvKernel v params (a, b)) :=
      IsMarkovKernel.isProbabilityMeasure (a, b)
    apply Integrable.mono
      (integrable_const (1 : Real))
      hRmeas.aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_eq_abs, norm_one]
    exact abs_le.2
      ⟨by linarith [
          (independentExtinctionRaceReal_bounds
            v params hDelta s).1],
        (independentExtinctionRaceReal_bounds
          v params hDelta s).2⟩
  have hOneSubInt :
      Integrable (fun s => 1 - R s)
        (lvKernel v params (a, b)) :=
    (integrable_const (1 : Real)).sub hRint
  have hOneSubNonneg :
      ∀ᵐ s ∂lvKernel v params (a, b),
        0 ≤ 1 - R s := by
    filter_upwards with s
    exact sub_nonneg.2
      (independentExtinctionRaceReal_bounds
        v params hDelta s).2
  have hNoDraw :
      ∀ᵐ s ∂lvKernel v params (a, b),
        s ≠ (0, 0) := by
    rw [ae_iff]
    simpa using lvKernel_interior_draw_null
      v params hAlpha0 hAlpha1 hDelta
      a b ha hb
  have hqComplement :
      q =ᵐ[lvKernel v params (a, b)]
        fun s => ENNReal.ofReal (1 - R s) := by
    filter_upwards [hNoDraw] with s hs
    exact intraspecificMajorityRaceBound_eq_complement
      v params hDelta hGamma0 hGamma1 s hs
  calc
    (∫⁻ s, q s ∂lvKernel v params (a, b)) =
        ∫⁻ s, ENNReal.ofReal (1 - R s)
          ∂lvKernel v params (a, b) :=
      lintegral_congr_ae hqComplement
    _ = ENNReal.ofReal
        (∫ s, (1 - R s)
          ∂lvKernel v params (a, b)) := by
      exact (ofReal_integral_eq_lintegral_ofReal
        hOneSubInt hOneSubNonneg).symm
    _ = ENNReal.ofReal (1 - R (a, b)) := by
      congr 1
      rw [integral_sub
        (integrable_const (1 : Real)) hRint]
      haveI : IsProbabilityMeasure
          (lvKernel v params (a, b)) :=
        IsMarkovKernel.isProbabilityMeasure (a, b)
      rw [MeasureTheory.integral_const,
        measureReal_univ_eq_one, one_smul,
        independentExtinctionRaceReal_integral_lvKernel
          v params hAlpha0 hAlpha1
          hGamma0 hGamma1 hDelta a b ha hb]
    _ = q (a, b) := by
      simp [q, R, intraspecificMajorityRaceBound,
        ha.ne', hb.ne']

lemma intraspecificMajorityRaceBound_superharmonic
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)] :
    ∀ s : PopState,
      (∫⁻ y,
        intraspecificMajorityRaceBound
          v params hDelta y
        ∂lvKernel v params s) ≤
        intraspecificMajorityRaceBound
          v params hDelta s := by
  intro s
  rcases s with ⟨a, b⟩
  by_cases ha : a = 0
  · have hzero :
        (∫⁻ y,
          intraspecificMajorityRaceBound
            v params hDelta y
          ∂lvKernel v params (a, b)) = 0 := by
      apply (lintegral_eq_zero_iff
        (measurable_of_countable
          (intraspecificMajorityRaceBound
            v params hDelta))).2
      filter_upwards [
        lvKernel_species0_dead_ae
          v params (a, b) ha] with y hy
      simp [intraspecificMajorityRaceBound, hy]
    rw [hzero]
    simp [intraspecificMajorityRaceBound, ha]
  · by_cases hb : b = 0
    · haveI : IsProbabilityMeasure
          (lvKernel v params (a, b)) :=
        IsMarkovKernel.isProbabilityMeasure (a, b)
      calc
        (∫⁻ y,
            intraspecificMajorityRaceBound
              v params hDelta y
            ∂lvKernel v params (a, b))
            ≤ ∫⁻ _y : PopState, 1
                ∂lvKernel v params (a, b) :=
          lintegral_mono fun y =>
            intraspecificMajorityRaceBound_le_one
              v params hDelta y
        _ = 1 := by
          rw [lintegral_one, measure_univ]
        _ = intraspecificMajorityRaceBound
              v params hDelta (a, b) := by
          simp [intraspecificMajorityRaceBound,
            ha, hb]
    · exact
        (intraspecificMajorityRaceBound_lintegral_lvKernel
          v params hAlpha0 hAlpha1 hGamma0 hGamma1
          hDelta a b (Nat.pos_of_ne_zero ha)
          (Nat.pos_of_ne_zero hb)).le

/-- The paper's continuous-time extinction race bounds the probability
that the initial majority wins in the embedded LV chain. -/
theorem majorityConsensusProb_le_extinctionRace_complement
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)]
    (a b : Nat) (ha : 0 < a) (hb : 0 < b)
    (hba : b < a) :
    majorityConsensusProb v params (a, b) ≤
      1 - independentExtinctionRaceProb
        v params hDelta a b := by
  let P : Measure (Nat → PopState) :=
    lvPathMeasure v params (a, b)
  let A : Set PopState :=
    {s | 0 < s.1 ∧ s.2 = 0}
  let q : PopState → ENNReal :=
    intraspecificMajorityRaceBound
      v params hDelta
  have hAq : ∀ s ∈ A, 1 ≤ q s := by
    intro s hs
    have hs0 : s.1 ≠ 0 := Nat.ne_of_gt hs.1
    simp [q, A, intraspecificMajorityRaceBound,
      hs0, hs.2]
  have hSuper : ∀ s,
      (∫⁻ y, q y ∂lvKernel v params s) ≤ q s :=
    intraspecificMajorityRaceBound_superharmonic
      v params hAlpha0 hAlpha1 hGamma0 hGamma1
      hDelta
  have hHit : ∀ N : Nat,
      P (pathHitsBy A N) ≤ q (a, b) := by
    intro N
    exact homogeneousPathMeasure_hitBy_le
      (lvKernel v params) q A hAq hSuper
      (a, b) N
  have hMono :
      Monotone (fun N : Nat => pathHitsBy A N) := by
    intro N M hNM ω hω
    rcases hω with ⟨t, ht, hAt⟩
    exact ⟨t, ht.trans hNM, hAt⟩
  have hMajoritySubset :
      {ω : Nat → PopState |
        majorityConsensusEvent (a, b) ω} ⊆
        ⋃ N : Nat, pathHitsBy A N := by
    intro ω hω
    change majorityConsensusEvent (a, b) ω at hω
    cases hct : consensusTime ω with
    | top =>
        simp [majorityConsensusEvent, hct] at hω
    | coe t =>
        have hMaj : species0Majority (a, b) := by
          exact Nat.le_of_lt hba
        simp only [majorityConsensusEvent, hct,
          hMaj, true_and, not_true_eq_false,
          false_and] at hω
        refine Set.mem_iUnion.mpr ⟨t, ?_⟩
        exact ⟨t, le_rfl, by
          simpa [A] using hω⟩
  have hToQ :
      majorityConsensusProb v params (a, b) ≤
        q (a, b) := by
    change P {ω : Nat → PopState |
      majorityConsensusEvent (a, b) ω} ≤ q (a, b)
    calc
      P {ω : Nat → PopState |
            majorityConsensusEvent (a, b) ω}
          ≤ P (⋃ N : Nat, pathHitsBy A N) :=
        measure_mono hMajoritySubset
      _ = ⨆ N : Nat, P (pathHitsBy A N) :=
        hMono.measure_iUnion
      _ ≤ q (a, b) := iSup_le hHit
  refine hToQ.trans_eq ?_
  simp only [q, intraspecificMajorityRaceBound,
    ha.ne', hb.ne', ↓reduceIte,
    independentExtinctionRaceReal]
  let H :=
    independentExtinctionRaceProb
      v params hDelta a b
  have hHle : H ≤ 1 :=
    independentExtinctionRaceProb_le_one
      v params hDelta a b
  calc
    ENNReal.ofReal (1 - H.toReal) =
        ENNReal.ofReal ((1 - H).toReal) := by
      rw [ENNReal.toReal_sub_of_le hHle
        ENNReal.one_ne_top]
      simp
    _ = 1 - H :=
      ENNReal.ofReal_toReal
        (ENNReal.sub_ne_top ENNReal.one_ne_top)

/-- Uniform form of the intraspecific-only failure theorem.  The
constant depends only on the rates and the competition mechanism, not
on the initial populations. -/
theorem exists_uniform_majorityConsensusProb_upper
    (v : LVVariant) (params : LVParams)
    (hAlpha0 : params.alpha0 = 0)
    (hAlpha1 : params.alpha1 = 0)
    (hGamma0 : 0 < params.gamma0)
    (hGamma1 : 0 < params.gamma1)
    (hDelta : 0 < params.delta)
    [IsMarkovKernel (lvKernel v params)] :
    ∃ ε : Real, 0 < ε ∧
      ∀ a b : Nat, 0 < b → b < a →
        majorityConsensusProb v params (a, b) ≤
          1 - ENNReal.ofReal ε := by
  obtain ⟨ε, hε, hRace⟩ :=
    exists_uniform_independent_extinction_race_lower
      v params hDelta
      (by simpa [speciesGamma] using hGamma0)
      (by simpa [speciesGamma] using hGamma1)
  refine ⟨ε, hε, ?_⟩
  intro a b hb hba
  have ha : 0 < a := lt_trans hb hba
  calc
    majorityConsensusProb v params (a, b) ≤
        1 - independentExtinctionRaceProb
          v params hDelta a b :=
      majorityConsensusProb_le_extinctionRace_complement
        v params hAlpha0 hAlpha1 hGamma0 hGamma1
        hDelta a b ha hb hba
    _ ≤ 1 - ENNReal.ofReal ε :=
      tsub_le_tsub_left
        (hRace a b ha hb) 1

end LVConsensus
