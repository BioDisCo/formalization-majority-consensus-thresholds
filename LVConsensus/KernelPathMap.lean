import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Preorder
open scoped ENNReal

namespace LVConsensus

/-!
# Mapping homogeneous Markov paths

This is the generic form of the projective-limit argument used for labelled
LV paths.  If a measurable state map intertwines two one-step kernels, then
mapping every coordinate of the first path gives exactly the second path law.
-/

private lemma compProd_map_prodMap_path
    {A A' B B' : Type*}
    [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [MeasurableSpace B']
    (μ : Measure A) (ν : Measure A')
    (κ : Kernel A B) (κ' : Kernel A' B')
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    (f : A → A') (g : B → B')
    (hf : Measurable f) (hg : Measurable g)
    (hμ : μ.map f = ν)
    (hκ : ∀ a, (κ a).map g = κ' (f a)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = ν ⊗ₘ κ' := by
  letI : SFinite ν := hμ ▸ (inferInstance : SFinite (μ.map f))
  ext S hS
  rw [Measure.map_apply (hf.prodMap hg) hS,
    Measure.compProd_apply (hS.preimage (hf.prodMap hg)),
    Measure.compProd_apply hS]
  rw [← hμ, MeasureTheory.lintegral_map
    (Kernel.measurable_kernel_prodMk_left hS) hf]
  apply lintegral_congr
  intro a
  have hpre :
      Prod.mk a ⁻¹' (Prod.map f g ⁻¹' S) =
        g ⁻¹' (Prod.mk (f a) ⁻¹' S) := rfl
  rw [hpre, ← hκ a]
  exact (Measure.map_apply hg
    (hS.preimage
      (Measurable.prodMk measurable_const measurable_id))).symm

private def mapIic
    {A B : Type*} (f : A → B) (n : Nat)
    (h : ∀ _ : Finset.Iic n, A) :
    ∀ _ : Finset.Iic n, B :=
  fun i => f (h i)

private lemma measurable_mapIic
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) (n : Nat) :
    Measurable (mapIic f n) :=
  measurable_pi_lambda _ fun i =>
    hf.comp (measurable_pi_apply i)

private def mapIocSingleton
    {A B : Type*} (f : A → B) (n : Nat)
    (h : ∀ _ : Finset.Ioc n (n + 1), A) :
    ∀ _ : Finset.Ioc n (n + 1), B :=
  fun i => f (h i)

private lemma measurable_mapIocSingleton
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) (n : Nat) :
    Measurable (mapIocSingleton f n) :=
  measurable_pi_lambda _ fun i =>
    hf.comp (measurable_pi_apply i)

private lemma mapIic_comp_IicProdIoc
    {A B : Type*} (f : A → B) (n : Nat) :
    (mapIic f (n + 1)) ∘
        (IicProdIoc (X := fun _ => A) n (n + 1)) =
      (IicProdIoc (X := fun _ => B) n (n + 1)) ∘
        Prod.map (mapIic f n) (mapIocSingleton f n) := by
  funext ⟨x, y⟩ ⟨i, hi⟩
  simp only [Function.comp_apply, Prod.map_apply, mapIic,
    mapIocSingleton, IicProdIoc]
  by_cases h : i ≤ n <;> simp [h]

private lemma mapIocSingleton_comp_piSingleton
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (n : Nat) :
    (mapIocSingleton f n) ∘
        (MeasurableEquiv.piSingleton (X := fun _ => A) n) =
      (MeasurableEquiv.piSingleton (X := fun _ => B) n) ∘ f := by
  funext z i
  simp [Function.comp_apply, mapIocSingleton,
    MeasurableEquiv.piSingleton]

private lemma homogeneousHistoryKernel_map_state
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (K : Kernel A A) (L : Kernel B B)
    (f : A → B) (hf : Measurable f)
    (hK : ∀ a, (K a).map f = L (f a))
    (n : Nat) (h : ∀ _ : Finset.Iic n, A) :
    (homogeneousHistoryKernel K n h).map f =
      homogeneousHistoryKernel L n (mapIic f n h) := by
  unfold homogeneousHistoryKernel
  rw [Kernel.comp_apply, Kernel.deterministic_apply (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _) _,
    Kernel.comp_apply, Kernel.deterministic_apply (by fun_prop),
    Measure.dirac_bind (Kernel.measurable _) _]
  exact hK _

private lemma partialTraj_map_state
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (K : Kernel A A) (L : Kernel B B)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (f : A → B) (hf : Measurable f)
    (hK : ∀ a, (K a).map f = L (f a))
    (a0 : A) (n : Nat) :
    let XA : Nat → Type _ := fun _ => A
    let XB : Nat → Type _ := fun _ => B
    let κA : (t : Nat) →
        Kernel (∀ i : Finset.Iic t, XA i) (XA (t + 1)) :=
      fun t => homogeneousHistoryKernel K t
    let κB : (t : Nat) →
        Kernel (∀ i : Finset.Iic t, XB i) (XB (t + 1)) :=
      fun t => homogeneousHistoryKernel L t
    let za : ∀ _ : Finset.Iic 0, XA 0 := fun _ => a0
    let zb : ∀ _ : Finset.Iic 0, XB 0 := fun _ => f a0
    (partialTraj (X := XA) κA 0 n za).map (mapIic f n) =
      partialTraj (X := XB) κB 0 n zb := by
  intro XA XB κA κB za zb
  haveI : ∀ t, IsMarkovKernel (κA t) := fun t => by
    simp only [κA, XA, homogeneousHistoryKernel]
    infer_instance
  haveI : ∀ t, IsMarkovKernel (κB t) := fun t => by
    simp only [κB, XB, homogeneousHistoryKernel]
    infer_instance
  induction n with
  | zero =>
      rw [partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_mapIic f hf 0),
        partialTraj_self, Kernel.id_apply]
      congr 1
  | succ n ih =>
      rw [partialTraj_succ_of_le (Nat.zero_le n)]
      rw [Kernel.map_apply _ measurable_IicProdIoc, Kernel.comp_apply]
      have hPairMeas : Measurable
          (Prod.map (mapIic f n) (mapIocSingleton f n)) :=
        (measurable_mapIic f hf n).prodMap
          (measurable_mapIocSingleton f hf n)
      have hIicMeas : Measurable
          (IicProdIoc (X := fun _ => B) n (n + 1)) :=
        measurable_IicProdIoc
      rw [Measure.map_map (measurable_mapIic f hf (n + 1))
          measurable_IicProdIoc,
        mapIic_comp_IicProdIoc f n,
        ← Measure.map_map hIicMeas hPairMeas]
      rw [← Measure.compProd_eq_comp_prod]
      have hstep :
          ∀ h,
            (((κA n).map
                (MeasurableEquiv.piSingleton
                  (X := fun _ => A) n)) h).map
                (mapIocSingleton f n) =
              ((κB n).map
                (MeasurableEquiv.piSingleton
                  (X := fun _ => B) n)) (mapIic f n h) := by
        intro h
        rw [← Kernel.map_apply _
            (measurable_mapIocSingleton f hf n),
          ← Kernel.map_comp_right _
            (MeasurableEquiv.piSingleton
              (X := fun _ => A) n).measurable
            (measurable_mapIocSingleton f hf n),
          mapIocSingleton_comp_piSingleton f n,
          Kernel.map_comp_right _ hf
            (MeasurableEquiv.piSingleton
              (X := fun _ => B) n).measurable,
          Kernel.map_apply _
            (MeasurableEquiv.piSingleton
              (X := fun _ => B) n).measurable,
          Kernel.map_apply _ hf,
          homogeneousHistoryKernel_map_state K L f hf hK n h,
          Kernel.map_apply _
            (MeasurableEquiv.piSingleton
              (X := fun _ => B) n).measurable]
      rw [compProd_map_prodMap_path
        (partialTraj (X := XA) κA 0 n za)
        (partialTraj (X := XB) κB 0 n zb)
        ((κA n).map
          (MeasurableEquiv.piSingleton
            (X := fun _ => A) n))
        ((κB n).map
          (MeasurableEquiv.piSingleton
            (X := fun _ => B) n))
        (mapIic f n) (mapIocSingleton f n)
        (measurable_mapIic f hf n)
        (measurable_mapIocSingleton f hf n) ih hstep]
      rw [Measure.compProd_eq_comp_prod,
        ← Kernel.comp_apply,
        ← Kernel.map_apply _ hIicMeas]
      exact congrArg
        (fun J : Kernel (∀ i : Finset.Iic 0, XB i)
            (∀ i : Finset.Iic (n + 1), XB i) => J zb)
        (partialTraj_succ_of_le (X := XB) (κ := κB) (Nat.zero_le n)).symm

/-- Apply a state map at every time of a path. -/
def pathMap {A B : Type*} (f : A → B) (ω : Nat → A) : Nat → B :=
  fun t => f (ω t)

lemma measurable_pathMap
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) :
    Measurable (pathMap f) :=
  measurable_pi_lambda _ fun t =>
    hf.comp (measurable_pi_apply t)

/-- A measurable map which intertwines two homogeneous Markov kernels also
intertwines their full path laws. -/
theorem homogeneousPathMeasure_map_pathMap
    {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B]
    (K : Kernel A A) (L : Kernel B B)
    [IsMarkovKernel K] [IsMarkovKernel L]
    (f : A → B) (hf : Measurable f)
    (hK : ∀ a, (K a).map f = L (f a))
    (a0 : A) :
    (homogeneousPathMeasure (Measure.dirac a0) K).map (pathMap f) =
      homogeneousPathMeasure (Measure.dirac (f a0)) L := by
  let XA : Nat → Type _ := fun _ => A
  let XB : Nat → Type _ := fun _ => B
  let κA : (t : Nat) →
      Kernel (∀ i : Finset.Iic t, XA i) (XA (t + 1)) :=
    fun t => homogeneousHistoryKernel K t
  let κB : (t : Nat) →
      Kernel (∀ i : Finset.Iic t, XB i) (XB (t + 1)) :=
    fun t => homogeneousHistoryKernel L t
  haveI : ∀ t, IsMarkovKernel (κA t) := fun t => by
    simp only [κA, XA, homogeneousHistoryKernel]
    infer_instance
  haveI : ∀ t, IsMarkovKernel (κB t) := fun t => by
    simp only [κB, XB, homogeneousHistoryKernel]
    infer_instance
  let za : ∀ _ : Finset.Iic 0, XA 0 := fun _ => a0
  let zb : ∀ _ : Finset.Iic 0, XB 0 := fun _ => f a0
  have hA :
      homogeneousPathMeasure (Measure.dirac a0) K =
        traj (X := XA) κA 0 za := by
    simp only [homogeneousPathMeasure, trajMeasure, κA, XA, za]
    rw [Measure.map_dirac'
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => A)).symm.measurable]
    exact Measure.dirac_bind (Kernel.measurable _) _
  have hB :
      homogeneousPathMeasure (Measure.dirac (f a0)) L =
        traj (X := XB) κB 0 zb := by
    simp only [homogeneousPathMeasure, trajMeasure, κB, XB, zb]
    rw [Measure.map_dirac'
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => B)).symm.measurable]
    exact Measure.dirac_bind (Kernel.measurable _) _
  rw [hA, hB]
  have hprojected :
      IsProjectiveLimit
        ((traj (X := XA) κA 0 za).map (pathMap f))
        (inducedFamily
          (fun n => partialTraj (X := XB) κB 0 n zb)) := by
    rw [isProjectiveLimit_nat_iff
      (isProjectiveMeasureFamily_partialTraj κB zb)]
    intro n
    rw [inducedFamily_Iic,
      Measure.map_map (measurable_frestrictLe n)
        (measurable_pathMap f hf),
      show (frestrictLe n : (Nat → B) → _) ∘ pathMap f =
        mapIic f n ∘ (frestrictLe n : (Nat → A) → _) by
          funext ω i
          rfl,
      ← Measure.map_map (measurable_mapIic f hf n)
        (measurable_frestrictLe n),
      traj_map_frestrictLe_apply]
    exact partialTraj_map_state K L f hf hK a0 n
  have horiginal :
      IsProjectiveLimit
        (traj (X := XB) κB 0 zb)
        (inducedFamily
          (fun n => partialTraj (X := XB) κB 0 n zb)) := by
    rw [traj_apply]
    exact isProjectiveLimit_trajFun
      (X := XB) (κ := κB) 0 zb
  exact hprojected.unique horiginal

/-- A one-step support relation for a homogeneous Markov kernel holds at
every consecutive pair of times on almost every path. -/
theorem homogeneousPathMeasure_transition_ae
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) (R : α → α → Prop)
    (hstep : ∀ x, ∀ᵐ y ∂K x, R x y) :
    ∀ᵐ ω ∂homogeneousPathMeasure (Measure.dirac s0) K,
      ∀ t : Nat, R (ω t) (ω (t + 1)) := by
  classical
  rw [ae_all_iff]
  intro t
  rw [ae_iff]
  let P := homogeneousPathMeasure (Measure.dirac s0) K
  let Bad : α → Set α := fun x => {y | ¬R x y}
  have hbad : ∀ x, K x (Bad x) = 0 := by
    intro x
    have hx := hstep x
    rw [ae_iff] at hx
    simpa only [Bad] using hx
  have hUnion :
      {ω : Nat → α | ¬R (ω t) (ω (t + 1))} =
        ⋃ x : α, {ω | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hω
      exact ⟨ω t, rfl, hω⟩
    · rintro ⟨x, hxt, hbadnext⟩
      subst x
      exact hbadnext
  change P {ω : Nat → α | ¬R (ω t) (ω (t + 1))} = 0
  rw [hUnion]
  apply measure_iUnion_null
  intro x
  let g : α → ℝ≥0∞ := fun y => if y = x then 1 else 0
  let φ : α → ℝ≥0∞ := fun y => if y ∈ Bad x then 1 else 0
  have hmeas :
      MeasurableSet
        ({ω : Nat → α | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x}) := by
    measurability
  rw [← lintegral_indicator_one hmeas]
  have heq : ∀ ω : Nat → α,
      ({ω : Nat → α | ω t = x} ∩
        {ω | ω (t + 1) ∈ Bad x}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω =
        g (ω t) * φ (ω (t + 1)) := by
    intro ω
    by_cases h1 : ω t = x
    · subst x
      by_cases h2 : ω (t + 1) ∈ Bad (ω t) <;>
        simp [g, φ, Set.indicator, h2]
    · simp [g, φ, Set.indicator, h1]
  change (∫⁻ ω,
    ({ω : Nat → α | ω t = x} ∩
      {ω | ω (t + 1) ∈ Bad x}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂P) = 0
  rw [show ∫⁻ ω,
        ({ω : Nat → α | ω t = x} ∩
          {ω | ω (t + 1) ∈ Bad x}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂P =
      ∫⁻ ω, g (ω t) * φ (ω (t + 1)) ∂P by
        congr 1
        funext ω
        exact heq ω]
  change (∫⁻ ω, g (ω t) * φ (ω (t + 1))
    ∂homogeneousPathMeasure (Measure.dirac s0) K) = 0
  rw [homogeneousPathMeasure_joint_lintegral K s0 t g φ
    (measurable_of_countable _) (measurable_of_countable _)]
  have hz : ∀ y : α, g y * ∫⁻ z, φ z ∂K y = 0 := by
    intro y
    by_cases hy : y = x
    · subst y
      simp only [g, φ, ↓reduceIte, one_mul]
      rw [show ∫⁻ z, (if z ∈ Bad x then 1 else 0) ∂K x =
          K x (Bad x) by
        rw [← lintegral_indicator_one
          ((Set.to_countable _).measurableSet)]
        congr 1
        funext z
        simp [Set.indicator]]
      exact hbad x
    · simp [g, hy]
  simp_rw [hz, lintegral_zero]

/-! ## The Markov property with a finite-history test

The usual consecutive-time formula in `MarkovLib` tests the state at time
`n`.  Stopping-time arguments need the slightly stronger version below,
where the test may inspect the entire finite history through time `n`.
-/

/-- Last coordinate of a history indexed by `Finset.Iic n`. -/
def finiteHistoryLast
    {α : Type*} (n : Nat) (h : ∀ _ : Finset.Iic n, α) : α :=
  h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

lemma finiteHistoryLast_frestrictLe
    {α : Type*} (n : Nat) (ω : Nat → α) :
    finiteHistoryLast n (frestrictLe n ω) = ω n := by
  rfl

lemma measurable_finiteHistoryLast
    {α : Type*} [MeasurableSpace α] (n : Nat) :
    Measurable (finiteHistoryLast (α := α) n) :=
  measurable_pi_apply _

/-- Finite-history form of the one-step Markov identity.  The factor `g`
may depend on every coordinate through time `n`, while `φ` tests the next
state. -/
theorem homogeneousPathMeasure_history_next_lintegral
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) (n : Nat)
    (g : (∀ _ : Finset.Iic n, α) → ℝ≥0∞)
    (φ : α → ℝ≥0∞)
    (hg : Measurable g) (hφ : Measurable φ) :
    ∫⁻ ω, g (frestrictLe n ω) * φ (ω (n + 1))
        ∂homogeneousPathMeasure (Measure.dirac s0) K =
      ∫⁻ h, g h * ∫⁻ y, φ y ∂K (finiteHistoryLast n h)
        ∂(homogeneousPathMeasure (Measure.dirac s0) K).map
          (frestrictLe n) := by
  let P := homogeneousPathMeasure (Measure.dirac s0) K
  let κ : (t : Nat) →
      Kernel (∀ i : Finset.Iic t, α) α :=
    fun t => homogeneousHistoryKernel K t
  let μ := P.map (frestrictLe n)
  haveI : IsProbabilityMeasure P := by
    simp only [P, homogeneousPathMeasure]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [show μ = P.map (frestrictLe n) from rfl,
      Measure.map_apply (measurable_frestrictLe n)
        MeasurableSet.univ,
      Set.preimage_univ, measure_univ]
  have hPair : Measurable (fun ω : Nat → α =>
      (frestrictLe n ω, ω (n + 1))) :=
    Measurable.prod (measurable_frestrictLe n)
      (measurable_pi_apply _)
  have hF : Measurable (fun p :
      (∀ _ : Finset.Iic n, α) × α =>
      g p.1 * φ p.2) :=
    (hg.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hCP : μ ⊗ₘ κ n =
      P.map (fun ω => (frestrictLe n ω, ω (n + 1))) := by
    show P.map (frestrictLe n) ⊗ₘ κ n = _
    rw [show P = trajMeasure
        (X := fun _ => α) (κ := κ) (Measure.dirac s0) from rfl]
    exact
      map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  calc
    ∫⁻ ω, g (frestrictLe n ω) * φ (ω (n + 1)) ∂P =
        ∫⁻ p, g p.1 * φ p.2
          ∂(P.map (fun ω =>
            (frestrictLe n ω, ω (n + 1)))) :=
      (lintegral_map hF hPair).symm
    _ = ∫⁻ p, g p.1 * φ p.2 ∂(μ ⊗ₘ κ n) := by
      rw [hCP]
    _ = ∫⁻ h, ∫⁻ y, g h * φ y ∂κ n h ∂μ :=
      Measure.lintegral_compProd hF
    _ = ∫⁻ h, g h * ∫⁻ y, φ y
          ∂K (finiteHistoryLast n h) ∂μ := by
      congr 1
      funext h
      rw [show κ n h = K (finiteHistoryLast n h) by
        unfold κ homogeneousHistoryKernel finiteHistoryLast
        rw [Kernel.comp_apply,
          Kernel.deterministic_apply (by fun_prop)]
        exact Measure.dirac_bind (Kernel.measurable K) _,
        lintegral_const_mul _ hφ]

/-- Singleton-cylinder recursion for a homogeneous Markov path. -/
theorem homogeneousPathMeasure_frestrictLe_singleton_succ
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) (k : Nat)
    (qnext : ∀ _ : Finset.Iic (k + 1), α) :
    let q : ∀ _ : Finset.Iic k, α :=
      fun i => qnext
        ⟨i.1, Finset.mem_Iic.mpr
          (Nat.le_trans (Finset.mem_Iic.mp i.2)
            (Nat.le_succ k))⟩
    let b := qnext
      ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
    let P := homogeneousPathMeasure (Measure.dirac s0) K
    P {ω | frestrictLe (k + 1) ω = qnext} =
      K (q ⟨k, Finset.mem_Iic.mpr le_rfl⟩) {b} *
        P {ω | frestrictLe k ω = q} := by
  classical
  let q : ∀ _ : Finset.Iic k, α :=
    fun i => qnext
      ⟨i.1, Finset.mem_Iic.mpr
        (Nat.le_trans (Finset.mem_Iic.mp i.2)
          (Nat.le_succ k))⟩
  let b := qnext
    ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
  let P := homogeneousPathMeasure (Measure.dirac s0) K
  let A : Set (Nat → α) := {ω | frestrictLe k ω = q}
  let c := K (q ⟨k, Finset.mem_Iic.mpr le_rfl⟩) {b}
  let g : (∀ _ : Finset.Iic k, α) → ℝ≥0∞ :=
    fun h => if h = q then 1 else 0
  let φ : α → ℝ≥0∞ :=
    fun y => if y = b then 1 else 0
  have hg : Measurable g := measurable_of_countable g
  have hφ : Measurable φ := measurable_of_countable φ
  have hprefix :
      ∀ ω : Nat → α,
        frestrictLe (k + 1) ω = qnext ↔
          frestrictLe k ω = q ∧ ω (k + 1) = b := by
    intro ω
    constructor
    · intro h
      constructor
      · funext i
        let hi : Finset.Iic (k + 1) :=
          ⟨i.1, Finset.mem_Iic.mpr
            (Nat.le_trans (Finset.mem_Iic.mp i.2)
              (Nat.le_succ k))⟩
        have := congrFun h hi
        simpa only [frestrictLe_apply, q] using this
      · have := congrFun h
          ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
        simpa only [frestrictLe_apply, b] using this
    · rintro ⟨hpre, hlast⟩
      funext i
      by_cases hi : i.1 ≤ k
      · let j : Finset.Iic k :=
          ⟨i.1, Finset.mem_Iic.mpr hi⟩
        have := congrFun hpre j
        simpa only [frestrictLe_apply, q, j] using this
      · have hieq : i.1 = k + 1 := by
          have := Finset.mem_Iic.mp i.2
          omega
        have hieq' :
            i = ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
          Subtype.ext hieq
        rw [hieq']
        simpa only [frestrictLe_apply, b] using hlast
  have hpoint :
      ∀ ω : Nat → α,
        ({ω | frestrictLe (k + 1) ω = qnext} :
            Set (Nat → α)).indicator
              (fun _ => (1 : ℝ≥0∞)) ω =
          g (frestrictLe k ω) * φ (ω (k + 1)) := by
    intro ω
    by_cases hpre : frestrictLe k ω = q
    · by_cases hlast : ω (k + 1) = b
      · have hall := (hprefix ω).2 ⟨hpre, hlast⟩
        simp [Set.indicator, g, φ, hpre, hlast, hall]
      · have hall : frestrictLe (k + 1) ω ≠ qnext :=
          fun h => hlast ((hprefix ω).1 h).2
        simp [Set.indicator, g, φ, hpre, hlast, hall]
    · have hall : frestrictLe (k + 1) ω ≠ qnext :=
        fun h => hpre ((hprefix ω).1 h).1
      simp [Set.indicator, g, φ, hpre, hall]
  have hintegrand :
      ∀ h : ∀ _ : Finset.Iic k, α,
        g h * ∫⁻ y, φ y ∂K (finiteHistoryLast k h) =
          c * g h := by
    intro h
    by_cases hq : h = q
    · subst h
      have hφint :
          ∫⁻ y, φ y ∂K
              (finiteHistoryLast k q) = c := by
        calc
          ∫⁻ y, φ y ∂K (finiteHistoryLast k q) =
              K (finiteHistoryLast k q) {b} := by
            rw [← lintegral_indicator_one
              (measurableSet_singleton b)]
            congr 1
          _ = c := by rfl
      simpa [g, hφint]
    · simp [g, hq]
  have hleftMeas :
      MeasurableSet
        {ω : Nat → α |
          frestrictLe (k + 1) ω = qnext} :=
    (measurableSet_singleton qnext).preimage
      (measurable_frestrictLe (k + 1))
  have hAmeas : MeasurableSet A :=
    (measurableSet_singleton q).preimage
      (measurable_frestrictLe k)
  change P {ω | frestrictLe (k + 1) ω = qnext} =
    c * P A
  calc
    P {ω | frestrictLe (k + 1) ω = qnext} =
        ∫⁻ ω,
          ({ω | frestrictLe (k + 1) ω = qnext} :
            Set (Nat → α)).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂P :=
      (lintegral_indicator_one (μ := P) hleftMeas).symm
    _ = ∫⁻ ω, g (frestrictLe k ω) *
          φ (ω (k + 1)) ∂P := by
      apply lintegral_congr
      exact hpoint
    _ = ∫⁻ h, g h * ∫⁻ y, φ y
          ∂K (finiteHistoryLast k h)
          ∂P.map (frestrictLe k) := by
      simpa only [P] using
        homogeneousPathMeasure_history_next_lintegral
          K s0 k g φ hg hφ
    _ = ∫⁻ h, c * g h ∂P.map (frestrictLe k) := by
      apply lintegral_congr
      exact hintegrand
    _ = c * ∫⁻ h, g h ∂P.map (frestrictLe k) := by
      rw [lintegral_const_mul c hg]
    _ = c * ∫⁻ ω, g (frestrictLe k ω) ∂P := by
      congr 1
      exact lintegral_map hg (measurable_frestrictLe k)
    _ = c * ∫⁻ ω, A.indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
      congr 1
      apply lintegral_congr
      intro ω
      by_cases hω : frestrictLe k ω = q
      · simp [g, A, Set.indicator, hω]
      · simp [g, A, Set.indicator, hω]
    _ = c * P A := by
      congr 1
      exact lintegral_indicator_one (μ := P) hAmeas

/-- The time-zero singleton cylinder is the initial Dirac law. -/
theorem homogeneousPathMeasure_frestrictLe_singleton_zero
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) (q : ∀ _ : Finset.Iic 0, α) :
    homogeneousPathMeasure (Measure.dirac s0) K
        {ω | frestrictLe 0 ω = q} =
      Measure.dirac s0
        {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
  let q0 := q ⟨0, Finset.mem_Iic.mpr le_rfl⟩
  have hevent :
      {ω : Nat → α | frestrictLe 0 ω = q} =
        {ω | ω 0 = q0} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := congrFun h
        ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      simpa only [frestrictLe_apply, q0] using this
    · intro h
      funext i
      have hi :
          i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
        apply Subtype.ext
        exact Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
      rw [hi]
      simpa only [frestrictLe_apply, q0] using h
  rw [hevent]
  calc
    homogeneousPathMeasure (Measure.dirac s0) K
        {ω | ω 0 = q0} =
        (homogeneousPathMeasure (Measure.dirac s0) K).map
          (fun ω => ω 0) {q0} := by
      rw [Measure.map_apply
        (μ := homogeneousPathMeasure (Measure.dirac s0) K)
        (measurable_pi_apply 0)
        (measurableSet_singleton q0)]
      rfl
    _ = (kernelIter K 0) s0 {q0} := by
      rw [homogeneousPathMeasure_dirac_marginal]
    _ = Measure.dirac s0
        {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
      simp only [kernelIter_zero, Kernel.id_apply, q0]

/-! ## Stopping a path on entry to a set -/

/-- Freeze a path forever once it first enters `A`. -/
noncomputable def pathStoppedAt
    {α : Type*} (A : Set α) (ω : Nat → α) : Nat → α := by
  classical
  exact fun n =>
    Nat.rec (ω 0)
      (fun m previous =>
        @ite α (previous ∈ A) (Classical.propDecidable _)
          previous (ω (m + 1))) n

@[simp] lemma pathStoppedAt_zero
    {α : Type*} (A : Set α) (ω : Nat → α) :
    pathStoppedAt A ω 0 = ω 0 := by
  simp [pathStoppedAt]

@[simp] lemma pathStoppedAt_succ
    {α : Type*} (A : Set α) (ω : Nat → α) (n : Nat) :
    pathStoppedAt A ω (n + 1) =
      @ite α (pathStoppedAt A ω n ∈ A)
        (Classical.propDecidable _)
        (pathStoppedAt A ω n) (ω (n + 1)) := by
  simp [pathStoppedAt]

/-- Kernel obtained by making every state in `A` absorbing. -/
noncomputable def kernelStoppedAt
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α]
    (A : Set α) (K : Kernel α α) :
    Kernel α α := by
  exact Kernel.ofFunOfCountable fun x =>
    @ite (Measure α) (x ∈ A) (Classical.propDecidable _)
      (Measure.dirac x) (K x)

instance kernelStoppedAt_isMarkovKernel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α]
    (A : Set α) (K : Kernel α α) [IsMarkovKernel K] :
    IsMarkovKernel (kernelStoppedAt A K) where
  isProbabilityMeasure x := by
    simp only [kernelStoppedAt, Kernel.ofFunOfCountable,
      Kernel.coe_mk]
    split <;> infer_instance

lemma measurable_pathStoppedAt
    {α : Type*} [MeasurableSpace α]
    (A : Set α) (hA : MeasurableSet A) :
    Measurable (pathStoppedAt A) := by
  have hcoord :
      ∀ n, Measurable (fun ω : Nat → α =>
        pathStoppedAt A ω n) := by
    intro n
    induction n with
    | zero =>
        simpa only [pathStoppedAt_zero] using
          (measurable_pi_apply 0 :
            Measurable (fun ω : Nat → α => ω 0))
    | succ n ih =>
        simp only [pathStoppedAt_succ]
        exact Measurable.ite (hA.preimage ih) ih
          (measurable_pi_apply (n + 1))
  exact measurable_pi_lambda _ hcoord

lemma pathStoppedAt_congr_up_to
    {α : Type*} (A : Set α)
    {ω ω' : Nat → α} {t : Nat}
    (hEq : ∀ u, u ≤ t → ω u = ω' u) :
    ∀ u, u ≤ t →
      pathStoppedAt A ω u = pathStoppedAt A ω' u := by
  intro u hut
  induction u with
  | zero =>
      simp only [pathStoppedAt_zero, hEq 0 (Nat.zero_le t)]
  | succ u ih =>
      rw [pathStoppedAt_succ, pathStoppedAt_succ,
        ih (by omega), hEq (u + 1) hut]

noncomputable def extendFiniteHistory
    {α : Type*} [Nonempty α]
    (t : Nat) (h : ∀ _ : Finset.Iic t, α) :
    Nat → α :=
  fun u =>
    if hu : u ≤ t then
      h ⟨u, Finset.mem_Iic.mpr hu⟩
    else Classical.choice inferInstance

lemma extendFiniteHistory_frestrictLe
    {α : Type*} [Nonempty α]
    (ω : Nat → α) (t u : Nat) (hu : u ≤ t) :
    extendFiniteHistory t (frestrictLe t ω) u = ω u := by
  simp only [extendFiniteHistory, hu, ↓reduceDIte,
    frestrictLe_apply]

lemma pathStoppedAt_extend_frestrictLe
    {α : Type*} [Nonempty α]
    (A : Set α) (ω : Nat → α) (t u : Nat) (hu : u ≤ t) :
    pathStoppedAt A
        (extendFiniteHistory t (frestrictLe t ω)) u =
      pathStoppedAt A ω u := by
  exact pathStoppedAt_congr_up_to A
    (fun r hr => extendFiniteHistory_frestrictLe ω t r hr)
      u hu

lemma pathStoppedAt_eq_current_of_not_mem
    {α : Type*} (A : Set α) (ω : Nat → α) (n : Nat)
    (hnot : pathStoppedAt A ω n ∉ A) :
    pathStoppedAt A ω n = ω n := by
  induction n with
  | zero =>
      exact pathStoppedAt_zero A ω
  | succ n _ =>
      by_cases hprev : pathStoppedAt A ω n ∈ A
      · have hnext :
            pathStoppedAt A ω (n + 1) ∈ A := by
          rw [pathStoppedAt_succ]
          simp only [hprev, ↓reduceIte]
        exact False.elim (hnot hnext)
      · rw [pathStoppedAt_succ]
        simp only [hprev, ↓reduceIte]

lemma pathStoppedAt_eq_of_forall_not_mem_before
    {α : Type*} (A : Set α) (ω : Nat → α) (n : Nat)
    (hnot : ∀ u, u < n → ω u ∉ A) :
    pathStoppedAt A ω n = ω n := by
  induction n with
  | zero =>
      exact pathStoppedAt_zero A ω
  | succ n ih =>
      have hprev : pathStoppedAt A ω n = ω n :=
        ih (fun u hu => hnot u (by omega))
      rw [pathStoppedAt_succ, hprev]
      simp only [hnot n (Nat.lt_succ_self n), ↓reduceIte]

lemma pathStoppedAt_first_mem_iff
    {α : Type*} (A : Set α) (ω : Nat → α) (n : Nat) :
    (pathStoppedAt A ω n ∈ A ∧
        ∀ u < n, pathStoppedAt A ω u ∉ A) ↔
      (ω n ∈ A ∧ ∀ u < n, ω u ∉ A) := by
  constructor
  · rintro ⟨hn, hbefore⟩
    have hrawBefore : ∀ u < n, ω u ∉ A := by
      intro u hu
      have heq := pathStoppedAt_eq_current_of_not_mem
        A ω u (hbefore u hu)
      simpa only [heq] using hbefore u hu
    have heqn := pathStoppedAt_eq_of_forall_not_mem_before
      A ω n hrawBefore
    exact ⟨by simpa only [heqn] using hn, hrawBefore⟩
  · rintro ⟨hn, hbefore⟩
    have heqn := pathStoppedAt_eq_of_forall_not_mem_before
      A ω n hbefore
    refine ⟨by simpa only [heqn] using hn, ?_⟩
    intro u hu
    have hequ := pathStoppedAt_eq_of_forall_not_mem_before
      A ω u (fun r hr => hbefore r (by omega))
    simpa only [hequ] using hbefore u hu

noncomputable def stoppedFiniteHistory
    {α : Type*} [Nonempty α]
    (A : Set α) (t : Nat)
    (h : ∀ _ : Finset.Iic t, α) :
    ∀ _ : Finset.Iic t, α :=
  frestrictLe t (pathStoppedAt A (extendFiniteHistory t h))

lemma stoppedFiniteHistory_frestrictLe
    {α : Type*} [Nonempty α]
    (A : Set α) (ω : Nat → α) (t : Nat) :
    stoppedFiniteHistory A t (frestrictLe t ω) =
      frestrictLe t (pathStoppedAt A ω) := by
  funext i
  exact pathStoppedAt_extend_frestrictLe
    A ω t i.1 (Finset.mem_Iic.mp i.2)

lemma measurable_stoppedFiniteHistory
    {α : Type*} [MeasurableSpace α] [Nonempty α] [Countable α]
    [MeasurableSingletonClass α]
    (A : Set α) (t : Nat) :
    Measurable (stoppedFiniteHistory A t) :=
  measurable_of_countable _

/-- A singleton-cylinder recursion for a homogeneous path after it is
deterministically frozen on first entry to `A`. -/
theorem homogeneousPathMeasure_pathStoppedAt_singleton_succ
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (A : Set α) (hA : MeasurableSet A)
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) (k : Nat)
    (qnext : ∀ _ : Finset.Iic (k + 1), α) :
    let q : ∀ _ : Finset.Iic k, α :=
      fun i => qnext
        ⟨i.1, Finset.mem_Iic.mpr
          (Nat.le_trans (Finset.mem_Iic.mp i.2)
            (Nat.le_succ k))⟩
    let a := q ⟨k, Finset.mem_Iic.mpr le_rfl⟩
    let b := qnext
      ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
    let P := homogeneousPathMeasure (Measure.dirac s0) K
    P {ω | frestrictLe (k + 1) (pathStoppedAt A ω) = qnext} =
      kernelStoppedAt A K a {b} *
        P {ω | frestrictLe k (pathStoppedAt A ω) = q} := by
  classical
  let q : ∀ _ : Finset.Iic k, α :=
    fun i => qnext
      ⟨i.1, Finset.mem_Iic.mpr
        (Nat.le_trans (Finset.mem_Iic.mp i.2)
          (Nat.le_succ k))⟩
  let a := q ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  let b := qnext
    ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
  let P := homogeneousPathMeasure (Measure.dirac s0) K
  let E : Set (Nat → α) :=
    {ω | frestrictLe k (pathStoppedAt A ω) = q}
  have hprefix :
      ∀ ω : Nat → α,
        frestrictLe (k + 1) (pathStoppedAt A ω) = qnext ↔
          frestrictLe k (pathStoppedAt A ω) = q ∧
            pathStoppedAt A ω (k + 1) = b := by
    intro ω
    constructor
    · intro h
      constructor
      · funext i
        let hi : Finset.Iic (k + 1) :=
          ⟨i.1, Finset.mem_Iic.mpr
            (Nat.le_trans (Finset.mem_Iic.mp i.2)
              (Nat.le_succ k))⟩
        have := congrFun h hi
        simpa only [frestrictLe_apply, q] using this
      · have := congrFun h
          ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
        simpa only [frestrictLe_apply, b] using this
    · rintro ⟨hpre, hlast⟩
      funext i
      by_cases hi : i.1 ≤ k
      · let j : Finset.Iic k :=
          ⟨i.1, Finset.mem_Iic.mpr hi⟩
        have := congrFun hpre j
        simpa only [frestrictLe_apply, q, j] using this
      · have hieq : i.1 = k + 1 := by
          have := Finset.mem_Iic.mp i.2
          omega
        have hieq' :
            i = ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ :=
          Subtype.ext hieq
        rw [hieq']
        simpa only [frestrictLe_apply, b] using hlast
  change P {ω | frestrictLe (k + 1)
      (pathStoppedAt A ω) = qnext} =
    kernelStoppedAt A K a {b} * P E
  by_cases ha : a ∈ A
  · by_cases hb : b = a
    · have hevents :
          {ω : Nat → α |
              frestrictLe (k + 1) (pathStoppedAt A ω) = qnext} =
            E := by
        ext ω
        simp only [Set.mem_setOf_eq, E]
        constructor
        · exact fun h => (hprefix ω).1 h |>.1
        · intro hpre
          apply (hprefix ω).2
          refine ⟨hpre, ?_⟩
          have hlast := congrFun hpre
            ⟨k, Finset.mem_Iic.mpr le_rfl⟩
          have hka :
              pathStoppedAt A ω k = a := by
            simpa only [frestrictLe_apply, a] using hlast
          rw [pathStoppedAt_succ, hka]
          simp only [ha, ↓reduceIte, hb]
      rw [hevents]
      have hcoeff :
          kernelStoppedAt A K a {b} = 1 := by
        simp only [kernelStoppedAt, Kernel.ofFunOfCountable,
          Kernel.coe_mk, ha, ↓reduceIte]
        rw [Measure.dirac_apply]
        simp [Set.indicator, hb]
      rw [hcoeff, one_mul]
    · have hevents :
          {ω : Nat → α |
              frestrictLe (k + 1) (pathStoppedAt A ω) = qnext} =
            ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        intro hall
        obtain ⟨hpre, hnext⟩ := (hprefix ω).1 hall
        have hlast := congrFun hpre
          ⟨k, Finset.mem_Iic.mpr le_rfl⟩
        have hka :
            pathStoppedAt A ω k = a := by
          simpa only [frestrictLe_apply, a] using hlast
        have : pathStoppedAt A ω (k + 1) = a := by
          rw [pathStoppedAt_succ, hka]
          simp only [ha, ↓reduceIte]
        exact hb (hnext.symm.trans this)
      have hcoeff :
          kernelStoppedAt A K a {b} = 0 := by
        simp only [kernelStoppedAt, Kernel.ofFunOfCountable,
          Kernel.coe_mk, ha, ↓reduceIte]
        rw [Measure.dirac_apply]
        simp [Set.indicator, hb, Ne.symm hb]
      rw [hevents, measure_empty, hcoeff, zero_mul]
  · let c := K a {b}
    let g : (∀ _ : Finset.Iic k, α) → ℝ≥0∞ :=
      fun h => if stoppedFiniteHistory A k h = q then 1 else 0
    let φ : α → ℝ≥0∞ :=
      fun y => if y = b then 1 else 0
    have hg : Measurable g := measurable_of_countable g
    have hφ : Measurable φ := measurable_of_countable φ
    have hpoint :
        ∀ ω : Nat → α,
          ({ω | frestrictLe (k + 1)
              (pathStoppedAt A ω) = qnext} :
              Set (Nat → α)).indicator
                (fun _ => (1 : ℝ≥0∞)) ω =
            g (frestrictLe k ω) * φ (ω (k + 1)) := by
      intro ω
      have hstopped :
          stoppedFiniteHistory A k (frestrictLe k ω) =
            frestrictLe k (pathStoppedAt A ω) :=
        stoppedFiniteHistory_frestrictLe A ω k
      by_cases hpre :
          frestrictLe k (pathStoppedAt A ω) = q
      · have hlast := congrFun hpre
          ⟨k, Finset.mem_Iic.mpr le_rfl⟩
        have hka :
            pathStoppedAt A ω k = a := by
          simpa only [frestrictLe_apply, a] using hlast
        have hnext :
            pathStoppedAt A ω (k + 1) = ω (k + 1) := by
          rw [pathStoppedAt_succ, hka]
          simp only [ha, ↓reduceIte]
        by_cases hy : ω (k + 1) = b
        · have hall := (hprefix ω).2
            ⟨hpre, hnext.trans hy⟩
          simp [Set.indicator, g, φ, hstopped, hpre, hy, hall]
        · have hall :
              frestrictLe (k + 1)
                  (pathStoppedAt A ω) ≠ qnext := by
            intro hall
            exact hy (hnext.symm.trans ((hprefix ω).1 hall).2)
          simp [Set.indicator, g, φ, hstopped, hpre, hy, hall]
      · have hall :
            frestrictLe (k + 1)
                (pathStoppedAt A ω) ≠ qnext :=
          fun hall => hpre ((hprefix ω).1 hall).1
        simp [Set.indicator, g, φ, hstopped, hpre, hall]
    have hintegrand :
        ∀ h : ∀ _ : Finset.Iic k, α,
          g h * ∫⁻ y, φ y
              ∂K (finiteHistoryLast k h) =
            c * g h := by
      intro h
      by_cases hq : stoppedFiniteHistory A k h = q
      · have hstop := congrFun hq
          ⟨k, Finset.mem_Iic.mpr le_rfl⟩
        have hstop' :
            pathStoppedAt A (extendFiniteHistory k h) k = a := by
          simpa only [stoppedFiniteHistory, frestrictLe_apply, a]
            using hstop
        have hnot :
            pathStoppedAt A (extendFiniteHistory k h) k ∉ A := by
          simpa only [hstop'] using ha
        have hraw :=
          pathStoppedAt_eq_current_of_not_mem A
            (extendFiniteHistory k h) k hnot
        have hlast :
            finiteHistoryLast k h = a := by
          calc
            finiteHistoryLast k h =
                extendFiniteHistory k h k := by
              simp [finiteHistoryLast, extendFiniteHistory]
            _ = pathStoppedAt A
                  (extendFiniteHistory k h) k := hraw.symm
            _ = a := hstop'
        have hφint :
            ∫⁻ y, φ y ∂K (finiteHistoryLast k h) = c := by
          rw [hlast]
          change ∫⁻ y, (if y = b then 1 else 0) ∂K a = K a {b}
          rw [← lintegral_indicator_one
            (measurableSet_singleton b)]
          congr 1
        simp [g, hq, hφint]
      · simp [g, hq]
    have hleftMeas :
        MeasurableSet
          {ω : Nat → α |
            frestrictLe (k + 1)
              (pathStoppedAt A ω) = qnext} :=
      (measurableSet_singleton qnext).preimage
        ((measurable_frestrictLe (k + 1)).comp
          (measurable_pathStoppedAt A hA))
    have hEmeas : MeasurableSet E :=
      (measurableSet_singleton q).preimage
        ((measurable_frestrictLe k).comp
          (measurable_pathStoppedAt A hA))
    have hkernel :
        kernelStoppedAt A K a {b} = c := by
      simp only [kernelStoppedAt, Kernel.ofFunOfCountable,
        Kernel.coe_mk, ha, ↓reduceIte, c]
    calc
      P {ω | frestrictLe (k + 1)
          (pathStoppedAt A ω) = qnext} =
          ∫⁻ ω,
            ({ω | frestrictLe (k + 1)
                (pathStoppedAt A ω) = qnext} :
              Set (Nat → α)).indicator
                (fun _ => (1 : ℝ≥0∞)) ω ∂P :=
        (lintegral_indicator_one (μ := P) hleftMeas).symm
      _ = ∫⁻ ω, g (frestrictLe k ω) *
            φ (ω (k + 1)) ∂P := by
        apply lintegral_congr
        exact hpoint
      _ = ∫⁻ h, g h * ∫⁻ y, φ y
            ∂K (finiteHistoryLast k h)
            ∂P.map (frestrictLe k) := by
        simpa only [P] using
          homogeneousPathMeasure_history_next_lintegral
            K s0 k g φ hg hφ
      _ = ∫⁻ h, c * g h ∂P.map (frestrictLe k) := by
        apply lintegral_congr
        exact hintegrand
      _ = c * ∫⁻ h, g h ∂P.map (frestrictLe k) := by
        rw [lintegral_const_mul c hg]
      _ = c * ∫⁻ ω, g (frestrictLe k ω) ∂P := by
        congr 1
        exact lintegral_map hg (measurable_frestrictLe k)
      _ = c * ∫⁻ ω, E.indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
        congr 1
        apply lintegral_congr
        intro ω
        have hstopped :
            stoppedFiniteHistory A k (frestrictLe k ω) =
              frestrictLe k (pathStoppedAt A ω) :=
          stoppedFiniteHistory_frestrictLe A ω k
        by_cases hω :
            frestrictLe k (pathStoppedAt A ω) = q
        · simp [g, E, Set.indicator, hstopped, hω]
        · simp [g, E, Set.indicator, hstopped, hω]
      _ = c * P E := by
        congr 1
        exact lintegral_indicator_one (μ := P) hEmeas
      _ = kernelStoppedAt A K a {b} * P E := by
        rw [hkernel]

theorem homogeneousPathMeasure_pathStoppedAt_singleton_zero
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (A : Set α)
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) (q : ∀ _ : Finset.Iic 0, α) :
    homogeneousPathMeasure (Measure.dirac s0) K
        {ω | frestrictLe 0 (pathStoppedAt A ω) = q} =
      Measure.dirac s0
        {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
  have hevent :
      {ω : Nat → α | frestrictLe 0 (pathStoppedAt A ω) = q} =
        {ω | frestrictLe 0 ω = q} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> funext i
    · have hi :
          i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
        apply Subtype.ext
        exact Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
      rw [hi]
      simpa only [frestrictLe_apply, pathStoppedAt_zero] using
        congrFun h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
    · have hi :
          i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := by
        apply Subtype.ext
        exact Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
      rw [hi]
      simpa only [frestrictLe_apply, pathStoppedAt_zero] using
        congrFun h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
  rw [hevent]
  exact homogeneousPathMeasure_frestrictLe_singleton_zero K s0 q

/-- Deterministically freezing a homogeneous Markov path on first entry to
`A` produces exactly the homogeneous path law of the kernel made absorbing
on `A`. -/
theorem homogeneousPathMeasure_map_pathStoppedAt
    {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [Nonempty α]
    [MeasurableSingletonClass α] [Countable α]
    (A : Set α) (hA : MeasurableSet A)
    (K : Kernel α α) [IsMarkovKernel K]
    (s0 : α) :
    (homogeneousPathMeasure (Measure.dirac s0) K).map
        (pathStoppedAt A) =
      homogeneousPathMeasure (Measure.dirac s0)
        (kernelStoppedAt A K) := by
  let P := homogeneousPathMeasure (Measure.dirac s0) K
  let Q := homogeneousPathMeasure (Measure.dirac s0)
    (kernelStoppedAt A K)
  let M := P.map (pathStoppedAt A)
  haveI : IsProbabilityMeasure Q := by
    simp only [Q, homogeneousPathMeasure]
    infer_instance
  have hcylinder :
      ∀ k (q : ∀ _ : Finset.Iic k, α),
        P {ω | frestrictLe k (pathStoppedAt A ω) = q} =
          Q {η | frestrictLe k η = q} := by
    intro k
    induction k with
    | zero =>
        intro q
        calc
          P {ω | frestrictLe 0 (pathStoppedAt A ω) = q} =
              Measure.dirac s0
                {q ⟨0, Finset.mem_Iic.mpr le_rfl⟩} := by
            simpa only [P] using
              homogeneousPathMeasure_pathStoppedAt_singleton_zero
                A K s0 q
          _ = Q {η | frestrictLe 0 η = q} := by
            simpa only [Q] using
              (homogeneousPathMeasure_frestrictLe_singleton_zero
                (kernelStoppedAt A K) s0 q).symm
    | succ k ih =>
        intro qnext
        let q : ∀ _ : Finset.Iic k, α :=
          fun i => qnext
            ⟨i.1, Finset.mem_Iic.mpr
              (Nat.le_trans (Finset.mem_Iic.mp i.2)
                (Nat.le_succ k))⟩
        let a := q ⟨k, Finset.mem_Iic.mpr le_rfl⟩
        let b := qnext
          ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩
        calc
          P {ω | frestrictLe (k + 1)
              (pathStoppedAt A ω) = qnext} =
              kernelStoppedAt A K a {b} *
                P {ω | frestrictLe k
                  (pathStoppedAt A ω) = q} := by
            simpa only [P, q, a, b] using
              homogeneousPathMeasure_pathStoppedAt_singleton_succ
                A hA K s0 k qnext
          _ = kernelStoppedAt A K a {b} *
                Q {η | frestrictLe k η = q} := by
            rw [ih q]
          _ = Q {η | frestrictLe (k + 1) η = qnext} := by
            simpa only [Q, q, a, b] using
              (homogeneousPathMeasure_frestrictLe_singleton_succ
                (kernelStoppedAt A K) s0 k qnext).symm
  have hprefixMap : ∀ k,
      M.map (frestrictLe k) =
        Q.map (frestrictLe k) := by
    intro k
    apply Measure.ext_of_singleton
    intro q
    have hqmeas :
        MeasurableSet
          ({q} : Set (∀ _ : Finset.Iic k, α)) :=
      measurableSet_singleton q
    calc
      M.map (frestrictLe k) {q} =
          M ((frestrictLe k) ⁻¹' {q}) := by
        rw [Measure.map_apply (measurable_frestrictLe k) hqmeas]
      _ = P ((pathStoppedAt A) ⁻¹'
            ((frestrictLe k) ⁻¹' {q})) := by
        rw [show M = P.map (pathStoppedAt A) from rfl,
          Measure.map_apply (measurable_pathStoppedAt A hA)
            (hqmeas.preimage (measurable_frestrictLe k))]
      _ = P {ω | frestrictLe k
            (pathStoppedAt A ω) = q} := by
        rfl
      _ = Q {η | frestrictLe k η = q} :=
        hcylinder k q
      _ = Q.map (frestrictLe k) {q} := by
        rw [Measure.map_apply (measurable_frestrictLe k) hqmeas]
        rfl
  let F : (I : Finset Nat) →
      Measure (∀ _ : I, α) :=
    fun I => Q.map I.restrict
  have hFprojective :
      IsProjectiveMeasureFamily
        (α := fun _ : Nat => α) F := by
    exact isProjectiveMeasureFamily_map_restrict
      (P := Q)
      (X := fun t (η : Nat → α) => η t)
      (fun t => (measurable_pi_apply t).aemeasurable)
  have hQlimit :
      IsProjectiveLimit
        (α := fun _ : Nat => α) Q F := by
    intro I
    rfl
  have hMlimit :
      IsProjectiveLimit
        (α := fun _ : Nat => α) M F := by
    rw [isProjectiveLimit_nat_iff hFprojective]
    intro k
    change M.map (frestrictLe k) =
      Q.map (Finset.Iic k).restrict
    rw [show (Finset.Iic k).restrict = frestrictLe k from by
      funext η i
      rfl]
    exact hprefixMap k
  haveI (I : Finset Nat) : IsFiniteMeasure (F I) := by
    simp only [F]
    infer_instance
  exact hMlimit.unique hQlimit

end LVConsensus
