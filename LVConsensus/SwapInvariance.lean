import LVConsensus.MarkovBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Kernel Finset Preorder
open scoped ProbabilityTheory

namespace LVConsensus

/-- Swap the two species in a population state. -/
def PopState.swap (s : PopState) : PopState := (s.2, s.1)

@[simp]
theorem PopState.swap_swap (s : PopState) : s.swap.swap = s := by
  simp [PopState.swap]

@[simp]
theorem PopState.swap_fst (s : PopState) : s.swap.1 = s.2 := rfl

@[simp]
theorem PopState.swap_snd (s : PopState) : s.swap.2 = s.1 := rfl

@[simp]
theorem PopState.swap_mk (a b : Nat) : PopState.swap (a, b) = (b, a) := rfl

/-- Swapping a diagonal state is the identity. -/
@[simp]
theorem PopState.swap_diag (m : Nat) : PopState.swap (m, m) = (m, m) := rfl

/-- Consensus is swap-invariant. -/
theorem reachedConsensus_swap (s : PopState) :
    reachedConsensus s.swap ↔ reachedConsensus s := by
  simp [reachedConsensus, PopState.swap, or_comm]

/-- The gap changes sign under swap. -/
theorem gap_swap (s : PopState) : gap s.swap = -gap s := by
  simp [gap, PopState.swap]

/-- Total propensity is swap-invariant for identical species. -/
theorem lvTotalPropensity_swap
    (params : LVParams)
    (hAlpha : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (s : PopState) :
    lvTotalPropensity params s.swap = lvTotalPropensity params s := by
  simp only [lvTotalPropensity, PopState.swap_fst, PopState.swap_snd]
  rw [hAlpha, hGamma]
  ring

/-- `Nat.min` is swap-invariant. -/
@[simp]
theorem min_swap (s : PopState) : Nat.min s.swap.1 s.swap.2 = Nat.min s.1 s.2 := by
  simp [PopState.swap, Nat.min_comm]

/-- Swap on trajectories: swap every state in a trajectory. -/
def swapTraj (ω : Nat → PopState) : Nat → PopState :=
  fun t => (ω t).swap

@[simp]
theorem swapTraj_apply (ω : Nat → PopState) (t : Nat) :
    swapTraj ω t = (ω t).swap := rfl

@[simp]
theorem swapTraj_involutive : Function.Involutive swapTraj := by
  intro ω; funext t; simp [swapTraj, PopState.swap]

/-- Consensus is preserved under trajectory swap. -/
theorem reachedConsensus_of_swap_traj (ω : Nat → PopState) (t : Nat) :
    reachedConsensus (swapTraj ω t) ↔ reachedConsensus (ω t) := by
  simp [swapTraj, reachedConsensus_swap]

/-- The lvKernel applied to the swapped state produces the swapped measure,
    assuming identical species (α₀ = α₁, γ₀ = γ₁).

    This is the key algebraic swap-equivariance property:
      lvKernel v params s.swap = Measure.map PopState.swap (lvKernel v params s)

    The proof establishes equality of the sums of scaled Dirac measures under
    the swap map. -/
theorem lvKernel_swap_equivariant
    (v : LVVariant)
    (params : LVParams)
    (hAlpha : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (s : PopState) :
    (lvKernel v params) s.swap = Measure.map PopState.swap ((lvKernel v params) s) := by
  have hm : Measurable PopState.swap := measurable_of_countable _
  have hprop : lvTotalPropensity params s.swap = lvTotalPropensity params s :=
    lvTotalPropensity_swap params hAlpha hGamma s
  -- Reduce to singleton equality on countable type
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply hm (measurableSet_singleton _)]
  -- swap ⁻¹' {x} = {x.swap}
  have hpre : PopState.swap ⁻¹' {x} = {x.swap} := by
    ext y; simp [Set.mem_preimage, Set.mem_singleton_iff, PopState.swap,
      Prod.ext_iff, and_comm]
  rw [hpre]
  -- Unfold kernel
  simp only [lvKernel, ProbabilityTheory.Kernel.ofFunOfCountable,
    ProbabilityTheory.Kernel.coe_mk]
  -- Case split on propensity
  by_cases hφ : lvTotalPropensity params s = 0
  · -- φ = 0: both are Dirac
    have hφ' : lvTotalPropensity params s.swap = 0 := hprop ▸ hφ
    simp only [hφ, hφ', ↓reduceDIte]
    -- Dirac(s.swap){x} = Dirac(s){x.swap}
    simp only [Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
    have : PopState.swap s = x ↔ s = PopState.swap x := by
      constructor
      · intro h; rw [← h, PopState.swap_swap]
      · intro h; rw [h, PopState.swap_swap]
    simp only [PopState.swap] at this ⊢
    split_ifs <;> simp_all [Prod.ext_iff]
  · -- φ ≠ 0
    have hφ' : lvTotalPropensity params s.swap ≠ 0 := hprop ▸ hφ
    simp only [hφ, hφ', ↓reduceDIte]
    -- Case split on variant to eliminate `match v with`
    cases v <;> {
      simp only [Measure.smul_apply, smul_eq_mul, Measure.add_apply,
        Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply,
        PopState.swap, Prod.mk.injEq]
      rw [hAlpha, hGamma,
        show lvTotalPropensity params (s.2, s.1) = lvTotalPropensity params s from hprop]
      simp only [Prod.ext_iff, and_comm]
      -- Factor out the common invφ multiplier
      congr 1
      -- Fix Real multiplication order inside ENNReal.ofReal
      simp only [mul_right_comm]
      -- Both sides have the same 8 terms in different addition order
      abel
    }

/- ## Infrastructure for path measure swap-invariance via Ionescu-Tulcea

  We prove that the path measure starting from (m,m) is invariant under swapping
  species at every time step. The proof proceeds by:
  1. One-step swap equivariance of `partialTraj` (using kernel swap-equivariance)
  2. Full induction to get swap-equivariance for all finite-dimensional marginals
  3. Projective limit uniqueness (`IsProjectiveLimit.unique`) for the infinite product

  Key technical point: we use `abbrev PS : ℕ → Type := fun _ => PopState` so that
  dependent types in `partialTraj` (parameterized by `X : ℕ → Type*`) unify correctly
  with our concrete `PopState` type. -/

/-- The constant type family used in the Ionescu-Tulcea construction. -/
private abbrev PS : ℕ → Type := fun _ => PopState

/-- Componentwise swap on trajectories restricted to `Iic n`. -/
private def swapIic (n : ℕ) (x : (i : Iic n) → PS ↑i) : (i : Iic n) → PS ↑i :=
  fun i => (x i).swap

/-- Componentwise swap on trajectories restricted to `Ioc n (n+1)`. -/
private def swapIoc (n : ℕ) (x : (i : Ioc n (n + 1)) → PS ↑i) : (i : Ioc n (n + 1)) → PS ↑i :=
  fun i => (x i).swap

private lemma measurable_swapIic (n : ℕ) : Measurable (swapIic n) := measurable_of_countable _

private lemma measurable_swapTraj : Measurable (swapTraj) :=
  measurable_pi_lambda _ (fun n => (measurable_of_countable _).comp (measurable_pi_apply n))

@[simp] private lemma swapIic_swapIic (n : ℕ) (x : (i : Iic n) → PS ↑i) :
    swapIic n (swapIic n x) = x := by funext i; simp [swapIic, PopState.swap]

/-- History kernel with explicit dependent-type signature for Ionescu-Tulcea. -/
private noncomputable def HHK (K : Kernel PopState PopState) [IsMarkovKernel K] :
    (n : ℕ) → Kernel ((i : Iic n) → PS ↑i) (PS (n + 1)) :=
  fun n => homogeneousHistoryKernel K n

private instance hhk_markov (K : Kernel PopState PopState) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (HHK K n) := by dsimp [HHK, homogeneousHistoryKernel]; infer_instance

private lemma piSingleton_swap_comm (n : ℕ) :
    (MeasurableEquiv.piSingleton (X := PS) n) ∘ PopState.swap =
    swapIoc n ∘ (MeasurableEquiv.piSingleton (X := PS) n) := by
  funext s ⟨i, hi⟩; simp [Function.comp_apply, MeasurableEquiv.piSingleton, swapIoc]

private lemma eta_swap (K : Kernel PopState PopState) [IsMarkovKernel K]
    (hK : ∀ s, K s.swap = (K s).map PopState.swap) (n : ℕ) (y : (i : Iic n) → PS ↑i) :
    ((HHK K n).map (MeasurableEquiv.piSingleton (X := PS) n) y).map (swapIoc n) =
    (HHK K n).map (MeasurableEquiv.piSingleton (X := PS) n) (swapIic n y) := by
  set pS := MeasurableEquiv.piSingleton (X := PS) n
  simp only [Kernel.map_apply _ pS.measurable, HHK, homogeneousHistoryKernel,
    Kernel.comp_apply, Kernel.deterministic_apply]
  rw [Measure.dirac_bind (Kernel.measurable K), Measure.dirac_bind (Kernel.measurable K)]
  simp only [swapIic]
  rw [Measure.map_map (measurable_of_countable _) pS.measurable, ← piSingleton_swap_comm n,
      ← Measure.map_map pS.measurable (measurable_of_countable _), hK (y ⟨n, mem_Iic.2 le_rfl⟩)]

private lemma compProd_swap_eq (K : Kernel PopState PopState) [IsMarkovKernel K]
    (hK : ∀ s, K s.swap = (K s).map PopState.swap) (n : ℕ) (y : (i : Iic n) → PS ↑i) :
    ((Kernel.id ×ₖ (HHK K n).map (MeasurableEquiv.piSingleton (X := PS) n)) y).map
      (fun x => (swapIic n x.1, swapIoc n x.2)) =
    (Kernel.id ×ₖ (HHK K n).map (MeasurableEquiv.piSingleton (X := PS) n)) (swapIic n y) := by
  set η := (HHK K n).map (MeasurableEquiv.piSingleton (X := PS) n)
  apply Measure.ext (fun s hs => ?_)
  rw [Measure.map_apply (measurable_of_countable _) hs, id_prod_apply' _ _ hs,
      id_prod_apply' _ _ (measurableSet_preimage (measurable_of_countable _) hs)]
  have hpre : Prod.mk y ⁻¹' ((fun x : ((i : Iic n) → PS ↑i) × ((i : Ioc n (n + 1)) → PS ↑i) =>
      (swapIic n x.1, swapIoc n x.2)) ⁻¹' s) = swapIoc n ⁻¹' (Prod.mk (swapIic n y) ⁻¹' s) := by
    ext z; simp [Set.mem_preimage]
  rw [hpre, ← eta_swap K hK n y,
      Measure.map_apply (measurable_of_countable _) (measurable_of_countable _ hs)]

private lemma IicProdIoc_swap_comm_fn (n : ℕ) :
    swapIic (n + 1) ∘ IicProdIoc (X := PS) n (n + 1) =
    IicProdIoc (X := PS) n (n + 1) ∘ (fun x => (swapIic n x.1, swapIoc n x.2)) := by
  funext ⟨lo, hi⟩ ⟨i, _⟩
  simp only [Function.comp_apply, swapIic, swapIoc, IicProdIoc]; split <;> rfl

private lemma partialTraj_step_swap (K : Kernel PopState PopState) [IsMarkovKernel K]
    (hK : ∀ s, K s.swap = (K s).map PopState.swap) (n : ℕ)
    (y : (i : Iic n) → PS ↑i) :
    ((partialTraj (HHK K) n (n + 1) y)).map (swapIic (n + 1)) =
    partialTraj (HHK K) n (n + 1) (swapIic n y) := by
  rw [partialTraj_succ_self]
  rw [Kernel.map_apply _ measurable_IicProdIoc,
      Kernel.map_apply _ measurable_IicProdIoc]
  have hPairMeas : Measurable
      (fun x : ((i : Iic n) → PS ↑i) × ((i : Ioc n (n + 1)) → PS ↑i) =>
        (swapIic n x.1, swapIoc n x.2)) :=
    measurable_of_countable _
  have hIicMeas : Measurable (IicProdIoc (X := PS) n (n + 1)) :=
    measurable_IicProdIoc
  rw [Measure.map_map (measurable_swapIic _) measurable_IicProdIoc, IicProdIoc_swap_comm_fn n,
      ← Measure.map_map hIicMeas hPairMeas]
  congr 1; exact compProd_swap_eq K hK n y

private lemma comap_comp_measure {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (κ : Kernel β γ) [IsSFiniteKernel κ] (f : α → β) (hf : Measurable f)
    (μ : Measure α) [SigmaFinite μ] : (κ.comap f hf) ∘ₘ μ = κ ∘ₘ (μ.map f) := by
  ext s hs
  simp only [Measure.bind_apply hs (Kernel.measurable _).aemeasurable, Kernel.comap_apply]
  rw [lintegral_map (Kernel.measurable_coe κ hs) hf]

private lemma partialTraj_swap_induction (K : Kernel PopState PopState) [IsMarkovKernel K]
    (hK : ∀ s, K s.swap = (K s).map PopState.swap) (k : ℕ) (y : (i : Iic 0) → PS ↑i) :
    ((partialTraj (HHK K) 0 k) y).map (swapIic k) =
    (partialTraj (HHK K) 0 k) (swapIic 0 y) := by
  induction k with
  | zero =>
    simp only [partialTraj_self, Kernel.id_apply, Measure.map_dirac' (measurable_swapIic 0)]
  | succ n ih =>
    have hcomp := partialTraj_succ_eq_comp (κ := HHK K) (Nat.zero_le n)
    have hL : (partialTraj (HHK K) 0 (n + 1)) y =
        (partialTraj (HHK K) n (n + 1)) ∘ₘ ((partialTraj (HHK K) 0 n) y) := by
      rw [hcomp, Kernel.comp_apply]
    have hR : (partialTraj (HHK K) 0 (n + 1)) (swapIic 0 y) =
        (partialTraj (HHK K) n (n + 1)) ∘ₘ ((partialTraj (HHK K) 0 n) (swapIic 0 y)) := by
      rw [hcomp, Kernel.comp_apply]
    rw [hL, hR, Measure.map_comp _ _ (measurable_swapIic _)]
    have hstep : (partialTraj (HHK K) n (n + 1)).map (swapIic (n + 1)) =
        (partialTraj (HHK K) n (n + 1)).comap (swapIic n) (measurable_swapIic n) := by
      ext1 z; rw [Kernel.map_apply _ (measurable_swapIic _), Kernel.comap_apply]
      exact partialTraj_step_swap K hK n z
    rw [hstep, comap_comp_measure, ih]

private lemma frestrictLe_comp_swapTraj (n : ℕ) :
    frestrictLe (π := PS) n ∘ swapTraj = swapIic n ∘ frestrictLe (π := PS) n := by
  funext f ⟨i, _⟩; simp [frestrictLe, Finset.restrict, swapTraj, swapIic, PopState.swap]

private lemma traj_swap_eq (K : Kernel PopState PopState) [IsMarkovKernel K]
    (hK : ∀ s, K s.swap = (K s).map PopState.swap) (x₀ : (i : Iic 0) → PS ↑i) :
    (traj (HHK K) 0 x₀).map swapTraj = traj (HHK K) 0 (swapIic 0 x₀) := by
  have hPL1 := isProjectiveLimit_trajFun (HHK K) 0 (swapIic 0 x₀)
  rw [← traj_apply] at hPL1
  have hPL2 : IsProjectiveLimit ((traj (HHK K) 0 x₀).map swapTraj)
      (inducedFamily (fun n ↦ partialTraj (HHK K) 0 n (swapIic 0 x₀))) := by
    rw [isProjectiveLimit_nat_iff (isProjectiveMeasureFamily_partialTraj (HHK K) (swapIic 0 x₀))]
    intro n; rw [inducedFamily_Iic]
    rw [Measure.map_map (measurable_frestrictLe n) measurable_swapTraj,
        frestrictLe_comp_swapTraj n,
        ← Measure.map_map (measurable_swapIic n) (measurable_frestrictLe n),
        traj_map_frestrictLe_apply, partialTraj_swap_induction K hK n x₀]
  exact hPL2.unique hPL1

private lemma swapIic_piUnique_diag (m : ℕ) :
    (swapIic 0 ∘ (MeasurableEquiv.piUnique (fun (_ : Iic (0 : ℕ)) => PopState)).symm)
      ((m, m) : PopState) =
    (MeasurableEquiv.piUnique (fun (_ : Iic (0 : ℕ)) => PopState)).symm
      ((m, m) : PopState) := by
  funext ⟨i, hi⟩
  simp only [Function.comp_apply, swapIic]
  have hi0 : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi)
  subst hi0; simp [MeasurableEquiv.piUnique, Equiv.piUnique, PopState.swap]

/-- Swapping every state of a neutral LV trajectory started from `(a,b)`
    gives the path law started from `(b,a)`. -/
theorem lvPathMeasure_swap
    (v : LVVariant)
    (params : LVParams)
    (hAlpha : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (a b : Nat)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    (lvPathMeasure v params (a, b)).map swapTraj =
      lvPathMeasure v params (b, a) := by
  unfold lvPathMeasure homogeneousPathMeasure
  set K := lvKernel v params
  change (trajMeasure (Measure.dirac (a, b)) (HHK K)).map swapTraj =
    trajMeasure (Measure.dirac (b, a)) (HHK K)
  simp only [trajMeasure]
  rw [Measure.map_comp _ _ measurable_swapTraj]
  have hkernel : (traj (HHK K) 0).map swapTraj =
      (traj (HHK K) 0).comap (swapIic 0) (measurable_swapIic 0) := by
    ext1 y
    rw [Kernel.map_apply _ measurable_swapTraj, Kernel.comap_apply]
    exact traj_swap_eq K
      (lvKernel_swap_equivariant v params hAlpha hGamma) y
  rw [hkernel, comap_comp_measure,
    Measure.map_map (measurable_swapIic 0)
      (MeasurableEquiv.piUnique _).symm.measurable]
  congr 1
  rw [Measure.map_dirac'
      ((measurable_swapIic 0).comp
        (MeasurableEquiv.piUnique _).symm.measurable),
    Measure.map_dirac' (MeasurableEquiv.piUnique _).symm.measurable]
  congr 1

/-- Path measure swap-invariance from (m,m) for identical species.
    This lifts kernel swap-equivariance to the full path measure via Ionescu-Tulcea.
    The proof uses induction on finite-dimensional marginals (`partialTraj`) and
    projective limit uniqueness (`IsProjectiveLimit.unique`). -/
theorem lvPathMeasure_swap_invariant
    (v : LVVariant)
    (params : LVParams)
    (hAlpha : params.alpha0 = params.alpha1)
    (hGamma : params.gamma0 = params.gamma1)
    (m : Nat)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    (lvPathMeasure v params (m, m)).map swapTraj = lvPathMeasure v params (m, m) := by
  unfold lvPathMeasure homogeneousPathMeasure
  set K := lvKernel v params
  change (trajMeasure (Measure.dirac (m, m)) (HHK K)).map swapTraj =
         trajMeasure (Measure.dirac (m, m)) (HHK K)
  simp only [trajMeasure]
  rw [Measure.map_comp _ _ measurable_swapTraj]
  have hkernel : (traj (HHK K) 0).map swapTraj =
      (traj (HHK K) 0).comap (swapIic 0) (measurable_swapIic 0) := by
    ext1 y; rw [Kernel.map_apply _ measurable_swapTraj, Kernel.comap_apply]
    exact traj_swap_eq K (lvKernel_swap_equivariant v params hAlpha hGamma) y
  rw [hkernel, comap_comp_measure,
      Measure.map_map (measurable_swapIic 0) (MeasurableEquiv.piUnique _).symm.measurable]
  congr 1
  rw [Measure.map_dirac' ((measurable_swapIic 0).comp (MeasurableEquiv.piUnique _).symm.measurable),
      Measure.map_dirac' (MeasurableEquiv.piUnique _).symm.measurable]
  exact congrArg _ (swapIic_piUnique_diag m)

/-- Consensus time is invariant under trajectory swap. -/
theorem consensusTime_swapTraj (ω : Nat → PopState) :
    consensusTime (swapTraj ω) = consensusTime ω := by
  unfold consensusTime MeasureTheory.hittingAfter
  have hmem : ∀ j, popCoord j (swapTraj ω) ∈ {s : PopState | reachedConsensus s}
      ↔ popCoord j ω ∈ {s : PopState | reachedConsensus s} :=
    fun j => by simp [popCoord, swapTraj, reachedConsensus_swap]
  have hset : {i : ℕ | 0 ≤ i ∧ popCoord i (swapTraj ω) ∈ {s | reachedConsensus s}} =
      {i : ℕ | 0 ≤ i ∧ popCoord i ω ∈ {s | reachedConsensus s}} := by
    ext j; exact and_congr_right (fun _ => hmem j)
  rw [hset, (exists_congr (fun j => and_congr_right (fun _ => hmem j))).eq]

/-- species0Majority fails on the diagonal. -/
theorem not_species0Majority_diag' (m : Nat) : ¬ species0Majority (m, m) := by
  simp [species0Majority]

/-- The majorityConsensusEvent on the diagonal under swapTraj gives the "opposite species wins"
    event. -/
theorem majorityConsensusEvent_swapTraj_diag
    (m : Nat) (ω : Nat → PopState) :
    majorityConsensusEvent (m, m) (swapTraj ω) ↔
      (match consensusTime ω with
       | ⊤ => False
       | (t : Nat) => (ω t).1 > 0 ∧ (ω t).2 = 0) := by
  simp only [majorityConsensusEvent, consensusTime_swapTraj, swapTraj_apply,
    PopState.swap_fst, PopState.swap_snd]
  cases consensusTime ω with
  | top => simp
  | coe t =>
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h1, h2⟩)
      · exact absurd h (not_species0Majority_diag' m)
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨not_species0Majority_diag' m, h1, h2⟩

/-- The majorityConsensusEvent on the diagonal (without swap) gives the "species 1 wins" event. -/
theorem majorityConsensusEvent_diag_iff
    (m : Nat) (ω : Nat → PopState) :
    majorityConsensusEvent (m, m) ω ↔
      (match consensusTime ω with
       | ⊤ => False
       | (t : Nat) => (ω t).2 > 0 ∧ (ω t).1 = 0) := by
  simp only [majorityConsensusEvent]
  cases consensusTime ω with
  | top => simp
  | coe t =>
    constructor
    · rintro (⟨h, _⟩ | ⟨_, h1, h2⟩)
      · exact absurd h (not_species0Majority_diag' m)
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨not_species0Majority_diag' m, h1, h2⟩

/-- The "species 1 wins" and "species 0 wins" events are disjoint on the diagonal. -/
theorem disjoint_majorityConsensus_swap_diag (m : Nat) :
    Disjoint
      {ω | majorityConsensusEvent (m, m) ω}
      {ω | majorityConsensusEvent (m, m) (swapTraj ω)} := by
  rw [Set.disjoint_iff]
  intro ω ⟨h1, h2⟩
  rw [Set.mem_setOf_eq, majorityConsensusEvent_diag_iff] at h1
  rw [Set.mem_setOf_eq, majorityConsensusEvent_swapTraj_diag] at h2
  cases hc : consensusTime ω with
  | top => simp [hc] at h1
  | coe t =>
    simp only [hc] at h1 h2
    omega

/-- Any predicate on coordinate `t` gives a measurable set in the path space. -/
private lemma measurableSet_coord_pred (t : ℕ) (S : Set PopState) :
    MeasurableSet ((fun ω : ℕ → PopState => ω t) ⁻¹' S) :=
  (measurable_pi_apply t) (DiscreteMeasurableSpace.forall_measurableSet _)

/-- `consensusTime ω = ↑t` iff consensus is first reached at time `t`. -/
lemma consensusTime_eq_coe_iff (ω : ℕ → PopState) (t : ℕ) :
    consensusTime ω = ↑t ↔
      reachedConsensus (ω t) ∧ ∀ j < t, ¬reachedConsensus (ω j) := by
  unfold consensusTime hittingAfter
  simp only [popCoord]
  constructor
  · intro h
    split_ifs at h with hex
    · have hinf : sInf {i | 0 ≤ i ∧ ω i ∈ {s | reachedConsensus s}} = t :=
        WithTop.coe_eq_coe.mp h
      constructor
      · have hmem : t ∈ {i | 0 ≤ i ∧ ω i ∈ {s | reachedConsensus s}} := by
          rw [← hinf]; exact csInf_mem ⟨hex.choose, hex.choose_spec⟩
        exact hmem.2
      · intro j hj hcons
        have hle := csInf_le (OrderBot.bddBelow _)
          (show j ∈ {i | 0 ≤ i ∧ ω i ∈ {s | reachedConsensus s}} from
            ⟨Nat.zero_le j, hcons⟩)
        rw [hinf] at hle; exact Nat.not_lt.mpr hle hj
    · exact absurd h WithTop.top_ne_coe
  · intro ⟨hcons, hprev⟩
    split_ifs with hex
    · congr 1
      apply le_antisymm
      · exact csInf_le (OrderBot.bddBelow _)
          (show t ∈ {i | 0 ≤ i ∧ ω i ∈ {s | reachedConsensus s}} from
            ⟨Nat.zero_le t, hcons⟩)
      · apply le_csInf ⟨hex.choose, hex.choose_spec⟩
        intro j hj_mem
        by_contra h_lt
        exact hprev j (Nat.lt_of_not_le h_lt) hj_mem.2
    · exact absurd
        ⟨t, Nat.zero_le t, (hcons : popCoord t ω ∈ {s | reachedConsensus s})⟩ hex

/-- The level set `{ω | consensusTime ω = ↑t}` is measurable. -/
lemma measurableSet_consensusTime_eq_coe (t : ℕ) :
    MeasurableSet {ω : ℕ → PopState | consensusTime ω = ↑t} := by
  have : {ω : ℕ → PopState | consensusTime ω = ↑t} =
      ((fun ω : ℕ → PopState => ω t) ⁻¹' {s | reachedConsensus s}) ∩
        ⋂ j ∈ Finset.range t,
          ((fun ω : ℕ → PopState => ω j) ⁻¹' {s | reachedConsensus s})ᶜ := by
    ext ω; simp only [Set.mem_setOf, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_setOf, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
    exact consensusTime_eq_coe_iff ω t
  rw [this]
  exact (measurableSet_coord_pred t _).inter
    (MeasurableSet.biInter (Finset.range t).countable_toSet fun j _ =>
      (measurableSet_coord_pred j _).compl)

/-- The majority-consensus event on the diagonal state `(m,m)` is measurable. -/
theorem measurableSet_majorityConsensusEvent_diag (m : ℕ) :
    MeasurableSet {ω : ℕ → PopState | majorityConsensusEvent (m, m) ω} := by
  suffices hset : {ω : ℕ → PopState | majorityConsensusEvent (m, m) ω} =
      ⋃ t : ℕ, {ω | consensusTime ω = ↑t} ∩
        ((fun ω : ℕ → PopState => ω t) ⁻¹'
          {s : PopState | s.2 > 0 ∧ s.1 = 0}) by
    rw [hset]
    exact MeasurableSet.iUnion fun t =>
      (measurableSet_consensusTime_eq_coe t).inter (measurableSet_coord_pred t _)
  ext ω
  simp only [Set.mem_setOf, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    unfold majorityConsensusEvent at h
    cases hct : consensusTime ω with
    | top => simp [hct] at h
    | coe t =>
      simp only [hct] at h
      rcases h with ⟨hmaj, -⟩ | ⟨-, h2, h1⟩
      · exact absurd hmaj (not_species0Majority_diag' m)
      · exact ⟨t, rfl, h2, h1⟩
  · intro ⟨t, ht, h2, h1⟩
    unfold majorityConsensusEvent
    cases hct : consensusTime ω with
    | top => exact absurd (ht ▸ hct) WithTop.coe_ne_top
    | coe t' =>
      have : t' = t := WithTop.coe_eq_coe.mp (hct.symm.trans ht)
      subst this
      exact Or.inr ⟨not_species0Majority_diag' m, h2, h1⟩

/-- The majority-consensus event is measurable for every initial state. -/
theorem measurableSet_majorityConsensusEvent (s0 : PopState) :
    MeasurableSet {ω : ℕ → PopState | majorityConsensusEvent s0 ω} := by
  suffices hset : {ω : ℕ → PopState | majorityConsensusEvent s0 ω} =
      ⋃ t : ℕ, {ω | consensusTime ω = ↑t} ∩
        ((fun ω : ℕ → PopState => ω t) ⁻¹'
          {s : PopState |
            (species0Majority s0 ∧ s.1 > 0 ∧ s.2 = 0) ∨
              (¬species0Majority s0 ∧ s.2 > 0 ∧ s.1 = 0)}) by
    rw [hset]
    exact MeasurableSet.iUnion fun t =>
      (measurableSet_consensusTime_eq_coe t).inter (measurableSet_coord_pred t _)
  ext ω
  simp only [Set.mem_setOf, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    unfold majorityConsensusEvent at h
    cases hct : consensusTime ω with
    | top => simp [hct] at h
    | coe t => exact ⟨t, rfl, by simpa [hct] using h⟩
  · rintro ⟨t, ht, hpred⟩
    unfold majorityConsensusEvent
    cases hct : consensusTime ω with
    | top => exact absurd (ht ▸ hct) WithTop.coe_ne_top
    | coe t' =>
      have : t' = t := WithTop.coe_eq_coe.mp (hct.symm.trans ht)
      subst this
      exact hpred

/-! ## Diagonal swap-invariance bounds -/

/-- Paper `lemma:identical-gap-fail`: from diagonal (m,m), majority consensus ≤ 1/2.
    By swap invariance P_{(m,m)}(sp0 wins) = P_{(m,m)}(sp1 wins), so each ≤ 1/2. -/
theorem lemma_identical_gap_fail
    (v : LVVariant)
    (params : LVParams)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    (m : Nat)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    majorityConsensusProb v params (m, m) ≤ ENNReal.ofReal (1 / (2 : Real)) := by
  set μ := lvPathMeasure v params (m, m) with hμ_def
  haveI : IsProbabilityMeasure μ := by
    rw [hμ_def]; unfold lvPathMeasure homogeneousPathMeasure; infer_instance
  set A := {ω : ℕ → PopState | majorityConsensusEvent (m, m) ω}
  set C := {ω : ℕ → PopState | majorityConsensusEvent (m, m) (swapTraj ω)}
  have hswap_meas : Measurable swapTraj := by
    rw [measurable_pi_iff]; intro n
    show Measurable (fun ω => swapTraj ω n)
    simp only [swapTraj]
    exact (measurable_of_countable PopState.swap).comp (measurable_pi_apply n)
  have hA_meas : MeasurableSet A := measurableSet_majorityConsensusEvent_diag m
  have hC_eq : C = swapTraj ⁻¹' A := Set.ext fun ω => Iff.rfl
  have hC_meas : MeasurableSet C := hC_eq ▸ hA_meas.preimage hswap_meas
  have h_inv : μ.map swapTraj = μ := lvPathMeasure_swap_invariant v params
    hNeutralAlpha hNeutralGamma m
  have hA_eq_C : μ A = μ C := by
    rw [hC_eq, ← Measure.map_apply hswap_meas hA_meas, h_inv]
  have h_disj : Disjoint A C := disjoint_majorityConsensus_swap_diag m
  have h_prob : μ A + μ C ≤ 1 := by
    calc μ A + μ C = μ (A ∪ C) := (measure_union h_disj hC_meas).symm
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have h_double : μ A + μ A ≤ 1 := hA_eq_C ▸ h_prob
  change μ A ≤ _
  rw [show ENNReal.ofReal (1 / (2 : ℝ)) = (2 : ENNReal)⁻¹ from by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
    simp only [ENNReal.ofReal_ofNat]]
  rw [ENNReal.le_inv_iff_mul_le, mul_comm, two_mul]
  exact h_double

/-- From diagonal state (m,m), probability of MC for ANY s0 is ≤ 1/2.
    Generalizes `lemma_identical_gap_fail`. -/
theorem mc_any_from_diagonal_le_half
    (v : LVVariant) (params : LVParams) (s0 : PopState) (m : ℕ)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] :
    (lvPathMeasure v params (m, m))
      {ω | majorityConsensusEvent s0 ω} ≤ ENNReal.ofReal (1 / 2) := by
  set μ := lvPathMeasure v params (m, m) with hμ_def
  haveI : IsProbabilityMeasure μ := by
    rw [hμ_def]; unfold lvPathMeasure homogeneousPathMeasure; infer_instance
  by_cases hs0 : species0Majority s0
  · -- species 0 is majority: MC_{s0} ↔ "sp0 wins" ↔ MC_{(m,m)} ∘ swapTraj
    have h_eq_set : {ω | majorityConsensusEvent s0 ω} =
        swapTraj ⁻¹' {ω | majorityConsensusEvent (m, m) ω} := by
      ext ω; simp only [Set.mem_setOf, Set.mem_preimage]
      rw [majorityConsensusEvent_swapTraj_diag]
      unfold majorityConsensusEvent
      cases consensusTime ω with
      | top => simp
      | coe t =>
        constructor
        · rintro (⟨_, h1, h2⟩ | ⟨h, _⟩)
          · exact ⟨h1, h2⟩
          · exact absurd hs0 h
        · intro ⟨h1, h2⟩; exact Or.inl ⟨hs0, h1, h2⟩
    have hswap_meas : Measurable swapTraj := by
      rw [measurable_pi_iff]; intro n
      exact (measurable_of_countable PopState.swap).comp (measurable_pi_apply n)
    have hA_meas : MeasurableSet {ω : ℕ → PopState | majorityConsensusEvent (m, m) ω} :=
      measurableSet_majorityConsensusEvent_diag m
    have h_inv : μ.map swapTraj = μ :=
      lvPathMeasure_swap_invariant v params hNeutralAlpha hNeutralGamma m
    rw [h_eq_set, ← Measure.map_apply hswap_meas hA_meas, h_inv]
    exact lemma_identical_gap_fail v params hNeutralAlpha hNeutralGamma m
  · -- species 0 is not majority: MC_{s0} ⊆ MC_{(m,m)}
    apply le_trans (measure_mono _) (lemma_identical_gap_fail v params hNeutralAlpha hNeutralGamma m)
    intro ω hω; simp only [Set.mem_setOf] at hω ⊢
    have hm : ¬species0Majority (m, m) := not_species0Majority_diag' m
    show majorityConsensusEvent (m, m) ω
    unfold majorityConsensusEvent at hω ⊢
    cases hct : consensusTime ω with
    | top => simp [hct] at hω
    | coe t =>
      simp only [hct] at hω ⊢
      rcases hω with ⟨h, _⟩ | ⟨_, h1, h2⟩
      · exact absurd h hs0
      · exact Or.inr ⟨hm, h1, h2⟩

/-- Key Markov property bound at fixed time k: if the chain is at a diagonal
    state (m,m) with m > 0 at time k (first such visit), then
    P(MC ∩ F_k) ≤ (1/2) · P(F_k), where F_k is the first diagonal visit event.

    The proof uses:
    1. LV absorption: consensus states are absorbing for the extinct species.
       So on F_k, ω(0),...,ω(k) are all interior (otherwise a species went extinct
       before k, but then can't reach diagonal at k — contradiction).
    2. Since T > k on F_k, MC(ω) = MC(σ_k(ω)) where σ_k is the shift.
    3. Markov property: E[1_{MC} · 1_{F_k}] = E[P_{ω(k)}(MC_shifted) · 1_{F_k}].
    4. On F_k, ω(k) = (m,m) with m > 0, so P_{(m,m)}(MC) ≤ 1/2
       by `mc_any_from_diagonal_le_half`. -/

private lemma majorityConsensusEvent_mk (s0 : PopState) (ω : ℕ → PopState) (t : ℕ)
    (hct : consensusTime ω = ↑t)
    (h : (species0Majority s0 ∧ (ω t).1 > 0 ∧ (ω t).2 = 0) ∨
         (¬species0Majority s0 ∧ (ω t).2 > 0 ∧ (ω t).1 = 0)) :
    majorityConsensusEvent s0 ω := by
  unfold majorityConsensusEvent; split
  · rename_i heq; exact absurd hct (by rw [heq]; intro h; exact WithTop.coe_ne_top h.symm)
  · rename_i t' heq
    have : t' = t := WithTop.coe_eq_coe.mp (heq.symm.trans hct)
    subst this; exact h

private lemma majorityConsensusEvent_elim (s0 : PopState) (ω : ℕ → PopState)
    (h : majorityConsensusEvent s0 ω) :
    ∃ t : ℕ, consensusTime ω = ↑t ∧
      ((species0Majority s0 ∧ (ω t).1 > 0 ∧ (ω t).2 = 0) ∨
       (¬species0Majority s0 ∧ (ω t).2 > 0 ∧ (ω t).1 = 0)) := by
  have h' := h; unfold majorityConsensusEvent at h'; split at h'
  · exact h'.elim
  · rename_i t heq; exact ⟨t, heq, h'⟩

private lemma mc_first_diagonal_bound
    (v : LVVariant) (params : LVParams) (s s0 : PopState)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)]
    (hNR0 : ∀ t, (lvPathMeasure v params s)
      {ω | (ω t).1 = 0 ∧ (ω (t + 1)).1 ≠ 0} = 0)
    (hNR1 : ∀ t, (lvPathMeasure v params s)
      {ω | (ω t).2 = 0 ∧ (ω (t + 1)).2 ≠ 0} = 0)
    (k : ℕ) :
    (lvPathMeasure v params s)
      ({ω | majorityConsensusEvent s0 ω} ∩
       {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
            ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)}) ≤
    ENNReal.ofReal (1 / 2) *
    (lvPathMeasure v params s)
      {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
           ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)} := by
  set μ := lvPathMeasure v params s
  set MC := {ω : ℕ → PopState | majorityConsensusEvent s0 ω}
  set F := {ω : ℕ → PopState | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
              ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)}
  -- Multi-step no-revival from one-step (species 0)
  have hNR0m : ∀ t j, μ {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + j)).1 ≠ 0} = 0 := by
    intro t j; induction j with
    | zero =>
      convert measure_empty (μ := μ); ext ω; simp [Set.mem_setOf_eq]
    | succ n ih =>
      apply le_antisymm _ zero_le
      have hsub : ({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω (t + (n + 1))).1 ≠ 0} :
          Set (ℕ → PopState)) ⊆
          {ω | (ω t).1 = 0 ∧ (ω (t + n)).1 ≠ 0} ∪
          {ω | (ω (t + n)).1 = 0 ∧ (ω (t + n + 1)).1 ≠ 0} := by
        intro ω ⟨h1, h2⟩
        by_cases h : (ω (t + n)).1 = 0
        · right; exact ⟨h, by rwa [show t + (n + 1) = t + n + 1 from by omega] at h2⟩
        · left; exact ⟨h1, h⟩
      exact le_trans (le_trans (measure_mono hsub) (measure_union_le _ _))
        (by rw [ih, hNR0 (t + n), add_zero])
  -- Multi-step no-revival (species 1)
  have hNR1m : ∀ t j, μ {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + j)).2 ≠ 0} = 0 := by
    intro t j; induction j with
    | zero =>
      convert measure_empty (μ := μ); ext ω; simp [Set.mem_setOf_eq]
    | succ n ih =>
      apply le_antisymm _ zero_le
      have hsub : ({ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω (t + (n + 1))).2 ≠ 0} :
          Set (ℕ → PopState)) ⊆
          {ω | (ω t).2 = 0 ∧ (ω (t + n)).2 ≠ 0} ∪
          {ω | (ω (t + n)).2 = 0 ∧ (ω (t + n + 1)).2 ≠ 0} := by
        intro ω ⟨h1, h2⟩
        by_cases h : (ω (t + n)).2 = 0
        · right; exact ⟨h, by rwa [show t + (n + 1) = t + n + 1 from by omega] at h2⟩
        · left; exact ⟨h1, h⟩
      exact le_trans (le_trans (measure_mono hsub) (measure_union_le _ _))
        (by rw [ih, hNR1 (t + n), add_zero])
  -- "Bad" set: F_k ∩ {early consensus} has measure 0
  have hBadZero : μ (F ∩ {ω : ℕ → PopState | ∃ t, t ≤ k ∧ reachedConsensus (ω t)}) = 0 := by
    apply le_antisymm _ zero_le
    -- Subset into union of revival events
    have hsub : F ∩ {ω | ∃ t, t ≤ k ∧ reachedConsensus (ω t)} ⊆
        ⋃ t ∈ Finset.range (k + 1),
          ({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω k).1 ≠ 0} ∪
           {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω k).2 ≠ 0}) := by
      intro ω ⟨hF, hcons⟩
      have hdiag : (ω k).1 = (ω k).2 := hF.1
      have hpos : 0 < (ω k).1 := hF.2.1
      obtain ⟨t, htk, hrc⟩ := hcons
      simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range]
      exact ⟨t, by omega, by
        cases hrc with
        | inl h0 => left; exact ⟨h0, by omega⟩
        | inr h1 => right; exact ⟨h1, by omega⟩⟩
    calc μ (F ∩ {ω | ∃ t, t ≤ k ∧ reachedConsensus (ω t)})
        ≤ μ (⋃ t ∈ Finset.range (k + 1),
              ({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω k).1 ≠ 0} ∪
               {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω k).2 ≠ 0})) := measure_mono hsub
      _ ≤ ∑ t ∈ Finset.range (k + 1),
            μ ({ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω k).1 ≠ 0} ∪
               {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω k).2 ≠ 0}) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ t ∈ Finset.range (k + 1),
            (μ {ω : ℕ → PopState | (ω t).1 = 0 ∧ (ω k).1 ≠ 0} +
             μ {ω : ℕ → PopState | (ω t).2 = 0 ∧ (ω k).2 ≠ 0}) :=
          Finset.sum_le_sum fun t _ => measure_union_le _ _
      _ = 0 := by
          apply Finset.sum_eq_zero; intro t ht
          have htk : t ≤ k := by have := Finset.mem_range.mp ht; omega
          rw [show k = t + (k - t) from by omega,
              hNR0m t (k - t), hNR1m t (k - t), add_zero]
  -- Pointwise: on MC ∩ F, either σ_k⁻¹(MC) or early consensus
  have hSubset : MC ∩ F ⊆
      (F ∩ (pathShift k) ⁻¹' MC) ∪
      (F ∩ {ω : ℕ → PopState | ∃ t, t ≤ k ∧ reachedConsensus (ω t)}) := by
    intro ω ⟨hMC, hF⟩
    obtain ⟨ct, hct, hMC_prop⟩ := majorityConsensusEvent_elim s0 ω hMC
    by_cases hle : ct ≤ k
    · -- Consensus at or before k → bad set
      right; exact ⟨hF, ct, hle, ((consensusTime_eq_coe_iff ω ct).mp hct).1⟩
    · -- Consensus after k → shifted path also in MC
      push_neg at hle
      left; refine ⟨hF, ?_⟩
      show majorityConsensusEvent s0 (pathShift k ω)
      have hshift_ct : consensusTime (pathShift k ω) = ↑(ct - k) := by
        rw [consensusTime_eq_coe_iff]; constructor
        · show reachedConsensus ((pathShift k ω) (ct - k))
          show reachedConsensus (ω (k + (ct - k)))
          rw [show k + (ct - k) = ct from by omega]
          exact ((consensusTime_eq_coe_iff ω ct).mp hct).1
        · intro j hj
          show ¬reachedConsensus (ω (k + j))
          exact ((consensusTime_eq_coe_iff ω ct).mp hct).2 (k + j) (by omega)
      exact majorityConsensusEvent_mk s0 (pathShift k ω) (ct - k) hshift_ct (by
        show (species0Majority s0 ∧ (ω (k + (ct - k))).1 > 0 ∧ (ω (k + (ct - k))).2 = 0) ∨
             (¬species0Majority s0 ∧ (ω (k + (ct - k))).2 > 0 ∧ (ω (k + (ct - k))).1 = 0)
        rw [show k + (ct - k) = ct from by omega]
        exact hMC_prop)
  -- Markov bound: P(F ∩ σ_k⁻¹ MC) ≤ (1/2) P(F) using homogeneousPathMeasure_markov_bound
  have hMarkov : μ (F ∩ (pathShift k) ⁻¹' MC) ≤ ENNReal.ofReal (1/2) * μ F := by
    simp only [μ, lvPathMeasure]
    exact homogeneousPathMeasure_markov_bound (lvKernel v params) s k
      (ENNReal.ofReal (1/2)) F MC
      (by -- F is measurable
        change MeasurableSet {ω : ℕ → PopState | _}
        have : {ω : ℕ → PopState | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
            ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)} =
          ((fun ω : ℕ → PopState => ω k) ⁻¹' {p : PopState | p.1 = p.2 ∧ 0 < p.1}) ∩
            ⋂ j ∈ Finset.range k,
              ((fun ω : ℕ → PopState => ω j) ⁻¹' {p : PopState | p.1 = p.2 ∧ 0 < p.1})ᶜ := by
          ext ω; simp only [Set.mem_setOf, Set.mem_inter_iff, Set.mem_preimage,
            Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]; tauto
        rw [this]
        exact (measurableSet_coord_pred k _).inter
          (MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ =>
            (measurableSet_coord_pred j _).compl))
      (by -- MC is measurable
        change MeasurableSet {ω : ℕ → PopState | majorityConsensusEvent s0 ω}
        have : {ω : ℕ → PopState | majorityConsensusEvent s0 ω} =
            ⋃ t : ℕ, {ω | consensusTime ω = ↑t} ∩
              ((fun ω : ℕ → PopState => ω t) ⁻¹'
                {q : PopState |
                  (species0Majority s0 ∧ q.1 > 0 ∧ q.2 = 0) ∨
                    (¬species0Majority s0 ∧ q.2 > 0 ∧ q.1 = 0)}) := by
          ext ω
          simp only [Set.mem_setOf, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
          constructor
          · intro h; unfold majorityConsensusEvent at h
            cases hc : consensusTime ω with
            | top => simp [hc] at h
            | coe t => exact ⟨t, rfl, by simp [hc] at h; exact h⟩
          · intro ⟨t, ht, hpred⟩; unfold majorityConsensusEvent
            cases hc : consensusTime ω with
            | top => exact absurd (ht ▸ hc) WithTop.coe_ne_top
            | coe t' =>
              have : t' = t := WithTop.coe_eq_coe.mp (hc.symm.trans ht)
              subst this; exact hpred
        rw [this]
        exact MeasurableSet.iUnion fun t =>
          (measurableSet_consensusTime_eq_coe t).inter (measurableSet_coord_pred t _))
      (by -- F is cylinder up to k
        intro ω ω' hagree ⟨hdiag, hpos, hfirst⟩
        exact ⟨by rw [← hagree k (le_refl k)]; exact hdiag,
               by rw [← hagree k (le_refl k)]; exact hpos,
               fun j hj => by rw [← hagree j (le_of_lt hj)]; exact hfirst j hj⟩)
      (by -- On F, P_{ω(k)}(MC) ≤ 1/2
        intro ω hω
        have hdiag := hω.1; have hpos := hω.2.1
        -- ω(k) = (m, m) with m > 0
        have heq : (ω k) = ((ω k).1, (ω k).1) := by ext <;> simp [hdiag]
        rw [show (ω k) = ((ω k).1, (ω k).1) from heq]
        show lvPathMeasure v params ((ω k).1, (ω k).1) MC ≤ ENNReal.ofReal (1/2)
        exact mc_any_from_diagonal_le_half v params s0 (ω k).1
          hNeutralAlpha hNeutralGamma)
  -- Combine: P(MC ∩ F) ≤ P(F ∩ σ⁻¹MC) + P(bad) ≤ (1/2) P(F) + 0
  calc μ (MC ∩ F) ≤ μ ((F ∩ (pathShift k) ⁻¹' MC) ∪
      (F ∩ {ω : ℕ → PopState | ∃ t, t ≤ k ∧ reachedConsensus (ω t)})) := measure_mono hSubset
    _ ≤ μ (F ∩ (pathShift k) ⁻¹' MC) +
        μ (F ∩ {ω : ℕ → PopState | ∃ t, t ≤ k ∧ reachedConsensus (ω t)}) :=
      measure_union_le _ _
    _ = μ (F ∩ (pathShift k) ⁻¹' MC) + 0 := by rw [hBadZero]
    _ = μ (F ∩ (pathShift k) ⁻¹' MC) := add_zero _
    _ ≤ ENNReal.ofReal (1 / 2) * μ F := hMarkov

/-- Markov property + swap invariance:
    `P(MC ∩ {chain visits a positive diagonal}) ≤ (1/2) P(chain visits a positive diagonal)`.

    **Proof**: decompose D = {∃ k, diagonal} into disjoint first-visit events F_k.
    By `mc_first_diagonal_bound`, P(MC ∩ F_k) ≤ (1/2) · P(F_k).
    Sum over `k`. -/
theorem mc_cap_any_diagonal_le_half_mul
    (v : LVVariant) (params : LVParams) (s s0 : PopState)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)]
    (hNR0 : ∀ t, (lvPathMeasure v params s)
      {ω | (ω t).1 = 0 ∧ (ω (t + 1)).1 ≠ 0} = 0)
    (hNR1 : ∀ t, (lvPathMeasure v params s)
      {ω | (ω t).2 = 0 ∧ (ω (t + 1)).2 ≠ 0} = 0) :
    (lvPathMeasure v params s)
      ({ω | majorityConsensusEvent s0 ω} ∩
        {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}) ≤
      ENNReal.ofReal (1 / 2) *
        (lvPathMeasure v params s)
          {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} := by
  set μ := lvPathMeasure v params s
  set MC := {ω : ℕ → PopState | majorityConsensusEvent s0 ω}
  set D := {ω : ℕ → PopState | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}
  -- F_k = first diagonal visit at time k
  set F : ℕ → Set (ℕ → PopState) :=
    fun k => {ω | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
                  ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)}
  -- D = ⋃_k F_k
  have hD_eq : D = ⋃ k, F k := by
    ext ω; constructor
    · rintro ⟨k₀, hk₀⟩
      -- take the minimal k
      have hex : ∃ k, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 := ⟨k₀, hk₀⟩
      refine Set.mem_iUnion.mpr ⟨Nat.find hex, (Nat.find_spec hex).1,
        (Nat.find_spec hex).2, fun j hj => Nat.find_min hex hj⟩
    · intro h
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      exact ⟨k, hk.1, hk.2.1⟩
  -- F_k are pairwise disjoint
  have hF_disj : Pairwise (Function.onFun Disjoint F) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω ⟨hi1, hi2, himin⟩ ⟨hj1, hj2, hjmin⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact hjmin i h ⟨hi1, hi2⟩
    · exact himin j h ⟨hj1, hj2⟩
  -- F_k are measurable
  -- F_k are measurable: F k = {ω(k) on diagonal} ∩ ⋂_{j<k} {ω(j) not on diagonal}
  have hF_meas : ∀ k, MeasurableSet (F k) := fun k => by
    change MeasurableSet {ω : ℕ → PopState | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
        ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)}
    have hsame : {ω : ℕ → PopState | (ω k).1 = (ω k).2 ∧ 0 < (ω k).1 ∧
        ∀ j, j < k → ¬((ω j).1 = (ω j).2 ∧ 0 < (ω j).1)} =
      ((fun ω : ℕ → PopState => ω k) ⁻¹' {s : PopState | s.1 = s.2 ∧ 0 < s.1}) ∩
        ⋂ j ∈ Finset.range k,
          ((fun ω : ℕ → PopState => ω j) ⁻¹' {s : PopState | s.1 = s.2 ∧ 0 < s.1})ᶜ := by
      ext ω; simp only [Set.mem_setOf, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]; tauto
    rw [hsame]
    exact (measurableSet_coord_pred k _).inter
      (MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ =>
        (measurableSet_coord_pred j _).compl)
  have hMC_meas : MeasurableSet MC := by
    change MeasurableSet {ω : ℕ → PopState | majorityConsensusEvent s0 ω}
    suffices h : {ω : ℕ → PopState | majorityConsensusEvent s0 ω} =
        ⋃ t : ℕ, {ω | consensusTime ω = ↑t} ∩
          ((fun ω : ℕ → PopState => ω t) ⁻¹'
            {q : PopState |
              (species0Majority s0 ∧ q.1 > 0 ∧ q.2 = 0) ∨
                (¬species0Majority s0 ∧ q.2 > 0 ∧ q.1 = 0)}) by
      rw [h]
      exact MeasurableSet.iUnion fun t =>
        (measurableSet_consensusTime_eq_coe t).inter (measurableSet_coord_pred t _)
    ext ω
    simp only [Set.mem_setOf, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro h
      unfold majorityConsensusEvent at h
      cases hct : consensusTime ω with
      | top => simp [hct] at h
      | coe t => exact ⟨t, rfl, by simp [hct] at h; exact h⟩
    · intro ⟨t, ht, hpred⟩
      unfold majorityConsensusEvent
      cases hct : consensusTime ω with
      | top => exact absurd (ht ▸ hct) WithTop.coe_ne_top
      | coe t' =>
        have : t' = t := WithTop.coe_eq_coe.mp (hct.symm.trans ht)
        subst this; exact hpred
  -- P(MC ∩ D) = Σ_k P(MC ∩ F_k)
  have h_sum : μ (MC ∩ D) = ∑' k, μ (MC ∩ F k) := by
    rw [hD_eq, Set.inter_iUnion]
    exact measure_iUnion (fun i j hij => (hF_disj hij).mono
      Set.inter_subset_right Set.inter_subset_right)
      (fun k => hMC_meas.inter (hF_meas k))
  -- For each k: P(MC ∩ F_k) ≤ (1/2) · P(F_k)
  have h_bound : ∀ k, μ (MC ∩ F k) ≤ ENNReal.ofReal (1 / 2) * μ (F k) :=
    fun k => mc_first_diagonal_bound v params s s0 hNeutralAlpha hNeutralGamma hNR0 hNR1 k
  -- Sum the bounds
  calc μ (MC ∩ D) = ∑' k, μ (MC ∩ F k) := h_sum
    _ ≤ ∑' k, ENNReal.ofReal (1 / 2) * μ (F k) :=
        ENNReal.tsum_le_tsum h_bound
    _ = ENNReal.ofReal (1 / 2) * ∑' k, μ (F k) :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 / 2) * μ (⋃ k, F k) := by
        rw [measure_iUnion hF_disj (fun k => hF_meas k)]
    _ = ENNReal.ofReal (1 / 2) * μ D := by rw [hD_eq]

/-- The weaker half bound retained for existing callers. -/
theorem mc_cap_any_diagonal_le_half
    (v : LVVariant) (params : LVParams) (s s0 : PopState)
    (hNeutralAlpha : params.alpha0 = params.alpha1)
    (hNeutralGamma : params.gamma0 = params.gamma1)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)]
    (hNR0 : ∀ t, (lvPathMeasure v params s)
      {ω | (ω t).1 = 0 ∧ (ω (t + 1)).1 ≠ 0} = 0)
    (hNR1 : ∀ t, (lvPathMeasure v params s)
      {ω | (ω t).2 = 0 ∧ (ω (t + 1)).2 ≠ 0} = 0) :
    (lvPathMeasure v params s)
      ({ω | majorityConsensusEvent s0 ω} ∩
        {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1}) ≤
      ENNReal.ofReal (1 / 2) := by
  calc
    (lvPathMeasure v params s)
        ({ω | majorityConsensusEvent s0 ω} ∩
          {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1})
        ≤ ENNReal.ofReal (1 / 2) *
            (lvPathMeasure v params s)
              {ω | ∃ k : ℕ, (ω k).1 = (ω k).2 ∧ 0 < (ω k).1} :=
      mc_cap_any_diagonal_le_half_mul v params s s0 hNeutralAlpha hNeutralGamma hNR0 hNR1
    _ ≤ ENNReal.ofReal (1 / 2) * 1 := by
        apply mul_le_mul_left'
        haveI : IsProbabilityMeasure (lvPathMeasure v params s) := by
          unfold lvPathMeasure homogeneousPathMeasure
          infer_instance
        exact prob_le_one
    _ = ENNReal.ofReal (1 / 2) := mul_one _

end LVConsensus
