import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.HittingTime

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open scoped BigOperators

namespace LVConsensus

abbrev PopState := Nat × Nat

instance : MeasurableSpace PopState := inferInstance

/-- Gap between species 0 and species 1. -/
def gap (s : PopState) : Int := (s.1 : Int) - (s.2 : Int)

/-- A state has reached consensus iff one species is extinct. -/
def reachedConsensus (s : PopState) : Prop := s.1 = 0 ∨ s.2 = 0

/-- Species `0` is the majority in this state, with ties assigned to species `0`. -/
def species0Majority (s : PopState) : Prop := s.1 ≥ s.2

/-- Birth-death transition parameters on `Nat`. -/
structure BirthDeathChain where
  p : Nat → Real
  q : Nat → Real
  p_nonneg : ∀ n : Nat, 0 ≤ p n
  q_nonneg : ∀ n : Nat, 0 ≤ q n
  pq_le_one : ∀ n : Nat, p n + q n ≤ 1
  absorb_zero : p 0 = 0 ∧ q 0 = 0

/-- Holding probability in state `n`. -/
def holdProb (N : BirthDeathChain) (n : Nat) : Real := 1 - N.p n - N.q n

/-- Nice chains as in the paper. -/
structure NiceChain where
  toBirthDeathChain : BirthDeathChain
  C : Real
  D : Real
  C_pos : 0 < C
  D_pos : 0 < D
  p_le : ∀ n : Nat, 0 < n → toBirthDeathChain.p n ≤ C / (n : Real)
  q_ge : ∀ n : Nat, 0 < n → D ≤ toBirthDeathChain.q n

/-- Two-species LV variant. -/
inductive LVVariant where
  | selfDestructive
  | nonSelfDestructive
  deriving DecidableEq, Repr

/-- Parameters for two-species LV dynamics. -/
structure LVParams where
  beta : Real
  delta : Real
  alpha0 : Real
  alpha1 : Real
  gamma0 : Real
  gamma1 : Real
  beta_nonneg : 0 ≤ beta
  delta_nonneg : 0 ≤ delta
  alpha0_nonneg : 0 ≤ alpha0
  alpha1_nonneg : 0 ≤ alpha1
  gamma0_nonneg : 0 ≤ gamma0
  gamma1_nonneg : 0 ≤ gamma1

/-- Birth-death transition kernel on `Nat` (discrete state-space kernel). -/
noncomputable def bdKernel (N : BirthDeathChain) : ProbabilityTheory.Kernel Nat Nat :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun n : Nat =>
    ENNReal.ofReal (N.p n) • Measure.dirac (n + 1)
      + ENNReal.ofReal (N.q n) • Measure.dirac (n - 1)
      + ENNReal.ofReal (holdProb N n) • Measure.dirac n

/-- History-dependent kernel obtained from a homogeneous kernel by reading the latest state. -/
noncomputable def homogeneousHistoryKernel {α : Type*} [MeasurableSpace α]
    (K : ProbabilityTheory.Kernel α α) (t : Nat) :
    ProbabilityTheory.Kernel ((_ : Finset.Iic t) → α) α :=
  ProbabilityTheory.Kernel.comp K
    (ProbabilityTheory.Kernel.deterministic (fun h => h ⟨t, by simp⟩) (by fun_prop))

/-- Path-space measure of a homogeneous chain with initial measure `μ0` and kernel `K`. -/
noncomputable def homogeneousPathMeasure {α : Type*} [MeasurableSpace α]
    (μ0 : Measure α) (K : ProbabilityTheory.Kernel α α) [ProbabilityTheory.IsMarkovKernel K] :
    Measure (Nat → α) :=
  by
    let κ : (n : Nat) → ProbabilityTheory.Kernel (∀ i : Finset.Iic n, α) α :=
      fun t => homogeneousHistoryKernel K t
    letI : ∀ n, ProbabilityTheory.IsMarkovKernel (κ n) := by
      intro n
      dsimp [κ, homogeneousHistoryKernel]
      infer_instance
    exact ProbabilityTheory.Kernel.trajMeasure (μ₀ := μ0) (κ := κ)

/-- Path-space measure of the birth-death chain started at `n0`. -/
noncomputable def bdPathMeasure (N : BirthDeathChain) (n0 : Nat)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)] : Measure (Nat → Nat) :=
  homogeneousPathMeasure (μ0 := Measure.dirac n0) (K := bdKernel N)

/-- Coordinate process for `Nat`-valued trajectories. -/
def natCoord (t : Nat) (ω : Nat → Nat) : Nat := ω t

/-- Extinction time (first hit of `0`) for a birth-death trajectory. -/
noncomputable def extinctionTime (ω : Nat → Nat) : WithTop Nat :=
  MeasureTheory.hittingAfter natCoord ({0} : Set Nat) 0 ω

/-- Number of births in the first `t` transitions of a trajectory. -/
def birthsUpTo (ω : Nat → Nat) (t : Nat) : Nat :=
  Finset.sum (Finset.range t) (fun i => if ω (i + 1) = ω i + 1 then 1 else 0)

/-- Number of births before extinction (0 if extinction never occurs). -/
noncomputable def birthsBeforeExtinction (ω : Nat → Nat) : Nat :=
  match extinctionTime ω with
  | ⊤ => 0
  | (t : Nat) => birthsUpTo ω t

/-- Expected extinction time (as `ℝ≥0∞`) under the chain law. -/
noncomputable def expectedExtinctionTime (N : BirthDeathChain) (n0 : Nat)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)] : ℝ≥0∞ :=
  ∫⁻ ω, (((extinctionTime ω).untopD 0 : Nat) : ℝ≥0∞) ∂bdPathMeasure N n0

/-- Expected number of births before extinction (as `ℝ≥0∞`). -/
noncomputable def expectedBirthsBeforeExtinction (N : BirthDeathChain) (n0 : Nat)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)] : ℝ≥0∞ :=
  ∫⁻ ω, (birthsBeforeExtinction ω : ℝ≥0∞) ∂bdPathMeasure N n0

/-- Tail probability for extinction time. -/
noncomputable def extinctionTail (N : BirthDeathChain) (n0 t : Nat)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)] : ℝ≥0∞ :=
  bdPathMeasure N n0 {ω | extinctionTime ω ≥ t}

/-- Tail probability for the number of births before extinction. -/
noncomputable def birthTail (N : BirthDeathChain) (n0 t : Nat)
    [ProbabilityTheory.IsMarkovKernel (bdKernel N)] : ℝ≥0∞ :=
  bdPathMeasure N n0 {ω | birthsBeforeExtinction ω ≥ t}

/-- LV total propensity at a population state. -/
noncomputable def lvTotalPropensity (params : LVParams) (s : PopState) : Real :=
  let x0 := s.1
  let x1 := s.2
  params.beta * x0 + params.beta * x1 +
    params.delta * x0 + params.delta * x1 +
      (params.alpha0 + params.alpha1) * x0 * x1 +
        params.gamma0 * (x0 * (x0 - 1) / 2) +
          params.gamma1 * (x1 * (x1 - 1) / 2)

/-- One-step kernel for two-species LV jump chain. -/
noncomputable def lvKernel (v : LVVariant) (params : LVParams) :
    ProbabilityTheory.Kernel PopState PopState :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun s : PopState =>
    let x0 := s.1
    let x1 := s.2
    let φ := lvTotalPropensity params s
    if _hφ : φ = 0 then
      Measure.dirac s
    else
      let invφ := ENNReal.ofReal (1 / φ)
      let wBirth0 := ENNReal.ofReal (params.beta * x0)
      let wBirth1 := ENNReal.ofReal (params.beta * x1)
      let wDeath0 := ENNReal.ofReal (params.delta * x0)
      let wDeath1 := ENNReal.ofReal (params.delta * x1)
      let wInter0 := ENNReal.ofReal (params.alpha0 * x0 * x1)
      let wInter1 := ENNReal.ofReal (params.alpha1 * x0 * x1)
      let wIntra0 := ENNReal.ofReal (params.gamma0 * (x0 * (x0 - 1) / 2))
      let wIntra1 := ENNReal.ofReal (params.gamma1 * (x1 * (x1 - 1) / 2))
      let mBirth0 := Measure.dirac (x0 + 1, x1)
      let mBirth1 := Measure.dirac (x0, x1 + 1)
      let mDeath0 := Measure.dirac (x0 - 1, x1)
      let mDeath1 := Measure.dirac (x0, x1 - 1)
      let mInterSD := Measure.dirac (x0 - 1, x1 - 1)
      let mInter0NSD := Measure.dirac (x0, x1 - 1)
      let mInter1NSD := Measure.dirac (x0 - 1, x1)
      let mIntra0SD := Measure.dirac (x0 - 2, x1)
      let mIntra1SD := Measure.dirac (x0, x1 - 2)
      let mIntra0NSD := Measure.dirac (x0 - 1, x1)
      let mIntra1NSD := Measure.dirac (x0, x1 - 1)
      match v with
      | .selfDestructive =>
          invφ •
              (wBirth0 • mBirth0 + wBirth1 • mBirth1 +
                wDeath0 • mDeath0 + wDeath1 • mDeath1 +
                  wInter0 • mInterSD + wInter1 • mInterSD +
                    wIntra0 • mIntra0SD + wIntra1 • mIntra1SD)
      | .nonSelfDestructive =>
          invφ •
              (wBirth0 • mBirth0 + wBirth1 • mBirth1 +
                wDeath0 • mDeath0 + wDeath1 • mDeath1 +
                  wInter0 • mInter0NSD + wInter1 • mInter1NSD +
                    wIntra0 • mIntra0NSD + wIntra1 • mIntra1NSD)

/-- Path-space measure of the two-species LV chain started at `s0`. -/
noncomputable def lvPathMeasure (v : LVVariant) (params : LVParams) (s0 : PopState)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] : Measure (Nat → PopState) :=
  homogeneousPathMeasure (μ0 := Measure.dirac s0) (K := lvKernel v params)

/-- Coordinate process for `PopState` trajectories. -/
def popCoord (t : Nat) (ω : Nat → PopState) : PopState := ω t

/-- Consensus time (first hit of `x0 = 0` or `x1 = 0`). -/
noncomputable def consensusTime (ω : Nat → PopState) : WithTop Nat :=
  MeasureTheory.hittingAfter popCoord ({s : PopState | reachedConsensus s}) 0 ω

/-- Gap-decreasing bad step used in domination-style bounds. -/
def isBadGapStep (ω : Nat → PopState) (t : Nat) : Prop :=
  let s := ω t
  let s' := ω (t + 1)
  Nat.min s.1 s.2 > 0 ∧ gap s' = gap s - 1

/-- Number of bad gap steps in the first `t` transitions. -/
noncomputable def badGapCountUpTo (ω : Nat → PopState) (t : Nat) : Nat :=
  by
    classical
    exact Finset.sum (Finset.range t) (fun i => if isBadGapStep ω i then 1 else 0)

/-- Number of bad gap steps before consensus (0 if consensus never occurs). -/
noncomputable def badGapCountBeforeConsensus (ω : Nat → PopState) : Nat :=
  match consensusTime ω with
  | ⊤ => 0
  | (t : Nat) => badGapCountUpTo ω t

/-- An individual event step is one where exactly one species' count changes by
    ±1 and the other stays the same (i.e., a birth or death of a single species).
    Under self-destructive competition with γ=0, these are exactly the gap-changing
    steps. Under NSD, this characterization also captures some competitive events
    that happen to look like individual events at the state level; see paper Section 6
    for the precise probabilistic decomposition. -/
def isIndividualEventStep (ω : Nat → PopState) (t : Nat) : Prop :=
  let s := ω t
  let s' := ω (t + 1)
  Nat.min s.1 s.2 > 0 ∧
    ((s'.1 = s.1 + 1 ∧ s'.2 = s.2) ∨    -- Birth of species 0
     (s'.1 + 1 = s.1 ∧ s'.2 = s.2) ∨    -- Death of species 0
     (s'.1 = s.1 ∧ s'.2 = s.2 + 1) ∨    -- Birth of species 1
     (s'.1 = s.1 ∧ s'.2 + 1 = s.2))     -- Death of species 1

/-- Number of individual event steps in the first `t` transitions. -/
noncomputable def individualEventCountUpTo (ω : Nat → PopState) (t : Nat) : Nat :=
  by
    classical
    exact Finset.sum (Finset.range t) (fun i => if isIndividualEventStep ω i then 1 else 0)

/-- Number of individual events before consensus (0 if consensus never occurs). -/
noncomputable def individualEventCountBeforeConsensus (ω : Nat → PopState) : Nat :=
  match consensusTime ω with
  | ⊤ => 0
  | (t : Nat) => individualEventCountUpTo ω t

/-- Event that consensus is reached in finite time. -/
def consensusReachedEvent (ω : Nat → PopState) : Prop :=
  consensusTime ω < ⊤

/-- Event that the initial majority species wins at consensus time. -/
def majorityConsensusEvent (s0 : PopState) (ω : Nat → PopState) : Prop :=
  match consensusTime ω with
  | ⊤ => False
  | (t : Nat) =>
      ((species0Majority s0 ∧ (ω t).1 > 0 ∧ (ω t).2 = 0) ∨
        (¬ species0Majority s0 ∧ (ω t).2 > 0 ∧ (ω t).1 = 0))

/-- Probability of majority consensus under LV dynamics. -/
noncomputable def majorityConsensusProb (v : LVVariant) (params : LVParams) (s0 : PopState)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] : ℝ≥0∞ :=
  lvPathMeasure v params s0 {ω | majorityConsensusEvent s0 ω}

/-- Tail probability of consensus time. -/
noncomputable def consensusTail (v : LVVariant) (params : LVParams) (s0 : PopState) (t : Nat)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] : ℝ≥0∞ :=
  lvPathMeasure v params s0 {ω | consensusTime ω ≥ t}

/-- Tail probability of the number of bad gap steps before consensus. -/
noncomputable def badGapTail (v : LVVariant) (params : LVParams) (s0 : PopState) (t : Nat)
    [ProbabilityTheory.IsMarkovKernel (lvKernel v params)] : ℝ≥0∞ :=
  lvPathMeasure v params s0 {ω | badGapCountBeforeConsensus ω ≥ t}

/-- Eventual `O`-bound (`for sufficiently large n`). -/
def IsBigOEventually (f g : Nat → Real) : Prop :=
  ∃ C : Real, ∃ n0 : Nat, 0 ≤ C ∧ ∀ n : Nat, n0 ≤ n → f n ≤ C * g n

/-- Eventual `Ω`-bound (`for sufficiently large n`). -/
def IsBigOmegaEventually (f g : Nat → Real) : Prop :=
  ∃ c : Real, ∃ n0 : Nat, 0 < c ∧ ∀ n : Nat, n0 ≤ n → c * g n ≤ f n

/-- Eventual `Θ`-bound (`for sufficiently large n`). -/
def IsThetaEventually (f g : Nat → Real) : Prop :=
  IsBigOEventually f g ∧ IsBigOmegaEventually f g

/-- Eventual `O`-bound for an `ℝ≥0∞`-valued quantity. The bound is the image of
a real number under `ENNReal.ofReal`, so it also rules out `f n = ⊤`; stating a
bound on `(f n).toReal` would not, since `(⊤ : ℝ≥0∞).toReal = 0`. -/
def IsBigOEventuallyENN (f : Nat → ℝ≥0∞) (g : Nat → Real) : Prop :=
  ∃ C : Real, ∃ n0 : Nat, 0 ≤ C ∧ ∀ n : Nat, n0 ≤ n → f n ≤ ENNReal.ofReal (C * g n)

/-- `log (n+1)` helper. -/
noncomputable def logScale (n : Nat) : Real := Real.log (n + 1)

/-- `log^2` helper. -/
noncomputable def logSqScale (n : Nat) : Real := (logScale n) ^ (2 : Nat)

/-- Nat-valued logarithmic scale used in tail bounds. -/
noncomputable def logScaleNat (n : Nat) : Nat := Int.toNat (Int.ceil (logScale n))

/-- Nat-valued squared logarithmic scale used in tail bounds. -/
noncomputable def logSqScaleNat (n : Nat) : Nat := Int.toNat (Int.ceil (logSqScale n))

/-- High-probability tail template with eventual quantifier. -/
def WhpTailBound (tail : Nat → Nat → ℝ≥0∞) (f : Nat → Nat) : Prop :=
  ∀ k : Nat, ∃ C n0 : Nat, 0 < C ∧
    ∀ n : Nat, n0 ≤ n → tail n (C * f n) ≤ ((n + 1 : ℝ≥0∞) ^ k)⁻¹

/-- Stochastic domination for `Nat`-valued random variables on one probability space. -/
def StochDominates {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → Nat) : Prop :=
  ∀ t : Nat, μ {ω | t ≤ X ω} ≤ μ {ω | t ≤ Y ω}

end LVConsensus

/-! ## Path shift and Markov property -/

namespace LVConsensus

open ProbabilityTheory ProbabilityTheory.Kernel Preorder

/-- Path shift by k steps: maps ω to (fun n => ω (k + n)). -/
def pathShift {α : Type*} (k : ℕ) (ω : ℕ → α) : ℕ → α := fun n => ω (k + n)

/-- A set B on ℕ → α is a cylinder up to time k if membership depends only on
    coordinates 0, ..., k. -/
def isCylinderUpTo {α : Type*} (k : ℕ) (B : Set (ℕ → α)) : Prop :=
  ∀ ω ω' : ℕ → α, (∀ i, i ≤ k → ω i = ω' i) → ω ∈ B → ω' ∈ B

end LVConsensus
