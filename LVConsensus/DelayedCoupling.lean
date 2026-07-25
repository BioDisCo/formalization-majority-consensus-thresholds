import LVConsensus.MarkovLib
import LVConsensus.ProofHelpers

set_option autoImplicit false

open MeasureTheory

namespace LVConsensus

/-!
# The delayed time change used by the pseudo-coupling

The pseudo-coupling inserts a finite (possibly random) number of frozen steps
between successive transitions of the original chain.  This file isolates and
proves the exact time-change statement: sampling the delayed path at its
successive active times recovers the original path, pathwise and hence in
distribution.
-/

/-- Number of active transitions completed by physical time `t`. -/
def delayedActiveIndex (τ : Nat → Nat) (t : Nat) : Nat :=
  Nat.findGreatest (fun k => τ k ≤ t) t

/-- Insert frozen intervals into a path according to the strictly increasing
sequence of active times `τ`. -/
def delayedPath {σ : Type*} (X : Nat → σ) (τ : Nat → Nat) : Nat → σ :=
  fun t => X (delayedActiveIndex τ t)

private lemma strictMono_id_le (τ : Nat → Nat) (hτ : StrictMono τ) :
    ∀ k, k ≤ τ k :=
  StrictMono.id_le hτ

lemma delayedActiveIndex_at_active
    (τ : Nat → Nat) (hτ : StrictMono τ) (k : Nat) :
    delayedActiveIndex τ (τ k) = k := by
  unfold delayedActiveIndex
  rw [Nat.findGreatest_eq_iff]
  refine ⟨strictMono_id_le τ hτ k, ?_, ?_⟩
  · intro _
    exact le_rfl
  · intro j hkj hjτ
    exact Nat.not_le_of_lt (hτ hkj)

/-- At the `k`-th active time, the delayed path is exactly at the `k`-th
state of the original path. -/
theorem delayedPath_at_active
    {σ : Type*} (X : Nat → σ) (τ : Nat → Nat)
    (hτ : StrictMono τ) (k : Nat) :
    delayedPath X τ (τ k) = X k := by
  simp [delayedPath, delayedActiveIndex_at_active τ hτ k]

/-- Every active time is finite when represented by the finite return-time
sequence produced by the pseudo-coupling construction. -/
theorem delayed_active_time_finite
    (τ : Nat → Nat) (k : Nat) :
    (τ k : WithTop Nat) < ⊤ := by
  simp

/-- Distributional form of `delayedPath_at_active`, allowing the active-time
sequence to depend on the sample point. -/
theorem delayedPath_marginal_eq
    {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ]
    (μ : Measure Ω)
    (X : Ω → Nat → σ) (τ : Ω → Nat → Nat)
    (hτ : ∀ ω, StrictMono (τ ω)) (k : Nat) :
    Measure.map
        (fun ω => delayedPath (X ω) (τ ω) (τ ω k)) μ =
      Measure.map (fun ω => X ω k) μ := by
  congr 1
  funext ω
  exact delayedPath_at_active (X ω) (τ ω) (hτ ω) k

/-- A skip-free path which later reaches zero must visit every lower level. -/
lemma skipFree_path_hits_level
    (N : Nat → Nat) (start T r : Nat)
    (hstartT : start ≤ T)
    (hzero : N T = 0)
    (hstep : ∀ t, N (t + 1) + 1 ≥ N t)
    (hr : r ≤ N start) :
    ∃ t, start ≤ t ∧ N t = r := by
  let f : Nat → Nat := fun u => N (start + u)
  have hend : f (T - start) = 0 := by
    simp only [f]
    rw [Nat.add_sub_of_le hstartT, hzero]
  have hlocal : ∀ u, u < T - start → f (u + 1) + 1 ≥ f u := by
    intro u _
    simpa only [f, Nat.add_assoc] using hstep (start + u)
  obtain ⟨u, _, hu⟩ :=
    discrete_descending_ivt f (T - start) (N start) rfl hend hlocal r hr
  exact ⟨start + u, Nat.le_add_right start u, hu⟩

/-- First occurrence of `r` no earlier than `start`; it falls back to `start`
only when no such occurrence exists. -/
noncomputable def firstLevelHitAfter
    (N : Nat → Nat) (start r : Nat) : Nat := by
  classical
  exact if h : ∃ t, start ≤ t ∧ N t = r then Nat.find h else start

lemma firstLevelHitAfter_spec
    (N : Nat → Nat) (start r : Nat)
    (h : ∃ t, start ≤ t ∧ N t = r) :
    start ≤ firstLevelHitAfter N start r ∧
      N (firstLevelHitAfter N start r) = r := by
  rw [firstLevelHitAfter, dif_pos h]
  exact Nat.find_spec h

/-- Active return times obtained by letting the auxiliary chain catch the
level of each successive state of the original path. -/
noncomputable def pseudoActiveTime
    {σ : Type*} (level : σ → Nat) (X : Nat → σ) (N : Nat → Nat) :
    Nat → Nat
  | 0 => 0
  | k + 1 =>
      firstLevelHitAfter N (pseudoActiveTime level X N k + 1)
        (level (X (k + 1)))

lemma pseudoActiveTime_succ_spec
    {σ : Type*} (level : σ → Nat) (X : Nat → σ) (N : Nat → Nat)
    (hstep : ∀ t, N (t + 1) + 1 ≥ N t)
    (hextinct : ∀ start, ∃ T, start ≤ T ∧ N T = 0)
    (hdom : ∀ k,
      level (X (k + 1)) ≤ N (pseudoActiveTime level X N k + 1))
    (k : Nat) :
    pseudoActiveTime level X N k + 1 ≤
        pseudoActiveTime level X N (k + 1) ∧
      N (pseudoActiveTime level X N (k + 1)) =
        level (X (k + 1)) := by
  obtain ⟨T, hT, hT0⟩ :=
    hextinct (pseudoActiveTime level X N k + 1)
  have hhit :
      ∃ t, pseudoActiveTime level X N k + 1 ≤ t ∧
        N t = level (X (k + 1)) :=
    skipFree_path_hits_level N
      (pseudoActiveTime level X N k + 1) T
      (level (X (k + 1))) hT hT0 hstep (hdom k)
  simpa only [pseudoActiveTime] using
    firstLevelHitAfter_spec N
      (pseudoActiveTime level X N k + 1)
      (level (X (k + 1))) hhit

lemma pseudoActiveTime_strictMono
    {σ : Type*} (level : σ → Nat) (X : Nat → σ) (N : Nat → Nat)
    (hstep : ∀ t, N (t + 1) + 1 ≥ N t)
    (hextinct : ∀ start, ∃ T, start ≤ T ∧ N T = 0)
    (hdom : ∀ k,
      level (X (k + 1)) ≤ N (pseudoActiveTime level X N k + 1)) :
    StrictMono (pseudoActiveTime level X N) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hspec :=
    pseudoActiveTime_succ_spec level X N hstep hextinct hdom k
  omega

/-- Pathwise delayed-coupling conclusion from the three properties used in
the paper's proof: skip-free auxiliary motion, eventual extinction, and the
domination inequality immediately after each active update. -/
theorem lemma_delayed_coupling_pathwise
    {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ]
    (μ : Measure Ω) (level : σ → Nat)
    (X : Ω → Nat → σ) (N : Ω → Nat → Nat)
    (hstep : ∀ ω t, N ω (t + 1) + 1 ≥ N ω t)
    (hextinct : ∀ ω start, ∃ T, start ≤ T ∧ N ω T = 0)
    (hdom : ∀ ω k,
      level (X ω (k + 1)) ≤
        N ω (pseudoActiveTime level (X ω) (N ω) k + 1)) :
    ∀ k : Nat,
      (∀ ω,
        (pseudoActiveTime level (X ω) (N ω) k : WithTop Nat) < ⊤) ∧
      Measure.map
          (fun ω =>
            delayedPath (X ω)
              (pseudoActiveTime level (X ω) (N ω))
              (pseudoActiveTime level (X ω) (N ω) k)) μ =
      Measure.map (fun ω => X ω k) μ := by
  intro k
  have hmono : ∀ ω,
      StrictMono (pseudoActiveTime level (X ω) (N ω)) := by
    intro ω
    exact pseudoActiveTime_strictMono level (X ω) (N ω)
      (hstep ω) (hextinct ω) (hdom ω)
  constructor
  · intro ω
    exact delayed_active_time_finite _ k
  · exact delayedPath_marginal_eq μ X
      (fun ω => pseudoActiveTime level (X ω) (N ω)) hmono k

/-- Paper `lemma:delayed-coupling`.  The construction and its three path
properties need only hold almost surely.  Sampling the delayed path at its
successive active return times then has exactly the marginal law of the
original chain. -/
theorem lemma_delayed_coupling
    {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ]
    (μ : Measure Ω) (level : σ → Nat)
    (X : Ω → Nat → σ) (N : Ω → Nat → Nat)
    (hstep : ∀ᵐ ω ∂μ, ∀ t, N ω (t + 1) + 1 ≥ N ω t)
    (hextinct : ∀ᵐ ω ∂μ, ∀ start, ∃ T, start ≤ T ∧ N ω T = 0)
    (hdom : ∀ᵐ ω ∂μ, ∀ k,
      level (X ω (k + 1)) ≤
        N ω (pseudoActiveTime level (X ω) (N ω) k + 1)) :
    ∀ k : Nat,
      (∀ᵐ ω ∂μ,
        (pseudoActiveTime level (X ω) (N ω) k : WithTop Nat) < ⊤) ∧
      Measure.map
          (fun ω =>
            delayedPath (X ω)
              (pseudoActiveTime level (X ω) (N ω))
              (pseudoActiveTime level (X ω) (N ω) k)) μ =
        Measure.map (fun ω => X ω k) μ := by
  intro k
  constructor
  · filter_upwards with ω
    exact delayed_active_time_finite _ k
  · apply Measure.map_congr
    filter_upwards [hstep, hextinct, hdom] with ω hs he hd
    exact delayedPath_at_active
      (X ω) (pseudoActiveTime level (X ω) (N ω))
      (pseudoActiveTime_strictMono level (X ω) (N ω) hs he hd) k

/-- Paper `lemma:delayed-coupling`, with the paper's indexing convention
`τ(1)=0`: the state at `τ(k+1)` has the `k`-step marginal of the original
chain, and `τ(k+1)` is finite. -/
theorem delayedCoupling_time_change_succ
    {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ]
    (μ : Measure Ω)
    (X : Ω → Nat → σ) (τ : Ω → Nat → Nat)
    (_hτzero : ∀ ω, τ ω 0 = 0)
    (hτ : ∀ ω, StrictMono (τ ω)) :
    ∀ k : Nat,
      (∀ ω, (τ ω (k + 1) : WithTop Nat) < ⊤) ∧
      Measure.map
          (fun ω => delayedPath (X ω) (τ ω) (τ ω (k + 1))) μ =
        Measure.map (fun ω => X ω (k + 1)) μ := by
  intro k
  constructor
  · intro ω
    exact delayed_active_time_finite (τ ω) (k + 1)
  · exact delayedPath_marginal_eq μ X τ hτ (k + 1)

/-- Version matching the paper's shifted notation exactly: its `τ(k+1)` is
our active time `τ(k)`, because the paper numbers the initial active time as
`τ(1)`. -/
theorem delayedCoupling_time_change
    {Ω σ : Type*} [MeasurableSpace Ω] [MeasurableSpace σ]
    (μ : Measure Ω)
    (X : Ω → Nat → σ) (τ : Ω → Nat → Nat)
    (_hτzero : ∀ ω, τ ω 0 = 0)
    (hτ : ∀ ω, StrictMono (τ ω)) :
    ∀ k : Nat,
      (∀ ω, (τ ω k : WithTop Nat) < ⊤) ∧
      Measure.map
          (fun ω => delayedPath (X ω) (τ ω) (τ ω k)) μ =
        Measure.map (fun ω => X ω k) μ := by
  intro k
  constructor
  · intro ω
    exact delayed_active_time_finite (τ ω) k
  · exact delayedPath_marginal_eq μ X τ hτ k

end LVConsensus
