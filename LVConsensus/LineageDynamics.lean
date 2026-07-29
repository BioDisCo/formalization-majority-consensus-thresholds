import LVConsensus.Definitions
import LVConsensus.MarkovLib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace LVConsensus

/-!
# Reaction-level lineage dynamics

This file formalizes the lineage chain used in the proof of
`lem:nsd-intra:symmetry` and `lem:nsd-intra:lineages`.  In the neutral NSD
regime every living individual has the same per-capita birth rate and the same
per-capita death/competition rate.  A lineage is therefore selected with
weight proportional to its current number of descendants.

## Scope

`lineageKernel` is defined by the per-capita rates that the paper derives for
the descendant-count process, namely `β L i` for a birth and
`(δ + α₀ (N-1)) L i` for a death, where `N` is the total population. The
equivariance results below are theorems about that kernel.

`LineageAggregation.lean` proves the missing model bridge. Under
`α₀ = α₁` and `γᵢ = 2 αᵢ`, aggregating the lineage counts by the species of the
initial individuals pushes `lineageKernel` forward to the non-self-destructive
`lvKernel`. It also proves the corresponding identity of full path laws.
-/

/-- Lineage index type for an initial population of size `n`. -/
abbrev Lineage (n : Nat) := Fin n

/-- A lineage state records the number of living descendants of every initial
individual. -/
abbrev LinState (n : Nat) := Lineage n → Nat

/-- The action used in the paper: `(π • L)(i) = L(π(i))`. -/
def permuteLineageCounts {n : Nat} (π : Equiv.Perm (Lineage n))
    (L : LinState n) : LinState n :=
  fun i => L (π i)

/-- Total number of living descendants. -/
def lineageTotal {n : Nat} (L : LinState n) : Nat :=
  ∑ i, L i

/-- Add one descendant to lineage `i`. -/
def lineageBirth {n : Nat} (L : LinState n) (i : Lineage n) : LinState n :=
  Function.update L i (L i + 1)

/-- Remove one descendant from lineage `i`.  A zero lineage remains zero. -/
def lineageDeath {n : Nat} (L : LinState n) (i : Lineage n) : LinState n :=
  Function.update L i (L i - 1)

/-- Birth mass assigned to lineage `i`. -/
noncomputable def lineageBirthMass
    (params : LVParams) {n : Nat} (L : LinState n) (i : Lineage n) : ENNReal :=
  ENNReal.ofReal (params.beta * L i)

/-- Death/competition mass assigned to lineage `i` in the neutral NSD
lineage chain.  `α₀ (N-1)` is the common per-individual competition rate. -/
noncomputable def lineageDeathMass
    (params : LVParams) {n : Nat} (L : LinState n) (i : Lineage n) : ENNReal :=
  ENNReal.ofReal
    ((params.delta + params.alpha0 * (lineageTotal L - 1 : Nat)) * L i)

/-- Total reaction mass of the lineage chain. -/
noncomputable def lineageTotalMass
    (params : LVParams) {n : Nat} (L : LinState n) : ENNReal :=
  ∑ i, (lineageBirthMass params L i + lineageDeathMass params L i)

/-- Unnormalised one-step measure of the lineage chain. -/
noncomputable def lineageRawMeasure
    (params : LVParams) {n : Nat} (L : LinState n) : Measure (LinState n) :=
  ∑ i, (lineageBirthMass params L i) • Measure.dirac (lineageBirth L i) +
    ∑ i, (lineageDeathMass params L i) • Measure.dirac (lineageDeath L i)

/-- The neutral NSD lineage transition kernel.  When the total reaction mass is
zero the state is held fixed. -/
noncomputable def lineageKernel (params : LVParams) (n : Nat) :
    Kernel (LinState n) (LinState n) :=
  Kernel.ofFunOfCountable fun L =>
    if h : lineageTotalMass params L = 0 then
      Measure.dirac L
    else
      (lineageTotalMass params L)⁻¹ • lineageRawMeasure params L

private lemma lineageRawMeasure_univ
    (params : LVParams) {n : Nat} (L : LinState n) :
    lineageRawMeasure params L Set.univ = lineageTotalMass params L := by
  simp [lineageRawMeasure, lineageTotalMass, Measure.finset_sum_apply,
    Measure.smul_apply]
  rw [Finset.sum_add_distrib]

instance lineageKernel_isMarkovKernel (params : LVParams) (n : Nat) :
    IsMarkovKernel (lineageKernel params n) where
  isProbabilityMeasure L := ⟨by
    simp only [lineageKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
    split_ifs with h
    · simp
    · rw [Measure.smul_apply, lineageRawMeasure_univ]
      apply ENNReal.inv_mul_cancel h
      unfold lineageTotalMass
      rw [ENNReal.sum_ne_top]
      intro i _
      exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩⟩

lemma lineageTotal_permute
    {n : Nat} (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    lineageTotal (permuteLineageCounts π L) = lineageTotal L := by
  unfold lineageTotal permuteLineageCounts
  simpa only [Function.comp_apply] using
    π.bijective.sum_comp L

lemma lineageBirth_permute
    {n : Nat} (π : Equiv.Perm (Lineage n)) (L : LinState n)
    (i : Lineage n) :
    lineageBirth (permuteLineageCounts π L) i =
      permuteLineageCounts π (lineageBirth L (π i)) := by
  funext j
  simp only [lineageBirth, permuteLineageCounts]
  by_cases hji : j = i
  · subst j
    simp
  · have hp : π j ≠ π i := fun h => hji (π.injective h)
    simp [lineageBirth, permuteLineageCounts, hji, hp]

lemma lineageDeath_permute
    {n : Nat} (π : Equiv.Perm (Lineage n)) (L : LinState n)
    (i : Lineage n) :
    lineageDeath (permuteLineageCounts π L) i =
      permuteLineageCounts π (lineageDeath L (π i)) := by
  funext j
  simp only [lineageDeath, permuteLineageCounts]
  by_cases hji : j = i
  · subst j
    simp
  · have hp : π j ≠ π i := fun h => hji (π.injective h)
    simp [lineageDeath, permuteLineageCounts, hji, hp]

lemma lineageBirthMass_permute
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) (i : Lineage n) :
    lineageBirthMass params (permuteLineageCounts π L) i =
      lineageBirthMass params L (π i) := by
  rfl

lemma lineageDeathMass_permute
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) (i : Lineage n) :
    lineageDeathMass params (permuteLineageCounts π L) i =
      lineageDeathMass params L (π i) := by
  simp [lineageDeathMass, permuteLineageCounts, lineageTotal_permute]

lemma lineageTotalMass_permute
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    lineageTotalMass params (permuteLineageCounts π L) =
      lineageTotalMass params L := by
  unfold lineageTotalMass
  calc
    (∑ i, (lineageBirthMass params (permuteLineageCounts π L) i +
      lineageDeathMass params (permuteLineageCounts π L) i))
        = ∑ i, (lineageBirthMass params L (π i) +
            lineageDeathMass params L (π i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [lineageBirthMass_permute, lineageDeathMass_permute]
    _ = ∑ i, (lineageBirthMass params L i +
          lineageDeathMass params L i) := by
      simpa only [Function.comp_apply] using
        π.bijective.sum_comp
          (fun i => lineageBirthMass params L i +
            lineageDeathMass params L i)

private lemma permuteLineageCounts_measurable
    {n : Nat} (π : Equiv.Perm (Lineage n)) :
    Measurable (permuteLineageCounts π : LinState n → LinState n) :=
  measurable_of_countable _

lemma lineageRawMeasure_permute
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    lineageRawMeasure params (permuteLineageCounts π L) =
      (lineageRawMeasure params L).map (permuteLineageCounts π) := by
  ext A hA
  rw [Measure.map_apply (permuteLineageCounts_measurable π) hA]
  simp only [lineageRawMeasure, Measure.add_apply,
    Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply, Set.mem_preimage]
  apply congrArg₂ (· + ·)
  · exact Fintype.sum_bijective π π.bijective _ _ fun i => by
      rw [lineageBirthMass_permute, lineageBirth_permute]
      rfl
  · exact Fintype.sum_bijective π π.bijective _ _ fun i => by
      rw [lineageDeathMass_permute, lineageDeath_permute]
      rfl

/-- Paper `lem:nsd-intra:symmetry`: the concrete lineage transition kernel is
equivariant under every permutation of the initial individuals. -/
theorem lineageKernel_equivariant
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    lineageKernel params n (permuteLineageCounts π L) =
      (lineageKernel params n L).map (permuteLineageCounts π) := by
  simp only [lineageKernel, Kernel.ofFunOfCountable, Kernel.coe_mk]
  rw [lineageTotalMass_permute]
  split_ifs with h
  · exact (Measure.map_dirac' (permuteLineageCounts_measurable π) L).symm
  · rw [lineageRawMeasure_permute, Measure.map_smul]

/-- Singleton form of the paper's conditional transition-probability
identity. -/
theorem lineageKernel_singleton_equivariant
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L L' : LinState n) :
    lineageKernel params n L {L'} =
      lineageKernel params n (permuteLineageCounts π L)
        {permuteLineageCounts π L'} := by
  rw [lineageKernel_equivariant]
  rw [Measure.map_apply (permuteLineageCounts_measurable π)
    (measurableSet_singleton _)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact (show Function.Injective (permuteLineageCounts π) by
    intro X Y h
    calc
      X = permuteLineageCounts π.symm (permuteLineageCounts π X) := by
        funext i
        simp [permuteLineageCounts]
      _ = permuteLineageCounts π.symm (permuteLineageCounts π Y) :=
        congrArg (permuteLineageCounts π.symm) h
      _ = Y := by
        funext i
        simp [permuteLineageCounts]).eq_iff.symm

/-- The all-ones initial lineage state. -/
def initialLineages (n : Nat) : LinState n := fun _ => 1

lemma initialLineages_permute
    {n : Nat} (π : Equiv.Perm (Lineage n)) :
    permuteLineageCounts π (initialLineages n) = initialLineages n := by
  rfl

/-- Every iterate of the concrete lineage kernel is equivariant. -/
theorem lineageKernel_iter_equivariant
    (params : LVParams) {n t : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    (kernelIter (lineageKernel params n) t)
        (permuteLineageCounts π L) =
      ((kernelIter (lineageKernel params n) t) L).map
        (permuteLineageCounts π) := by
  induction t generalizing L with
  | zero =>
      simp [kernelIter_zero, Kernel.id_apply,
        Measure.map_dirac' (permuteLineageCounts_measurable π)]
  | succ t ih =>
      ext A hA
      rw [kernelIter_succ_right]
      rw [Kernel.comp_apply, Kernel.comp_apply]
      rw [Measure.map_apply (permuteLineageCounts_measurable π) hA]
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
      rw [Measure.bind_apply
        ((permuteLineageCounts_measurable π) hA) (Kernel.aemeasurable _)]
      rw [lineageKernel_equivariant]
      rw [lintegral_map
        (measurable_of_countable
          (fun x => (kernelIter (lineageKernel params n) t) x A))
        (permuteLineageCounts_measurable π)]
      apply lintegral_congr
      intro x
      rw [ih]
      exact Measure.map_apply (permuteLineageCounts_measurable π) hA

/-- Paper `lem:nsd-intra:lineages`: every finite-time lineage distribution
started from the all-ones state is invariant under every permutation. -/
theorem lineageKernel_iter_singleton_invariant
    (params : LVParams) {n t : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    (kernelIter (lineageKernel params n) t) (initialLineages n) {L} =
      (kernelIter (lineageKernel params n) t) (initialLineages n)
        {permuteLineageCounts π L} := by
  have h :=
    lineageKernel_iter_equivariant params π (initialLineages n) (t := t)
  rw [initialLineages_permute] at h
  symm
  calc
    (kernelIter (lineageKernel params n) t) (initialLineages n)
        {permuteLineageCounts π L}
        = ((kernelIter (lineageKernel params n) t) (initialLineages n)).map
            (permuteLineageCounts π) {permuteLineageCounts π L} :=
          congrArg
            (fun μ : Measure (LinState n) => μ {permuteLineageCounts π L}) h
    _ = (kernelIter (lineageKernel params n) t) (initialLineages n) {L} := by
      rw [Measure.map_apply (permuteLineageCounts_measurable π)
        (measurableSet_singleton _)]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (show Function.Injective (permuteLineageCounts π) by
        intro X Y hXY
        calc
          X = permuteLineageCounts π.symm (permuteLineageCounts π X) := by
            funext i
            simp [permuteLineageCounts]
          _ = permuteLineageCounts π.symm (permuteLineageCounts π Y) :=
            congrArg (permuteLineageCounts π.symm) hXY
          _ = Y := by
            funext i
            simp [permuteLineageCounts]).eq_iff

end LVConsensus
