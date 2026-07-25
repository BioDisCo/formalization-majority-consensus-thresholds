/-
  AxiomProbe — check which declarations are axiom-clean, and fail the build
  if a result hides a custom `axiom` or if a verified-badge result regresses
  to `sorry`.

  `#print axioms f` reports every axiom in `f`'s entire transitive dependency
  graph. Interpretation:

    • [propext, Classical.choice, Quot.sound]  → axiom-clean (only the
      standard Lean/Mathlib axioms). This is necessary but not sufficient for
      a `\leanproof` badge: the declaration must also state the paper result
      exactly and must not assume a certificate containing the missing proof.
    • ... sorryAx ...                          → a `sorry` is reached somewhere
      below this theorem; NOT proved. At most `\leanformalized`.
    • any other name (e.g. coupling_nat_aux)   → depends on a custom `axiom`;
      NOT unconditional, and easy to miss — `check_sorry.sh`'s per-file grep
      does not catch a `private axiom` in another file. The audit below does.

  A file passing check_sorry.sh only means it has no `sorry`/`axiom` of its own
  — a theorem there can still hit a `sorry` or custom `axiom` in an imported
  lemma. Only `#print axioms` / `collectAxioms` see through imports.

  Usage (from the lean/ directory):
      lake env lean AxiomProbe.lean          -- dump + audit; nonzero exit on failure
      lake env lean AxiomProbe.lean 2>&1 | grep -iB1 sorryAx   -- open items only

  This file lives at the package root (not under LVConsensus/), so `lake build`
  and check_sorry.sh ignore it during the per-file scan; check_sorry.sh runs it
  explicitly as the axiom-audit step.
-/
import Lean
import LVConsensus

open Lean Elab Command

/-! ## Human-readable dump -/

-- § Preliminaries (paper Section 2)
#print axioms LVConsensus.Paper.lemma_chernoff
#print axioms LVConsensus.Paper.lemma_hoeffding
#print axioms LVConsensus.Paper.lemma_clt
#print axioms LVConsensus.Paper.lemma_couple_with_independent

-- § Nice single-species chains (paper Section 3)
#print axioms LVConsensus.Paper.lemma_nice_extinction
#print axioms LVConsensus.Paper.lemma_nice_expected_births
#print axioms LVConsensus.Paper.lemma_nice_whp_births
#print axioms LVConsensus.Paper.lemma_nice_whp_extinction

-- § Dominating chains (paper Section 4)
#print axioms LVConsensus.Paper.lemma_chain_domination
#print axioms LVConsensus.Paper.lem_coupling_dominates
#print axioms LVConsensus.Paper.lemma_delayed_coupling
#print axioms LVConsensus.Paper.lemma_domination
#print axioms LVConsensus.Paper.theorem_nice_upper_domination

-- § Self-destructive competition (paper Section 5)
#print axioms LVConsensus.Paper.theorem_self_destructive_upper
#print axioms LVConsensus.Paper.lemma_identical_gap_fail
#print axioms LVConsensus.Paper.lemma_log_individual_events
#print axioms LVConsensus.Paper.theorem_self_destructive_lower

-- § Non-self-destructive competition (paper Section 6)
#print axioms LVConsensus.Paper.theorem_non_self_destructive_upper
#print axioms LVConsensus.Paper.thm_non_self_destructive_lower

-- § Intraspecific competition (paper Section 7)
#print axioms LVConsensus.Paper.theorem_nsd_intra
#print axioms LVConsensus.Paper.lem_nsd_intra_symmetry
#print axioms LVConsensus.Paper.lem_nsd_intra_lineages
#print axioms LVConsensus.Paper.corollary_nsd_intra
#print axioms LVConsensus.Paper.theorem_sd_intra
#print axioms LVConsensus.Paper.lemma_continuous_extinction
#print axioms LVConsensus.Paper.theorem_intraspecific_only

/-! ## Machine-checked audit

Two guarantees, both enforced by `throwError` (nonzero exit → CI fails):

1. No probed result depends on a custom `axiom` outside `toleratedAxioms`.
   This catches things a per-file grep misses, e.g. `coupling_nat_aux`.
2. Every result carrying a `verified` (`\leanproof`) badge in the paper stays
   free of `sorry`. If an upstream lemma regresses to `sorry`, the badge claim
   breaks and so does this check.

To probe a new theorem, add it to `allProbed` (and to the dump above). To claim
a new verified badge, add it to `verifiedBadge`. The `` ``name `` literals are
resolved at elaboration, so a rename here fails loudly instead of silently
skipping the check.
-/

/-- The standard Lean/Mathlib axioms; a proof using only these is unconditional. -/
private def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Custom axioms we knowingly tolerate. Keep empty; add an entry only with a
    written justification, since anything here is an unproved assumption. -/
private def toleratedAxioms : List Name := []

private def isSorryAx (a : Name) : Bool := a == `sorryAx

private def isCustomAxiom (a : Name) : Bool :=
  !standardAxioms.contains a && !isSorryAx a && !toleratedAxioms.contains a

/-- All results in the dump above. -/
private def allProbed : List Name :=
  [``LVConsensus.Paper.lemma_chernoff, ``LVConsensus.Paper.lemma_hoeffding,
   ``LVConsensus.Paper.lemma_clt,
   ``LVConsensus.Paper.lemma_couple_with_independent,
   ``LVConsensus.Paper.lemma_nice_extinction,
   ``LVConsensus.Paper.lemma_nice_expected_births,
   ``LVConsensus.Paper.lemma_nice_whp_births,
   ``LVConsensus.Paper.lemma_nice_whp_extinction,
   ``LVConsensus.Paper.lemma_chain_domination,
   ``LVConsensus.Paper.lem_coupling_dominates,
   ``LVConsensus.Paper.lemma_delayed_coupling,
   ``LVConsensus.Paper.lemma_domination,
   ``LVConsensus.Paper.theorem_nice_upper_domination,
   ``LVConsensus.Paper.theorem_self_destructive_upper,
   ``LVConsensus.Paper.lemma_identical_gap_fail,
   ``LVConsensus.Paper.lemma_log_individual_events,
   ``LVConsensus.Paper.theorem_self_destructive_lower,
   ``LVConsensus.Paper.theorem_non_self_destructive_upper,
   ``LVConsensus.Paper.thm_non_self_destructive_lower,
   ``LVConsensus.Paper.theorem_nsd_intra,
   ``LVConsensus.Paper.lem_nsd_intra_symmetry,
   ``LVConsensus.Paper.lem_nsd_intra_lineages,
   ``LVConsensus.Paper.corollary_nsd_intra,
   ``LVConsensus.Paper.theorem_sd_intra,
   ``LVConsensus.Paper.lemma_continuous_extinction,
   ``LVConsensus.Paper.theorem_intraspecific_only]

/-- Results carrying a `verified` (`\leanproof`) badge in `paper_revision.tex`.
    These must stay free of `sorry`. -/
private def verifiedBadge : List Name :=
  allProbed

run_cmd do
  let mut violations : Array MessageData := #[]
  let mut nUncond : Nat := 0
  let mut nSorry : Nat := 0
  for n in allProbed do
    let axs ← liftCoreM <| collectAxioms n
    let custom := axs.filter isCustomAxiom
    let hasSorry := axs.any isSorryAx
    unless custom.isEmpty do
      violations := violations.push m!"  {n} depends on custom axiom(s): {custom.toList}"
    if hasSorry then nSorry := nSorry + 1
    else if custom.isEmpty then nUncond := nUncond + 1
  for n in verifiedBadge do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any isSorryAx then
      violations := violations.push
        m!"  {n} carries a verified badge but now depends on sorry"
  logWarning m!"AxiomProbe audit: {nUncond} axiom-clean, {nSorry} depend on sorry, \
             of {allProbed.length} probed"
  unless violations.isEmpty do
    throwError m!"Axiom audit failed:\n{MessageData.joinSep violations.toList "\n"}\n\
      Prove the offending lemma, or (custom axioms only) add it to \
      `toleratedAxioms` with justification."
