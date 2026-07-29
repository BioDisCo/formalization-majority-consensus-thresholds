import LVConsensus.LineageAggregation

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lem:nsd-intra:lineages`. -/
theorem lem_nsd_intra_lineages
    (params : LVParams) {n t : Nat}
    (π : Equiv.Perm (Lineage n)) (L : LinState n) :
    (kernelIter (lineageKernel params n) t)
        (initialLineages n) {L} =
      (kernelIter (lineageKernel params n) t)
        (initialLineages n) {permuteLineageCounts π L} :=
  LVConsensus.lineageKernel_iter_singleton_invariant params π L

/-- The bridge needed to interpret the lineage chain in the paper as a
refinement of the non-self-destructive Lotka--Volterra chain. -/
theorem nsd_lineage_path_recovers_lv
    (params : LVParams)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) :
    (lineagePathMeasure params (a + b)).map
        (pathMap (lineageAggregate a)) =
      lvPathMeasure .nonSelfDestructive params (a, b) :=
  LVConsensus.lineagePathMeasure_map_aggregate
    params hNeutral hEq0 hEq1 a b

end LVConsensus.Paper
