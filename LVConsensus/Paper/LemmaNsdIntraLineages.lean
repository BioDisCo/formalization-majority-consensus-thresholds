import LVConsensus.LineageDynamics

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

end LVConsensus.Paper
