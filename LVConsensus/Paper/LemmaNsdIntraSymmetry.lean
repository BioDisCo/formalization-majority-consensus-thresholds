import LVConsensus.LineageAggregation

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lem:nsd-intra:symmetry`. -/
theorem lem_nsd_intra_symmetry
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) (L L' : LinState n) :
    lineageKernel params n L {L'} =
      lineageKernel params n (permuteLineageCounts π L)
        {permuteLineageCounts π L'} :=
  LVConsensus.lineageKernel_singleton_equivariant params π L L'

end LVConsensus.Paper
