import LVConsensus.LineageFixation

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lem:nsd-intra:lineages`: invariance of the entire lineage path law
under every permutation of the initial lineage labels. -/
theorem lem_nsd_intra_lineages
    (params : LVParams) {n : Nat}
    (π : Equiv.Perm (Lineage n)) :
    (lineagePathMeasure params n).map
        (pathMap (permuteLineageCounts π)) =
      lineagePathMeasure params n :=
  LVConsensus.lineagePathMeasure_permute params π

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

/-- End-to-end form of the lineage argument: the first lineage to become the
sole living lineage is uniform, and aggregation identifies its initial
species with the LV majority winner. -/
theorem nsd_majority_probability_via_lineages
    (params : LVParams)
    (hAlpha : 0 < params.alpha0)
    (hNeutral : params.alpha0 = params.alpha1)
    (hEq0 : params.gamma0 = 2 * params.alpha0)
    (hEq1 : params.gamma1 = 2 * params.alpha1)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    majorityConsensusProb .nonSelfDestructive params (a, b) =
      ENNReal.ofReal ((a : Real) / (a + b)) :=
  LVConsensus.nsd_majority_probability_via_lineages
    params hAlpha hNeutral hEq0 hEq1 a b ha hb hba

end LVConsensus.Paper
