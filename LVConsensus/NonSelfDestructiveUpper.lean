import LVConsensus.NiceUpperDomination
import LVConsensus.NonSelfDestructiveUpperCore

set_option autoImplicit false

namespace LVConsensus

/-- Section 6 upper bound for non-self-destructive competition. -/
theorem thm_non_self_destructive_upper
    (params : LVParams)
    (hInter : 0 < min params.alpha0 params.alpha1)
    (hBias : params.alpha1 ≤ params.alpha0)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : NiceChain)
    (hDom : IsDominatingChain N.toBirthDeathChain
      (lvEventProfile .nonSelfDestructive params))
    [ProbabilityTheory.IsMarkovKernel
      (lvKernel LVVariant.nonSelfDestructive params)] :
    ∀ k : Nat, ∃ C : Real, 0 < C ∧
      ∃ n₀ : Nat, ∀ a b : Nat, n₀ ≤ a + b →
        0 < b →
        b < a →
        C *
            Real.sqrt
              (((a + b : Nat) : Real) *
                logScale (a + b)) ≤
          (a : Real) - (b : Real) →
        majorityConsensusProb
            LVVariant.nonSelfDestructive params (a, b) ≥
          ENNReal.ofReal
            (1 - 1 /
              (((a + b : Nat) + 1 : Real) ^ k)) := by
  clear hInter
  intro k
  exact chain_domination_nsd_upper_bound_unconditional
    params k hBias hGamma0 hGamma1 N hDom

end LVConsensus
