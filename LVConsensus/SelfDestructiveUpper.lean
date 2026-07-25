import LVConsensus.NiceUpperDomination
import LVConsensus.SelfDestructiveUpperCore

set_option autoImplicit false

namespace LVConsensus

/-- Section 5 upper bound for self-destructive competition.
    Paper Theorem (line 654): for any k ≥ 0, ∃ C(k) such that if Δ₀ > C(k)·log²(n),
    then ρ(S) ≥ 1 - 1/n^k. -/
theorem thm_self_destructive_upper
    (params : LVParams)
    (hInter : 0 < params.alpha0 + params.alpha1)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (N : NiceChain)
    (hDom : IsDominatingChain N.toBirthDeathChain
      (lvEventProfile .selfDestructive params))
    [ProbabilityTheory.IsMarkovKernel (lvKernel LVVariant.selfDestructive params)] :
    ∀ k : Nat, ∃ C : Real, 0 < C ∧
      ∃ n0 : Nat, ∀ a b : Nat, n0 ≤ a + b →
        b < a →
        C * logSqScale (a + b) ≤ (a : Real) - (b : Real) →
          majorityConsensusProb LVVariant.selfDestructive params (a, b)
            ≥ ENNReal.ofReal (1 - (1 / (((a + b : Nat) + 1 : Real) ^ k))) := by
  clear hInter
  intro k
  exact chain_domination_upper_bound_unconditional
    params k hGamma0 hGamma1 N hDom

end LVConsensus
