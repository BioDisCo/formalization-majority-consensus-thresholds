import LVConsensus.DominationCategoricalCoupling

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper Lemma 4.1 (chain domination), stated as the two tail inequalities
which define the stochastic orders `T(S) ≼ E(N)` and `J(S) ≼ B(N)`. -/
theorem lemma_chain_domination
    (v : LVVariant) (params : LVParams)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0)
    (s0 : PopState)
    (N : BirthDeathChain) (n0 : Nat)
    (hStart : Nat.min s0.1 s0.2 ≤ n0)
    (hDom : IsDominatingChain N (lvEventProfile v params))
    (hExtinct :
      bdPathMeasure N n0 {η | extinctionTime η = ⊤} = 0) :
    (∀ t : Nat,
      consensusTail v params s0 t ≤ extinctionTail N n0 t) ∧
    (∀ L : Nat,
      labeledBadTail v params s0 L ≤ birthTail N n0 L) :=
  chain_domination_unconditional
    v params hGamma0 hGamma1 s0 N n0
      hStart hDom hExtinct

end LVConsensus.Paper
