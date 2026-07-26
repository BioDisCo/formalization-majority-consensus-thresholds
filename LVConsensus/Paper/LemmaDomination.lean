import LVConsensus.ChainDomination

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:domination`. -/
theorem lemma_domination
    (v : LVVariant)
    (params : LVParams)
    (hGood : 0 < effectiveGoodRate v params)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∃ N : NiceChain,
      IsDominatingChain N.toBirthDeathChain (lvEventProfile v params) ∧
      (∀ n : Nat,
        N.toBirthDeathChain.p n =
          if n = 0 then 0 else
            (params.beta + params.delta) /
              ((params.alpha0 + params.alpha1) * (n : Real) +
                (params.beta + params.delta))) ∧
      (∀ n : Nat,
        N.toBirthDeathChain.q n =
          if n = 0 then 0 else
            effectiveGoodRate v params /
              ((params.alpha0 + params.alpha1) +
                2 * (params.beta + params.delta))) :=
  LVConsensus.lemma_domination_spec
    v params hGood hGamma0 hGamma1

end LVConsensus.Paper
