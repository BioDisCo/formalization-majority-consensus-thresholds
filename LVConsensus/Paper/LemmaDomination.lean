import LVConsensus.ChainDomination

set_option autoImplicit false

namespace LVConsensus.Paper

/-- Paper `lemma:domination`. -/
theorem lemma_domination
    (v : LVVariant)
    (params : LVParams)
    (hAlpha : 0 < effectiveGoodRate v params)
    (hGamma0 : params.gamma0 = 0)
    (hGamma1 : params.gamma1 = 0) :
    ∃ N : NiceChain,
      IsDominatingChain N.toBirthDeathChain (lvEventProfile v params) :=
  LVConsensus.lemma_domination v params hAlpha hGamma0 hGamma1

end LVConsensus.Paper
