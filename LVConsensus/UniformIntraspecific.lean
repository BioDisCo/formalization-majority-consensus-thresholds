import LVConsensus.ContinuousTimeExtinction
import LVConsensus.MarkovLib
import LVConsensus.KernelPathMap
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace LVConsensus

/-!
# Uniform failure for intraspecific-only competition

This file formalizes the extinction-time race argument used in the paper.
The two species evolve independently in continuous time when the
interspecific rates vanish.  A uniform upper bound on the majority
species' mean extinction time, a uniform lower tail supplied by the last
holding time of the minority species, and independence give a failure
probability that is uniform over the initial population counts.
-/

/-- Intraspecific rate of the selected species. -/
noncomputable def speciesGamma (params : LVParams) (i : Bool) : Real :=
  if i then params.gamma1 else params.gamma0

/-- Birth rate of one isolated species. -/
noncomputable def singleSpeciesBirthRate
    (params : LVParams) (n : Nat) : Real :=
  params.beta * n

/-- Individual-death rate of one isolated species. -/
noncomputable def singleSpeciesIndividualDeathRate
    (params : LVParams) (n : Nat) : Real :=
  params.delta * n

/-- Intraspecific-reaction rate of one isolated species. -/
noncomputable def singleSpeciesIntraRate
    (params : LVParams) (i : Bool) (n : Nat) : Real :=
  speciesGamma params i * ((n : Real) * ((n : Real) - 1) / 2)

/-- Reference continuous-time birth--death chain in which every downward
reaction removes one individual.  Its bounded increasing potential will
also control the SD process, where an intraspecific reaction removes two
individuals. -/
noncomputable def singleSpeciesReferenceCT
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    ContinuousTimeBirthDeathChain where
  birthRate := singleSpeciesBirthRate params
  deathRate := fun n =>
    singleSpeciesIndividualDeathRate params n +
      singleSpeciesIntraRate params i n
  birth_nonneg := by
    intro n
    exact mul_nonneg params.beta_nonneg (Nat.cast_nonneg n)
  death_nonneg := by
    intro n
    apply add_nonneg
    · exact mul_nonneg params.delta_nonneg (Nat.cast_nonneg n)
    · apply mul_nonneg
      · cases i <;> simp [speciesGamma, params.gamma0_nonneg,
          params.gamma1_nonneg]
      · rcases n with _ | n
        · norm_num
        · have hn : (1 : Real) ≤ (n + 1 : Nat) := by exact_mod_cast Nat.succ_pos n
          positivity
  rates_zero := by
    simp [singleSpeciesBirthRate, singleSpeciesIndividualDeathRate,
      singleSpeciesIntraRate]
  death_pos := by
    intro n hn
    have hnR : (0 : Real) < n := Nat.cast_pos.mpr hn
    have hIndividual :
        0 < singleSpeciesIndividualDeathRate params n := by
      exact mul_pos hDelta hnR
    have hIntra :
        0 ≤ singleSpeciesIntraRate params i n := by
      apply mul_nonneg
      · cases i <;> simp [speciesGamma, params.gamma0_nonneg,
          params.gamma1_nonneg]
      · have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
        positivity
    exact add_pos_of_pos_of_nonneg hIndividual hIntra

lemma singleSpeciesReferenceCT_rate_bounds
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) :
    HasAtMostLinearBirthQuadraticDeathRates
      (singleSpeciesReferenceCT params i hDelta) := by
  constructor
  · refine ⟨params.beta, 0, params.beta_nonneg, ?_⟩
    intro n _
    simp [singleSpeciesReferenceCT, singleSpeciesBirthRate]
  · refine ⟨speciesGamma params i / 4, 2, by positivity, ?_⟩
    intro n hn
    have hnR : (2 : Real) ≤ n := by exact_mod_cast hn
    have hGammaNonneg : 0 ≤ speciesGamma params i := hGamma.le
    have hDeltaTerm :
        0 ≤ singleSpeciesIndividualDeathRate params n := by
      exact mul_nonneg params.delta_nonneg (Nat.cast_nonneg n)
    have hQuad :
        (speciesGamma params i / 4) * (n : Real) ^ 2 ≤
          singleSpeciesIntraRate params i n := by
      simp only [singleSpeciesIntraRate]
      nlinarith [mul_nonneg hGammaNonneg
        (sq_nonneg ((n : Real) - 2))]
    dsimp only [singleSpeciesReferenceCT]
    linarith

theorem exists_singleSpecies_monotone_certificate
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) :
    ∃ cert : CTAbsorptionCertificate
        (singleSpeciesReferenceCT params i hDelta),
      Monotone cert.V :=
  exists_monotone_ctAbsorptionCertificate
    (singleSpeciesReferenceCT params i hDelta)
    (singleSpeciesReferenceCT_rate_bounds params i hDelta hGamma)

/-- A Boolean selects species `0` (`false`) or species `1` (`true`). -/
def speciesState (i : Bool) (n : Nat) : PopState :=
  if i then (0, n) else (n, 0)

/-- Read the selected coordinate from a population state. -/
def speciesCount (i : Bool) (s : PopState) : Nat :=
  if i then s.2 else s.1

@[simp] lemma speciesCount_speciesState (i : Bool) (n : Nat) :
    speciesCount i (speciesState i n) = n := by
  cases i <;> simp [speciesState, speciesCount]

/-- Count reached by one intraspecific reaction. -/
def singleSpeciesIntraTarget (v : LVVariant) (n : Nat) : Nat :=
  match v with
  | .selfDestructive => n - 2
  | .nonSelfDestructive => n - 1

/-- Total reaction rate of one species when the other species is absent. -/
noncomputable def singleSpeciesTotalRate
    (params : LVParams) (i : Bool) (n : Nat) : Real :=
  lvTotalPropensity params (speciesState i n)

/-- Embedded jump law of the selected species in isolation. -/
noncomputable def singleSpeciesJumpMeasure
    (v : LVVariant) (params : LVParams) (i : Bool) (n : Nat) :
    Measure Nat :=
  (lvKernel v params (speciesState i n)).map (speciesCount i)

instance singleSpeciesJumpMeasure_isProbability
    (v : LVVariant) (params : LVParams) (i : Bool) (n : Nat) :
    IsProbabilityMeasure (singleSpeciesJumpMeasure v params i n) := by
  unfold singleSpeciesJumpMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_of_countable (speciesCount i)).aemeasurable

lemma singleSpeciesTotalRate_pos
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) (hn : 0 < n) :
    0 < singleSpeciesTotalRate params i n := by
  have hnR : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
  have hquad : 0 ≤ (n : Real) * ((n : Real) - 1) / 2 := by positivity
  have hβ := LVParams.beta_nonneg params
  have hα0 := LVParams.alpha0_nonneg params
  have hα1 := LVParams.alpha1_nonneg params
  have hγ0 := LVParams.gamma0_nonneg params
  have hγ1 := LVParams.gamma1_nonneg params
  cases i <;>
    simp only [singleSpeciesTotalRate, speciesState, Bool.false_eq_true,
      ↓reduceIte, lvTotalPropensity] <;>
    nlinarith [mul_nonneg hβ hnR.le, mul_pos hDelta hnR,
      mul_nonneg hγ0 hquad, mul_nonneg hγ1 hquad]

lemma singleSpeciesTotalRate_eq
    (params : LVParams) (i : Bool) (n : Nat) :
    singleSpeciesTotalRate params i n =
      singleSpeciesBirthRate params n +
        singleSpeciesIndividualDeathRate params n +
          singleSpeciesIntraRate params i n := by
  cases i <;>
    simp [singleSpeciesTotalRate, speciesState, lvTotalPropensity,
      singleSpeciesBirthRate, singleSpeciesIndividualDeathRate,
      singleSpeciesIntraRate, speciesGamma] <;>
    ring

lemma singleSpeciesJumpMeasure_eq
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) (hn : 0 < n) :
    singleSpeciesJumpMeasure v params i n =
      ENNReal.ofReal (1 / singleSpeciesTotalRate params i n) •
        (ENNReal.ofReal (singleSpeciesBirthRate params n) •
            Measure.dirac (n + 1) +
          ENNReal.ofReal (singleSpeciesIndividualDeathRate params n) •
            Measure.dirac (n - 1) +
          ENNReal.ofReal (singleSpeciesIntraRate params i n) •
            Measure.dirac (singleSpeciesIntraTarget v n)) := by
  have hRate :
      singleSpeciesTotalRate params i n ≠ 0 :=
    (singleSpeciesTotalRate_pos params i hDelta n hn).ne'
  cases v <;> cases i
  · simp only [singleSpeciesJumpMeasure, speciesState, speciesCount,
      Bool.false_eq_true, ↓reduceIte, singleSpeciesTotalRate] at hRate ⊢
    rw [lvKernel_sd_apply params n 0 hRate]
    simp [Measure.map_smul, Measure.map_add, Measure.map_dirac',
      measurable_of_countable, singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate, singleSpeciesIntraRate,
      speciesGamma, singleSpeciesIntraTarget, speciesCount]
  · simp only [singleSpeciesJumpMeasure, speciesState, speciesCount,
      Bool.false_eq_true, ↓reduceIte, singleSpeciesTotalRate] at hRate ⊢
    rw [lvKernel_sd_apply params 0 n hRate]
    simp [Measure.map_smul, Measure.map_add, Measure.map_dirac',
      measurable_of_countable, singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate, singleSpeciesIntraRate,
      speciesGamma, singleSpeciesIntraTarget, speciesCount]
  · simp only [singleSpeciesJumpMeasure, speciesState, speciesCount,
      Bool.false_eq_true, ↓reduceIte, singleSpeciesTotalRate] at hRate ⊢
    rw [lvKernel_nsd_apply params n 0 hRate]
    simp [Measure.map_smul, Measure.map_add, Measure.map_dirac',
      measurable_of_countable, singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate, singleSpeciesIntraRate,
      speciesGamma, singleSpeciesIntraTarget, speciesCount]
  · simp only [singleSpeciesJumpMeasure, speciesState, speciesCount,
      Bool.false_eq_true, ↓reduceIte, singleSpeciesTotalRate] at hRate ⊢
    rw [lvKernel_nsd_apply params 0 n hRate]
    simp [Measure.map_smul, Measure.map_add, Measure.map_dirac',
      measurable_of_countable, singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate, singleSpeciesIntraRate,
      speciesGamma, singleSpeciesIntraTarget, speciesCount]

/-- Mean holding time at an isolated-species count. -/
noncomputable def singleSpeciesHoldingCost
    (params : LVParams) (i : Bool) (n : Nat) : ENNReal :=
  if n = 0 then 0
  else ENNReal.ofReal (1 / singleSpeciesTotalRate params i n)

lemma singleSpeciesHoldingCost_eq_reference
    (params : LVParams) (i : Bool) (hDelta : 0 < params.delta)
    (n : Nat) :
    singleSpeciesHoldingCost params i n =
      ctHoldingCost (singleSpeciesReferenceCT params i hDelta) n := by
  by_cases hn : n = 0
  · simp [singleSpeciesHoldingCost, ctHoldingCost, hn]
  · simp only [singleSpeciesHoldingCost, ctHoldingCost, hn, ↓reduceIte]
    congr 2
    rw [singleSpeciesTotalRate_eq]
    dsimp only [singleSpeciesReferenceCT]
    ring

lemma singleSpeciesIntraTarget_le_pred
    (v : LVVariant) (n : Nat) :
    singleSpeciesIntraTarget v n ≤ n - 1 := by
  cases v <;> simp [singleSpeciesIntraTarget] <;> omega

lemma singleSpeciesReferenceJumpMeasure_eq
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) (hn : 0 < n) :
    bdKernel (singleSpeciesReferenceCT params i hDelta).embedded n =
      ENNReal.ofReal (1 / singleSpeciesTotalRate params i n) •
        (ENNReal.ofReal (singleSpeciesBirthRate params n) •
            Measure.dirac (n + 1) +
          ENNReal.ofReal (singleSpeciesIndividualDeathRate params n) •
            Measure.dirac (n - 1) +
          ENNReal.ofReal (singleSpeciesIntraRate params i n) •
            Measure.dirac (n - 1)) := by
  have hTotal :
      singleSpeciesTotalRate params i n =
        (singleSpeciesReferenceCT params i hDelta).birthRate n +
          (singleSpeciesReferenceCT params i hDelta).deathRate n := by
    rw [singleSpeciesTotalRate_eq]
    dsimp only [singleSpeciesReferenceCT]
    ring
  have hTotalPos :
      0 < singleSpeciesTotalRate params i n :=
    singleSpeciesTotalRate_pos params i hDelta n hn
  have hBirth :
      0 ≤ singleSpeciesBirthRate params n :=
    mul_nonneg params.beta_nonneg (Nat.cast_nonneg n)
  have hIndividual :
      0 ≤ singleSpeciesIndividualDeathRate params n :=
    mul_nonneg params.delta_nonneg (Nat.cast_nonneg n)
  have hIntra :
      0 ≤ singleSpeciesIntraRate params i n := by
    apply mul_nonneg
    · cases i <;> simp [speciesGamma, params.gamma0_nonneg,
        params.gamma1_nonneg]
    · have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
      positivity
  have hHold :
      holdProb (singleSpeciesReferenceCT params i hDelta).embedded n = 0 := by
    unfold holdProb
    simp only [ContinuousTimeBirthDeathChain.embedded, hn.ne',
      ↓reduceIte]
    rw [← hTotal]
    field_simp [hTotalPos.ne']
    linarith [hTotal]
  rw [bdKernel_apply, hHold]
  simp only [ContinuousTimeBirthDeathChain.embedded, hn.ne',
    ↓reduceIte]
  simp only [ENNReal.ofReal_zero, zero_smul, add_zero]
  rw [← hTotal]
  change
    ENNReal.ofReal
          (singleSpeciesBirthRate params n /
            singleSpeciesTotalRate params i n) •
        Measure.dirac (n + 1) +
      ENNReal.ofReal
          ((singleSpeciesIndividualDeathRate params n +
              singleSpeciesIntraRate params i n) /
            singleSpeciesTotalRate params i n) •
        Measure.dirac (n - 1) =
      ENNReal.ofReal (1 / singleSpeciesTotalRate params i n) •
        (ENNReal.ofReal (singleSpeciesBirthRate params n) •
            Measure.dirac (n + 1) +
          ENNReal.ofReal (singleSpeciesIndividualDeathRate params n) •
            Measure.dirac (n - 1) +
          ENNReal.ofReal (singleSpeciesIntraRate params i n) •
            Measure.dirac (n - 1))
  rw [show
      ENNReal.ofReal
          (singleSpeciesBirthRate params n /
            singleSpeciesTotalRate params i n) =
      ENNReal.ofReal (1 / singleSpeciesTotalRate params i n) *
          ENNReal.ofReal (singleSpeciesBirthRate params n) by
      rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hTotalPos.le)]
      congr 2
      field_simp [hTotalPos.ne']]
  rw [show
      ENNReal.ofReal
          ((singleSpeciesIndividualDeathRate params n +
              singleSpeciesIntraRate params i n) /
            singleSpeciesTotalRate params i n) =
        ENNReal.ofReal (1 / singleSpeciesTotalRate params i n) *
          ENNReal.ofReal
            (singleSpeciesIndividualDeathRate params n +
              singleSpeciesIntraRate params i n) by
      rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hTotalPos.le)]
      congr 2
      field_simp [hTotalPos.ne']]
  rw [ENNReal.ofReal_add hIndividual hIntra]
  module

lemma singleSpecies_lintegral_le_reference
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (f : Nat → ENNReal) (hf : Monotone f)
    (n : Nat) (hn : 0 < n) :
    ∫⁻ m, f m ∂singleSpeciesJumpMeasure v params i n ≤
      ∫⁻ m, f m ∂
        bdKernel (singleSpeciesReferenceCT params i hDelta).embedded n := by
  rw [singleSpeciesJumpMeasure_eq v params i hDelta n hn,
    singleSpeciesReferenceJumpMeasure_eq params i hDelta n hn]
  simp only [lintegral_smul_measure, lintegral_add_measure,
    lintegral_dirac, smul_eq_mul]
  gcongr
  exact hf (singleSpeciesIntraTarget_le_pred v n)

/-- Finite-horizon expected holding time for the actual isolated species. -/
noncomputable def singleSpeciesAbsorptionReward
    (v : LVVariant) (params : LVParams) (i : Bool) :
    Nat → Nat → ENNReal
  | 0, _ => 0
  | t + 1, n =>
      if n = 0 then 0
      else
        singleSpeciesHoldingCost params i n +
          ∫⁻ m, singleSpeciesAbsorptionReward v params i t m ∂
            singleSpeciesJumpMeasure v params i n

lemma singleSpeciesAbsorptionReward_le_certificate
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params i hDelta))
    (hmono : Monotone cert.V) :
    ∀ t n, singleSpeciesAbsorptionReward v params i t n ≤ cert.V n := by
  intro t
  induction t with
  | zero =>
      intro n
      simp [singleSpeciesAbsorptionReward]
  | succ t ih =>
      intro n
      by_cases hn : n = 0
      · subst n
        simp [singleSpeciesAbsorptionReward, cert.zero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        simp only [singleSpeciesAbsorptionReward, hn, ↓reduceIte]
        calc
          singleSpeciesHoldingCost params i n +
              ∫⁻ m, singleSpeciesAbsorptionReward v params i t m ∂
                singleSpeciesJumpMeasure v params i n
              ≤ singleSpeciesHoldingCost params i n +
                  ∫⁻ m, cert.V m ∂
                    singleSpeciesJumpMeasure v params i n := by
                gcongr with m
                exact ih m
          _ ≤ singleSpeciesHoldingCost params i n +
                  ∫⁻ m, cert.V m ∂
                    bdKernel
                      (singleSpeciesReferenceCT params i hDelta).embedded n := by
                exact add_le_add le_rfl
                  (singleSpecies_lintegral_le_reference
                    v params i hDelta cert.V hmono n hnpos)
          _ = ctHoldingCost
                  (singleSpeciesReferenceCT params i hDelta) n +
                ∫⁻ m, cert.V m ∂
                  bdKernel
                    (singleSpeciesReferenceCT params i hDelta).embedded n := by
                rw [singleSpeciesHoldingCost_eq_reference]
          _ ≤ cert.V n := cert.drift n hnpos

lemma expMeasure_Ioi
    {r t : Real} (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi t) =
      ENNReal.ofReal (Real.exp (-(r * t))) := by
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  have hfinite : expMeasure r (Set.Iic t) ≠ ⊤ :=
    measure_ne_top _ _
  have hIic :
      expMeasure r (Set.Iic t) =
        ENNReal.ofReal (1 - Real.exp (-(r * t))) := by
    calc
      expMeasure r (Set.Iic t) =
          ENNReal.ofReal ((expMeasure r (Set.Iic t)).toReal) :=
            (ENNReal.ofReal_toReal hfinite).symm
      _ = ENNReal.ofReal (cdf (expMeasure r) t) := by
            rw [cdf_eq_real, measureReal_def]
      _ = ENNReal.ofReal (1 - Real.exp (-(r * t))) := by
            rw [cdf_expMeasure_eq hr, if_pos ht]
  have hexp_le_one : Real.exp (-(r * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  rw [show Set.Ioi t = (Set.Iic t)ᶜ by ext x; simp]
  rw [measure_compl measurableSet_Iic hfinite, measure_univ, hIic]
  rw [ENNReal.ofReal_sub _ (Real.exp_nonneg _), ENNReal.ofReal_one]
  exact ENNReal.sub_sub_cancel ENNReal.one_ne_top
    (ENNReal.ofReal_le_one.mpr hexp_le_one)

lemma expMeasure_ae_nonneg {r : Real} (hr : 0 < r) :
    0 ≤ᵐ[expMeasure r] (fun x : Real => x) := by
  have hIic :
      expMeasure r (Set.Iic 0) = 0 := by
    letI : IsProbabilityMeasure (expMeasure r) :=
      isProbabilityMeasure_expMeasure hr
    have hfinite : expMeasure r (Set.Iic 0) ≠ ⊤ :=
      measure_ne_top _ _
    calc
      expMeasure r (Set.Iic 0) =
          ENNReal.ofReal ((expMeasure r (Set.Iic 0)).toReal) :=
            (ENNReal.ofReal_toReal hfinite).symm
      _ = ENNReal.ofReal (cdf (expMeasure r) 0) := by
            rw [cdf_eq_real, measureReal_def]
      _ = 0 := by simp [cdf_expMeasure_eq hr]
  change ∀ᵐ x ∂expMeasure r, 0 ≤ x
  rw [ae_iff]
  have hsub : {x : Real | x < 0} ⊆ Set.Iic 0 := by
    intro x hx
    change x < 0 at hx
    exact hx.le
  simpa only [not_le] using measure_mono_null hsub hIic

lemma expMeasure_lintegral_id
    {r : Real} (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal x ∂expMeasure r =
      ENNReal.ofReal (1 / r) := by
  rw [lintegral_eq_lintegral_meas_lt
    (expMeasure r) (expMeasure_ae_nonneg hr) measurable_id.aemeasurable]
  have htail :
      ∀ t ∈ Set.Ioi (0 : Real),
        expMeasure r {x : Real | t < x} =
          ENNReal.ofReal (Real.exp (-(r * t))) := by
    intro t ht
    exact expMeasure_Ioi hr ht.le
  rw [setLIntegral_congr_fun measurableSet_Ioi htail]
  have hint :
      IntegrableOn (fun t : Real => Real.exp (-(r * t))) (Set.Ioi 0) := by
    convert integrableOn_exp_mul_Ioi (a := -r) (by linarith) 0 using 1
    · funext t
      congr 2
      ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
  have hIntegral :
      ∫ t : Real in Set.Ioi 0, Real.exp (-(r * t)) = 1 / r := by
    have hGamma :
        Real.Gamma (1 / (1 : Real) + 1) = 1 := by
      norm_num
    have hFormula :=
      integral_exp_neg_mul_rpow
        (p := (1 : Real)) (b := r) zero_lt_one hr
    rw [hGamma, mul_one] at hFormula
    norm_num [Real.rpow_neg_one] at hFormula
    simpa [one_div] using hFormula
  rw [hIntegral]

/-- Markov kernel of the isolated embedded count chain. -/
noncomputable def singleSpeciesJumpKernel
    (v : LVVariant) (params : LVParams) (i : Bool) :
    Kernel Nat Nat :=
  Kernel.ofFunOfCountable (singleSpeciesJumpMeasure v params i)

lemma singleSpeciesJumpKernel_isMarkov
    (v : LVVariant) (params : LVParams) (i : Bool) :
    IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
  ⟨singleSpeciesJumpMeasure_isProbability v params i⟩

/-- Path law of the isolated embedded count chain. -/
noncomputable def singleSpeciesCountPathMeasure
    (v : LVVariant) (params : LVParams) (i : Bool) (m : Nat) :
    Measure (Nat → Nat) := by
  letI := singleSpeciesJumpKernel_isMarkov v params i
  exact homogeneousPathMeasure
    (Measure.dirac m)
    (singleSpeciesJumpKernel v params i)

/-- One timed transition.  At positive count `n`, it independently samples
the next embedded count and the exponential holding time spent at `n`.
At zero it returns `(0,0)`. -/
noncomputable def singleSpeciesTimedStep
    (v : LVVariant) (params : LVParams) (i : Bool) (n : Nat) :
    Measure (Nat × Real) :=
  if n = 0 then Measure.dirac (0, 0)
  else
    (singleSpeciesJumpMeasure v params i n).prod
      (expMeasure (singleSpeciesTotalRate params i n))

lemma singleSpeciesTimedStep_isProbability
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) :
    IsProbabilityMeasure (singleSpeciesTimedStep v params i n) := by
  unfold singleSpeciesTimedStep
  split_ifs with hn
  · infer_instance
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    letI : IsProbabilityMeasure
        (expMeasure (singleSpeciesTotalRate params i n)) :=
      isProbabilityMeasure_expMeasure
        (singleSpeciesTotalRate_pos params i hDelta n hnpos)
    infer_instance

/-- Timed Markov kernel on `(count, previous holding time)`.  The second
coordinate does not influence the next transition. -/
noncomputable def singleSpeciesTimedKernel
    (v : LVVariant) (params : LVParams) (i : Bool) :
    Kernel (Nat × Real) (Nat × Real) :=
  (Kernel.ofFunOfCountable
      (singleSpeciesTimedStep v params i)).comap
    Prod.fst measurable_fst

lemma singleSpeciesTimedKernel_isMarkov
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    IsMarkovKernel (singleSpeciesTimedKernel v params i) := by
  refine ⟨fun z => ?_⟩
  rw [singleSpeciesTimedKernel, Kernel.comap_apply]
  exact singleSpeciesTimedStep_isProbability v params i hDelta z.1

/-- Timed single-species path law started with count `m`. -/
noncomputable def singleSpeciesTimedPathMeasure
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) :
    Measure (Nat → Nat × Real) := by
  letI := singleSpeciesTimedKernel_isMarkov v params i hDelta
  exact homogeneousPathMeasure
    (Measure.dirac (m, 0))
    (singleSpeciesTimedKernel v params i)

/-- Holding-time contribution of one timed state. -/
noncomputable def timedStateHolding (z : Nat × Real) : ENNReal :=
  ENNReal.ofReal z.2

lemma measurable_timedStateHolding :
    Measurable timedStateHolding :=
  ENNReal.measurable_ofReal.comp measurable_snd

lemma singleSpeciesTimedStep_map_fst
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) :
    (singleSpeciesTimedStep v params i n).map Prod.fst =
      singleSpeciesJumpMeasure v params i n := by
  by_cases hn : n = 0
  · subst n
    simp [singleSpeciesTimedStep, singleSpeciesJumpMeasure,
      speciesState, speciesCount, lvKernel_apply_zero_propensity,
      lvTotalPropensity, Measure.map_dirac']
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hRate :
        0 < singleSpeciesTotalRate params i n :=
      singleSpeciesTotalRate_pos params i hDelta n hnpos
    letI : IsProbabilityMeasure
        (expMeasure (singleSpeciesTotalRate params i n)) :=
      isProbabilityMeasure_expMeasure hRate
    simp [singleSpeciesTimedStep, hn, Measure.map_fst_prod]

lemma singleSpeciesTimedStep_holding
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) :
    ∫⁻ z, timedStateHolding z ∂
        singleSpeciesTimedStep v params i n =
      singleSpeciesHoldingCost params i n := by
  by_cases hn : n = 0
  · subst n
    simp [singleSpeciesTimedStep, timedStateHolding,
      singleSpeciesHoldingCost]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hRate :
        0 < singleSpeciesTotalRate params i n :=
      singleSpeciesTotalRate_pos params i hDelta n hnpos
    letI : IsProbabilityMeasure
        (expMeasure (singleSpeciesTotalRate params i n)) :=
      isProbabilityMeasure_expMeasure hRate
    simp only [singleSpeciesTimedStep, hn, ↓reduceIte]
    rw [lintegral_prod timedStateHolding
      measurable_timedStateHolding.aemeasurable]
    simp only [timedStateHolding]
    rw [expMeasure_lintegral_id hRate, lintegral_const, measure_univ,
      mul_one]
    simp [singleSpeciesHoldingCost, hn]

lemma singleSpeciesTimedStep_lintegral_fst
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (f : Nat → ENNReal) (hf : Measurable f) (n : Nat) :
    ∫⁻ z, f z.1 ∂singleSpeciesTimedStep v params i n =
      ∫⁻ m, f m ∂singleSpeciesJumpMeasure v params i n := by
  calc
    ∫⁻ z, f z.1 ∂singleSpeciesTimedStep v params i n =
        ∫⁻ m, f m ∂
          (singleSpeciesTimedStep v params i n).map Prod.fst := by
            exact (lintegral_map hf measurable_fst).symm
    _ = ∫⁻ m, f m ∂singleSpeciesJumpMeasure v params i n := by
          rw [singleSpeciesTimedStep_map_fst v params i hDelta n]

lemma singleSpeciesTimedKernel_map_fst
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (z : Nat × Real) :
    ((singleSpeciesTimedKernel v params i) z).map Prod.fst =
      singleSpeciesJumpKernel v params i z.1 := by
  rw [singleSpeciesTimedKernel, Kernel.comap_apply]
  exact singleSpeciesTimedStep_map_fst v params i hDelta z.1

lemma singleSpeciesTimedStep_certificate_drift
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params i hDelta))
    (hmono : Monotone cert.V) (n : Nat) :
    ∫⁻ z, timedStateHolding z + cert.V z.1 ∂
        singleSpeciesTimedStep v params i n ≤
      cert.V n := by
  rw [lintegral_add_left measurable_timedStateHolding
    (fun z => cert.V z.1)]
  rw [singleSpeciesTimedStep_holding v params i hDelta n,
    singleSpeciesTimedStep_lintegral_fst
      v params i hDelta cert.V (measurable_of_countable _) n]
  by_cases hn : n = 0
  · subst n
    simp [singleSpeciesHoldingCost, cert.zero,
      singleSpeciesJumpMeasure, speciesState, speciesCount,
      lvKernel_apply_zero_propensity, lvTotalPropensity]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    calc
      singleSpeciesHoldingCost params i n +
          ∫⁻ m, cert.V m ∂singleSpeciesJumpMeasure v params i n
          ≤ singleSpeciesHoldingCost params i n +
              ∫⁻ m, cert.V m ∂
                bdKernel
                  (singleSpeciesReferenceCT params i hDelta).embedded n := by
            exact add_le_add le_rfl
              (singleSpecies_lintegral_le_reference
                v params i hDelta cert.V hmono n hnpos)
      _ = ctHoldingCost
              (singleSpeciesReferenceCT params i hDelta) n +
            ∫⁻ m, cert.V m ∂
              bdKernel
                (singleSpeciesReferenceCT params i hDelta).embedded n := by
            rw [singleSpeciesHoldingCost_eq_reference]
      _ ≤ cert.V n := cert.drift n hnpos

lemma singleSpeciesAbsorptionReward_eq_sum
    (v : LVVariant) (params : LVParams) (i : Bool)
    (t m : Nat) :
    singleSpeciesAbsorptionReward v params i t m =
      ∑ k ∈ Finset.range t,
        ∫⁻ n, singleSpeciesHoldingCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  induction t generalizing m with
  | zero =>
      simp [singleSpeciesAbsorptionReward]
  | succ t ih =>
      have hshift (k : Nat) :
          ∫⁻ n, (∫⁻ x, singleSpeciesHoldingCost params i x ∂
              (kernelIter (singleSpeciesJumpKernel v params i) k) n) ∂
                singleSpeciesJumpKernel v params i m =
            ∫⁻ x, singleSpeciesHoldingCost params i x ∂
              (kernelIter
                (singleSpeciesJumpKernel v params i) (k + 1)) m := by
        rw [show k + 1 = 1 + k by omega]
        rw [kernelIter_lintegral_add
          (singleSpeciesJumpKernel v params i) 1 k m
          (singleSpeciesHoldingCost params i)
          (measurable_of_countable _)]
        rw [kernelIter_one]
      by_cases hm : m = 0
      · subst m
        have hzero :
            singleSpeciesJumpKernel v params i 0 = Measure.dirac 0 := by
          change singleSpeciesJumpMeasure v params i 0 = Measure.dirac 0
          simp [singleSpeciesJumpKernel, singleSpeciesJumpMeasure,
            speciesState, speciesCount, lvKernel_apply_zero_propensity,
            lvTotalPropensity]
        have hiter :
            ∀ k : Nat,
              (kernelIter (singleSpeciesJumpKernel v params i) k) 0 =
                Measure.dirac 0 := by
          intro k
          induction k with
          | zero =>
              simp [kernelIter_zero, Kernel.id_apply]
          | succ k hk =>
              rw [kernelIter_succ, Kernel.comp_apply, hk]
              rw [Measure.dirac_bind (Kernel.measurable _) 0]
              exact hzero
        simp_rw [hiter]
        simp [singleSpeciesAbsorptionReward, singleSpeciesHoldingCost,
          lintegral_dirac]
      · simp only [singleSpeciesAbsorptionReward, hm, ↓reduceIte]
        change
          singleSpeciesHoldingCost params i m +
              ∫⁻ n, singleSpeciesAbsorptionReward v params i t n ∂
                singleSpeciesJumpKernel v params i m =
            ∑ k ∈ Finset.range (t + 1),
              ∫⁻ n, singleSpeciesHoldingCost params i n ∂
                (kernelIter (singleSpeciesJumpKernel v params i) k) m
        simp_rw [ih]
        rw [lintegral_finset_sum (Finset.range t)
          (fun _ _ => Measurable.lintegral_kernel
            (measurable_of_countable _))]
        simp_rw [hshift]
        rw [Finset.sum_range_succ']
        simp [kernelIter_zero, Kernel.id_apply, lintegral_dirac]
        ac_rfl

theorem singleSpecies_expected_holding_sum_le
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params i hDelta))
    (hmono : Monotone cert.V) (m : Nat) :
    ∑' k : Nat,
        ∫⁻ n, singleSpeciesHoldingCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m ≤
      cert.bound := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun t => ?_
  rw [← singleSpeciesAbsorptionReward_eq_sum v params i t m]
  exact
    (singleSpeciesAbsorptionReward_le_certificate
      v params i hDelta cert hmono t m).trans
        (cert.le_bound m)

theorem singleSpeciesTimedPathMeasure_map_count
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m : Nat) :
    (singleSpeciesTimedPathMeasure v params i hDelta m).map
        (pathMap Prod.fst) =
      singleSpeciesCountPathMeasure v params i m := by
  letI : IsMarkovKernel (singleSpeciesTimedKernel v params i) :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  change
    (homogeneousPathMeasure (Measure.dirac (m, 0))
        (singleSpeciesTimedKernel v params i)).map
          (pathMap Prod.fst) =
      homogeneousPathMeasure (Measure.dirac m)
        (singleSpeciesJumpKernel v params i)
  exact homogeneousPathMeasure_map_pathMap
    (singleSpeciesTimedKernel v params i)
    (singleSpeciesJumpKernel v params i)
    Prod.fst measurable_fst
    (singleSpeciesTimedKernel_map_fst v params i hDelta) (m, 0)

lemma singleSpeciesTimedKernel_iter_map_fst
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m k : Nat) :
    ((kernelIter (singleSpeciesTimedKernel v params i) k) (m, 0)).map
        Prod.fst =
      (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
  letI : IsMarkovKernel (singleSpeciesTimedKernel v params i) :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  let P :=
    homogeneousPathMeasure (Measure.dirac (m, 0))
      (singleSpeciesTimedKernel v params i)
  have hTimed :
      P.map (fun ω => ω k) =
        (kernelIter (singleSpeciesTimedKernel v params i) k) (m, 0) := by
    exact homogeneousPathMeasure_dirac_marginal
      (singleSpeciesTimedKernel v params i) (m, 0) k
  have hCount :
      (homogeneousPathMeasure (Measure.dirac m)
        (singleSpeciesJumpKernel v params i)).map (fun ω => ω k) =
          (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
    exact homogeneousPathMeasure_dirac_marginal
      (singleSpeciesJumpKernel v params i) m k
  calc
    ((kernelIter (singleSpeciesTimedKernel v params i) k) (m, 0)).map
          Prod.fst =
        (P.map (fun ω => ω k)).map Prod.fst := by rw [hTimed]
    _ = P.map (fun ω => (ω k).1) := by
          rw [Measure.map_map measurable_fst (measurable_pi_apply k)]
          rfl
    _ = (P.map (pathMap Prod.fst)).map (fun ω => ω k) := by
          rw [Measure.map_map (measurable_pi_apply k)
            (measurable_pathMap Prod.fst measurable_fst)]
          rfl
    _ = (homogeneousPathMeasure (Measure.dirac m)
          (singleSpeciesJumpKernel v params i)).map (fun ω => ω k) := by
          have hmap :=
            singleSpeciesTimedPathMeasure_map_count
              v params i hDelta m
          change
            P.map (pathMap Prod.fst) =
              singleSpeciesCountPathMeasure v params i m at hmap
          change
            P.map (pathMap Prod.fst) =
              homogeneousPathMeasure (Measure.dirac m)
                (singleSpeciesJumpKernel v params i) at hmap
          rw [hmap]
    _ = (kernelIter (singleSpeciesJumpKernel v params i) k) m := hCount

lemma singleSpeciesTimedPathMeasure_contribution
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m k : Nat) :
    ∫⁻ ω, timedStateHolding (ω (k + 1)) ∂
        singleSpeciesTimedPathMeasure v params i hDelta m =
      ∫⁻ n, singleSpeciesHoldingCost params i n ∂
        (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
  letI : IsMarkovKernel (singleSpeciesTimedKernel v params i) :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  change
    (∫⁻ ω, timedStateHolding (ω (k + 1)) ∂
        homogeneousPathMeasure (Measure.dirac (m, 0))
          (singleSpeciesTimedKernel v params i)) =
      _
  rw [show
    (∫⁻ ω, timedStateHolding (ω (k + 1)) ∂
        homogeneousPathMeasure (Measure.dirac (m, 0))
          (singleSpeciesTimedKernel v params i)) =
      ∫⁻ ω, (1 : ENNReal) * timedStateHolding (ω (k + 1)) ∂
        homogeneousPathMeasure (Measure.dirac (m, 0))
          (singleSpeciesTimedKernel v params i) by simp]
  rw [homogeneousPathMeasure_joint_lintegral
    (singleSpeciesTimedKernel v params i) (m, 0) k
    (fun _ => (1 : ENNReal)) timedStateHolding
    measurable_const measurable_timedStateHolding]
  simp only [one_mul]
  have hinner (z : Nat × Real) :
      ∫⁻ y, timedStateHolding y ∂
          singleSpeciesTimedKernel v params i z =
        singleSpeciesHoldingCost params i z.1 := by
    rw [singleSpeciesTimedKernel, Kernel.comap_apply]
    exact singleSpeciesTimedStep_holding
      v params i hDelta z.1
  simp_rw [hinner]
  calc
    ∫⁻ z, singleSpeciesHoldingCost params i z.1 ∂
          (kernelIter (singleSpeciesTimedKernel v params i) k) (m, 0) =
        ∫⁻ n, singleSpeciesHoldingCost params i n ∂
          ((kernelIter (singleSpeciesTimedKernel v params i) k) (m, 0)).map
            Prod.fst := by
              exact (lintegral_map
                (measurable_of_countable _) measurable_fst).symm
    _ = ∫⁻ n, singleSpeciesHoldingCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
            rw [singleSpeciesTimedKernel_iter_map_fst
              v params i hDelta m k]

/-- Holding cost contributed by jump index `k`.  Once the species is
extinct, every later contribution is zero. -/
noncomputable def timedHoldingContribution
    (ω : Nat → Nat × Real) (k : Nat) : ENNReal :=
  if k = 0 then 0 else timedStateHolding (ω k)

lemma measurable_timedHoldingContribution (k : Nat) :
    Measurable (fun ω : Nat → Nat × Real =>
      timedHoldingContribution ω k) := by
  unfold timedHoldingContribution
  split_ifs
  · exact measurable_const
  · exact measurable_timedStateHolding.comp (measurable_pi_apply k)

/-- Calendar-time extinction time of a timed single-species path. -/
noncomputable def timedExtinctionTime
    (ω : Nat → Nat × Real) : ENNReal :=
  ∑' k : Nat, timedHoldingContribution ω k

lemma measurable_timedExtinctionTime :
    Measurable timedExtinctionTime := by
  exact Measurable.tsum measurable_timedHoldingContribution

theorem singleSpecies_timedExtinctionTime_lintegral_le
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params i hDelta))
    (hmono : Monotone cert.V) (m : Nat) :
    ∫⁻ ω, timedExtinctionTime ω ∂
        singleSpeciesTimedPathMeasure v params i hDelta m ≤
      cert.bound := by
  change
    (∫⁻ ω, ∑' k : Nat, timedHoldingContribution ω k ∂
      singleSpeciesTimedPathMeasure v params i hDelta m) ≤ cert.bound
  rw [lintegral_tsum
    (fun k => (measurable_timedHoldingContribution k).aemeasurable)]
  let q : Nat → ENNReal := fun k =>
    ∫⁻ ω, timedHoldingContribution ω k ∂
      singleSpeciesTimedPathMeasure v params i hDelta m
  have hshift :
      ∑' k : Nat, q (k + 1) = ∑' k : Nat, q k := by
    have h :=
      ENNReal.summable.sum_add_tsum_nat_add'
        (f := q) (k := 1)
    simpa [q, timedHoldingContribution] using h
  change (∑' k : Nat, q k) ≤ cert.bound
  rw [← hshift]
  simp_rw [q, timedHoldingContribution]
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
  have hcontribution (k : Nat) :
      ∫⁻ ω, timedStateHolding (ω k.succ) ∂
          singleSpeciesTimedPathMeasure v params i hDelta m =
        ∫⁻ n, singleSpeciesHoldingCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
    simpa [Nat.succ_eq_add_one] using
      singleSpeciesTimedPathMeasure_contribution
        v params i hDelta m k
  simp_rw [hcontribution]
  exact singleSpecies_expected_holding_sum_le
    v params i hDelta cert hmono m

theorem singleSpecies_timedExtinctionTime_lintegral_le_value
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params i hDelta))
    (hmono : Monotone cert.V) (m : Nat) :
    ∫⁻ ω, timedExtinctionTime ω ∂
        singleSpeciesTimedPathMeasure v params i hDelta m ≤
      cert.V m := by
  change
    (∫⁻ ω, ∑' k : Nat, timedHoldingContribution ω k ∂
      singleSpeciesTimedPathMeasure v params i hDelta m) ≤ cert.V m
  rw [lintegral_tsum
    (fun k => (measurable_timedHoldingContribution k).aemeasurable)]
  let q : Nat → ENNReal := fun k =>
    ∫⁻ ω, timedHoldingContribution ω k ∂
      singleSpeciesTimedPathMeasure v params i hDelta m
  have hshift :
      ∑' k : Nat, q (k + 1) = ∑' k : Nat, q k := by
    have h :=
      ENNReal.summable.sum_add_tsum_nat_add'
        (f := q) (k := 1)
    simpa [q, timedHoldingContribution] using h
  change (∑' k : Nat, q k) ≤ cert.V m
  rw [← hshift]
  simp_rw [q, timedHoldingContribution]
  simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte]
  have hcontribution (k : Nat) :
      ∫⁻ ω, timedStateHolding (ω k.succ) ∂
          singleSpeciesTimedPathMeasure v params i hDelta m =
        ∫⁻ n, singleSpeciesHoldingCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
    simpa [Nat.succ_eq_add_one] using
      singleSpeciesTimedPathMeasure_contribution
        v params i hDelta m k
  simp_rw [hcontribution]
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun t => ?_
  rw [← singleSpeciesAbsorptionReward_eq_sum v params i t m]
  exact singleSpeciesAbsorptionReward_le_certificate
    v params i hDelta cert hmono t m

/-! ## Almost-sure extinction of an isolated species

The continuous-time mean calculation above is complemented by a
discrete jump-chain argument.  An infinite positive trajectory would
have to contain infinitely many births.  We rule this out with an
unbounded Lyapunov function whose one-step drift pays for every birth.
-/

/-- Increment shape for the birth-count Lyapunov function.  Above the
cutoff its increments are one; below the cutoff they grow geometrically
towards zero. -/
noncomputable def birthCountIncrement
    (cutoff : Nat) (ratio : Real) (n : Nat) : Real :=
  if n = 0 then 0
  else if cutoff ≤ n then 1
  else ratio ^ (cutoff - n)

lemma birthCountIncrement_nonneg
    (cutoff : Nat) (ratio : Real) (hratio : 0 ≤ ratio) :
    ∀ n, 0 ≤ birthCountIncrement cutoff ratio n := by
  intro n
  simp only [birthCountIncrement]
  split_ifs <;> positivity

lemma birthCountIncrement_one_le
    (cutoff : Nat) (ratio : Real) (hratio : 1 ≤ ratio)
    (n : Nat) (hn : 0 < n) :
    1 ≤ birthCountIncrement cutoff ratio n := by
  simp only [birthCountIncrement, hn.ne', ↓reduceIte]
  split_ifs
  · exact le_rfl
  · exact one_le_pow₀ hratio

lemma birthCountIncrement_low_step
    (cutoff : Nat) (ratio : Real)
    (n : Nat) (hn : 0 < n) (hnlow : n < cutoff) :
    birthCountIncrement cutoff ratio n =
      ratio * birthCountIncrement cutoff ratio (n + 1) := by
  have hn0 : n ≠ 0 := hn.ne'
  have hnnot : ¬cutoff ≤ n := Nat.not_le_of_gt hnlow
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hnlow) with hsucc | hsucc
  · have hsucc0 : n + 1 ≠ 0 := by omega
    have hsuccnot : ¬cutoff ≤ n + 1 :=
      Nat.not_le_of_gt hsucc
    have hexp : cutoff - n = (cutoff - (n + 1)) + 1 := by
      omega
    simp only [birthCountIncrement, hn0, ↓reduceIte, hnnot,
      hsucc0, hsuccnot]
    rw [hexp, pow_succ]
    ring
  · have hsucc0 : n + 1 ≠ 0 := by omega
    have hsuccle : cutoff ≤ n + 1 := hsucc.ge
    have hexp : cutoff - n = 1 := by omega
    simp only [birthCountIncrement, hn0, ↓reduceIte, hnnot,
      hsucc0, hsuccle, hexp, pow_one]
    ring

/-- The real-valued birth-count Lyapunov function. -/
noncomputable def birthCountPotential
    (cutoff : Nat) (ratio : Real) (n : Nat) : Real :=
  ∑ j ∈ Finset.range (n + 1), birthCountIncrement cutoff ratio j

lemma birthCountPotential_zero (cutoff : Nat) (ratio : Real) :
    birthCountPotential cutoff ratio 0 = 0 := by
  simp [birthCountPotential, birthCountIncrement]

lemma birthCountPotential_succ
    (cutoff : Nat) (ratio : Real) (n : Nat) :
    birthCountPotential cutoff ratio (n + 1) =
      birthCountPotential cutoff ratio n +
        birthCountIncrement cutoff ratio (n + 1) := by
  simp [birthCountPotential, Finset.sum_range_succ]

lemma birthCountPotential_pred
    (cutoff : Nat) (ratio : Real) (n : Nat) (hn : 0 < n) :
    birthCountPotential cutoff ratio (n - 1) =
      birthCountPotential cutoff ratio n -
        birthCountIncrement cutoff ratio n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [birthCountPotential_succ]
  simp

lemma birthCountPotential_nonneg
    (cutoff : Nat) (ratio : Real) (hratio : 0 ≤ ratio) :
    ∀ n, 0 ≤ birthCountPotential cutoff ratio n := by
  intro n
  exact Finset.sum_nonneg fun j _ =>
    birthCountIncrement_nonneg cutoff ratio hratio j

lemma birthCountPotential_monotone
    (cutoff : Nat) (ratio : Real) (hratio : 0 ≤ ratio) :
    Monotone (birthCountPotential cutoff ratio) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [birthCountPotential_succ]
  exact le_add_of_nonneg_right
    (birthCountIncrement_nonneg cutoff ratio hratio (n + 1))

private lemma exists_birthCount_cutoff
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) :
    ∃ cutoff : Nat, 2 ≤ cutoff ∧
      ∀ n : Nat, cutoff ≤ n →
        2 * singleSpeciesBirthRate params n ≤
          (singleSpeciesReferenceCT params i
            hDelta).deathRate n := by
  obtain ⟨cutoff, hcutoff⟩ :
      ∃ cutoff : Nat,
        4 * params.beta / speciesGamma params i + 2 < cutoff :=
    exists_nat_gt (4 * params.beta / speciesGamma params i + 2)
  refine ⟨cutoff, ?_, ?_⟩
  · have hnonneg :
        0 ≤ 4 * params.beta / speciesGamma params i := by
      exact div_nonneg (mul_nonneg (by norm_num) params.beta_nonneg)
        hGamma.le
    have htwoR : (2 : Real) < cutoff := by
      linarith
    exact (by exact_mod_cast htwoR : 2 < cutoff).le
  · intro n hn
    have hcutNat : 2 ≤ cutoff := by
      have hnonneg :
          0 ≤ 4 * params.beta / speciesGamma params i := by
        exact div_nonneg
          (mul_nonneg (by norm_num) params.beta_nonneg) hGamma.le
      have htwoR : (2 : Real) < cutoff := by
        linarith
      exact (by exact_mod_cast htwoR : 2 < cutoff).le
    have hnR : (cutoff : Real) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : Real) < n := by
      have hnNat : 0 < n := by omega
      exact_mod_cast hnNat
    have hlarge :
        4 * params.beta / speciesGamma params i + 2 < (n : Real) := by
      exact lt_of_lt_of_le hcutoff hnR
    have hGammaNonneg : 0 ≤ speciesGamma params i := hGamma.le
    have hDeltaTerm :
        0 ≤ singleSpeciesIndividualDeathRate params n := by
      exact mul_nonneg params.delta_nonneg (Nat.cast_nonneg n)
    dsimp only [singleSpeciesReferenceCT]
    simp only [singleSpeciesBirthRate,
      singleSpeciesIndividualDeathRate, singleSpeciesIntraRate]
    have hmain :
        2 * params.beta * (n : Real) ≤
          speciesGamma params i *
            ((n : Real) * ((n : Real) - 1) / 2) := by
      have hratio :
          4 * params.beta <
            speciesGamma params i * ((n : Real) - 1) := by
        have hdiv :
            4 * params.beta / speciesGamma params i <
              (n : Real) - 1 := by
          linarith
        simpa [mul_comm] using (div_lt_iff₀ hGamma).mp hdiv
      nlinarith
    nlinarith

private lemma exists_birthCount_ratio
    (params : LVParams) (i : Bool) (hDelta : 0 < params.delta)
    (cutoff : Nat) :
    ∃ ratio : Real, 1 ≤ ratio ∧
      ∀ n : Nat, 0 < n → n < cutoff →
        2 * singleSpeciesBirthRate params n ≤
          (singleSpeciesReferenceCT params i hDelta).deathRate n *
            (ratio - 1) := by
  let birth := singleSpeciesBirthRate params
  let death :=
    (singleSpeciesReferenceCT params i hDelta).deathRate
  let ratio : Real :=
    1 + ∑ n ∈ Finset.range cutoff, 2 * birth n / death n
  have hDeath : ∀ n : Nat, 0 < n → 0 < death n := by
    intro n hn
    exact (singleSpeciesReferenceCT params i hDelta).death_pos n hn
  have hterm_nonneg :
      ∀ n ∈ Finset.range cutoff, 0 ≤ 2 * birth n / death n := by
    intro n _
    by_cases hn : n = 0
    · subst n
      simp [birth, singleSpeciesBirthRate]
    · exact div_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg params.beta_nonneg (Nat.cast_nonneg n)))
        (hDeath n (Nat.pos_of_ne_zero hn)).le
  have hsum_nonneg :
      0 ≤ ∑ n ∈ Finset.range cutoff, 2 * birth n / death n :=
    Finset.sum_nonneg hterm_nonneg
  refine ⟨ratio, by dsimp [ratio]; linarith, ?_⟩
  intro n hn hncut
  have hnmem : n ∈ Finset.range cutoff :=
    Finset.mem_range.mpr hncut
  have hsingle :
      2 * birth n / death n ≤
        ∑ j ∈ Finset.range cutoff, 2 * birth j / death j := by
    exact Finset.single_le_sum hterm_nonneg hnmem
  have hratio :
      2 * birth n / death n ≤ ratio - 1 := by
    simpa only [ratio, add_sub_cancel_left] using hsingle
  have hmul := (div_le_iff₀ (hDeath n hn)).mp hratio
  simpa only [birth, death, mul_comm] using hmul

theorem exists_birthCount_increments
    (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) :
    ∃ cutoff : Nat, ∃ ratio : Real,
      1 ≤ ratio ∧
      ∀ n : Nat, 0 < n →
        singleSpeciesBirthRate params n +
            singleSpeciesBirthRate params n *
              birthCountIncrement cutoff ratio (n + 1) ≤
          (singleSpeciesReferenceCT params i hDelta).deathRate n *
            birthCountIncrement cutoff ratio n := by
  obtain ⟨cutoff, hcutoff, hhigh⟩ :=
    exists_birthCount_cutoff params i hDelta hGamma
  obtain ⟨ratio, hratio, hlow⟩ :=
    exists_birthCount_ratio params i hDelta cutoff
  refine ⟨cutoff, ratio, hratio, ?_⟩
  intro n hn
  by_cases hncut : cutoff ≤ n
  · have hsucc : cutoff ≤ n + 1 := hncut.trans (Nat.le_add_right n 1)
    have hincn :
        birthCountIncrement cutoff ratio n = 1 := by
      simp [birthCountIncrement, hn.ne', hncut]
    have hincsucc :
        birthCountIncrement cutoff ratio (n + 1) = 1 := by
      simp [birthCountIncrement, hsucc]
    rw [hincn, hincsucc, mul_one]
    simpa only [two_mul, mul_one] using hhigh n hncut
  · have hnlow : n < cutoff := Nat.lt_of_not_ge hncut
    have hstep :=
      birthCountIncrement_low_step cutoff ratio n hn hnlow
    have hone :
        1 ≤ birthCountIncrement cutoff ratio (n + 1) :=
      birthCountIncrement_one_le cutoff ratio hratio
        (n + 1) (by omega)
    have hbirth :
        0 ≤ singleSpeciesBirthRate params n := by
      exact mul_nonneg params.beta_nonneg (Nat.cast_nonneg n)
    have hratioBound := hlow n hn hnlow
    rw [hstep]
    calc
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff ratio (n + 1)
          ≤ 2 * singleSpeciesBirthRate params n *
              birthCountIncrement cutoff ratio (n + 1) := by
            nlinarith
      _ ≤
          (singleSpeciesReferenceCT params i hDelta).deathRate n *
            (ratio - 1) *
              birthCountIncrement cutoff ratio (n + 1) := by
            gcongr
      _ ≤
          (singleSpeciesReferenceCT params i hDelta).deathRate n *
            (ratio *
              birthCountIncrement cutoff ratio (n + 1)) := by
            have hDeath :
                0 ≤ (singleSpeciesReferenceCT params i hDelta).deathRate n :=
              (singleSpeciesReferenceCT params i hDelta).death_nonneg n
            nlinarith

/-- Probability that the next isolated-species jump is a birth. -/
noncomputable def singleSpeciesBirthCost
    (params : LVParams) (i : Bool) (n : Nat) : ENNReal :=
  if n = 0 then 0
  else ENNReal.ofReal
    (singleSpeciesBirthRate params n /
      singleSpeciesTotalRate params i n)

lemma singleSpeciesJumpMeasure_birth
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (n : Nat) :
    singleSpeciesJumpMeasure v params i n {n + 1} =
      singleSpeciesBirthCost params i n := by
  by_cases hn : n = 0
  · subst n
    simp [singleSpeciesBirthCost, singleSpeciesJumpMeasure,
      speciesState, speciesCount, lvKernel_apply_zero_propensity,
      lvTotalPropensity]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [singleSpeciesJumpMeasure_eq v params i hDelta n hnpos]
    have hTarget :
        singleSpeciesIntraTarget v n ≠ n + 1 := by
      have := singleSpeciesIntraTarget_le_pred v n
      omega
    have hPred : n - 1 ≠ n + 1 := by omega
    simp only [Measure.smul_apply, Measure.add_apply,
      MeasurableSet.singleton, Measure.dirac_apply',
      smul_eq_mul, Set.indicator_apply, Set.mem_singleton_iff,
      hPred, hTarget, ↓reduceIte, mul_zero, add_zero,
      singleSpeciesBirthCost, hn, Pi.one_apply, mul_one]
    calc
      ENNReal.ofReal (1 / singleSpeciesTotalRate params i n) *
            ENNReal.ofReal (singleSpeciesBirthRate params n) =
          ENNReal.ofReal
            ((1 / singleSpeciesTotalRate params i n) *
              singleSpeciesBirthRate params n) :=
        (ENNReal.ofReal_mul
          (one_div_nonneg.mpr
            (singleSpeciesTotalRate_pos
              params i hDelta n hnpos).le)).symm
      _ = ENNReal.ofReal
            (singleSpeciesBirthRate params n /
              singleSpeciesTotalRate params i n) := by
        congr 1
        field_simp [
          (singleSpeciesTotalRate_pos params i hDelta n hnpos).ne']

lemma singleSpecies_birthCost_potential_drift
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cutoff : Nat) (ratio : Real) (hratio : 1 ≤ ratio)
    (hDrift : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff ratio (n + 1) ≤
        (singleSpeciesReferenceCT params i hDelta).deathRate n *
          birthCountIncrement cutoff ratio n)
    (n : Nat) (hn : 0 < n) :
    singleSpeciesBirthCost params i n +
        ∫⁻ m, ENNReal.ofReal (birthCountPotential cutoff ratio m) ∂
          singleSpeciesJumpMeasure v params i n ≤
      ENNReal.ofReal (birthCountPotential cutoff ratio n) := by
  have hratio0 : 0 ≤ ratio := zero_le_one.trans hratio
  have hmonoReal :=
    birthCountPotential_monotone cutoff ratio hratio0
  have hmono :
      Monotone
        (fun m => ENNReal.ofReal
          (birthCountPotential cutoff ratio m)) :=
    fun _ _ hle => ENNReal.ofReal_le_ofReal (hmonoReal hle)
  calc
    singleSpeciesBirthCost params i n +
        ∫⁻ m, ENNReal.ofReal (birthCountPotential cutoff ratio m) ∂
          singleSpeciesJumpMeasure v params i n
      ≤ singleSpeciesBirthCost params i n +
          ∫⁻ m, ENNReal.ofReal
              (birthCountPotential cutoff ratio m) ∂
            bdKernel
              (singleSpeciesReferenceCT params i hDelta).embedded n := by
        simpa only [add_comm] using
          add_le_add_left
            (singleSpecies_lintegral_le_reference
              v params i hDelta _ hmono n hn)
            (singleSpeciesBirthCost params i n)
    _ ≤ ENNReal.ofReal (birthCountPotential cutoff ratio n) := by
      have hRatePos :=
        singleSpeciesTotalRate_pos params i hDelta n hn
      have hBirth :
          0 ≤ singleSpeciesBirthRate params n :=
        mul_nonneg params.beta_nonneg (Nat.cast_nonneg n)
      have hDeath :
          0 ≤
            (singleSpeciesReferenceCT params i hDelta).deathRate n :=
        (singleSpeciesReferenceCT params i hDelta).death_nonneg n
      have hIndividual :
          0 ≤ singleSpeciesIndividualDeathRate params n :=
        mul_nonneg params.delta_nonneg (Nat.cast_nonneg n)
      have hIntra :
          0 ≤ singleSpeciesIntraRate params i n := by
        apply mul_nonneg
        · cases i <;> simp [speciesGamma, params.gamma0_nonneg,
            params.gamma1_nonneg]
        · have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
          positivity
      have hVnonneg :
          ∀ m, 0 ≤ birthCountPotential cutoff ratio m :=
        birthCountPotential_nonneg cutoff ratio hratio0
      rw [singleSpeciesReferenceJumpMeasure_eq
        params i hDelta n hn]
      simp only [singleSpeciesBirthCost, hn.ne', ↓reduceIte,
        lintegral_smul_measure, lintegral_add_measure,
        lintegral_dirac, smul_eq_mul]
      have hTotal :
          singleSpeciesTotalRate params i n =
            singleSpeciesBirthRate params n +
              (singleSpeciesReferenceCT params i hDelta).deathRate n := by
        rw [singleSpeciesTotalRate_eq]
        dsimp only [singleSpeciesReferenceCT]
        ring
      have hReal :
          singleSpeciesBirthRate params n /
                singleSpeciesTotalRate params i n +
              (1 / singleSpeciesTotalRate params i n) *
                (singleSpeciesBirthRate params n *
                    birthCountPotential cutoff ratio (n + 1) +
                  (singleSpeciesReferenceCT params i hDelta).deathRate n *
                    birthCountPotential cutoff ratio (n - 1)) ≤
            birthCountPotential cutoff ratio n := by
        have hFraction :
            singleSpeciesBirthRate params n /
                  singleSpeciesTotalRate params i n +
                (1 / singleSpeciesTotalRate params i n) *
                  (singleSpeciesBirthRate params n *
                      birthCountPotential cutoff ratio (n + 1) +
                    (singleSpeciesReferenceCT params i hDelta).deathRate n *
                      birthCountPotential cutoff ratio (n - 1)) =
              (singleSpeciesBirthRate params n +
                  (singleSpeciesBirthRate params n *
                      birthCountPotential cutoff ratio (n + 1) +
                    (singleSpeciesReferenceCT params i hDelta).deathRate n *
                      birthCountPotential cutoff ratio (n - 1))) /
                singleSpeciesTotalRate params i n := by
          field_simp [hRatePos.ne']
        rw [hFraction]
        apply (div_le_iff₀ hRatePos).2
        rw [birthCountPotential_succ,
          birthCountPotential_pred cutoff ratio n hn, hTotal]
        nlinarith [hDrift n hn]
      have hInner :
          ENNReal.ofReal (singleSpeciesBirthRate params n) *
                ENNReal.ofReal
                  (birthCountPotential cutoff ratio (n + 1)) +
              ENNReal.ofReal
                  (singleSpeciesIndividualDeathRate params n) *
                ENNReal.ofReal
                  (birthCountPotential cutoff ratio (n - 1)) +
              ENNReal.ofReal (singleSpeciesIntraRate params i n) *
                ENNReal.ofReal
                  (birthCountPotential cutoff ratio (n - 1)) =
            ENNReal.ofReal
              (singleSpeciesBirthRate params n *
                    birthCountPotential cutoff ratio (n + 1) +
                (singleSpeciesReferenceCT params i hDelta).deathRate n *
                    birthCountPotential cutoff ratio (n - 1)) := by
        rw [← ENNReal.ofReal_mul hBirth,
          ← ENNReal.ofReal_mul hIndividual,
          ← ENNReal.ofReal_mul hIntra]
        rw [← ENNReal.ofReal_add
          (mul_nonneg hBirth (hVnonneg (n + 1)))
          (mul_nonneg hIndividual (hVnonneg (n - 1)))]
        rw [← ENNReal.ofReal_add
          (add_nonneg
            (mul_nonneg hBirth (hVnonneg (n + 1)))
            (mul_nonneg hIndividual (hVnonneg (n - 1))))
          (mul_nonneg hIntra (hVnonneg (n - 1)))]
        congr 1
        dsimp only [singleSpeciesReferenceCT]
        ring
      rw [hInner]
      rw [← ENNReal.ofReal_mul
        (one_div_nonneg.mpr hRatePos.le)]
      rw [← ENNReal.ofReal_add
        (div_nonneg hBirth hRatePos.le)
        (mul_nonneg (one_div_nonneg.mpr hRatePos.le)
          (add_nonneg
            (mul_nonneg hBirth (hVnonneg (n + 1)))
            (mul_nonneg hDeath (hVnonneg (n - 1)))))]
      exact ENNReal.ofReal_le_ofReal hReal

/-- Expected number of births during the first `t` isolated-species
jumps, written in first-step form. -/
noncomputable def singleSpeciesBirthReward
    (v : LVVariant) (params : LVParams) (i : Bool) :
    Nat → Nat → ENNReal
  | 0, _ => 0
  | t + 1, n =>
      if n = 0 then 0
      else
        singleSpeciesBirthCost params i n +
          ∫⁻ m, singleSpeciesBirthReward v params i t m ∂
            singleSpeciesJumpMeasure v params i n

lemma singleSpeciesBirthReward_le_potential
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cutoff : Nat) (ratio : Real) (hratio : 1 ≤ ratio)
    (hDrift : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff ratio (n + 1) ≤
        (singleSpeciesReferenceCT params i hDelta).deathRate n *
          birthCountIncrement cutoff ratio n) :
    ∀ t n,
      singleSpeciesBirthReward v params i t n ≤
        ENNReal.ofReal (birthCountPotential cutoff ratio n) := by
  intro t
  induction t with
  | zero =>
      intro n
      simp [singleSpeciesBirthReward]
  | succ t ih =>
      intro n
      by_cases hn : n = 0
      · subst n
        simp [singleSpeciesBirthReward, birthCountPotential_zero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        simp only [singleSpeciesBirthReward, hn, ↓reduceIte]
        calc
          singleSpeciesBirthCost params i n +
              ∫⁻ m, singleSpeciesBirthReward v params i t m ∂
                singleSpeciesJumpMeasure v params i n
            ≤ singleSpeciesBirthCost params i n +
                ∫⁻ m, ENNReal.ofReal
                    (birthCountPotential cutoff ratio m) ∂
                  singleSpeciesJumpMeasure v params i n := by
              gcongr with m
              exact ih m
          _ ≤ ENNReal.ofReal
                (birthCountPotential cutoff ratio n) :=
            singleSpecies_birthCost_potential_drift
              v params i hDelta cutoff ratio hratio hDrift n hnpos

theorem singleSpeciesBirthReward_eq_sum
    (v : LVVariant) (params : LVParams) (i : Bool)
    (t m : Nat) :
    singleSpeciesBirthReward v params i t m =
      ∑ k ∈ Finset.range t,
        ∫⁻ n, singleSpeciesBirthCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  induction t generalizing m with
  | zero =>
      simp [singleSpeciesBirthReward]
  | succ t ih =>
      have hshift (k : Nat) :
          ∫⁻ n, (∫⁻ x, singleSpeciesBirthCost params i x ∂
              (kernelIter (singleSpeciesJumpKernel v params i) k) n) ∂
                singleSpeciesJumpKernel v params i m =
            ∫⁻ x, singleSpeciesBirthCost params i x ∂
              (kernelIter
                (singleSpeciesJumpKernel v params i) (k + 1)) m := by
        rw [show k + 1 = 1 + k by omega]
        rw [kernelIter_lintegral_add
          (singleSpeciesJumpKernel v params i) 1 k m
          (singleSpeciesBirthCost params i)
          (measurable_of_countable _)]
        rw [kernelIter_one]
      by_cases hm : m = 0
      · subst m
        have hzero :
            singleSpeciesJumpKernel v params i 0 = Measure.dirac 0 := by
          change singleSpeciesJumpMeasure v params i 0 = Measure.dirac 0
          simp [singleSpeciesJumpMeasure, speciesState, speciesCount,
            lvKernel_apply_zero_propensity, lvTotalPropensity]
        have hiter :
            ∀ k : Nat,
              (kernelIter (singleSpeciesJumpKernel v params i) k) 0 =
                Measure.dirac 0 := by
          intro k
          induction k with
          | zero =>
              simp [kernelIter_zero, Kernel.id_apply]
          | succ k hk =>
              rw [kernelIter_succ, Kernel.comp_apply, hk]
              rw [Measure.dirac_bind (Kernel.measurable _) 0]
              exact hzero
        simp_rw [hiter]
        simp [singleSpeciesBirthReward, singleSpeciesBirthCost,
          lintegral_dirac]
      · simp only [singleSpeciesBirthReward, hm, ↓reduceIte]
        change
          singleSpeciesBirthCost params i m +
              ∫⁻ n, singleSpeciesBirthReward v params i t n ∂
                singleSpeciesJumpKernel v params i m =
            ∑ k ∈ Finset.range (t + 1),
              ∫⁻ n, singleSpeciesBirthCost params i n ∂
                (kernelIter (singleSpeciesJumpKernel v params i) k) m
        simp_rw [ih]
        rw [lintegral_finsetSum (Finset.range t)
          (fun _ _ => Measurable.lintegral_kernel
            (measurable_of_countable _))]
        simp_rw [hshift]
        rw [Finset.sum_range_succ']
        simp [kernelIter_zero, Kernel.id_apply, lintegral_dirac]
        ac_rfl

theorem singleSpecies_expected_birth_sum_le
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (cutoff : Nat) (ratio : Real) (hratio : 1 ≤ ratio)
    (hDrift : ∀ n : Nat, 0 < n →
      singleSpeciesBirthRate params n +
          singleSpeciesBirthRate params n *
            birthCountIncrement cutoff ratio (n + 1) ≤
        (singleSpeciesReferenceCT params i hDelta).deathRate n *
          birthCountIncrement cutoff ratio n)
    (m : Nat) :
    ∑' k : Nat,
        ∫⁻ n, singleSpeciesBirthCost params i n ∂
          (kernelIter (singleSpeciesJumpKernel v params i) k) m ≤
      ENNReal.ofReal (birthCountPotential cutoff ratio m) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun t => ?_
  rw [← singleSpeciesBirthReward_eq_sum v params i t m]
  exact singleSpeciesBirthReward_le_potential
    v params i hDelta cutoff ratio hratio hDrift t m

/-- The `k`th embedded jump is a birth. -/
def singleSpeciesBirthEvent (k : Nat) : Set (Nat → Nat) :=
  {ω | ω (k + 1) = ω k + 1}

lemma measurableSet_singleSpeciesBirthEvent (k : Nat) :
    MeasurableSet (singleSpeciesBirthEvent k) := by
  have hpair : Measurable (fun ω : Nat → Nat =>
      (ω (k + 1), ω k + 1)) := by
    have hpairK : Measurable
        (fun ω : Nat → Nat => (ω k, (1 : Nat))) :=
      (measurable_pi_apply k).prod measurable_const
    have hadd : Measurable (fun ω : Nat → Nat => ω k + 1) := by
      exact (measurable_of_countable
        (fun p : Nat × Nat => p.1 + p.2)).comp hpairK
    exact (measurable_pi_apply (k + 1)).prod hadd
  have hdiag : MeasurableSet {p : Nat × Nat | p.1 = p.2} :=
    (Set.to_countable _).measurableSet
  exact hpair hdiag

lemma singleSpeciesCountPathMeasure_birthEvent
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m k : Nat) :
    singleSpeciesCountPathMeasure v params i m
        (singleSpeciesBirthEvent k) =
      ∫⁻ n, singleSpeciesBirthCost params i n ∂
        (kernelIter (singleSpeciesJumpKernel v params i) k) m := by
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  let K := singleSpeciesJumpKernel v params i
  let P := homogeneousPathMeasure (Measure.dirac m) K
  let A : Nat → Set (Nat → Nat) := fun n =>
    {ω | ω k = n ∧ ω (k + 1) = n + 1}
  have hUnion :
      singleSpeciesBirthEvent k = ⋃ n : Nat, A n := by
    ext ω
    simp only [singleSpeciesBirthEvent, Set.mem_setOf_eq,
      Set.mem_iUnion, A]
    constructor
    · intro h
      exact ⟨ω k, rfl, h⟩
    · rintro ⟨n, hn, hnext⟩
      simpa [hn] using hnext
  have hPair : Pairwise (fun x y => Disjoint (A x) (A y)) := by
    intro x y hxy
    apply Set.disjoint_left.2
    intro ω hx hy
    exact hxy (hx.1.symm.trans hy.1)
  have hMeas : ∀ n, MeasurableSet (A n) := by
    intro n
    measurability
  have hPiece : ∀ n : Nat,
      P (A n) =
        singleSpeciesBirthCost params i n *
          (kernelIter K k) m {n} := by
    intro n
    let g : Nat → ENNReal := fun x => if x = n then 1 else 0
    let φ : Nat → ENNReal := fun y => if y = n + 1 then 1 else 0
    have hg : Measurable g := measurable_of_countable _
    have hφ : Measurable φ := measurable_of_countable _
    have hIndicator :
        ∀ ω : Nat → Nat,
          (A n).indicator (1 : (Nat → Nat) → ENNReal) ω =
            g (ω k) * φ (ω (k + 1)) := by
      intro ω
      by_cases hcur : ω k = n
      · by_cases hnext : ω (k + 1) = n + 1
        <;> simp [A, g, φ, Set.indicator, hcur, hnext]
      · simp [A, g, Set.indicator, hcur]
    rw [← lintegral_indicator_one (hMeas n)]
    rw [show
      (∫⁻ ω, (A n).indicator
          (1 : (Nat → Nat) → ENNReal) ω ∂P) =
        ∫⁻ ω, g (ω k) * φ (ω (k + 1)) ∂P by
          congr 1
          funext ω
          exact hIndicator ω]
    rw [homogeneousPathMeasure_joint_lintegral
      K m k g φ hg hφ]
    have hInner : ∀ x : Nat,
        g x * ∫⁻ y, φ y ∂K x =
          if x = n then singleSpeciesBirthCost params i n else 0 := by
      intro x
      by_cases hx : x = n
      · subst x
        simp only [g, φ, ↓reduceIte, one_mul]
        rw [show
          (∫⁻ y, (if y = n + 1 then 1 else 0) ∂K n) =
            K n {n + 1} by
              rw [← lintegral_indicator_one
                (measurableSet_singleton (n + 1))]
              congr 1
              funext y
              simp [Set.indicator]]
        exact singleSpeciesJumpMeasure_birth
          v params i hDelta n
      · simp [g, hx]
    simp_rw [hInner]
    rw [lintegral_countable']
    simp only [ite_mul, zero_mul]
    rw [tsum_eq_single n]
    · simp
    · intro x hxn
      simp [hxn]
  change P (singleSpeciesBirthEvent k) =
    ∫⁻ n, singleSpeciesBirthCost params i n ∂
      (kernelIter K k) m
  rw [hUnion, measure_iUnion hPair hMeas]
  simp_rw [hPiece]
  rw [lintegral_countable']

theorem singleSpecies_birthEvents_tsum_ne_top
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) (m : Nat) :
    ∑' k : Nat,
        singleSpeciesCountPathMeasure v params i m
          (singleSpeciesBirthEvent k) ≠ ⊤ := by
  obtain ⟨cutoff, ratio, hratio, hDrift⟩ :=
    exists_birthCount_increments params i hDelta hGamma
  simp_rw [singleSpeciesCountPathMeasure_birthEvent
    v params i hDelta m]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (singleSpecies_expected_birth_sum_le
      v params i hDelta cutoff ratio hratio hDrift m)

/-- Every positive isolated-species jump is either a birth or decreases
the population by at least one.  Zero stays at zero. -/
def IsolatedCountStep (x y : Nat) : Prop :=
  (x = 0 ∧ y = 0) ∨
    (0 < x ∧ (y = x + 1 ∨ y ≤ x - 1))

lemma singleSpeciesJumpMeasure_step_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) :
    ∀ x : Nat, ∀ᵐ y ∂singleSpeciesJumpMeasure v params i x,
      IsolatedCountStep x y := by
  intro x
  rw [ae_iff]
  by_cases hx : x = 0
  · subst x
    simp [singleSpeciesJumpMeasure, speciesState, speciesCount,
      lvKernel_apply_zero_propensity, lvTotalPropensity,
      IsolatedCountStep]
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hx
    rw [singleSpeciesJumpMeasure_eq v params i hDelta x hxpos]
    simp only [Measure.smul_apply, Measure.add_apply,
      (Set.to_countable _).measurableSet, smul_eq_mul]
    have hUp : IsolatedCountStep x (x + 1) :=
      Or.inr ⟨hxpos, Or.inl rfl⟩
    have hDown : IsolatedCountStep x (x - 1) :=
      Or.inr ⟨hxpos, Or.inr le_rfl⟩
    have hIntra :
        IsolatedCountStep x (singleSpeciesIntraTarget v x) :=
      Or.inr ⟨hxpos, Or.inr
        (singleSpeciesIntraTarget_le_pred v x)⟩
    simp [Measure.dirac_apply', hUp, hDown, hIntra]

lemma path_hits_zero_of_eventually_no_birth
    (ω : Nat → Nat)
    (hstep : ∀ k, IsolatedCountStep (ω k) (ω (k + 1)))
    (hbirth : ∀ᶠ k in Filter.atTop,
      ω ∉ singleSpeciesBirthEvent k) :
    ∃ t, ω t = 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hbirth
  by_contra hnever
  push_neg at hnever
  have hdec : ∀ k, N ≤ k → ω (k + 1) < ω k := by
    intro k hk
    have hkpos : 0 < ω k := Nat.pos_of_ne_zero (hnever k)
    rcases hstep k with hzero | ⟨_, hup | hdown⟩
    · exact (hkpos.ne' hzero.1).elim
    · exact (hN k hk hup).elim
    · omega
  have hbound : ∀ j : Nat, ω (N + j) + j ≤ ω N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hd := hdec (N + j) (Nat.le_add_right N j)
        have hindex : N + (j + 1) = (N + j) + 1 := by omega
        rw [hindex]
        omega
  have := hbound (ω N + 1)
  omega

set_option maxHeartbeats 800000 in
theorem singleSpeciesCountPath_eventually_zero_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) (m : Nat) :
    ∀ᵐ ω ∂singleSpeciesCountPathMeasure v params i m,
      ∃ t, ω t = 0 := by
  letI : IsMarkovKernel (singleSpeciesJumpKernel v params i) :=
    singleSpeciesJumpKernel_isMarkov v params i
  have hsteps :
      ∀ᵐ ω ∂singleSpeciesCountPathMeasure v params i m,
        ∀ k, IsolatedCountStep (ω k) (ω (k + 1)) := by
    change
      ∀ᵐ ω ∂homogeneousPathMeasure (Measure.dirac m)
          (singleSpeciesJumpKernel v params i),
        ∀ k, IsolatedCountStep (ω k) (ω (k + 1))
    exact homogeneousPathMeasure_transition_ae
      (singleSpeciesJumpKernel v params i) m IsolatedCountStep
      (singleSpeciesJumpMeasure_step_ae
        v params i hDelta)
  have hnobirth :
      ∀ᵐ ω ∂singleSpeciesCountPathMeasure v params i m,
        ∀ᶠ k in Filter.atTop,
          ω ∉ singleSpeciesBirthEvent k :=
    ae_eventually_notMem
      (singleSpecies_birthEvents_tsum_ne_top
        v params i hDelta hGamma m)
  filter_upwards [hsteps, hnobirth] with ω hωstep hωbirth
  exact path_hits_zero_of_eventually_no_birth
    ω hωstep hωbirth

theorem singleSpeciesTimedPath_eventually_zero_ae
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i) (m : Nat) :
    ∀ᵐ ω ∂singleSpeciesTimedPathMeasure v params i hDelta m,
      ∃ t, (ω t).1 = 0 := by
  have hcount :=
    singleSpeciesCountPath_eventually_zero_ae
      v params i hDelta hGamma m
  rw [← singleSpeciesTimedPathMeasure_map_count
    v params i hDelta m] at hcount
  have hpull :=
    ae_of_ae_map
      (measurable_pathMap Prod.fst measurable_fst).aemeasurable
      hcount
  simpa [pathMap] using hpull

/-! ## Uniform lower tail from the final holding time -/

/-- A rate bounding the holding rate at every positive state from which
one isolated jump can reach zero. -/
noncomputable def singleSpeciesFinalRateBound
    (params : LVParams) (i : Bool) : Real :=
  max (singleSpeciesTotalRate params i 1)
    (singleSpeciesTotalRate params i 2)

lemma singleSpeciesFinalRateBound_pos
    (params : LVParams) (i : Bool) (hDelta : 0 < params.delta) :
    0 < singleSpeciesFinalRateBound params i := by
  exact lt_of_lt_of_le
    (singleSpeciesTotalRate_pos params i hDelta 1 (by omega))
    (le_max_left _ _)

lemma singleSpeciesTimedKernel_final_holding
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (z : Nat × Real)
    (hz : 0 < z.1) (x : Real) (hx : 0 ≤ x) :
    ENNReal.ofReal
          (Real.exp (-(singleSpeciesFinalRateBound params i * x))) *
        singleSpeciesTimedKernel v params i z {y | y.1 = 0} ≤
      singleSpeciesTimedKernel v params i z
        {y | y.1 = 0 ∧ x < y.2} := by
  let r := singleSpeciesTotalRate params i z.1
  have hr : 0 < r :=
    singleSpeciesTotalRate_pos params i hDelta z.1 hz
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  have hstep :
      singleSpeciesTimedKernel v params i z =
        (singleSpeciesJumpMeasure v params i z.1).prod
          (expMeasure r) := by
    rw [singleSpeciesTimedKernel, Kernel.comap_apply]
    change singleSpeciesTimedStep v params i z.1 =
      (singleSpeciesJumpMeasure v params i z.1).prod
        (expMeasure r)
    simp [singleSpeciesTimedStep, hz.ne', r]
  have hzero :
      singleSpeciesTimedKernel v params i z {y | y.1 = 0} =
        singleSpeciesJumpMeasure v params i z.1 {0} := by
    rw [hstep, show {y : Nat × Real | y.1 = 0} =
      ({0} : Set Nat) ×ˢ Set.univ by ext; simp]
    rw [Measure.prod_prod]
    simp
  have hlong :
      singleSpeciesTimedKernel v params i z
          {y | y.1 = 0 ∧ x < y.2} =
        singleSpeciesJumpMeasure v params i z.1 {0} *
          ENNReal.ofReal (Real.exp (-(r * x))) := by
    rw [hstep, show {y : Nat × Real | y.1 = 0 ∧ x < y.2} =
      ({0} : Set Nat) ×ˢ Set.Ioi x by ext; simp]
    rw [Measure.prod_prod, expMeasure_Ioi hr hx]
  rw [hzero, hlong]
  by_cases hsmall : z.1 ≤ 2
  · have hrle :
        r ≤ singleSpeciesFinalRateBound params i := by
      have hcases : z.1 = 1 ∨ z.1 = 2 := by omega
      rcases hcases with hone | htwo
      · simpa [r, hone, singleSpeciesFinalRateBound] using
          (le_max_left
            (singleSpeciesTotalRate params i 1)
            (singleSpeciesTotalRate params i 2))
      · simpa [r, htwo, singleSpeciesFinalRateBound] using
          (le_max_right
            (singleSpeciesTotalRate params i 1)
            (singleSpeciesTotalRate params i 2))
    have hexp :
        Real.exp (-(singleSpeciesFinalRateBound params i * x)) ≤
          Real.exp (-(r * x)) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [mul_comm
      (ENNReal.ofReal
        (Real.exp (-(singleSpeciesFinalRateBound params i * x))))]
    exact mul_le_mul_left'
      (ENNReal.ofReal_le_ofReal hexp) _
  · have hthree : 3 ≤ z.1 := by omega
    have hmass :
        singleSpeciesJumpMeasure v params i z.1 {0} = 0 := by
      rw [singleSpeciesJumpMeasure_eq
        v params i hDelta z.1 hz]
      have hPred : z.1 - 1 ≠ 0 := by omega
      have hTarget :
          singleSpeciesIntraTarget v z.1 ≠ 0 := by
        cases v <;> simp [singleSpeciesIntraTarget] <;> omega
      simp [Measure.smul_apply, Measure.add_apply,
        Measure.dirac_apply', hPred, hTarget]
    rw [hmass, mul_zero, zero_mul]

/-- The first zero occurs at jump `k+1`. -/
def timedFirstZeroAt (k : Nat) : Set (Nat → Nat × Real) :=
  {ω | (∀ j ∈ Finset.range (k + 1), 0 < (ω j).1) ∧
    (ω (k + 1)).1 = 0}

/-- The first zero occurs at jump `k+1`, and the final holding time
exceeds `x`. -/
def timedFirstZeroLongAt (x : Real) (k : Nat) :
    Set (Nat → Nat × Real) :=
  {ω | (∀ j ∈ Finset.range (k + 1), 0 < (ω j).1) ∧
    (ω (k + 1)).1 = 0 ∧ x < (ω (k + 1)).2}

lemma measurableSet_timedFirstZeroAt (k : Nat) :
    MeasurableSet (timedFirstZeroAt k) := by
  apply MeasurableSet.inter
  · have heq :
        {ω : Nat → Nat × Real |
            ∀ j ∈ Finset.range (k + 1), 0 < (ω j).1} =
          ⋂ j ∈ Finset.range (k + 1),
            {ω | (ω j).1 ∈ Set.Ioi 0} := by
        ext ω
        simp
    change MeasurableSet
      {ω : Nat → Nat × Real |
        ∀ j ∈ Finset.range (k + 1), 0 < (ω j).1}
    rw [heq]
    exact (Finset.range (k + 1)).measurableSet_biInter
      fun j _ =>
        ((measurable_pi_apply j :
            Measurable (fun ω : Nat → Nat × Real => ω j)).fst
          (measurableSet_Ioi : MeasurableSet (Set.Ioi 0)))
  · exact (measurable_pi_apply (k + 1)).fst
      (measurableSet_singleton 0)

lemma measurableSet_timedFirstZeroLongAt (x : Real) (k : Nat) :
    MeasurableSet (timedFirstZeroLongAt x k) := by
  apply MeasurableSet.inter
  · have heq :
        {ω : Nat → Nat × Real |
            ∀ j ∈ Finset.range (k + 1), 0 < (ω j).1} =
          ⋂ j ∈ Finset.range (k + 1),
            {ω | (ω j).1 ∈ Set.Ioi 0} := by
        ext ω
        simp
    change MeasurableSet
      {ω : Nat → Nat × Real |
        ∀ j ∈ Finset.range (k + 1), 0 < (ω j).1}
    rw [heq]
    exact (Finset.range (k + 1)).measurableSet_biInter
      fun j _ =>
        ((measurable_pi_apply j :
            Measurable (fun ω : Nat → Nat × Real => ω j)).fst
          (measurableSet_Ioi : MeasurableSet (Set.Ioi 0)))
  · exact MeasurableSet.inter
      ((measurable_pi_apply (k + 1)).fst
        (measurableSet_singleton 0))
      ((measurable_pi_apply (k + 1)).snd measurableSet_Ioi)

lemma timedFirstZeroAt_pairwise :
    Pairwise (fun k l => Disjoint (timedFirstZeroAt k)
      (timedFirstZeroAt l)) := by
  intro k l hkl
  apply Set.disjoint_left.2
  intro ω hk hl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hmem : k + 1 ∈ Finset.range (l + 1) := by
      simp only [Finset.mem_range]
      omega
    have hpos := hl.1 (k + 1) hmem
    rw [hk.2] at hpos
    omega
  · have hmem : l + 1 ∈ Finset.range (k + 1) := by
      simp only [Finset.mem_range]
      omega
    have hpos := hk.1 (l + 1) hmem
    rw [hl.2] at hpos
    omega

lemma timedFirstZeroLongAt_pairwise (x : Real) :
    Pairwise (fun k l => Disjoint (timedFirstZeroLongAt x k)
      (timedFirstZeroLongAt x l)) := by
  intro k l hkl
  exact (timedFirstZeroAt_pairwise hkl).mono
    (fun ω (h : ω ∈ timedFirstZeroLongAt x k) =>
      show ω ∈ timedFirstZeroAt k from ⟨h.1, h.2.1⟩)
    (fun ω (h : ω ∈ timedFirstZeroLongAt x l) =>
      show ω ∈ timedFirstZeroAt l from ⟨h.1, h.2.1⟩)

lemma mem_iUnion_timedFirstZeroAt
    (ω : Nat → Nat × Real) (hstart : 0 < (ω 0).1)
    (hzero : ∃ t, (ω t).1 = 0) :
    ω ∈ ⋃ k, timedFirstZeroAt k := by
  let t := Nat.find hzero
  have htzero : (ω t).1 = 0 := Nat.find_spec hzero
  have htpos : 0 < t := by
    by_contra h
    have ht : t = 0 := Nat.eq_zero_of_not_pos h
    rw [ht] at htzero
    omega
  let k := t - 1
  have hkt : k + 1 = t := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr htpos.ne')
  apply Set.mem_iUnion_of_mem k
  refine ⟨?_, by simpa only [hkt] using htzero⟩
  intro j hj
  have hjlt : j < t := by
    rw [← hkt]
    exact Finset.mem_range.mp hj
  exact Nat.pos_of_ne_zero fun hjzero =>
    (Nat.not_le_of_gt hjlt) (Nat.find_min' hzero hjzero)

set_option maxHeartbeats 600000 in
lemma timedFirstZeroLongAt_lower
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta) (m k : Nat)
    (x : Real) (hx : 0 ≤ x) :
    ENNReal.ofReal
          (Real.exp (-(singleSpeciesFinalRateBound params i * x))) *
        singleSpeciesTimedPathMeasure v params i hDelta m
          (timedFirstZeroAt k) ≤
      singleSpeciesTimedPathMeasure v params i hDelta m
        (timedFirstZeroLongAt x k) := by
  letI : IsMarkovKernel (singleSpeciesTimedKernel v params i) :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  let K := singleSpeciesTimedKernel v params i
  let P := homogeneousPathMeasure (Measure.dirac (m, 0)) K
  let e : ENNReal :=
    ENNReal.ofReal
      (Real.exp (-(singleSpeciesFinalRateBound params i * x)))
  let g : (∀ _ : Finset.Iic k, Nat × Real) → ENNReal := fun h =>
    if ∀ j : Finset.Iic k, 0 < (h j).1 then 1 else 0
  let φ0 : Nat × Real → ENNReal := fun y =>
    if y.1 = 0 then 1 else 0
  let φx : Nat × Real → ENNReal := fun y =>
    if y.1 = 0 ∧ x < y.2 then 1 else 0
  have hHistoryPositive :
      MeasurableSet
        {h : (∀ _ : Finset.Iic k, Nat × Real) |
          ∀ j : Finset.Iic k, 0 < (h j).1} := by
    have heq :
        {h : (∀ _ : Finset.Iic k, Nat × Real) |
            ∀ j : Finset.Iic k, 0 < (h j).1} =
          ⋂ j : Finset.Iic k, {h | (h j).1 ∈ Set.Ioi 0} := by
      ext h
      simp
    rw [heq]
    exact MeasurableSet.iInter fun j =>
        (measurable_pi_apply j :
            Measurable (fun h :
              (∀ _ : Finset.Iic k, Nat × Real) => h j)).fst
          (measurableSet_Ioi : MeasurableSet (Set.Ioi 0))
  have hg : Measurable g := by
    change Measurable fun h =>
      if h ∈
          {h : (∀ _ : Finset.Iic k, Nat × Real) |
            ∀ j : Finset.Iic k, 0 < (h j).1}
        then 1 else 0
    exact measurable_const.ite hHistoryPositive measurable_const
  have hφ0 : Measurable φ0 := by
    exact measurable_const.ite
      ((measurable_fst :
          Measurable (fun y : Nat × Real => y.1))
        (measurableSet_singleton 0))
      measurable_const
  have hφx : Measurable φx := by
    exact measurable_const.ite
      (MeasurableSet.inter
        ((measurable_fst :
            Measurable (fun y : Nat × Real => y.1))
          (measurableSet_singleton 0))
        ((measurable_snd :
            Measurable (fun y : Nat × Real => y.2))
          measurableSet_Ioi))
      measurable_const
  have hpositive_iff (ω : Nat → Nat × Real) :
      (∀ j ∈ Finset.range (k + 1), 0 < (ω j).1) ↔
        ∀ j : Finset.Iic k,
          0 < (frestrictLe k ω j).1 := by
    constructor
    · intro h j
      exact h j.1 (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))
    · intro h j hj
      exact h ⟨j, Finset.mem_Iic.mpr
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))⟩
  have hAt :
      P (timedFirstZeroAt k) =
        ∫⁻ h, g h * ∫⁻ y, φ0 y ∂
              K (finiteHistoryLast k h) ∂
          P.map (frestrictLe k) := by
    rw [← lintegral_indicator_one
      (measurableSet_timedFirstZeroAt k)]
    rw [show
      (∫⁻ ω, (timedFirstZeroAt k).indicator
          (1 : (Nat → Nat × Real) → ENNReal) ω ∂P) =
        ∫⁻ ω, g (frestrictLe k ω) * φ0 (ω (k + 1)) ∂P by
          congr 1
          funext ω
          by_cases hp :
              ∀ j ∈ Finset.range (k + 1), 0 < (ω j).1
          · have hpg := (hpositive_iff ω).mp hp
            have hpg' : ∀ j : Finset.Iic k,
                0 < (ω j.1).1 := by
              simpa only [frestrictLe_apply] using hpg
            simp only [timedFirstZeroAt, g, φ0,
              Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
              frestrictLe_apply]
            by_cases hz : (ω (k + 1)).1 = 0
            · rw [if_pos ⟨hp, hz⟩, if_pos hz, if_pos hpg',
                one_mul]
            · rw [if_neg (fun h => hz h.2), if_neg hz,
                mul_zero]
          · have hnpg : ¬∀ j : Finset.Iic k,
                0 < (frestrictLe k ω j).1 := by
              exact fun h => hp ((hpositive_iff ω).mpr h)
            have hnpg' : ¬∀ j : Finset.Iic k,
                0 < (ω j.1).1 := by
              exact fun h => hnpg (by
                simpa only [frestrictLe_apply] using h)
            simp only [timedFirstZeroAt, g, φ0,
              Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
              frestrictLe_apply]
            rw [if_neg (fun h => hp h.1), if_neg hnpg',
              zero_mul]]
    exact homogeneousPathMeasure_history_next_lintegral
      K (m, 0) k g φ0 hg hφ0
  have hLong :
      P (timedFirstZeroLongAt x k) =
        ∫⁻ h, g h * ∫⁻ y, φx y ∂
              K (finiteHistoryLast k h) ∂
          P.map (frestrictLe k) := by
    rw [← lintegral_indicator_one
      (measurableSet_timedFirstZeroLongAt x k)]
    rw [show
      (∫⁻ ω, (timedFirstZeroLongAt x k).indicator
          (1 : (Nat → Nat × Real) → ENNReal) ω ∂P) =
        ∫⁻ ω, g (frestrictLe k ω) * φx (ω (k + 1)) ∂P by
          congr 1
          funext ω
          by_cases hp :
              ∀ j ∈ Finset.range (k + 1), 0 < (ω j).1
          · have hpg := (hpositive_iff ω).mp hp
            have hpg' : ∀ j : Finset.Iic k,
                0 < (ω j.1).1 := by
              simpa only [frestrictLe_apply] using hpg
            simp only [timedFirstZeroLongAt, g, φx,
              Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
              frestrictLe_apply]
            by_cases ht :
                (ω (k + 1)).1 = 0 ∧ x < (ω (k + 1)).2
            · rw [if_pos ⟨hp, ht⟩, if_pos ht, if_pos hpg',
                one_mul]
            · rw [if_neg (fun h => ht h.2), if_neg ht,
                mul_zero]
          · have hnpg : ¬∀ j : Finset.Iic k,
                0 < (frestrictLe k ω j).1 := by
              exact fun h => hp ((hpositive_iff ω).mpr h)
            have hnpg' : ¬∀ j : Finset.Iic k,
                0 < (ω j.1).1 := by
              exact fun h => hnpg (by
                simpa only [frestrictLe_apply] using h)
            simp only [timedFirstZeroLongAt, g, φx,
              Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply,
              frestrictLe_apply]
            rw [if_neg (fun h => hp h.1), if_neg hnpg',
              zero_mul]]
    exact homogeneousPathMeasure_history_next_lintegral
      K (m, 0) k g φx hg hφx
  have hpoint : ∀ h,
      e * (g h * ∫⁻ y, φ0 y ∂K (finiteHistoryLast k h)) ≤
        g h * ∫⁻ y, φx y ∂K (finiteHistoryLast k h) := by
    intro h
    by_cases hall : ∀ j : Finset.Iic k, 0 < (h j).1
    · have hlast : 0 < (finiteHistoryLast k h).1 :=
        hall ⟨k, Finset.mem_Iic.mpr le_rfl⟩
      have hg_one : g h = 1 := by
        simp only [g, if_pos hall]
      rw [hg_one, one_mul]
      rw [show
          (∫⁻ y, φ0 y ∂K (finiteHistoryLast k h)) =
            K (finiteHistoryLast k h) {y | y.1 = 0} by
            rw [← lintegral_indicator_one
              (by measurability :
                MeasurableSet {y : Nat × Real | y.1 = 0})]
            congr 1
            funext y
            simp [φ0, Set.indicator],
        show
          (∫⁻ y, φx y ∂K (finiteHistoryLast k h)) =
            K (finiteHistoryLast k h)
              {y | y.1 = 0 ∧ x < y.2} by
            rw [← lintegral_indicator_one
              (by measurability :
                MeasurableSet
                  {y : Nat × Real | y.1 = 0 ∧ x < y.2})]
            congr 1
            funext y
            simp [φx, Set.indicator]]
      rw [one_mul]
      dsimp only [e, K]
      exact singleSpeciesTimedKernel_final_holding
        v params i hDelta (finiteHistoryLast k h)
          hlast x hx
    · have hg_zero : g h = 0 := by
        simp only [g, if_neg hall]
      rw [hg_zero, zero_mul, mul_zero, zero_mul]
  change e * P (timedFirstZeroAt k) ≤
    P (timedFirstZeroLongAt x k)
  rw [hAt, hLong]
  have hIntegrand : Measurable fun h =>
      g h * ∫⁻ y, φ0 y ∂K (finiteHistoryLast k h) :=
    hg.mul (hφ0.lintegral_kernel.comp
      (measurable_finiteHistoryLast k))
  rw [← lintegral_const_mul e hIntegrand]
  exact lintegral_mono hpoint

set_option maxHeartbeats 600000 in
theorem singleSpecies_timedExtinctionTime_tail
    (v : LVVariant) (params : LVParams) (i : Bool)
    (hDelta : 0 < params.delta)
    (hGamma : 0 < speciesGamma params i)
    (m : Nat) (hm : 0 < m)
    (x : Real) (hx : 0 ≤ x) :
    ENNReal.ofReal
          (Real.exp
            (-(singleSpeciesFinalRateBound params i * x))) ≤
      singleSpeciesTimedPathMeasure v params i hDelta m
        {ω | ENNReal.ofReal x ≤ timedExtinctionTime ω} := by
  letI : IsMarkovKernel (singleSpeciesTimedKernel v params i) :=
    singleSpeciesTimedKernel_isMarkov v params i hDelta
  let P :=
    homogeneousPathMeasure (Measure.dirac (m, 0))
      (singleSpeciesTimedKernel v params i)
  haveI : IsProbabilityMeasure P := by
    simp only [P, homogeneousPathMeasure]
    infer_instance
  let e : ENNReal :=
    ENNReal.ofReal
      (Real.exp
        (-(singleSpeciesFinalRateBound params i * x)))
  let A : Nat → Set (Nat → Nat × Real) := timedFirstZeroAt
  let B : Nat → Set (Nat → Nat × Real) :=
    timedFirstZeroLongAt x
  have hAmeas : ∀ k, MeasurableSet (A k) :=
    fun k => measurableSet_timedFirstZeroAt k
  have hBmeas : ∀ k, MeasurableSet (B k) :=
    fun k => measurableSet_timedFirstZeroLongAt x k
  have hAmass : P (⋃ k, A k) = 1 := by
    have hinit : ∀ᵐ ω ∂P, ω 0 = (m, 0) := by
      rw [ae_iff]
      change
        singleSpeciesTimedPathMeasure v params i hDelta m
          {ω | ω 0 ≠ (m, 0)} = 0
      change
        homogeneousPathMeasure (Measure.dirac (m, 0))
            (singleSpeciesTimedKernel v params i)
          {ω | ω 0 ≠ (m, 0)} = 0
      exact homogeneousPathMeasure_initial_ne_null
        (singleSpeciesTimedKernel v params i) (m, 0)
    have hextinct :=
      singleSpeciesTimedPath_eventually_zero_ae
        v params i hDelta hGamma m
    have hmem : ∀ᵐ ω ∂P, ω ∈ ⋃ k, A k := by
      have hextinctP :
          ∀ᵐ ω ∂P, ∃ t, (ω t).1 = 0 := by
        simpa only [P, singleSpeciesTimedPathMeasure] using
          hextinct
      filter_upwards [hinit, hextinctP] with ω hω0 hωzero
      exact mem_iUnion_timedFirstZeroAt
        ω (by simpa only [hω0] using hm) hωzero
    have heq : (⋃ k, A k) =ᵐ[P] Set.univ := by
      filter_upwards [hmem] with ω hω
      apply propext
      exact ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
    rw [measure_congr heq]
    exact measure_univ
  have hAlong : ∀ k, e * P (A k) ≤ P (B k) := by
    intro k
    simpa only [P, singleSpeciesTimedPathMeasure, e, A, B] using
      (timedFirstZeroLongAt_lower
        v params i hDelta m k x hx)
  have hBsubset :
      (⋃ k, B k) ⊆
        {ω | ENNReal.ofReal x ≤ timedExtinctionTime ω} := by
    intro ω hω
    rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
    have hxhold :
        ENNReal.ofReal x ≤
          timedHoldingContribution ω (k + 1) := by
      simp only [timedHoldingContribution,
        Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
        timedStateHolding]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hk.2.2)
    exact hxhold.trans (ENNReal.le_tsum (k + 1))
  change e ≤ P {ω | ENNReal.ofReal x ≤ timedExtinctionTime ω}
  calc
    e = e * P (⋃ k, A k) := by rw [hAmass, mul_one]
    _ = e * ∑' k, P (A k) := by
          rw [measure_iUnion timedFirstZeroAt_pairwise hAmeas]
    _ = ∑' k, e * P (A k) := by
          rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' k, P (B k) :=
          ENNReal.tsum_le_tsum hAlong
    _ = P (⋃ k, B k) := by
          rw [measure_iUnion
            (timedFirstZeroLongAt_pairwise x) hBmeas]
    _ ≤ P {ω | ENNReal.ofReal x ≤ timedExtinctionTime ω} :=
          measure_mono hBsubset

/-! ## The independent extinction-time race -/

/-- Under the product law of the two isolated species, the probability
that species `0` becomes extinct before species `1` has a positive lower
bound depending only on the reaction rates, not on the two positive
initial population counts. -/
theorem independent_singleSpecies_extinction_race_lower
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma1 : 0 < speciesGamma params true)
    (cert : CTAbsorptionCertificate
      (singleSpeciesReferenceCT params false hDelta))
    (hcertMono : Monotone cert.V)
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    let x : Real := 2 * (cert.bound.toReal + 1)
    (1 / 2 : ENNReal) *
          ENNReal.ofReal
            (Real.exp
              (-(singleSpeciesFinalRateBound params true * x))) ≤
      (singleSpeciesTimedPathMeasure
            v params false hDelta a).prod
          (singleSpeciesTimedPathMeasure
            v params true hDelta b)
        {z | timedExtinctionTime z.1 <
          timedExtinctionTime z.2} := by
  let μ0 :=
    singleSpeciesTimedPathMeasure
      v params false hDelta a
  let μ1 :=
    singleSpeciesTimedPathMeasure
      v params true hDelta b
  let C : ENNReal := cert.bound + 1
  let x : Real := 2 * (cert.bound.toReal + 1)
  let q : ENNReal := 2 * C
  let e : ENNReal :=
    ENNReal.ofReal
      (Real.exp
        (-(singleSpeciesFinalRateBound params true * x)))
  haveI hμ0prob : IsProbabilityMeasure μ0 := by
    simp only [μ0, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  haveI hμ1prob : IsProbabilityMeasure μ1 := by
    simp only [μ1, singleSpeciesTimedPathMeasure,
      homogeneousPathMeasure]
    infer_instance
  have hqeq : ENNReal.ofReal x = q := by
    simp only [x, q, C]
    rw [ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal cert.bound_ne_top]
    norm_num
  have hqzero : q ≠ 0 := by
    simp only [q, C]
    positivity
  have hqtop : q ≠ ⊤ := by
    simp only [q, C]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr
        ⟨cert.bound_ne_top, by norm_num⟩)
  let Bad : Set (Nat → Nat × Real) :=
    {ω | q ≤ timedExtinctionTime ω}
  let Good : Set (Nat → Nat × Real) :=
    {ω | timedExtinctionTime ω < q}
  let Long : Set (Nat → Nat × Real) :=
    {ω | q ≤ timedExtinctionTime ω}
  have hBadMeas : MeasurableSet Bad := by
    exact measurableSet_le measurable_const
      measurable_timedExtinctionTime
  have hGoodEq : Good = Badᶜ := by
    ext ω
    simp only [Good, Bad, Set.mem_setOf_eq, Set.mem_compl_iff]
    simp
  have hLongMeas : MeasurableSet Long := by
    exact measurableSet_le measurable_const
      measurable_timedExtinctionTime
  have hMean :
      ∫⁻ ω, timedExtinctionTime ω ∂μ0 ≤ cert.bound := by
    exact singleSpecies_timedExtinctionTime_lintegral_le
      v params false hDelta cert hcertMono a
  have hBad :
      μ0 Bad ≤ (1 / 2 : ENNReal) := by
    calc
      μ0 Bad ≤
          (∫⁻ ω, timedExtinctionTime ω ∂μ0) / q := by
            exact meas_ge_le_lintegral_div
              measurable_timedExtinctionTime.aemeasurable
              hqzero hqtop
      _ ≤ cert.bound / q :=
          ENNReal.div_le_div_right hMean q
      _ ≤ (1 / 2 : ENNReal) := by
        simp only [q, C]
        rw [ENNReal.div_le_iff]
        · rw [show (1 / 2 : ENNReal) = 2⁻¹ by norm_num,
            ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
          exact le_add_right le_rfl
        · positivity
        · exact ENNReal.mul_ne_top (by norm_num)
            (ENNReal.add_ne_top.mpr
              ⟨cert.bound_ne_top, by norm_num⟩)
  have hGood :
      (1 / 2 : ENNReal) ≤ μ0 Good := by
    rw [hGoodEq, measure_compl hBadMeas
      (measure_ne_top μ0 Bad), measure_univ]
    have hsub := tsub_le_tsub_left hBad (1 : ENNReal)
    norm_num at hsub ⊢
    exact hsub
  have hxnonneg : 0 ≤ x := by
    simp only [x]
    positivity
  have hLong :
      e ≤ μ1 Long := by
    have htail :=
      singleSpecies_timedExtinctionTime_tail
        v params true hDelta hGamma1 b hb x hxnonneg
    simpa only [μ1, Long, e, hqeq] using htail
  have hRectangle :
      Good ×ˢ Long ⊆
        {z | timedExtinctionTime z.1 <
          timedExtinctionTime z.2} := by
    intro z hz
    have hz0 :
        timedExtinctionTime z.1 < q := by
      exact hz.1
    have hz1 :
        q ≤ timedExtinctionTime z.2 := by
      exact hz.2
    exact lt_of_lt_of_le hz0 hz1
  change (1 / 2 : ENNReal) * e ≤
    μ0.prod μ1
      {z | timedExtinctionTime z.1 <
        timedExtinctionTime z.2}
  calc
    (1 / 2 : ENNReal) * e ≤ μ0 Good * μ1 Long :=
      mul_le_mul' hGood hLong
    _ = μ0.prod μ1 (Good ×ˢ Long) := by
      rw [Measure.prod_prod]
    _ ≤ μ0.prod μ1
          {z | timedExtinctionTime z.1 <
            timedExtinctionTime z.2} :=
      measure_mono hRectangle

/-- Uniform positive lower bound for the independent extinction-time
race.  The real constant depends only on the reaction rates and the
competition mechanism. -/
theorem exists_uniform_independent_extinction_race_lower
    (v : LVVariant) (params : LVParams)
    (hDelta : 0 < params.delta)
    (hGamma0 : 0 < speciesGamma params false)
    (hGamma1 : 0 < speciesGamma params true) :
    ∃ ε : Real, 0 < ε ∧
      ∀ a b : Nat, 0 < a → 0 < b →
        ENNReal.ofReal ε ≤
          (singleSpeciesTimedPathMeasure
                v params false hDelta a).prod
              (singleSpeciesTimedPathMeasure
                v params true hDelta b)
            {z | timedExtinctionTime z.1 <
              timedExtinctionTime z.2} := by
  obtain ⟨cert, hcertMono⟩ :=
    exists_singleSpecies_monotone_certificate
      params false hDelta hGamma0
  let x : Real := 2 * (cert.bound.toReal + 1)
  let ε : Real :=
    (1 / 2 : Real) *
      Real.exp
        (-(singleSpeciesFinalRateBound params true * x))
  refine ⟨ε, ?_, ?_⟩
  · simp only [ε]
    positivity
  · intro a b ha hb
    have hrace :=
      independent_singleSpecies_extinction_race_lower
        v params hDelta hGamma1 cert hcertMono
          a b ha hb
    have hhalf : (0 : Real) ≤ 1 / 2 := by norm_num
    have hhalfENN :
        ENNReal.ofReal (1 / 2 : Real) = (1 / 2 : ENNReal) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    simpa only [ε, x, ENNReal.ofReal_mul hhalf, hhalfENN]
      using hrace

/-! ## Exponential-clock identities for the embedded-chain bridge -/

/-- Laplace transform of an exponential holding time. -/
lemma expMeasure_laplace
    {r s : Real} (hr : 0 < r) (hs : 0 ≤ s) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x))) ∂expMeasure r =
      ENNReal.ofReal (r / (r + s)) := by
  rw [expMeasure, gammaMeasure]
  have hpdf : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hg : Measurable
      (fun x : Real => ENNReal.ofReal (Real.exp (-(s * x)))) := by
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul volume hpdf hg]
  have hrs : 0 < r + s := by linarith
  have hzero :
      ∀ x : Real,
        gammaPDF 1 r x *
            ENNReal.ofReal (Real.exp (-(s * x))) =
          (Set.Ici (0 : Real)).indicator
            (fun x => ENNReal.ofReal
              (r * Real.exp (-((r + s) * x)))) x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem
        (show x ∈ Set.Ici (0 : Real) from hx)]
      rw [gammaPDF_of_nonneg hx]
      norm_num only [Real.one_rpow, Real.Gamma_one,
        div_one, sub_self, Real.rpow_zero, mul_one]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show -((r + s) * x) = -(r * x) + -(s * x) by ring,
        Real.exp_add]
      rw [Real.rpow_one, mul_assoc]
    · rw [Set.indicator_of_notMem
        (show x ∉ Set.Ici (0 : Real) from hx)]
      have hxneg : x < 0 := lt_of_not_ge hx
      simp [gammaPDF_of_neg hxneg]
  simp_rw [Pi.mul_apply, hzero]
  rw [lintegral_indicator measurableSet_Ici]
  have hint :
      IntegrableOn
        (fun x : Real => r * Real.exp (-((r + s) * x)))
        (Set.Ioi 0) := by
    change Integrable
      (fun x : Real => r * Real.exp (-((r + s) * x)))
      (volume.restrict (Set.Ioi 0))
    convert
      (integrableOn_exp_mul_Ioi (a := -(r + s))
        (by linarith) 0).const_mul r using 1
    funext x
    congr 2
    ring
  have hint' :
      IntegrableOn
        (fun x : Real => r * Real.exp (-((r + s) * x)))
        (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (Filter.Eventually.of_forall fun _ => by positivity)]
  have hIntegral :
      ∫ x : Real in Set.Ioi 0,
          r * Real.exp (-((r + s) * x)) = r / (r + s) := by
    rw [MeasureTheory.integral_const_mul]
    have hExp :
        ∫ x : Real in Set.Ioi 0, Real.exp (-((r + s) * x)) =
          1 / (r + s) := by
      have hfun :
          (fun x : Real => Real.exp (-((r + s) * x))) =
            fun x : Real => Real.exp ((-(r + s)) * x) := by
        funext x
        congr 1
        ring
      rw [hfun, integral_exp_mul_Ioi (a := -(r + s)) (by linarith) 0]
      rw [mul_zero, Real.exp_zero]
      field_simp
    rw [hExp]
    field_simp
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, hIntegral]

end LVConsensus
