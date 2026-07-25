import LVConsensus.LabeledDynamics
import Mathlib.Probability.Distributions.Exponential

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LVConsensus.Paper

/-!
# Paper model: stochastic two-species Lotka--Volterra dynamics

This is the paper-facing entry point for Section 1.3.  It collects the
formal objects corresponding to the two chemical reaction networks, their
mass-action propensities, neutrality, the induced jump chain, consensus,
and majority consensus.

The continuous-time process waits an exponential time with parameter
`totalRate params s` and then chooses a reaction with probability
`reactionRate params s r / totalRate params s`.  Since every result in the
paper concerns the ordered sequence of reactions, the formal development
uses this induced discrete jump chain.
-/

/-- A population state `(x₀,x₁)` records the counts of the two species. -/
abbrev PopulationState := PopState

/-- The two competition mechanisms in equations (1) and (2) of the paper. -/
abbrev CompetitionMechanism := LVVariant

/-- The six nonnegative rate parameters
`(β,δ,α₀,α₁,γ₀,γ₁)`. -/
abbrev RateParameters := LVParams

/-- The reaction labels consist of the eight reactions appearing in the
paper models and an idle label used only at an absorbing state. -/
abbrev Reaction := LVReaction

/-- The paper's total interspecific competition rate `α=α₀+α₁`. -/
noncomputable def totalInterspecificRate (params : RateParameters) : ℝ :=
  params.alpha0 + params.alpha1

/-- The paper's total intraspecific competition rate `γ=γ₀+γ₁`. -/
noncomputable def totalIntraspecificRate (params : RateParameters) : ℝ :=
  params.gamma0 + params.gamma1

/-- Because `β` and `δ` are shared by the two species in `RateParameters`,
neutrality is exactly equality of the two interspecific rates and equality
of the two intraspecific rates. -/
def IsNeutral (params : RateParameters) : Prop :=
  params.alpha0 = params.alpha1 ∧ params.gamma0 = params.gamma1

/-- Births and individual deaths are the reactions with one reactant. -/
def IsIndividualReaction : Reaction → Prop
  | .birth0 | .birth1 | .death0 | .death1 => True
  | _ => False

/-- Interspecific and intraspecific competition reactions have two
reactants. -/
def IsPairwiseInteraction : Reaction → Prop
  | .inter0 | .inter1 | .intra0 | .intra1 => True
  | _ => False

/-- Mass-action propensity of a reaction in a population state.  It gives
`βxᵢ`, `δxᵢ`, `αᵢx₀x₁`, and `γᵢ xᵢ(xᵢ-1)/2`, respectively. -/
noncomputable abbrev reactionRate :=
  lvReactionWeight

/-- Population update produced by a reaction.  This is where the SD and
NSD models differ: an SD pairwise reaction removes both reactants, whereas
an NSD pairwise reaction removes only one. -/
abbrev reactionTarget :=
  lvReactionTarget

/-- Sum of all reaction propensities in the current state. -/
noncomputable abbrev totalRate :=
  lvTotalPropensity

/-- Conditional law of the time until the next reaction when the current
state has positive total propensity. -/
noncomputable def holdingTimeDistribution
    (params : RateParameters) (s : PopulationState) : Measure ℝ :=
  expMeasure (totalRate params s)

/-- Reaction-labelled jump kernel induced by the stochastic chemical
kinetics. -/
noncomputable abbrev reactionKernel :=
  lvLabeledKernel

/-- Population-state jump kernel obtained by forgetting reaction labels. -/
noncomputable abbrev populationKernel :=
  lvKernel

/-- Law of the population path started in `s₀`. -/
noncomputable abbrev populationPathMeasure :=
  lvPathMeasure

/-- A state is a consensus state exactly when at least one species has
count zero. -/
abbrev HasReachedConsensus :=
  reachedConsensus

/-- First time at which the population path reaches consensus. -/
noncomputable abbrev firstConsensusTime :=
  consensusTime

/-- Event that the species initially in the majority is the nonzero species
at the first consensus state. -/
abbrev MajorityConsensus :=
  majorityConsensusEvent

/-- Probability of majority consensus under the chosen mechanism and rate
parameters. -/
noncomputable abbrev majorityConsensusProbability :=
  majorityConsensusProb

/-- The total propensity is the sum of the eight reaction propensities. -/
theorem reaction_rates_sum_to_total
    (params : RateParameters) (s : PopulationState) :
    reactionRate params s .birth0 +
        reactionRate params s .birth1 +
        reactionRate params s .death0 +
        reactionRate params s .death1 +
        reactionRate params s .inter0 +
        reactionRate params s .inter1 +
        reactionRate params s .intra0 +
        reactionRate params s .intra1 =
      totalRate params s := by
  rcases s with ⟨x₀, x₁⟩
  simp only [reactionRate, totalRate, lvReactionWeight,
    lvTotalPropensity]
  ring

/-- At a nonabsorbing state, the holding-time distribution is a probability
measure. -/
theorem holding_time_is_probability
    (params : RateParameters) (s : PopulationState)
    (h : 0 < totalRate params s) :
    IsProbabilityMeasure (holdingTimeDistribution params s) :=
  isProbabilityMeasure_expMeasure h

/-- The holding time has the exponential distribution with rate equal to
the state's total propensity. -/
theorem holding_time_cdf
    (params : RateParameters) (s : PopulationState)
    (h : 0 < totalRate params s) (t : ℝ) :
    cdf (holdingTimeDistribution params s) t =
      if 0 ≤ t then
        1 - Real.exp (-(totalRate params s * t))
      else 0 :=
  cdf_expMeasure_eq h t

/-- If the total propensity is positive, the labelled jump chain chooses
reaction `r` with its mass-action propensity divided by the total
propensity. -/
theorem reaction_probability
    (v : CompetitionMechanism) (params : RateParameters)
    (z : LabeledPopState) (r : Reaction) :
    reactionKernel v params z {z' | z'.2 = r} =
      if _hφ : totalRate params z.1 = 0 then
        if r = .idle then 1 else 0
      else
        ENNReal.ofReal (1 / totalRate params z.1) *
          ENNReal.ofReal (reactionRate params z.1 r) :=
  lvLabeledKernel_reaction_probability v params z r

/-- The state stored by a labelled jump is almost surely the target of its
recorded reaction. -/
theorem reaction_updates_population
    (v : CompetitionMechanism) (params : RateParameters)
    (z : LabeledPopState) :
    ∀ᵐ z' ∂reactionKernel v params z,
      z'.1 = reactionTarget v z.1 z'.2 :=
  lvLabeledKernel_ae_reactionTarget v params z

/-- Forgetting reaction labels recovers exactly the population kernel used
throughout the paper's probability statements. -/
theorem forgetting_labels_recovers_population_model
    (v : CompetitionMechanism) (params : RateParameters)
    (z : LabeledPopState) :
    (reactionKernel v params z).map Prod.fst =
      populationKernel v params z.1 :=
  lvLabeledKernel_map_fst v params z

end LVConsensus.Paper
