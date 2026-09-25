/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Final
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Efficient
public import Complexitylib.Metacomplexity.MINCKT.Gap.Multiplicative

/-!
# The multiplicative-hardness consequence of conditional MinKT SoI

This module composes the complete finite spine of Hirahara's conditional MinKT
argument. An admissible primitive clock supplies a polynomial slack-amplified
gap clock, an operational condition-first compiler supplies the paired upper
chain, and one ordinary estimator, correct on the plan's own queries, plus
time-bounded symmetry of information supplies the conditional estimator. If the induced threshold
language is in `P`, NP-hardness of the corresponding multiplicative gap forces
`P = NP`.

Every remaining research obligation stays explicit in the theorem statement;
in particular, this result does not assert the SoI hypothesis, a concrete
universal evaluator, estimator efficiency, or multiplicative-gap hardness.

The estimator is required to be correct only on the plan's paired and
condition-only queries, whose clocks dominate their output lengths. Correctness
on every instance cannot hold for these ordinary parameters
(`not_satisfiesBounds_ordinaryParameters`).
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/-- The complete finite multiplicative-hardness consequence of the
slack-amplified SoI reduction.

The clock admissibility hypothesis proves that the final conditional clock is
both widening and polynomially bounded. Only widening is needed to construct
the promise; the polynomial bound remains available as part of the public
parameter theorem. -/
theorem P_eq_NP_of_multiplicative_hard_of_SoI
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBoundsOn ordinaryMachine
      (ordinaryParameters clock) (plan clock compilerLoss).IsEstimatorQuery)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock (logarithmicSoILoss clock additive))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor))
    (hpolynomial : GapMINCKT.estimatorLanguage
      ((plan clock compilerLoss).components ordinaryEstimate).estimate ∈ P) :
    P = NP := by
  have hcompatible :=
    Slack.IsRegularClock.compatible_of_pairComposition
      (additive := additive) hclock.toIsRegularClock hsupports
  exact GapMINCKT.Multiplicative.P_eq_NP_of_hard_of_estimatorLanguage_mem_P
    ordinaryMachine conditionalMachine (parameters clock additive compilerLoss)
      factor (Slack.IsAdmissibleClock.parameters_admissible hclock additive
        compilerLoss).widening
        hfactor hhard
          (hcompatible.satisfiesBoundsOnQueries hestimate hsoi
            (Slack.IsAdmissibleClock.parameters_admissible hclock additive
              compilerLoss).widening)
          hpolynomial

/-- The implementation-level form of the complete consequence. Polynomial-time
encoded query builders and an encoded ordinary estimator construct the induced
threshold language in `P`, so no separate semantic membership premise remains. -/
theorem P_eq_NP_of_multiplicative_hard_of_SoI_of_implementations
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBoundsOn ordinaryMachine
      (ordinaryParameters clock) (plan clock compilerLoss).IsEstimatorQuery)
    (encodedPlan : EncodedPlan (plan clock compilerLoss))
    (encodedEstimator : EncodedEstimator ordinaryEstimate)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock (logarithmicSoILoss clock additive))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor)) :
    P = NP :=
  P_eq_NP_of_multiplicative_hard_of_SoI additive compilerLoss ordinaryMachine
    conditionalMachine hclock hsupports hestimate hsoi factor hfactor hhard
      (encodedPlan.estimatorLanguage_mem_P encodedEstimator)

/-- Former name of `P_eq_NP_of_multiplicative_hard_of_SoI_of_implementations`,
which now requires estimator correctness only on the plan's queries. -/
@[deprecated P_eq_NP_of_multiplicative_hard_of_SoI_of_implementations
  (since := "2026-09-25")]
theorem P_eq_NP_of_multiplicative_hard_of_SoI_of_query_implementations
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBoundsOn ordinaryMachine
      (ordinaryParameters clock) (plan clock compilerLoss).IsEstimatorQuery)
    (encodedPlan : EncodedPlan (plan clock compilerLoss))
    (encodedEstimator : EncodedEstimator ordinaryEstimate)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock (logarithmicSoILoss clock additive))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor)) :
    P = NP :=
  P_eq_NP_of_multiplicative_hard_of_SoI_of_implementations additive compilerLoss
    ordinaryMachine conditionalMachine hclock hsupports hestimate encodedPlan
      encodedEstimator hsoi factor hfactor hhard

/-- Replace the abstract ordinary estimator and its encoded implementation by
an `FP` solver for logarithmic GapMINKT.

The bounded threshold sweep supplies both the Fact 3.4 estimator sandwich and
the encoded estimator consumed by the two-query conditional reduction. The
threshold sweep needs every query of the plan to have finite ordinary
complexity; that is the explicit premise `hfinite`. It holds when the ordinary
machine can print strings within the queries' clocks, which dominate their
output lengths. -/
theorem P_eq_NP_of_multiplicative_hard_of_SoI_of_logarithmic_solver
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    (hfinite : ∀ query : MINKT.Instance,
      (plan clock compilerLoss).IsEstimatorQuery query →
      ordinaryMachine.timeBoundedKolmogorovComplexity
        query.output query.time ≠ ⊤)
    (decide : List Bool → Bool)
    (hdecide : (fun bits => [decide bits]) ∈ FP)
    (hsolve : (GapMINKT.Logarithmic.problem ordinaryMachine
      (ordinaryParameters clock)
        hclock.toIsRegularClock.ordinaryParameters_widening).SolvedBy decide)
    (encodedPlan : EncodedPlan (plan clock compilerLoss))
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock (logarithmicSoILoss clock additive))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor)) :
    P = NP := by
  have hestimate :=
    GapMINKT.Logarithmic.Efficient.executableEstimator_satisfiesBoundsOn
      hclock.toIsRegularClock.ordinaryParameters_widening hsolve hfinite
  exact P_eq_NP_of_multiplicative_hard_of_SoI_of_implementations additive
    compilerLoss ordinaryMachine conditionalMachine hclock hsupports hestimate
      encodedPlan (encodedEstimatorOfGapSolver decide hdecide) hsoi factor
        hfactor hhard

/-- Assuming `P ≠ NP`, the simultaneous SoI, estimator-efficiency, compiler,
and multiplicative-hardness hypotheses are inconsistent. This is the precise
contrapositive needed before a future `DistNP ⊆ AvgP → SoI` theorem can rule
out Heuristica. -/
theorem not_timeBoundedSymmetryOfInformation_of_P_ne_NP
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBoundsOn ordinaryMachine
      (ordinaryParameters clock) (plan clock compilerLoss).IsEstimatorQuery)
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor))
    (hpolynomial : GapMINCKT.estimatorLanguage
      ((plan clock compilerLoss).components ordinaryEstimate).estimate ∈ P)
    (hne : P ≠ NP) :
    ¬TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock (logarithmicSoILoss clock additive) := by
  intro hsoi
  exact hne (P_eq_NP_of_multiplicative_hard_of_SoI additive compilerLoss
    ordinaryMachine conditionalMachine hclock hsupports hestimate hsoi factor
      hfactor hhard hpolynomial)

/-- Under `P ≠ NP`, implementation-level estimator efficiency and
multiplicative hardness rule out the corresponding time-bounded SoI statement. -/
theorem not_timeBoundedSymmetryOfInformation_of_P_ne_NP_of_implementations
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    {ordinaryEstimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : ordinaryEstimate.SatisfiesBoundsOn ordinaryMachine
      (ordinaryParameters clock) (plan clock compilerLoss).IsEstimatorQuery)
    (encodedPlan : EncodedPlan (plan clock compilerLoss))
    (encodedEstimator : EncodedEstimator ordinaryEstimate)
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor))
    (hne : P ≠ NP) :
    ¬TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock (logarithmicSoILoss clock additive) := by
  intro hsoi
  exact hne
    (P_eq_NP_of_multiplicative_hard_of_SoI_of_implementations additive
      compilerLoss ordinaryMachine conditionalMachine hclock hsupports hestimate
        encodedPlan encodedEstimator hsoi factor hfactor hhard)

/-- Under `P ≠ NP`, an efficient logarithmic GapMINKT solver, the encoded
two-query plan, and multiplicative conditional-gap hardness rule out the
corresponding SoI statement. -/
theorem not_timeBoundedSymmetryOfInformation_of_P_ne_NP_of_logarithmic_solver
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} (additive compilerLoss : ℕ)
    {composition : PairCompositionPlan}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (hclock : IsAdmissibleClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine)
    (hfinite : ∀ query : MINKT.Instance,
      (plan clock compilerLoss).IsEstimatorQuery query →
      ordinaryMachine.timeBoundedKolmogorovComplexity
        query.output query.time ≠ ⊤)
    (decide : List Bool → Bool)
    (hdecide : (fun bits => [decide bits]) ∈ FP)
    (hsolve : (GapMINKT.Logarithmic.problem ordinaryMachine
      (ordinaryParameters clock)
        hclock.toIsRegularClock.ordinaryParameters_widening).SolvedBy decide)
    (encodedPlan : EncodedPlan (plan clock compilerLoss))
    (factor : ℕ → ℕ) (hfactor : ∀ length, 1 ≤ factor length)
    (hhard : PromiseNPHard
      (GapMINCKT.Multiplicative.problem ordinaryMachine conditionalMachine
        (parameters clock additive compilerLoss) factor
          (Slack.IsAdmissibleClock.parameters_admissible hclock additive
            compilerLoss).widening
            hfactor))
    (hne : P ≠ NP) :
    ¬TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock (logarithmicSoILoss clock additive) := by
  intro hsoi
  exact hne
    (P_eq_NP_of_multiplicative_hard_of_SoI_of_logarithmic_solver additive
      compilerLoss ordinaryMachine conditionalMachine hclock hsupports hfinite
        decide hdecide hsolve encodedPlan hsoi factor hfactor hhard)

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
