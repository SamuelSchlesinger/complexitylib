/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.InputSplit
public import Complexitylib.Algebraic.MassProduction.ShannonCircuit
public import Complexitylib.Algebraic.MassProduction.UhligLayer

/-!
# Polynomial overhead bounds for the finite Uhlig layer

This module bounds the routing and decoding overhead of the complete finite
Uhlig layer. The result is an explicit polynomial bound used by the quantitative
recursion; no asymptotic claim is hidden in this module.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligCircuit

open scoped BigOperators

/-! ## Polynomial overhead bounds for the shared layer -/

/-- Prefix-equality testing costs at most two gates per tested bit. -/
theorem sourceIndicatorExpression_standardCost_le
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    (sourceIndicatorExpression (suffixWidth := suffixWidth)
      side source).standardCost <= 2 * prefixWidth := by
  rw [sourceIndicatorExpression,
    DeMorgan.Expression.finAnd_standardCost]
  calc
    (Finset.univ.sum fun bit : Fin prefixWidth =>
        (ShannonSynthesis.matchingLiteral
          (localInputIndex side (Fin.castAdd suffixWidth bit))
          (InputSplit.sourceBits
            (Fin.cast (prefixCount_eq prefixWidth) source) bit)).standardCost) +
        prefixWidth <=
      (Finset.univ.sum fun _bit : Fin prefixWidth => 1) +
        prefixWidth := by
          gcongr with bit
          exact ShannonSynthesis.matchingLiteral_standardCost_le _ _
    _ = 2 * prefixWidth := by
      simp
      omega

theorem stateSourceIndicatorExpression_standardCost_le
    (pair : Fin pairs)
    (side : Fin 2)
    (source : Fin (prefixLast prefixWidth + 1)) :
    (stateSourceIndicatorExpression (suffixWidth := suffixWidth)
      pair side source).standardCost <= 2 * prefixWidth := by
  rw [stateSourceIndicatorExpression,
    DeMorgan.Expression.mapInputs_standardCost]
  exact sourceIndicatorExpression_standardCost_le
    (suffixWidth := suffixWidth) side source

@[simp] theorem fixedRoutedSuffixExpression_standardCost
    (first second : Fin (prefixLast prefixWidth + 1))
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    (fixedRoutedSuffixExpression first second resource bit).standardCost =
      0 := by
  unfold fixedRoutedSuffixExpression
  split
  · rfl
  · split <;> rfl

@[simp] theorem resourceRouterCircuit_cost
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun bit : Fin suffixWidth =>
        (routedSuffixExpression resource bit).standardCost := by
  simp [resourceRouterCircuit]

/-- A direct polynomial bound for one routed suffix bit. -/
def routedSuffixCostBound (prefixWidth : Nat) : Nat :=
  let sources := prefixLast prefixWidth + 1
  sources *
      (2 * prefixWidth +
        (sources * (2 * prefixWidth + 1) + sources) + 1) +
    sources

theorem routedSuffixExpression_standardCost_le
    (resource : Fin (prefixLast prefixWidth + 2))
    (bit : Fin suffixWidth) :
    (routedSuffixExpression resource bit).standardCost <=
      routedSuffixCostBound prefixWidth := by
  let sources := prefixLast prefixWidth + 1
  have innerBound (first : Fin (prefixLast prefixWidth + 1)) :
      (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1) fun second =>
        .and (sourceIndicatorExpression
            (suffixWidth := suffixWidth) 1 second)
          (fixedRoutedSuffixExpression first second resource bit)).standardCost <=
        sources * (2 * prefixWidth + 1) + sources := by
    rw [DeMorgan.Expression.finOr_standardCost]
    calc
      (Finset.univ.sum fun second : Fin (prefixLast prefixWidth + 1) =>
          (DeMorgan.Expression.and
            (sourceIndicatorExpression
              (suffixWidth := suffixWidth) 1 second)
            (fixedRoutedSuffixExpression first second resource bit)).standardCost) +
          (prefixLast prefixWidth + 1) <=
        (Finset.univ.sum fun _second :
            Fin (prefixLast prefixWidth + 1) =>
          2 * prefixWidth + 1) +
          (prefixLast prefixWidth + 1) := by
            gcongr with second
            simp only [DeMorgan.Expression.standardCost,
              fixedRoutedSuffixExpression_standardCost]
            have indicatorBound :=
              sourceIndicatorExpression_standardCost_le
                (suffixWidth := suffixWidth) 1 second
            omega
      _ = sources * (2 * prefixWidth + 1) + sources := by
        simp [sources]
  rw [routedSuffixExpression,
    DeMorgan.Expression.finOr_standardCost]
  calc
    (Finset.univ.sum fun first : Fin (prefixLast prefixWidth + 1) =>
        (DeMorgan.Expression.and
          (sourceIndicatorExpression (suffixWidth := suffixWidth) 0 first)
          (DeMorgan.Expression.finOr (prefixLast prefixWidth + 1)
            fun second =>
              .and (sourceIndicatorExpression
                  (suffixWidth := suffixWidth) 1 second)
                (fixedRoutedSuffixExpression first second resource bit))).standardCost) +
        (prefixLast prefixWidth + 1) <=
      (Finset.univ.sum fun _first : Fin (prefixLast prefixWidth + 1) =>
        2 * prefixWidth +
          (sources * (2 * prefixWidth + 1) + sources) + 1) +
        (prefixLast prefixWidth + 1) := by
          gcongr with first
          simp only [DeMorgan.Expression.standardCost]
          have indicatorBound :=
            sourceIndicatorExpression_standardCost_le
              (suffixWidth := suffixWidth) 0 first
          have nestedBound := innerBound first
          omega
    _ = routedSuffixCostBound prefixWidth := by
      simp [routedSuffixCostBound, sources]

theorem resourceRouterCircuit_cost_le
    (resource : Fin (prefixLast prefixWidth + 2)) :
    (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
        DeMorgan.standardCost <=
      suffixWidth * routedSuffixCostBound prefixWidth := by
  rw [resourceRouterCircuit_cost]
  calc
    (Finset.univ.sum fun bit : Fin suffixWidth =>
      (routedSuffixExpression resource bit).standardCost) <=
        Finset.univ.sum fun _bit : Fin suffixWidth =>
          routedSuffixCostBound prefixWidth := by
            gcongr with bit
            exact routedSuffixExpression_standardCost_le
              (suffixWidth := suffixWidth) resource bit
    _ = suffixWidth * routedSuffixCostBound prefixWidth := by simp

theorem candidatePostprocessExpression_cost :
    candidatePostprocessExpression.circuit.cost DeMorgan.standardCost = 2 := by
  rfl

/-- Uniform charged cost bound for one hardwired source-pair candidate. -/
def candidateDecodedCostBound (prefixWidth : Nat) : Nat :=
  4 * prefixWidth + 4 * (prefixLast prefixWidth + 2) + 2

theorem candidateDecodedCircuit_cost_le
    (pair : Fin pairs) (side : Fin 2)
    (first second : Fin (prefixLast prefixWidth + 1)) :
    (candidateDecodedCircuit (suffixWidth := suffixWidth)
      pair side first second).cost DeMorgan.standardCost <=
      candidateDecodedCostBound prefixWidth := by
  change
    (candidatePostprocessExpression.circuit.comp
      ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
        pair 0 first).circuit.parallel
        ((stateSourceIndicatorExpression (suffixWidth := suffixWidth)
          pair 1 second).circuit.parallel
          (sharedFixedDecodedCircuit (suffixWidth := suffixWidth)
            pair side first second)))).cost DeMorgan.standardCost <= _
  rw [Circuit.cost_comp, Circuit.cost_parallel, Circuit.cost_parallel,
    DeMorgan.Expression.circuit_cost,
    DeMorgan.Expression.circuit_cost,
    sharedFixedDecodedCircuit_cost,
    candidatePostprocessExpression_cost]
  have firstBound := stateSourceIndicatorExpression_standardCost_le
    (suffixWidth := suffixWidth) pair 0 first
  have secondBound := stateSourceIndicatorExpression_standardCost_le
    (suffixWidth := suffixWidth) pair 1 second
  unfold candidateDecodedCostBound
  omega

/-- Uniform row cost after OR-ing over the second source. -/
def candidateRowCostBound (prefixWidth : Nat) : Nat :=
  (prefixLast prefixWidth + 1) *
      candidateDecodedCostBound prefixWidth +
    (prefixLast prefixWidth + 1)

theorem candidateRowCircuit_cost_le
    (pair : Fin pairs) (side : Fin 2)
    (first : Fin (prefixLast prefixWidth + 1)) :
    (candidateRowCircuit (suffixWidth := suffixWidth)
      pair side first).cost DeMorgan.standardCost <=
      candidateRowCostBound prefixWidth := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun second =>
          candidateDecodedCircuit pair side first second))).cost
        DeMorgan.standardCost <= _
  rw [Circuit.cost_comp, Circuit.cost_parallelFin, orInputCircuit_cost]
  calc
    (Finset.univ.sum fun second : Fin (prefixLast prefixWidth + 1) =>
        (candidateDecodedCircuit (suffixWidth := suffixWidth)
          pair side first second).cost DeMorgan.standardCost) +
        (prefixLast prefixWidth + 1) <=
      (Finset.univ.sum fun _second : Fin (prefixLast prefixWidth + 1) =>
        candidateDecodedCostBound prefixWidth) +
        (prefixLast prefixWidth + 1) := by
          gcongr with second
          exact candidateDecodedCircuit_cost_le
            (suffixWidth := suffixWidth) pair side first second
    _ = candidateRowCostBound prefixWidth := by
      simp [candidateRowCostBound]

/-- Uniform charged cost bound for one requested-output decoder. -/
def sharedDecodedCostBound (prefixWidth : Nat) : Nat :=
  (prefixLast prefixWidth + 1) * candidateRowCostBound prefixWidth +
    (prefixLast prefixWidth + 1)

theorem sharedDecodedCircuit_cost_le
    (pair : Fin pairs) (side : Fin 2) :
    (sharedDecodedCircuit (prefixWidth := prefixWidth)
      (suffixWidth := suffixWidth) pair side).cost DeMorgan.standardCost <=
      sharedDecodedCostBound prefixWidth := by
  change
    ((orInputCircuit (prefixLast prefixWidth + 1)).comp
      (Circuit.parallelFin (prefixLast prefixWidth + 1)
        (fun first => candidateRowCircuit pair side first))).cost
        DeMorgan.standardCost <= _
  rw [Circuit.cost_comp, Circuit.cost_parallelFin, orInputCircuit_cost]
  calc
    (Finset.univ.sum fun first : Fin (prefixLast prefixWidth + 1) =>
        (candidateRowCircuit (suffixWidth := suffixWidth)
          pair side first).cost DeMorgan.standardCost) +
        (prefixLast prefixWidth + 1) <=
      (Finset.univ.sum fun _first : Fin (prefixLast prefixWidth + 1) =>
        candidateRowCostBound prefixWidth) +
        (prefixLast prefixWidth + 1) := by
          gcongr with first
          exact candidateRowCircuit_cost_le
            (suffixWidth := suffixWidth) pair side first
    _ = sharedDecodedCostBound prefixWidth := by
      simp [sharedDecodedCostBound]

theorem sharedDecoderCircuit_cost_le
    (prefixWidth suffixWidth pairs : Nat) :
    (sharedDecoderCircuit prefixWidth suffixWidth pairs).cost
        DeMorgan.standardCost <=
      (2 * pairs) * sharedDecodedCostBound prefixWidth := by
  rw [sharedDecoderCircuit_cost]
  calc
    (Finset.univ.sum fun output : Fin (2 * pairs) =>
      let pairSide := decoderPairSide output
      (sharedDecodedCircuit (prefixWidth := prefixWidth)
        (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
          DeMorgan.standardCost) <=
        Finset.univ.sum fun _output : Fin (2 * pairs) =>
          sharedDecodedCostBound prefixWidth := by
            gcongr with output
            exact sharedDecodedCircuit_cost_le
              (suffixWidth := suffixWidth)
              (decoderPairSide output).1 (decoderPairSide output).2
    _ = (2 * pairs) * sharedDecodedCostBound prefixWidth := by simp

/-- Uniform routing cost across all resources and request pairs. -/
theorem resourceRoutingBankCost_le
    (prefixWidth suffixWidth pairs : Nat) :
    (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
      Finset.univ.sum fun _pair : Fin pairs =>
        (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
          DeMorgan.standardCost) <=
      (prefixLast prefixWidth + 2) *
        (pairs * (suffixWidth * routedSuffixCostBound prefixWidth)) := by
  calc
    (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
      Finset.univ.sum fun _pair : Fin pairs =>
        (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
          DeMorgan.standardCost) <=
      Finset.univ.sum fun _resource : Fin (prefixLast prefixWidth + 2) =>
        pairs * (suffixWidth * routedSuffixCostBound prefixWidth) := by
          gcongr with resource
          calc
            (Finset.univ.sum fun _pair : Fin pairs =>
              (resourceRouterCircuit (suffixWidth := suffixWidth)
                resource).cost DeMorgan.standardCost) =
                pairs *
                  (resourceRouterCircuit (suffixWidth := suffixWidth)
                    resource).cost DeMorgan.standardCost := by simp
            _ <= pairs *
                (suffixWidth * routedSuffixCostBound prefixWidth) := by
              gcongr
              exact resourceRouterCircuit_cost_le
                (suffixWidth := suffixWidth) resource
    _ = (prefixLast prefixWidth + 2) *
        (pairs * (suffixWidth * routedSuffixCostBound prefixWidth)) := by simp

/-- Polynomial overhead added by one shared Uhlig layer. -/
def sharedLayerOverheadBound
    (prefixWidth suffixWidth pairs : Nat) : Nat :=
  (prefixLast prefixWidth + 2) *
      (pairs * (suffixWidth * routedSuffixCostBound prefixWidth)) +
    (2 * pairs) * sharedDecodedCostBound prefixWidth

/-- The shared finite layer costs the sum of its recursive resource circuits
plus an explicit polynomial overhead. -/
theorem sharedUhligLayerCircuit_cost_le_resource_sum_add_overhead
    (pairs : Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth) pairs) :
    (sharedUhligLayerCircuit pairs resourceCircuits).cost
        DeMorgan.standardCost <=
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        (resourceCircuits resource).cost DeMorgan.standardCost) +
      sharedLayerOverheadBound prefixWidth suffixWidth pairs := by
  rw [sharedUhligLayerCircuit_cost]
  rw [Finset.sum_add_distrib]
  have routingBound := resourceRoutingBankCost_le
    prefixWidth suffixWidth pairs
  have decoderBound :
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
            DeMorgan.standardCost) <=
        (2 * pairs) * sharedDecodedCostBound prefixWidth := by
    rw [← sharedDecoderCircuit_cost]
    exact sharedDecoderCircuit_cost_le prefixWidth suffixWidth pairs
  unfold sharedLayerOverheadBound
  omega

end UhligCircuit
end MassProduction
end Algebraic
