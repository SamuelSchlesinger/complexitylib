/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.UhligDecoder

/-!
# Complete finite Uhlig layer

This module composes the routing and shared decoder circuits into one complete
finite mass-production layer. It proves exact correctness and exact cost
identities at finite widths and for an arbitrary number of request pairs.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligCircuit

open scoped BigOperators

/-! ## Complete finite Uhlig layer -/

/-- Preserve the original inputs and append every routed resource value. -/
noncomputable def layerStateCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        routedResourceGateCount prefixWidth suffixWidth pairs
          resourceGateCounts resource)
      (layerStateCount prefixWidth suffixWidth pairs) :=
  (Circuit.id DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)).parallel
    (resourceBankCircuit pairs resourceGateCounts resourceCircuits)
  |>.castCounts rfl (Nat.zero_add _) rfl

@[simp] theorem layerStateCircuit_eval_original
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (input : Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool) :
    originalInputFromState
        ((layerStateCircuit pairs resourceGateCounts resourceCircuits).eval
          DeMorgan.interpretation input) = input := by
  funext originalInput
  simp [originalInputFromState, layerStateCircuit]

theorem layerStateCircuit_eval_resource
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).ComputesWith DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs))
    (input : Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool)
    (resource : Fin (prefixLast prefixWidth + 2))
    (pair : Fin pairs) :
    (layerStateCircuit pairs resourceGateCounts resourceCircuits).eval
        DeMorgan.interpretation input (resourceStateIndex resource pair) =
      resourceValue function input pair resource := by
  rw [layerStateCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, Function.comp_id, id_eq]
  rw [Circuit.eval_parallel]
  unfold resourceStateIndex
  rw [Fin.append_right]
  exact resourceBankCircuit_eval function pairs resourceGateCounts
    resourceCircuits computes input resource pair

/-- Decoding the completed layer state agrees with the semantic Uhlig
decoder. -/
theorem decodedStateValue_layerStateCircuit_eval
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).ComputesWith DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs))
    (input : Fin (layerInputCount prefixWidth suffixWidth pairs) -> Bool)
    (pair : Fin pairs) (side : Fin 2) :
    decodedStateValue
        ((layerStateCircuit pairs resourceGateCounts resourceCircuits).eval
          DeMorgan.interpretation input)
        pair side =
      decodedValue function input pair side := by
  unfold decodedStateValue decodedValue
  rw [layerStateCircuit_eval_original pairs resourceGateCounts
    resourceCircuits input]
  unfold recoveryPair
  apply Finset.sum_congr rfl
  intro resource _member
  exact layerStateCircuit_eval_resource function pairs resourceGateCounts
    resourceCircuits computes input resource pair

/-- Quantitatively useful finite Uhlig layer, using circuit sharing inside
each XOR decoder. -/
noncomputable def sharedUhligLayerCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          routedResourceGateCount prefixWidth suffixWidth pairs
            resourceGateCounts resource) +
        (Finset.univ.sum fun output : Fin (2 * pairs) =>
          sharedDecoderOutputGateCount
            prefixWidth suffixWidth pairs output))
      (2 * pairs) :=
  (sharedDecoderCircuit prefixWidth suffixWidth pairs).comp
    (layerStateCircuit pairs resourceGateCounts resourceCircuits)

/-- Exact correctness of the shared finite layer. -/
theorem sharedUhligLayerCircuit_computes
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).ComputesWith DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs)) :
    (sharedUhligLayerCircuit pairs resourceGateCounts
      resourceCircuits).ComputesWith DeMorgan.interpretation
        (directProduct function (2 * pairs)) := by
  intro input
  funext output
  rw [sharedUhligLayerCircuit, Circuit.eval_comp,
    sharedDecoderCircuit_eval]
  let pairSide := decoderPairSide output
  rw [decodedStateValue_layerStateCircuit_eval function pairs
    resourceGateCounts resourceCircuits computes input pairSide.1 pairSide.2]
  exact congrFun (decodedValue_eq_directProduct function input) output

/-- Exact cost ledger for the shared finite layer. -/
@[simp] theorem sharedUhligLayerCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (sharedUhligLayerCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost)) +
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) pairSide.1 pairSide.2).cost
            DeMorgan.standardCost) := by
  simp [sharedUhligLayerCircuit]
  simp [layerStateCircuit]

/-- Compose routing, supplied resource evaluation, and exact decoding. -/
noncomputable def uhligLayerCircuit
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    Circuit DeMorgan.signature
      (layerInputCount prefixWidth suffixWidth pairs)
      ((Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          routedResourceGateCount prefixWidth suffixWidth pairs
            resourceGateCounts resource) +
        (Finset.univ.sum fun output : Fin (2 * pairs) =>
          decoderGateCount prefixWidth suffixWidth pairs output))
      (2 * pairs) :=
  (decoderCircuit prefixWidth suffixWidth pairs).comp
    (layerStateCircuit pairs resourceGateCounts resourceCircuits)

/-- Exact finite Uhlig circuit theorem. If each resource function is
available on `pairs` independent suffixes, one explicit De Morgan circuit
computes `2 * pairs` independent copies of the original function. -/
theorem uhligLayerCircuit_computes
    (function : ScalarFunction Bool (prefixWidth + suffixWidth))
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs)
    (computes : forall resource,
      (resourceCircuits resource).ComputesWith DeMorgan.interpretation
        (directProduct (resourceFunction function resource) pairs)) :
    (uhligLayerCircuit pairs resourceGateCounts resourceCircuits).ComputesWith
      DeMorgan.interpretation (directProduct function (2 * pairs)) := by
  intro input
  funext output
  rw [uhligLayerCircuit, Circuit.eval_comp, decoderCircuit_eval]
  let pairSide := decoderPairSide output
  rw [decodedStateValue_layerStateCircuit_eval function pairs
    resourceGateCounts resourceCircuits computes input pairSide.1 pairSide.2]
  exact congrFun (decodedValue_eq_directProduct function input) output

@[simp] theorem layerStateCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (layerStateCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost) := by
  simp [layerStateCircuit]

/-- Exact cost ledger for the complete finite layer. -/
@[simp] theorem uhligLayerCircuit_cost
    (pairs : Nat)
    (resourceGateCounts : Fin (prefixLast prefixWidth + 2) -> Nat)
    (resourceCircuits : (resource : Fin (prefixLast prefixWidth + 2)) ->
      Circuit DeMorgan.signature (pairs * suffixWidth)
        (resourceGateCounts resource) pairs) :
    (uhligLayerCircuit pairs resourceGateCounts resourceCircuits).cost
        DeMorgan.standardCost =
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin pairs =>
            (resourceRouterCircuit (suffixWidth := suffixWidth) resource).cost
              DeMorgan.standardCost) +
          (resourceCircuits resource).cost DeMorgan.standardCost)) +
      (Finset.univ.sum fun output : Fin (2 * pairs) =>
        (decoderOutputExpression (prefixWidth := prefixWidth)
          (suffixWidth := suffixWidth) output).standardCost) := by
  simp [uhligLayerCircuit]

end UhligCircuit
end MassProduction
end Algebraic
