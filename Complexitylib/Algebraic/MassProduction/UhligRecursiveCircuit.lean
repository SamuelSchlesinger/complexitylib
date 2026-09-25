/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ScalarSynthesis
public import Complexitylib.Algebraic.MassProduction.UhligCircuit

/-!
# Recursive Uhlig circuit

This module iterates the exact finite two-copy layer. Scalar synthesis data is
passed explicitly, so the construction introduces no instance-search burden.
It proves semantic correctness and exact cost identities for the recursion.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligRecursion

open UhligCircuit
open scoped BigOperators

/-- Width left after `depth` equal prefix blocks have been restored. -/
@[reducible] def recursiveWidth
    (prefixWidth baseWidth : Nat) : Nat -> Nat
  | 0 => baseWidth
  | depth + 1 => prefixWidth + recursiveWidth prefixWidth baseWidth depth

/-- Number of copies after `depth` two-copy layers. -/
@[reducible] def recursiveCopies : Nat -> Nat
  | 0 => 1
  | depth + 1 => 2 * recursiveCopies depth

theorem recursiveCopies_eq_two_pow (depth : Nat) :
    recursiveCopies depth = 2 ^ depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [recursiveCopies, inductionHypothesis, pow_succ, Nat.mul_comm]

theorem recursiveWidth_eq (prefixWidth baseWidth depth : Nat) :
    recursiveWidth prefixWidth baseWidth depth =
      depth * prefixWidth + baseWidth := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      simp [recursiveWidth, inductionHypothesis, Nat.succ_mul,
        Nat.add_left_comm, Nat.add_comm]

/-- Gate count determined by the chosen base synthesis and every explicit
routing/decoding layer above it. -/
noncomputable def recursiveGateCount
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth) :
    (depth : Nat) ->
      ScalarFunction Bool (recursiveWidth prefixWidth baseWidth depth) -> Nat
  | 0, function => 1 * base.gateCount function
  | depth + 1, function =>
      let suffixWidth := recursiveWidth prefixWidth baseWidth depth
      let pairs := recursiveCopies depth
      let resourceGateCounts :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveGateCount prefixWidth baseWidth base depth
            (resourceFunction function resource)
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
          routedResourceGateCount prefixWidth suffixWidth pairs
            resourceGateCounts resource) +
        (Finset.univ.sum fun output : Fin (2 * pairs) =>
          sharedDecoderOutputGateCount
            prefixWidth suffixWidth pairs output)

/-- The recursive circuit obtained by using the supplied synthesis at the
base and one exact Uhlig layer per recursive step. -/
noncomputable def recursiveCircuit
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth) :
    (depth : Nat) ->
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) ->
    Circuit DeMorgan.signature
      (recursiveCopies depth *
        recursiveWidth prefixWidth baseWidth depth)
      (recursiveCopies depth)
  | 0, function => (base.circuit function).replicateScalar 1
  | depth + 1, function =>
      let pairs := recursiveCopies depth
      let resourceCircuits :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource)
      sharedUhligLayerCircuit pairs resourceCircuits

/-- The recursive circuit emits exactly `recursiveGateCount` gates. -/
@[simp] theorem recursiveCircuit_size
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).size =
      recursiveGateCount prefixWidth baseWidth base depth function := by
  induction depth with
  | zero => simp [recursiveCircuit, recursiveGateCount]
  | succ depth inductionHypothesis =>
      simp [recursiveCircuit, recursiveGateCount, inductionHypothesis]

/-- Iterating the finite layer computes exactly `2 ^ depth` independent
copies of the original function. -/
theorem recursiveCircuit_computes
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).ComputesWith
      DeMorgan.interpretation
      (directProduct function (recursiveCopies depth)) := by
  induction depth with
  | zero =>
      have outputFunction :
          (base.circuit function).outputFunction
              DeMorgan.interpretation 0 = function :=
        Circuit.outputFunction_eq_of_computes_scalarTarget
          (base.computes function)
      exact Circuit.replicateScalar_computes_directProduct outputFunction 1
  | succ depth inductionHypothesis =>
      exact sharedUhligLayerCircuit_computes function (recursiveCopies depth)
        (fun resource =>
          recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource))
        (fun resource => inductionHypothesis
          (resourceFunction function resource))

@[simp] theorem recursiveCircuit_cost_zero
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (function : ScalarFunction Bool baseWidth) :
    (recursiveCircuit prefixWidth baseWidth base 0 function).cost
        DeMorgan.standardCost =
      (base.circuit function).cost DeMorgan.standardCost := by
  change ((base.circuit function).replicateScalar 1).cost
      DeMorgan.standardCost =
    (base.circuit function).cost DeMorgan.standardCost
  have costIdentity := Circuit.cost_replicateScalar
    (base.circuit function) 1 DeMorgan.standardCost
  simpa only [Nat.one_mul] using costIdentity

/-- Exact recursive cost identity.  The first summand at each resource is
explicit routing overhead, and the second is the recursively shared resource
computation. -/
@[simp] theorem recursiveCircuit_cost_succ
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth (depth + 1))) :
    (recursiveCircuit prefixWidth baseWidth base (depth + 1) function).cost
        DeMorgan.standardCost =
      (Finset.univ.sum fun resource : Fin (prefixLast prefixWidth + 2) =>
        ((Finset.univ.sum fun _pair : Fin (recursiveCopies depth) =>
            (resourceRouterCircuit
              (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
              resource).cost DeMorgan.standardCost) +
          (recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource)).cost
              DeMorgan.standardCost)) +
      (Finset.univ.sum fun output : Fin (2 * recursiveCopies depth) =>
        let pairSide := decoderPairSide output
        (sharedDecodedCircuit (prefixWidth := prefixWidth)
          (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
          pairSide.1 pairSide.2).cost DeMorgan.standardCost) := by
  change
    (sharedUhligLayerCircuit (recursiveCopies depth)
      (fun resource =>
        recursiveCircuit prefixWidth baseWidth base depth
          (resourceFunction function resource))).cost
        DeMorgan.standardCost = _
  have costIdentity := sharedUhligLayerCircuit_cost
    (prefixWidth := prefixWidth)
    (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
    (pairs := recursiveCopies depth)
    (resourceCircuits := fun resource =>
      recursiveCircuit prefixWidth baseWidth base depth
        (resourceFunction function resource))
  exact costIdentity

end UhligRecursion
end MassProduction
end Algebraic
