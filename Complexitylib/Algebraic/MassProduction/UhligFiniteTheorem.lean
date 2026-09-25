/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.UhligParameters

/-!
# Finite Uhlig theorem and sharpness predicates

This module packages the exact finite recursive construction used by Uhlig's
theorem. It also states the denominator-free one-copy and mass-production
sharpness predicates that form the asymptotic theorem's public interface.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligTheorem

open Filter
open UhligRecursion

/-! ## Finite end-to-end theorem -/

/-- Exact finite Uhlig construction for every positive sub-batch of the
power-of-two batch produced by the recursion. -/
theorem exists_finite_uhlig_circuit
    (prefixWidth baseWidth depth : Nat)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth))
    (copies : Nat)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <= 2 ^ depth) :
    exists gates,
      exists circuit : Circuit DeMorgan.signature
          (copies * recursiveWidth prefixWidth baseWidth depth) gates copies,
        circuit.ComputesWith DeMorgan.interpretation
            (directProduct function copies) /\
          circuit.cost DeMorgan.standardCost <=
            resourceCount prefixWidth ^ depth *
              (baseBound + depth *
                layerOverheadEnvelope prefixWidth
                  (recursiveWidth prefixWidth baseWidth depth)) := by
  let fullCircuit := recursiveCircuit prefixWidth baseWidth base depth function
  have copiesLeFull : copies <= recursiveCopies depth := by
    rw [recursiveCopies_eq_two_pow]
    exact copiesBound
  let circuit := fullCircuit.takeDirectProductPrefix
    copies copiesPositive copiesLeFull
  refine ⟨_, circuit, ?_, ?_⟩
  · exact Circuit.takeDirectProductPrefix_computes fullCircuit function
      (recursiveCircuit_computes prefixWidth baseWidth base depth function)
      copiesPositive copiesLeFull
  · simpa [circuit] using
      recursiveCircuit_cost_le_closed prefixWidth baseWidth base baseBound
        baseCost depth (recursiveWidth prefixWidth baseWidth depth) le_rfl
        function

/-- Width-transported form of the finite construction. -/
theorem exists_finite_uhlig_circuit_at_width
    (prefixWidth baseWidth depth inputs : Nat)
    (widthIdentity :
      recursiveWidth prefixWidth baseWidth depth = inputs)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (function : ScalarFunction Bool inputs)
    (copies : Nat)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <= 2 ^ depth) :
    exists gates,
      exists circuit : Circuit DeMorgan.signature
          (copies * inputs) gates copies,
        circuit.ComputesWith DeMorgan.interpretation
            (directProduct function copies) /\
          circuit.cost DeMorgan.standardCost <=
            resourceCount prefixWidth ^ depth *
              (baseBound + depth *
                layerOverheadEnvelope prefixWidth inputs) := by
  subst inputs
  exact exists_finite_uhlig_circuit prefixWidth baseWidth depth base
    baseBound baseCost function copies copiesPositive copiesBound

/-- Denominator-free formulation of a sharp one-copy upper bound.  For every
positive integer precision `q`, the normalized coefficient is eventually at
most `(q + 1) / q`. -/
def HasSharpOneCopyCost (family : ScalarSynthesisFamily) : Prop :=
  forall precision : Nat, 0 < precision ->
    exists cutoff : Nat,
      forall width : Nat, cutoff <= width ->
        forall function : ScalarFunction Bool width,
          precision *
                (((family width).circuit function).cost
                  DeMorgan.standardCost) *
              width <=
            (precision + 1) * 2 ^ width

/-- Uniform integral bound extracted from one normalized sharp estimate. -/
def normalizedBaseBound (precision width : Nat) : Nat :=
  ((precision + 1) * 2 ^ width) / (precision * width)

theorem normalizedBaseBound_spec
    (precision width : Nat) :
    precision * normalizedBaseBound precision width * width <=
      (precision + 1) * 2 ^ width := by
  unfold normalizedBaseBound
  have divisionBound := Nat.mul_div_le
    ((precision + 1) * 2 ^ width) (precision * width)
  calc
    precision *
          (((precision + 1) * 2 ^ width) / (precision * width)) * width =
        (precision * width) *
          (((precision + 1) * 2 ^ width) / (precision * width)) := by ring
    _ <= (precision + 1) * 2 ^ width := divisionBound

theorem circuit_cost_le_normalizedBaseBound
    (family : ScalarSynthesisFamily)
    (precision width : Nat)
    (precisionPositive : 0 < precision)
    (widthPositive : 0 < width)
    (function : ScalarFunction Bool width)
    (sharpBound :
      precision *
            (((family width).circuit function).cost
              DeMorgan.standardCost) * width <=
        (precision + 1) * 2 ^ width) :
    ((family width).circuit function).cost DeMorgan.standardCost <=
      normalizedBaseBound precision width := by
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos precisionPositive widthPositive)).2
  simpa only [normalizedBaseBound, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using sharpBound

/-- Exact discrete reading of `depth(n) = o(n / log n)`.  Quantifying over
every fixed positive multiplier avoids division and real-valued side
conditions. -/
def IsUhligDepth (depth : Nat -> Nat) : Prop :=
  forall multiplier : Nat, 0 < multiplier ->
    Filter.Eventually
      (fun inputs =>
        multiplier * depth inputs * Nat.log 2 inputs <= inputs)
      atTop

/-- Sharp mass production through the copy budget `2 ^ depth(n)`, stated
directly for minimum De Morgan cost. -/
def HasSharpMassProduction (depth : Nat -> Nat) : Prop :=
  forall precision : Nat, 0 < precision ->
    Filter.Eventually
      (fun inputs =>
        forall (function : ScalarFunction Bool inputs) (copies : Nat),
          0 < copies -> copies <= 2 ^ depth inputs ->
            (precision * inputs : ENat) *
                booleanMassComplexity function copies <=
              ((precision + 1) * 2 ^ inputs : Nat))
      atTop

end UhligTheorem
end MassProduction
end Algebraic
