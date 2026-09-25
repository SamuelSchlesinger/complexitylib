/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.UhligRecursiveCircuit

/-!
# Quantitative bounds for recursive Uhlig mass production

Building on the exact recursive circuit, this module bounds the resource tree
and accumulated routing/decoding overhead. Every estimate is an explicit
natural-number inequality used by the finite and asymptotic Uhlig theorems.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligRecursion

open UhligCircuit
open scoped BigOperators

/-- Number of shorter resource functions created by one Uhlig layer. -/
def resourceCount (prefixWidth : Nat) : Nat :=
  prefixLast prefixWidth + 2

theorem resourceCount_eq (prefixWidth : Nat) :
    resourceCount prefixWidth = 2 ^ prefixWidth + 1 := by
  unfold resourceCount
  have count := prefixCount_eq prefixWidth
  omega

/-- Total nonrecursive overhead accumulated by the full resource tree. -/
def recursiveOverhead
    (prefixWidth baseWidth : Nat) : Nat -> Nat
  | 0 => 0
  | depth + 1 =>
      resourceCount prefixWidth *
          recursiveOverhead prefixWidth baseWidth depth +
        sharedLayerOverheadBound prefixWidth
          (recursiveWidth prefixWidth baseWidth depth)
          (recursiveCopies depth)

/-- The overhead of one layer after factoring out its number of request
pairs.  Keeping this as an explicit natural-number expression makes the
subsequent recurrence bounds independent of asymptotic notation. -/
def layerOverheadEnvelope (prefixWidth suffixWidth : Nat) : Nat :=
  resourceCount prefixWidth *
      (suffixWidth * routedSuffixCostBound prefixWidth) +
    2 * sharedDecodedCostBound prefixWidth

theorem sharedLayerOverheadBound_eq
    (prefixWidth suffixWidth pairs : Nat) :
    sharedLayerOverheadBound prefixWidth suffixWidth pairs =
      pairs * layerOverheadEnvelope prefixWidth suffixWidth := by
  unfold sharedLayerOverheadBound layerOverheadEnvelope resourceCount
  ring

theorem layerOverheadEnvelope_mono_suffix
    (prefixWidth small large : Nat)
    (bounded : small <= large) :
    layerOverheadEnvelope prefixWidth small <=
      layerOverheadEnvelope prefixWidth large := by
  unfold layerOverheadEnvelope
  gcongr

theorem resourceCount_positive (prefixWidth : Nat) :
    0 < resourceCount prefixWidth := by
  rw [resourceCount_eq]
  positivity

theorem recursiveCopies_le_resourcePower
    (prefixWidth depth : Nat) :
    recursiveCopies depth <= resourceCount prefixWidth ^ depth := by
  rw [recursiveCopies_eq_two_pow]
  exact Nat.pow_le_pow_left (by
    rw [resourceCount_eq]
    have powerPositive := Nat.two_pow_pos prefixWidth
    omega) depth

/-- A denominator-free upper estimate for `(base + 1)^depth`.  It is the
finite inequality behind the fact that the extra one resource per layer does
not alter Uhlig's leading coefficient when `depth / base` tends to zero. -/
theorem sub_mul_succ_pow_le_pow_succ
    (base depth : Nat)
    (depthLe : depth <= base) :
    (base - depth) * (base + 1) ^ depth <= base ^ (depth + 1) := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      have priorDepthLe : depth <= base := by omega
      have coefficientBound :
          (base - (depth + 1)) * (base + 1) <=
            (base - depth) * base := by
        let remainder := base - (depth + 1)
        have baseSplit :
            base = remainder + (depth + 1) :=
          (Nat.sub_add_cancel depthLe).symm
        have priorSub :
            base - depth = remainder + 1 := by
          dsimp only [remainder]
          omega
        change remainder * (base + 1) <= (base - depth) * base
        rw [priorSub, baseSplit]
        nlinarith
      calc
        (base - (depth + 1)) * (base + 1) ^ (depth + 1) =
            ((base - (depth + 1)) * (base + 1)) *
              (base + 1) ^ depth := by
          rw [pow_succ]
          ring
        _ <= ((base - depth) * base) * (base + 1) ^ depth := by
          gcongr
        _ = base * ((base - depth) * (base + 1) ^ depth) := by ring
        _ <= base * base ^ (depth + 1) := by
          gcongr
          exact inductionHypothesis priorDepthLe
        _ = base ^ ((depth + 1) + 1) := by
          rw [pow_succ]
          ring

/-- Quantitative leading-coefficient control for the resource tree.  If the
base resource count `2^p` dominates `(precision + 1) * depth`, then the extra
resource at each layer costs at most the factor
`(precision + 1) / precision`. -/
theorem precision_mul_resourcePower_le
    (precision prefixWidth depth : Nat)
    (depthSmall : (precision + 1) * depth <= 2 ^ prefixWidth) :
    precision * resourceCount prefixWidth ^ depth <=
      (precision + 1) * (2 ^ prefixWidth) ^ depth := by
  let base := 2 ^ prefixWidth
  have basePositive : 0 < base := by
    dsimp [base]
    positivity
  have depthLeBase : depth <= base := by
    exact (Nat.le_mul_of_pos_left depth (by omega : 0 < precision + 1)).trans
      depthSmall
  have powerBound :
      (base - depth) * (base + 1) ^ depth <= base ^ (depth + 1) :=
    sub_mul_succ_pow_le_pow_succ base depth depthLeBase
  have coefficientBound :
      precision * base <= (precision + 1) * (base - depth) := by
    let remainder := base - (precision + 1) * depth
    have baseSplit :
        base = remainder + (precision + 1) * depth :=
      (Nat.sub_add_cancel depthSmall).symm
    have differenceSplit :
        base - depth = remainder + precision * depth := by
      have productSplit :
          (precision + 1) * depth = precision * depth + depth := by ring
      dsimp only [remainder]
      omega
    rw [differenceSplit, baseSplit]
    nlinarith
  apply le_of_mul_le_mul_left (a := base) _ basePositive
  calc
    base * (precision * resourceCount prefixWidth ^ depth) =
        precision * base * (base + 1) ^ depth := by
      rw [resourceCount_eq]
      dsimp [base]
      ring
    _ <= (precision + 1) * (base - depth) *
          (base + 1) ^ depth := by
      gcongr
    _ <= (precision + 1) * base ^ (depth + 1) := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_left (precision + 1) powerBound
    _ = base * ((precision + 1) * base ^ depth) := by
      rw [pow_succ]
      ring

/-- Closed finite bound for all routing and decoding accumulated through the
resource tree.  The chosen `maxWidth` may be any upper bound on the final
recursive width; in applications it is the original input width. -/
theorem recursiveOverhead_le
    (prefixWidth baseWidth depth maxWidth : Nat)
    (widthBound :
      recursiveWidth prefixWidth baseWidth depth <= maxWidth) :
    recursiveOverhead prefixWidth baseWidth depth <=
      depth * resourceCount prefixWidth ^ depth *
        layerOverheadEnvelope prefixWidth maxWidth := by
  induction depth with
  | zero => simp [recursiveOverhead]
  | succ depth inductionHypothesis =>
      have priorWidthBound :
          recursiveWidth prefixWidth baseWidth depth <= maxWidth := by
        exact (Nat.le_add_left _ _).trans widthBound
      have priorBound := inductionHypothesis priorWidthBound
      have layerBound :
          sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) <=
            resourceCount prefixWidth ^ depth *
              layerOverheadEnvelope prefixWidth maxWidth := by
        rw [sharedLayerOverheadBound_eq]
        exact Nat.mul_le_mul
          (recursiveCopies_le_resourcePower prefixWidth depth)
          (layerOverheadEnvelope_mono_suffix prefixWidth _ _ priorWidthBound)
      have resourceAtLeastOne : 1 <= resourceCount prefixWidth :=
        resourceCount_positive prefixWidth
      rw [recursiveOverhead]
      calc
        resourceCount prefixWidth *
              recursiveOverhead prefixWidth baseWidth depth +
            sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) <=
            resourceCount prefixWidth *
                (depth * resourceCount prefixWidth ^ depth *
                  layerOverheadEnvelope prefixWidth maxWidth) +
              resourceCount prefixWidth ^ depth *
                layerOverheadEnvelope prefixWidth maxWidth :=
          Nat.add_le_add (Nat.mul_le_mul_left _ priorBound) layerBound
        _ <= resourceCount prefixWidth *
                (depth * resourceCount prefixWidth ^ depth *
                  layerOverheadEnvelope prefixWidth maxWidth) +
              resourceCount prefixWidth *
                (resourceCount prefixWidth ^ depth *
                  layerOverheadEnvelope prefixWidth maxWidth) := by
          exact Nat.add_le_add_left
            (Nat.le_mul_of_pos_left _ (resourceCount_positive prefixWidth)) _
        _ = (depth + 1) * resourceCount prefixWidth ^ (depth + 1) *
              layerOverheadEnvelope prefixWidth maxWidth := by
          rw [pow_succ]
          ring

/-- Finite quantitative Uhlig recurrence.  A uniform scalar base bound `B`
lifts to `(2^p + 1)^d * B` plus the fully explicit routing/decoding
overhead. -/
theorem recursiveCircuit_cost_le
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (depth : Nat)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).cost
        DeMorgan.standardCost <=
      resourceCount prefixWidth ^ depth * baseBound +
        recursiveOverhead prefixWidth baseWidth depth := by
  induction depth with
  | zero =>
      rw [recursiveCircuit_cost_zero]
      simpa [recursiveOverhead] using baseCost function
  | succ depth inductionHypothesis =>
      let resourceCircuits :=
        fun resource : Fin (prefixLast prefixWidth + 2) =>
          recursiveCircuit prefixWidth baseWidth base depth
            (resourceFunction function resource)
      change
        (sharedUhligLayerCircuit (recursiveCopies depth)
          resourceCircuits).cost
            DeMorgan.standardCost <= _
      calc
        (sharedUhligLayerCircuit (recursiveCopies depth)
            resourceCircuits).cost
              DeMorgan.standardCost <=
            (Finset.univ.sum fun resource :
                Fin (prefixLast prefixWidth + 2) =>
              (resourceCircuits resource).cost DeMorgan.standardCost) +
            sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) :=
          sharedUhligLayerCircuit_cost_le_resource_sum_add_overhead
            (prefixWidth := prefixWidth)
            (suffixWidth := recursiveWidth prefixWidth baseWidth depth)
            (pairs := recursiveCopies depth)
            (resourceCircuits := resourceCircuits)
        _ <=
            (Finset.univ.sum fun _resource :
                Fin (prefixLast prefixWidth + 2) =>
              resourceCount prefixWidth ^ depth * baseBound +
                recursiveOverhead prefixWidth baseWidth depth) +
            sharedLayerOverheadBound prefixWidth
              (recursiveWidth prefixWidth baseWidth depth)
              (recursiveCopies depth) := by
          gcongr with resource
          exact inductionHypothesis (resourceFunction function resource)
        _ = resourceCount prefixWidth ^ (depth + 1) * baseBound +
              recursiveOverhead prefixWidth baseWidth (depth + 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.nsmul_eq_mul, recursiveOverhead]
          rw [pow_succ]
          unfold resourceCount
          ring_nf

/-- The recursive cost recurrence with the accumulated overhead replaced by
its closed envelope bound. -/
theorem recursiveCircuit_cost_le_closed
    (prefixWidth baseWidth : Nat)
    (base : ScalarSynthesis baseWidth)
    (baseBound : Nat)
    (baseCost : forall function,
      (base.circuit function).cost DeMorgan.standardCost <= baseBound)
    (depth maxWidth : Nat)
    (widthBound :
      recursiveWidth prefixWidth baseWidth depth <= maxWidth)
    (function : ScalarFunction Bool
      (recursiveWidth prefixWidth baseWidth depth)) :
    (recursiveCircuit prefixWidth baseWidth base depth function).cost
        DeMorgan.standardCost <=
      resourceCount prefixWidth ^ depth *
        (baseBound + depth *
          layerOverheadEnvelope prefixWidth maxWidth) := by
  have recurrence := recursiveCircuit_cost_le prefixWidth baseWidth base
    baseBound baseCost depth function
  have overhead := recursiveOverhead_le prefixWidth baseWidth depth maxWidth
    widthBound
  calc
    (recursiveCircuit prefixWidth baseWidth base depth function).cost
        DeMorgan.standardCost <=
      resourceCount prefixWidth ^ depth * baseBound +
        recursiveOverhead prefixWidth baseWidth depth := recurrence
    _ <= resourceCount prefixWidth ^ depth * baseBound +
        depth * resourceCount prefixWidth ^ depth *
          layerOverheadEnvelope prefixWidth maxWidth := by gcongr
    _ = resourceCount prefixWidth ^ depth *
        (baseBound + depth *
          layerOverheadEnvelope prefixWidth maxWidth) := by ring

end UhligRecursion
end MassProduction
end Algebraic
