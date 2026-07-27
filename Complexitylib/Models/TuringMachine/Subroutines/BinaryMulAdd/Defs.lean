/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd.Defs

/-!
# Canonical binary multiply-add — definitions

This module defines multiply-add by nesting the canonical binary addition
routine inside a canonical binary count-up loop. Five pairwise-distinct work
tapes hold a preserved left operand, a preserved right operand, an updated
accumulator, an outer multiplication counter, and the addition routine's
private counter. Both counters are restored to canonical zero.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- The five work-tape roles of binary multiply-add are pairwise distinct. -/
structure BinaryMulAddDistinct {n : ℕ}
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) : Prop where
  left_ne_right : leftIdx ≠ rightIdx
  left_ne_acc : leftIdx ≠ accIdx
  left_ne_mulCounter : leftIdx ≠ mulCounterIdx
  left_ne_addCounter : leftIdx ≠ addCounterIdx
  right_ne_acc : rightIdx ≠ accIdx
  right_ne_mulCounter : rightIdx ≠ mulCounterIdx
  right_ne_addCounter : rightIdx ≠ addCounterIdx
  acc_ne_mulCounter : accIdx ≠ mulCounterIdx
  acc_ne_addCounter : accIdx ≠ addCounterIdx
  mulCounter_ne_addCounter : mulCounterIdx ≠ addCounterIdx

/-- Repeatedly add `leftIdx` into `accIdx`, once per value below `rightIdx`.
The addition counter is restored by every body invocation; the multiplication
counter equals the right operand when this loop halts. -/
def binaryMulAddLoopTM {n : ℕ}
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) : TM n :=
  binaryForTM (binaryAddIntoTM leftIdx accIdx addCounterIdx)
    mulCounterIdx rightIdx

/-- Add the product of two preserved canonical binary operands into an
accumulator, then restore the outer multiplication counter to zero. -/
def binaryMulAddIntoTM {n : ℕ}
    (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) : TM n :=
  seqTM
    (binaryMulAddLoopTM leftIdx rightIdx accIdx mulCounterIdx addCounterIdx)
    (clearWorkTM mulCounterIdx)

/-- Public upper bound for the nested repeated-addition loop. -/
def binaryMulAddLoopTime (leftValue rightValue accValue : ℕ) : ℕ :=
  binaryForLoopTime
    (fun current => binaryAddTime leftValue (accValue + leftValue * current))
    rightValue 0 rightValue

/-- Public time bound for multiply-add, including the composition seam and
restoration of the outer counter. -/
def binaryMulAddTime (leftValue rightValue accValue : ℕ) : ℕ :=
  binaryMulAddLoopTime leftValue rightValue accValue + 1 +
    clearWorkTimeBound rightValue.size

/-- All-prefix space bound for the repeated-addition loop. The bound uses
only binary widths: the largest accumulator value, the left operand, and the
right operand. -/
def binaryMulAddLoopSpace
    (initialSpace leftValue rightValue accValue : ℕ) : ℕ :=
  binaryAddSpace initialSpace leftValue
      (accValue + leftValue * rightValue) +
    2 * rightValue.size + 2

/-- All-prefix space bound for multiply-add followed by counter restoration. -/
def binaryMulAddSpace
    (initialSpace leftValue rightValue accValue : ℕ) : ℕ :=
  binaryMulAddLoopSpace initialSpace leftValue rightValue accValue +
    clearWorkTimeBound rightValue.size

end TM

end Complexity
