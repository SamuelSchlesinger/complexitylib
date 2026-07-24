/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlotQuery.Defs
import Complexitylib.Circuits.BarringtonSlotQuery.Internal

/-!
# Direct queries into fixed-address Barrington slots

`barringtonCompileSlot?` locates one instruction in the depth-bounded fixed
schedule without constructing the complete recursive list. Its structural
first- and last-occupied-address recurrences are independent of the target
permutation, so they are suitable for a finite-state machine controller.

## Main results

- `barringtonFirstOccupiedSlot?_eq` -- the structural first address is exact.
- `barringtonLastOccupiedSlot?_eq` -- the structural last address is exact.
- `barringtonCompileSlotsNonempty_eq` -- the small nonemptiness recurrence is
  exact.
- `barringtonCompileSlotOccupied_eq` -- the target-free Boolean slot query is
  exact.
- `barringtonCompileSlot?_eq_instruction?` -- every direct query agrees with
  the list-valued fixed-slot compiler.
- `BPInstrTransform.apply_invertOutput` and `apply_postMulOutput` -- the finite
  pending-transform state realizes the two instruction wrappers used during
  recursive descent.
- `BarringtonSlotCursor.localSlot_succ` and `localSlot_descend` -- the current
  base-four digit selects one of four child blocks, while inverse blocks are
  tracked by one reflection bit and the original numeric slot remains fixed.
- `BarringtonSlotCursor.selectsRight_eq_rawLowBit` and
  `selectsInverse_eq_rawHighBit` -- those two finite branch decisions are the
  corresponding binary address bits, xor the reflection flag.
-/

namespace Complexity

/-- The identity finite-control transformation leaves an instruction fixed. -/
@[simp] theorem BPInstrTransform.apply_identity (instruction : BPInstr 5) :
    BPInstrTransform.identity.apply instruction = instruction :=
  BPInstrTransform.apply_identity_internal instruction

/-- Updating finite control for an inverse block is exactly instruction
inversion after the previously accumulated transformation. -/
@[simp] theorem BPInstrTransform.apply_invertOutput
    (transform : BPInstrTransform) (instruction : BPInstr 5) :
    transform.invertOutput.apply instruction =
      (transform.apply instruction).inverse :=
  BPInstrTransform.apply_invertOutput_internal transform instruction

/-- Updating finite control at the last occupied slot is exactly
postmultiplication after the previously accumulated transformation. -/
@[simp] theorem BPInstrTransform.apply_postMulOutput
    (transform : BPInstrTransform) (instruction : BPInstr 5)
    (permutation : Equiv.Perm (Fin 5)) :
    (transform.postMulOutput permutation).apply instruction =
      (transform.apply instruction).postMul permutation :=
  BPInstrTransform.apply_postMulOutput_internal transform instruction
    permutation

/-- Pending permutation transformations never change the queried variable. -/
@[simp] theorem BPInstrTransform.apply_var
    (transform : BPInstrTransform) (instruction : BPInstr 5) :
    (transform.apply instruction).var = instruction.var :=
  BPInstrTransform.apply_var_internal transform instruction

/-- Every raw base-four address digit lies in its four-element alphabet. -/
theorem BarringtonSlotCursor.rawDigit_lt
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.rawDigit fuel < 4 :=
  BarringtonSlotCursor.rawDigit_lt_internal cursor fuel

/-- Reflection preserves the four-element range of the current digit. -/
theorem BarringtonSlotCursor.digit_lt
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.digit fuel < 4 :=
  BarringtonSlotCursor.digit_lt_internal cursor fuel

/-- The low bit of the current base-four digit is the binary slot bit at
position `2 * fuel`. -/
theorem BarringtonSlotCursor.rawLowBit_eq_testBit
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.rawLowBit fuel = (cursor.rawDigit fuel).testBit 0 :=
  BarringtonSlotCursor.rawLowBit_eq_testBit_internal cursor fuel

/-- The high bit of the current base-four digit is the binary slot bit at
position `2 * fuel + 1`. -/
theorem BarringtonSlotCursor.rawHighBit_eq_testBit
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.rawHighBit fuel = (cursor.rawDigit fuel).testBit 1 :=
  BarringtonSlotCursor.rawHighBit_eq_testBit_internal cursor fuel

/-- Right-child selection needs only the low raw address bit and the finite
reflection flag. -/
theorem BarringtonSlotCursor.selectsRight_eq_rawLowBit
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.selectsRight fuel =
      (cursor.rawLowBit fuel != cursor.reversed) :=
  BarringtonSlotCursor.selectsRight_eq_rawLowBit_internal cursor fuel

/-- Inverse-block selection needs only the high raw address bit and the finite
reflection flag. -/
theorem BarringtonSlotCursor.selectsInverse_eq_rawHighBit
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.selectsInverse fuel =
      (cursor.rawHighBit fuel != cursor.reversed) :=
  BarringtonSlotCursor.selectsInverse_eq_rawHighBit_internal cursor fuel

/-- After descending, the next reflection flag is exactly the raw high bit of
the block just selected; no reflection stack is required. -/
theorem BarringtonSlotCursor.descend_reversed
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    (cursor.descend fuel).reversed = cursor.rawHighBit fuel :=
  BarringtonSlotCursor.descend_reversed_internal cursor fuel

/-- The represented local address always fits in the remaining base-four
block. -/
theorem BarringtonSlotCursor.localSlot_lt
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.localSlot fuel < 4 ^ fuel :=
  BarringtonSlotCursor.localSlot_lt_internal cursor fuel

/-- The effective address splits exactly into its current base-four block and
the remaining local address. -/
theorem BarringtonSlotCursor.localSlot_succ
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    cursor.localSlot (fuel + 1) =
      cursor.digit fuel * 4 ^ fuel + cursor.localSlot fuel :=
  BarringtonSlotCursor.localSlot_succ_internal cursor fuel

/-- Descending preserves the original stored address and toggles reflection
exactly when the selected child block is inverse. -/
theorem BarringtonSlotCursor.localSlot_descend
    (cursor : BarringtonSlotCursor) (fuel : ℕ) :
    (cursor.descend fuel).localSlot fuel =
      if cursor.selectsInverse fuel then
        4 ^ fuel - 1 - cursor.localSlot fuel
      else
        cursor.localSlot fuel :=
  BarringtonSlotCursor.localSlot_descend_internal cursor fuel

/-- The structural first-address recurrence finds the first occupied slot of
the list-valued fixed schedule. -/
theorem barringtonFirstOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonFirstOccupiedSlot? fuel formula =
      BPSlots.firstOccupiedSlot?
        (barringtonCompileSlots fuel formula target) :=
  (barringtonOccupiedSlots_correct_internal fuel formula target).1

/-- The structural last-address recurrence finds the last occupied slot of
the list-valued fixed schedule. -/
theorem barringtonLastOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonLastOccupiedSlot? fuel formula =
      BPSlots.lastOccupiedSlot?
        (barringtonCompileSlots fuel formula target) :=
  (barringtonOccupiedSlots_correct_internal fuel formula target).2

/-- The target-independent nonemptiness recurrence agrees with either
structural extreme-address query. -/
theorem barringtonCompileSlotsNonempty_eq (fuel : ℕ)
    (formula : BoolFormula) :
    barringtonCompileSlotsNonempty fuel formula =
        (barringtonFirstOccupiedSlot? fuel formula).isSome ∧
      barringtonCompileSlotsNonempty fuel formula =
        (barringtonLastOccupiedSlot? fuel formula).isSome :=
  barringtonCompileSlotsNonempty_correct_internal fuel formula

/-- The target-free Boolean occupancy query agrees with the instruction query
at every fixed address. -/
theorem barringtonCompileSlotOccupied_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileSlotOccupied fuel formula slot =
      (BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot).isSome := by
  rw [barringtonCompileSlotOccupied_correct_internal]
  rw [barringtonCompileSlot?_correct_internal]

/-- Every direct fixed-address query agrees with the corresponding query into
the list-valued fixed schedule. -/
theorem barringtonCompileSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileSlot? fuel formula target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot :=
  barringtonCompileSlot?_correct_internal fuel formula target slot

end Complexity
