/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlots.Defs

/-!
# Direct queries into fixed-address Barrington slots -- definitions

The list-valued fixed-slot compiler is the extensional reference for uniform
generation, but a log-space controller must locate one slot without building
the full list. This file gives structural first/last occupied-slot recurrences
and a direct indexed query. Every recursive query descends under a strictly
smaller fuel bound; inverse blocks reverse the local address, while `postMul`
uses the structural last occupied address.
-/

namespace Complexity

namespace BPSlots

/-- Occupied instruction at a zero-based fixed-slot address. -/
def instruction? (slots : BPSlots w) (slot : ℕ) : Option (BPInstr w) :=
  slots[slot]?.join

/-- First occupied fixed-slot address, if one exists. -/
def firstOccupiedSlot? : BPSlots w → Option ℕ
  | [] => none
  | none :: slots => (firstOccupiedSlot? slots).map Nat.succ
  | some _ :: _ => some 0

/-- Last occupied fixed-slot address, if one exists. -/
def lastOccupiedSlot? : BPSlots w → Option ℕ
  | [] => none
  | slot :: slots =>
      match lastOccupiedSlot? slots with
      | some last => some (last + 1)
      | none => if slot.isSome then some 0 else none

end BPSlots

/-- Finite-control transformation accumulated while a direct Barrington query
descends through inverse blocks and postmultiplication wrappers.

Both branches of an instruction undergo the same map
`p ↦ left * p^(±1) * right`; the variable index is unchanged. Since every
field is finite at width five, the complete transformation can live in a
Turing machine's finite state. -/
structure BPInstrTransform where
  /-- Whether to invert the selected permutation before multiplying. -/
  inverted : Bool
  /-- Fixed permutation multiplied on the left. -/
  left : Equiv.Perm (Fin 5)
  /-- Fixed permutation multiplied on the right. -/
  right : Equiv.Perm (Fin 5)
  deriving DecidableEq

instance : Fintype BPInstrTransform :=
  Fintype.ofEquiv
    (Bool × Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))
    { toFun := fun data =>
        { inverted := data.1, left := data.2.1, right := data.2.2 }
      invFun := fun transform =>
        (transform.inverted, transform.left, transform.right)
      left_inv := fun data => by cases data; rfl
      right_inv := fun transform => by cases transform; rfl }

/-- Apply a pending finite-control transformation to one permutation. -/
def BPInstrTransform.applyPerm (transform : BPInstrTransform)
    (permutation : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 5) :=
  transform.left *
    (if transform.inverted then permutation⁻¹ else permutation) *
    transform.right

/-- Apply a pending finite-control transformation to both instruction
branches while preserving its variable index. -/
def BPInstrTransform.apply (transform : BPInstrTransform)
    (instruction : BPInstr 5) : BPInstr 5 :=
  { instruction with
    perm0 := transform.applyPerm instruction.perm0
    perm1 := transform.applyPerm instruction.perm1 }

/-- Identity pending transformation. -/
def BPInstrTransform.identity : BPInstrTransform :=
  { inverted := false, left := 1, right := 1 }

/-- Update a pending transformation when the enclosing block inverts the
instruction selected below it. -/
def BPInstrTransform.invertOutput (transform : BPInstrTransform) :
    BPInstrTransform :=
  { inverted := !transform.inverted
    left := transform.right⁻¹
    right := transform.left⁻¹ }

/-- Update a pending transformation when the selected instruction is the last
occupied slot of a postmultiplication wrapper. -/
def BPInstrTransform.postMulOutput (transform : BPInstrTransform)
    (permutation : Equiv.Perm (Fin 5)) : BPInstrTransform :=
  { transform with right := transform.right * permutation }

/-- Stack-free address state for direct Barrington descent. The original slot
stays fixed; `reversed` records whether the remaining low base-four digits are
read in reverse order because the path entered an inverse block. -/
structure BarringtonSlotCursor where
  /-- Original fixed-schedule slot address. -/
  slot : ℕ
  /-- Whether the remaining local address is reflected. -/
  reversed : Bool
  deriving DecidableEq

/-- Raw base-four digit at the boundary between `fuel` lower digits and the
current digit. -/
def BarringtonSlotCursor.rawDigit (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : ℕ :=
  cursor.slot / 4 ^ fuel % 4

/-- Low bit of the current raw base-four digit, read directly from the binary
slot address. -/
def BarringtonSlotCursor.rawLowBit (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : Bool :=
  cursor.slot.testBit (2 * fuel)

/-- High bit of the current raw base-four digit, read directly from the binary
slot address. -/
def BarringtonSlotCursor.rawHighBit (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : Bool :=
  cursor.slot.testBit (2 * fuel + 1)

/-- Effective current base-four digit after accounting for a pending address
reflection. -/
def BarringtonSlotCursor.digit (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : ℕ :=
  if cursor.reversed then 3 - cursor.rawDigit fuel else cursor.rawDigit fuel

/-- Whether the current block selects the right child. Digits zero and two
select the left child; digits one and three select the right child. -/
def BarringtonSlotCursor.selectsRight (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : Bool :=
  cursor.digit fuel % 2 == 1

/-- Whether the selected child block is inverted. -/
def BarringtonSlotCursor.selectsInverse (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : Bool :=
  decide (2 ≤ cursor.digit fuel)

/-- Descend one base-four level without modifying the stored address. Entering
an inverse block toggles the reflection flag. -/
def BarringtonSlotCursor.descend (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : BarringtonSlotCursor :=
  { slot := cursor.slot
    reversed := cursor.reversed != cursor.selectsInverse fuel }

/-- Effective local address represented by the lowest `fuel` base-four digits. -/
def BarringtonSlotCursor.localSlot (cursor : BarringtonSlotCursor)
    (fuel : ℕ) : ℕ :=
  let blockSize := 4 ^ fuel
  let raw := cursor.slot % blockSize
  if cursor.reversed then blockSize - 1 - raw else raw

/-- Apply fixed-schedule `postMul` to one direct slot query. A missing last
occupied address means the underlying schedule is empty, so the wrapper places
its constant instruction in slot zero. -/
def barringtonPostMulSlot? (query : ℕ → Option (BPInstr 5))
    (lastOccupied : Option ℕ) (permutation : Equiv.Perm (Fin 5))
    (slot : ℕ) : Option (BPInstr 5) :=
  match lastOccupied with
  | none => if slot = 0 then some (BPInstr.const permutation) else none
  | some last =>
      (query slot).map fun instruction =>
        if slot = last then instruction.postMul permutation else instruction

/-- Query an inverse block of fixed size without constructing it. -/
def barringtonInverseSlot? (blockSize : ℕ)
    (query : ℕ → Option (BPInstr 5)) (slot : ℕ) :
    Option (BPInstr 5) :=
  if slot < blockSize then
    (query (blockSize - 1 - slot)).map BPInstr.inverse
  else
    none

/-- First occupied slot of the fixed-address compilation, if any. Occupancy is
independent of the target permutation. -/
def barringtonFirstOccupiedSlot? : ℕ → BoolFormula → Option ℕ
  | _, .var _ | _, .tru => some 0
  | _, .fls => none
  | 0, .neg _ | 0, .conj _ _ | 0, .disj _ _ => none
  | fuel + 1, .neg formula =>
      some ((barringtonFirstOccupiedSlot? fuel formula).getD 0)
  | fuel + 1, .conj left right =>
      match barringtonFirstOccupiedSlot? fuel left with
      | some slot => some slot
      | none =>
          (barringtonFirstOccupiedSlot? fuel right).map
            (4 ^ fuel + ·)
  | fuel + 1, .disj left _ =>
      some ((barringtonFirstOccupiedSlot? fuel left).getD 0)

/-- Last occupied slot of the fixed-address compilation, if any. Inverse
blocks turn a child's first occupied address into the block's last one. -/
def barringtonLastOccupiedSlot? : ℕ → BoolFormula → Option ℕ
  | _, .var _ | _, .tru => some 0
  | _, .fls => none
  | 0, .neg _ | 0, .conj _ _ | 0, .disj _ _ => none
  | fuel + 1, .neg formula =>
      some ((barringtonLastOccupiedSlot? fuel formula).getD 0)
  | fuel + 1, .conj left right =>
      let blockSize := 4 ^ fuel
      match barringtonFirstOccupiedSlot? fuel right with
      | some slot => some (3 * blockSize + (blockSize - 1 - slot))
      | none =>
          (barringtonFirstOccupiedSlot? fuel left).map fun slot =>
            2 * blockSize + (blockSize - 1 - slot)
  | fuel + 1, .disj _ right =>
      let blockSize := 4 ^ fuel
      let firstRight :=
        (barringtonFirstOccupiedSlot? fuel right).getD 0
      some (3 * blockSize + (blockSize - 1 - firstRight))

/-- Whether the fixed-address compilation has any occupied slot. This
target-independent recurrence is smaller than computing either extreme
address: negation and disjunction are automatically nonempty after their
postmultiplications, while conjunction is nonempty exactly when one child is. -/
def barringtonCompileSlotsNonempty : ℕ → BoolFormula → Bool
  | _, .var _ | _, .tru => true
  | _, .fls => false
  | 0, .neg _ | 0, .conj _ _ | 0, .disj _ _ => false
  | _ + 1, .neg _ | _ + 1, .disj _ _ => true
  | fuel + 1, .conj left right =>
      barringtonCompileSlotsNonempty fuel left ||
        barringtonCompileSlotsNonempty fuel right

/-- Occupancy after a fixed-schedule postmultiplication. An empty source gains
a constant instruction at address zero; a nonempty source retains exactly its
occupied addresses. -/
def barringtonPostMulSlotOccupied (nonempty : Bool)
    (occupied : ℕ → Bool) (slot : ℕ) : Bool :=
  if nonempty then occupied slot else slot == 0

/-- Occupancy of a reversed fixed-size block. Instruction inversion does not
affect occupancy. -/
def barringtonInverseSlotOccupied (blockSize : ℕ)
    (occupied : ℕ → Bool) (slot : ℕ) : Bool :=
  if slot < blockSize then occupied (blockSize - 1 - slot) else false

/-- First true address below a fixed bound, queried without materializing the
Boolean list. Recursive calls shift the query so the result remains local. -/
def firstTrueSlot? : ℕ → (ℕ → Bool) → Option ℕ
  | 0, _ => none
  | bound + 1, occupied =>
      if occupied 0 then some 0
      else (firstTrueSlot? bound fun slot => occupied (slot + 1)).map Nat.succ

/-- Last true address below a fixed bound, queried without materializing the
Boolean list. -/
def lastTrueSlot? : ℕ → (ℕ → Bool) → Option ℕ
  | 0, _ => none
  | bound + 1, occupied =>
      match lastTrueSlot? bound fun slot => occupied (slot + 1) with
      | some slot => some (slot + 1)
      | none => if occupied 0 then some 0 else none

/-- Query only whether one fixed Barrington address is occupied. Unlike the
instruction query below, this recurrence carries no permutation and performs
no first/last-address query. It is therefore the small Boolean kernel used by
the eventual scanning controller. -/
def barringtonCompileSlotOccupied : ℕ → BoolFormula → ℕ → Bool
  | _, .var _, slot | _, .tru, slot => slot == 0
  | _, .fls, _ => false
  | 0, .neg _, _ | 0, .conj _ _, _ | 0, .disj _ _, _ => false
  | fuel + 1, .neg formula, slot =>
      let blockSize := 4 ^ fuel
      if slot < blockSize then
        barringtonPostMulSlotOccupied
          (barringtonCompileSlotsNonempty fuel formula)
          (barringtonCompileSlotOccupied fuel formula) slot
      else
        false
  | fuel + 1, .conj left right, slot =>
      let blockSize := 4 ^ fuel
      let leftOccupied := barringtonCompileSlotOccupied fuel left
      let rightOccupied := barringtonCompileSlotOccupied fuel right
      if slot < blockSize then
        leftOccupied slot
      else if slot < 2 * blockSize then
        rightOccupied (slot - blockSize)
      else if slot < 3 * blockSize then
        barringtonInverseSlotOccupied blockSize leftOccupied
          (slot - 2 * blockSize)
      else if slot < 4 * blockSize then
        barringtonInverseSlotOccupied blockSize rightOccupied
          (slot - 3 * blockSize)
      else
        false
  | fuel + 1, .disj left right, slot =>
      let blockSize := 4 ^ fuel
      let leftOccupied := barringtonPostMulSlotOccupied
        (barringtonCompileSlotsNonempty fuel left)
        (barringtonCompileSlotOccupied fuel left)
      let rightOccupied := barringtonPostMulSlotOccupied
        (barringtonCompileSlotsNonempty fuel right)
        (barringtonCompileSlotOccupied fuel right)
      if slot < blockSize then
        leftOccupied slot
      else if slot < 2 * blockSize then
        rightOccupied (slot - blockSize)
      else if slot < 3 * blockSize then
        barringtonInverseSlotOccupied blockSize leftOccupied
          (slot - 2 * blockSize)
      else if slot < 4 * blockSize then
        barringtonInverseSlotOccupied blockSize rightOccupied
          (slot - 3 * blockSize)
      else
        false

/-- Directly query one fixed-address compilation slot. This follows only the
selected base-four block. The finite permutation data and pending instruction
transformations can therefore live in a concrete controller's finite state. -/
def barringtonCompileSlot? : ℕ → BoolFormula →
    Equiv.Perm (Fin 5) → ℕ → Option (BPInstr 5)
  | _, .var index, target, slot =>
      if slot = 0 then some ⟨index, 1, target⟩ else none
  | _, .tru, target, slot =>
      if slot = 0 then some (BPInstr.const target) else none
  | _, .fls, _, _ => none
  | 0, .neg _, _, _ | 0, .conj _ _, _, _ | 0, .disj _ _, _, _ => none
  | fuel + 1, .neg formula, target, slot =>
      let blockSize := 4 ^ fuel
      if slot < blockSize then
        barringtonPostMulSlot?
          (barringtonCompileSlot? fuel formula target⁻¹)
          (barringtonLastOccupiedSlot? fuel formula) target slot
      else
        none
  | fuel + 1, .conj left right, target, slot =>
      let blockSize := 4 ^ fuel
      let leftQuery :=
        barringtonCompileSlot? fuel left (barringtonLeft target)
      let rightQuery :=
        barringtonCompileSlot? fuel right (barringtonRight target)
      if slot < blockSize then
        leftQuery slot
      else if slot < 2 * blockSize then
        rightQuery (slot - blockSize)
      else if slot < 3 * blockSize then
        barringtonInverseSlot? blockSize leftQuery
          (slot - 2 * blockSize)
      else if slot < 4 * blockSize then
        barringtonInverseSlot? blockSize rightQuery
          (slot - 3 * blockSize)
      else
        none
  | fuel + 1, .disj left right, target, slot =>
      let blockSize := 4 ^ fuel
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftQuery := barringtonPostMulSlot?
        (barringtonCompileSlot? fuel left leftTarget⁻¹)
        (barringtonLastOccupiedSlot? fuel left) leftTarget
      let rightQuery := barringtonPostMulSlot?
        (barringtonCompileSlot? fuel right rightTarget⁻¹)
        (barringtonLastOccupiedSlot? fuel right) rightTarget
      let commutatorQuery := fun localSlot =>
        if localSlot < blockSize then
          leftQuery localSlot
        else if localSlot < 2 * blockSize then
          rightQuery (localSlot - blockSize)
        else if localSlot < 3 * blockSize then
          barringtonInverseSlot? blockSize leftQuery
            (localSlot - 2 * blockSize)
        else if localSlot < 4 * blockSize then
          barringtonInverseSlot? blockSize rightQuery
            (localSlot - 3 * blockSize)
        else
          none
      let firstRight :=
        (barringtonFirstOccupiedSlot? fuel right).getD 0
      let commutatorLast :=
        3 * blockSize + (blockSize - 1 - firstRight)
      barringtonPostMulSlot? commutatorQuery (some commutatorLast)
        target slot

end Complexity
