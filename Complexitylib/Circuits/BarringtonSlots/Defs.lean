/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonCompiler.Defs

/-!
# Fixed-address Barrington compilation slots -- definitions

A depth bound `fuel` gives `4 ^ fuel` addressable slots. Real compiler
instructions occupy some slots and the rest are empty. Binary nodes use four
equal blocks; unary nodes use the first block and pad the other three. This
fixed layout removes recursive child-length arithmetic from the eventual
log-space controller while retaining the existing compiler after empty slots
are erased.
-/

namespace Complexity

/-- A fixed-address schedule whose occupied slots contain branching-program
instructions. -/
abbrev BPSlots (w : ℕ) := List (Option (BPInstr w))

namespace BPSlots

/-- Modify the first occupied slot, leaving all later slots unchanged. -/
def postMulFirst (permutation : Equiv.Perm (Fin w)) : BPSlots w → BPSlots w
  | [] => []
  | none :: slots => none :: postMulFirst permutation slots
  | some instruction :: slots =>
      some (BPInstr.postMul instruction permutation) :: slots

/-- Fold a constant permutation into the last occupied slot. If every slot is
empty, place the required constant instruction in the first available slot. -/
def postMul (slots : BPSlots w) (permutation : Equiv.Perm (Fin w)) :
    BPSlots w :=
  if slots.filterMap id = [] then
    match slots with
    | [] => []
    | _ :: rest => some (BPInstr.const permutation) :: rest
  else
    (postMulFirst permutation slots.reverse).reverse

/-- Reverse the schedule and invert each occupied instruction. -/
def inverse (slots : BPSlots w) : BPSlots w :=
  (slots.map fun slot => slot.map BPInstr.inverse).reverse

/-- One occupied slot followed by padding to total length `4 ^ fuel`. -/
def singletonAt (fuel : ℕ) (instruction : BPInstr w) : BPSlots w :=
  some instruction :: List.replicate (4 ^ fuel - 1) none

/-- A completely empty schedule of total length `4 ^ fuel`. -/
def emptyAt (fuel : ℕ) : BPSlots w :=
  List.replicate (4 ^ fuel) none

end BPSlots

/-- Compile into exactly `4 ^ fuel` optional instruction slots. Correctness is
claimed when `formula.depth ≤ fuel`; shallower nodes are padded on the right. -/
def barringtonCompileSlots : ℕ → BoolFormula →
    Equiv.Perm (Fin 5) → BPSlots 5
  | fuel, .var index, target =>
      .singletonAt fuel ⟨index, 1, target⟩
  | fuel, .tru, target =>
      .singletonAt fuel (BPInstr.const target)
  | fuel, .fls, _ =>
      .emptyAt fuel
  | 0, .neg _, _ =>
      .emptyAt 0
  | fuel + 1, .neg formula, target =>
      let child :=
        (barringtonCompileSlots fuel formula target⁻¹).postMul target
      child ++ List.replicate (3 * 4 ^ fuel) none
  | 0, .conj _ _, _ =>
      .emptyAt 0
  | fuel + 1, .conj left right, target =>
      let leftSlots :=
        barringtonCompileSlots fuel left (barringtonLeft target)
      let rightSlots :=
        barringtonCompileSlots fuel right (barringtonRight target)
      leftSlots ++ rightSlots ++ leftSlots.inverse ++ rightSlots.inverse
  | 0, .disj _ _, _ =>
      .emptyAt 0
  | fuel + 1, .disj left right, target =>
      let innerTarget := target⁻¹
      let leftTarget := barringtonLeft innerTarget
      let rightTarget := barringtonRight innerTarget
      let leftSlots :=
        (barringtonCompileSlots fuel left leftTarget⁻¹).postMul leftTarget
      let rightSlots :=
        (barringtonCompileSlots fuel right rightTarget⁻¹).postMul rightTarget
      (leftSlots ++ rightSlots ++ leftSlots.inverse ++
        rightSlots.inverse).postMul target

end Complexity
