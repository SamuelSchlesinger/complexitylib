/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlotQuery.Defs
import Complexitylib.Circuits.FormulaEncoding.Navigation.Defs

/-!
# Direct Barrington queries over postfix token streams -- definitions

The machine-facing controller receives a canonical postfix token stream rather
than an inductive `BoolFormula`. A binary root recovers its right-child width
with the backwards owed-subtree scan, then represents both children by slices
of the same stream. The recursive Barrington query follows only one fixed
base-four block.
-/

namespace Complexity

namespace FormulaCode

/-- Split the body below a postfix binary root into its left and right child
token streams. Malformed streams may fail. -/
def postfixBinaryChildren? (stream : List Token) :
    Option (List Token × List Token) := do
  let body := stream.dropLast
  let rightWidth ← subtreeWidth? stream (stream.length - 2)
  if rightWidth ≤ body.length then
    let leftWidth := body.length - rightWidth
    some (body.take leftWidth, body.drop leftWidth)
  else
    none

end FormulaCode

/-- First occupied fixed address, computed from a postfix token stream. -/
def barringtonTokensFirstOccupiedSlot? : ℕ →
    List FormulaCode.Token → Option ℕ
  | 0, stream =>
      match stream.getLast? with
      | some (.var _) | some .tru => some 0
      | _ => none
  | fuel + 1, stream =>
      match stream.getLast? with
      | some (.var _) | some .tru => some 0
      | some .fls => none
      | some .neg =>
          some ((barringtonTokensFirstOccupiedSlot?
            fuel stream.dropLast).getD 0)
      | some .conj =>
          match FormulaCode.postfixBinaryChildren? stream with
          | none => none
          | some (left, right) =>
              match barringtonTokensFirstOccupiedSlot? fuel left with
              | some slot => some slot
              | none =>
                  (barringtonTokensFirstOccupiedSlot? fuel right).map
                    (4 ^ fuel + ·)
      | some .disj =>
          match FormulaCode.postfixBinaryChildren? stream with
          | none => none
          | some (left, _) =>
              some ((barringtonTokensFirstOccupiedSlot? fuel left).getD 0)
      | none => none

/-- Last occupied fixed address, computed from a postfix token stream. -/
def barringtonTokensLastOccupiedSlot? : ℕ →
    List FormulaCode.Token → Option ℕ
  | 0, stream =>
      match stream.getLast? with
      | some (.var _) | some .tru => some 0
      | _ => none
  | fuel + 1, stream =>
      match stream.getLast? with
      | some (.var _) | some .tru => some 0
      | some .fls => none
      | some .neg =>
          some ((barringtonTokensLastOccupiedSlot?
            fuel stream.dropLast).getD 0)
      | some .conj =>
          match FormulaCode.postfixBinaryChildren? stream with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              match barringtonTokensFirstOccupiedSlot? fuel right with
              | some slot =>
                  some (3 * blockSize + (blockSize - 1 - slot))
              | none =>
                  (barringtonTokensFirstOccupiedSlot? fuel left).map
                    fun slot => 2 * blockSize + (blockSize - 1 - slot)
      | some .disj =>
          match FormulaCode.postfixBinaryChildren? stream with
          | none => none
          | some (_, right) =>
              let blockSize := 4 ^ fuel
              let firstRight :=
                (barringtonTokensFirstOccupiedSlot? fuel right).getD 0
              some (3 * blockSize + (blockSize - 1 - firstRight))
      | none => none

/-- Query one fixed-address Barrington instruction directly from a postfix
token stream. -/
def barringtonCompileTokensSlot? : ℕ → List FormulaCode.Token →
    Equiv.Perm (Fin 5) → ℕ → Option (BPInstr 5)
  | fuel, stream, target, slot =>
      match fuel, stream.getLast? with
      | _, some (.var index) =>
          if slot = 0 then some ⟨index, 1, target⟩ else none
      | _, some .tru =>
          if slot = 0 then some (BPInstr.const target) else none
      | _, some .fls => none
      | 0, _ => none
      | fuel + 1, some .neg =>
          let blockSize := 4 ^ fuel
          if slot < blockSize then
            barringtonPostMulSlot?
              (barringtonCompileTokensSlot? fuel stream.dropLast target⁻¹)
              (barringtonTokensLastOccupiedSlot? fuel stream.dropLast)
              target slot
          else
            none
      | fuel + 1, some .conj =>
          match FormulaCode.postfixBinaryChildren? stream with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              let leftQuery := barringtonCompileTokensSlot? fuel left
                (barringtonLeft target)
              let rightQuery := barringtonCompileTokensSlot? fuel right
                (barringtonRight target)
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
      | fuel + 1, some .disj =>
          match FormulaCode.postfixBinaryChildren? stream with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              let innerTarget := target⁻¹
              let leftTarget := barringtonLeft innerTarget
              let rightTarget := barringtonRight innerTarget
              let leftQuery := barringtonPostMulSlot?
                (barringtonCompileTokensSlot? fuel left leftTarget⁻¹)
                (barringtonTokensLastOccupiedSlot? fuel left) leftTarget
              let rightQuery := barringtonPostMulSlot?
                (barringtonCompileTokensSlot? fuel right rightTarget⁻¹)
                (barringtonTokensLastOccupiedSlot? fuel right) rightTarget
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
                (barringtonTokensFirstOccupiedSlot? fuel right).getD 0
              let commutatorLast :=
                3 * blockSize + (blockSize - 1 - firstRight)
              barringtonPostMulSlot? commutatorQuery
                (some commutatorLast) target slot
      | _, none => none

end Complexity
