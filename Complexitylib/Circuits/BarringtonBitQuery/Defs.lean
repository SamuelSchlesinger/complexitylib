/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonTokenQuery.Defs
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Defs

/-!
# Direct Barrington queries over encoded token segments -- definitions

These recurrences are the pure semantics of the eventual probe controller.
They retain only a token segment, query its root from encoded bits, recover
binary child spans by the backwards owed-subtree scan, and follow one selected
base-four Barrington address.
-/

namespace Complexity

namespace FormulaCode

/-- Query the root token of a nonempty segment. -/
def segmentRootToken? (bits : List Bool)
    (segment : TokenSegment) : Option Token := do
  let root ← segment.root?
  tokenValueAt? bits root

end FormulaCode

/-- First occupied fixed address computed from one encoded token segment. -/
def barringtonBitsFirstOccupiedSlot? : ℕ → List Bool →
    FormulaCode.TokenSegment → Option ℕ
  | 0, bits, segment =>
      match FormulaCode.segmentRootToken? bits segment with
      | some (.var _) | some .tru => some 0
      | _ => none
  | fuel + 1, bits, segment =>
      match FormulaCode.segmentRootToken? bits segment with
      | some (.var _) | some .tru => some 0
      | some .fls => none
      | some .neg =>
          match segment.dropRoot? with
          | none => none
          | some child =>
              some ((barringtonBitsFirstOccupiedSlot?
                fuel bits child).getD 0)
      | some .conj =>
          match FormulaCode.encodedBinaryChildren? bits segment with
          | none => none
          | some (left, right) =>
              match barringtonBitsFirstOccupiedSlot? fuel bits left with
              | some slot => some slot
              | none =>
                  (barringtonBitsFirstOccupiedSlot? fuel bits right).map
                    (4 ^ fuel + ·)
      | some .disj =>
          match FormulaCode.encodedBinaryChildren? bits segment with
          | none => none
          | some (left, _) =>
              some ((barringtonBitsFirstOccupiedSlot?
                fuel bits left).getD 0)
      | none => none

/-- Last occupied fixed address computed from one encoded token segment. -/
def barringtonBitsLastOccupiedSlot? : ℕ → List Bool →
    FormulaCode.TokenSegment → Option ℕ
  | 0, bits, segment =>
      match FormulaCode.segmentRootToken? bits segment with
      | some (.var _) | some .tru => some 0
      | _ => none
  | fuel + 1, bits, segment =>
      match FormulaCode.segmentRootToken? bits segment with
      | some (.var _) | some .tru => some 0
      | some .fls => none
      | some .neg =>
          match segment.dropRoot? with
          | none => none
          | some child =>
              some ((barringtonBitsLastOccupiedSlot?
                fuel bits child).getD 0)
      | some .conj =>
          match FormulaCode.encodedBinaryChildren? bits segment with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              match barringtonBitsFirstOccupiedSlot? fuel bits right with
              | some slot =>
                  some (3 * blockSize + (blockSize - 1 - slot))
              | none =>
                  (barringtonBitsFirstOccupiedSlot? fuel bits left).map
                    fun slot => 2 * blockSize + (blockSize - 1 - slot)
      | some .disj =>
          match FormulaCode.encodedBinaryChildren? bits segment with
          | none => none
          | some (_, right) =>
              let blockSize := 4 ^ fuel
              let firstRight :=
                (barringtonBitsFirstOccupiedSlot? fuel bits right).getD 0
              some (3 * blockSize + (blockSize - 1 - firstRight))
      | none => none

/-- Query one fixed-address Barrington instruction from an encoded token
segment. -/
def barringtonCompileBitsSlot? : ℕ → List Bool →
    FormulaCode.TokenSegment → Equiv.Perm (Fin 5) → ℕ →
      Option (BPInstr 5)
  | fuel, bits, segment, target, slot =>
      match fuel, FormulaCode.segmentRootToken? bits segment with
      | _, some (.var index) =>
          if slot = 0 then some ⟨index, 1, target⟩ else none
      | _, some .tru =>
          if slot = 0 then some (BPInstr.const target) else none
      | _, some .fls => none
      | 0, _ => none
      | fuel + 1, some .neg =>
          match segment.dropRoot? with
          | none => none
          | some child =>
              let blockSize := 4 ^ fuel
              if slot < blockSize then
                barringtonPostMulSlot?
                  (barringtonCompileBitsSlot? fuel bits child target⁻¹)
                  (barringtonBitsLastOccupiedSlot? fuel bits child)
                  target slot
              else
                none
      | fuel + 1, some .conj =>
          match FormulaCode.encodedBinaryChildren? bits segment with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              let leftQuery := barringtonCompileBitsSlot? fuel bits left
                (barringtonLeft target)
              let rightQuery := barringtonCompileBitsSlot? fuel bits right
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
          match FormulaCode.encodedBinaryChildren? bits segment with
          | none => none
          | some (left, right) =>
              let blockSize := 4 ^ fuel
              let innerTarget := target⁻¹
              let leftTarget := barringtonLeft innerTarget
              let rightTarget := barringtonRight innerTarget
              let leftQuery := barringtonPostMulSlot?
                (barringtonCompileBitsSlot? fuel bits left leftTarget⁻¹)
                (barringtonBitsLastOccupiedSlot? fuel bits left) leftTarget
              let rightQuery := barringtonPostMulSlot?
                (barringtonCompileBitsSlot? fuel bits right rightTarget⁻¹)
                (barringtonBitsLastOccupiedSlot? fuel bits right) rightTarget
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
                (barringtonBitsFirstOccupiedSlot? fuel bits right).getD 0
              let commutatorLast :=
                3 * blockSize + (blockSize - 1 - firstRight)
              barringtonPostMulSlot? commutatorQuery
                (some commutatorLast) target slot
      | _, none => none

end Complexity
