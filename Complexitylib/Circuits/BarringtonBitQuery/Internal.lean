/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonBitQuery.Defs
import Complexitylib.Circuits.BarringtonTokenQuery.Internal
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Internal

/-!
# Direct Barrington queries over encoded token segments -- proof internals
-/

namespace Complexity

namespace FormulaCode

theorem segmentRootToken?_encodeTokenStream_context_internal
    (before after : List Token) (formula : BoolFormula) :
    segmentRootToken?
        (encodeTokenStream (before ++ tokens formula ++ after))
        ⟨before.length, formula.size⟩ =
      (tokens formula).getLast? := by
  have hpositive : 0 < formula.size := by
    cases formula <;> simp [BoolFormula.size]
  rw [segmentRootToken?]
  rw [show formula.size = (formula.size - 1) + 1 by omega]
  simp only [TokenSegment.root?, Option.bind_eq_bind, Option.bind_some]
  have hglobal : before.length + (formula.size - 1) <
      (before ++ tokens formula ++ after).length := by
    simp
    omega
  rw [tokenValueAt?_encodeTokenStream_internal _ _ hglobal]
  rw [← List.getElem?_eq_getElem hglobal]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by omega)]
  rw [show before.length + (formula.size - 1) - before.length =
    formula.size - 1 by omega]
  rw [List.getLast?_eq_getElem?]
  simp

end FormulaCode

theorem barringtonBitsOccupiedSlots_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula) :
    let bits := FormulaCode.encodeTokenStream
      (before ++ FormulaCode.tokens formula ++ after)
    let segment : FormulaCode.TokenSegment :=
      ⟨before.length, formula.size⟩
    barringtonBitsFirstOccupiedSlot? fuel bits segment =
        barringtonTokensFirstOccupiedSlot? fuel
          (FormulaCode.tokens formula) ∧
      barringtonBitsLastOccupiedSlot? fuel bits segment =
        barringtonTokensLastOccupiedSlot? fuel
          (FormulaCode.tokens formula) := by
  induction fuel generalizing before after formula with
  | zero =>
      have hroot :=
        FormulaCode.segmentRootToken?_encodeTokenStream_context_internal
          before after formula
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot <;>
        simp [barringtonBitsFirstOccupiedSlot?,
          barringtonBitsLastOccupiedSlot?,
          barringtonTokensFirstOccupiedSlot?,
          barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
          BoolFormula.size, List.append_assoc, hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.segmentRootToken?_encodeTokenStream_context_internal
          before after formula
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonBitsFirstOccupiedSlot?,
            barringtonBitsLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonBitsFirstOccupiedSlot?,
            barringtonBitsLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          simp [barringtonBitsFirstOccupiedSlot?,
            barringtonBitsLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchild := ih before (FormulaCode.Token.neg :: after) formula
          have hchild' :
              barringtonBitsFirstOccupiedSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.neg formula) ++ after))
                  ⟨before.length, formula.size⟩ =
                    barringtonTokensFirstOccupiedSlot? fuel
                      (FormulaCode.tokens formula) ∧
                barringtonBitsLastOccupiedSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.neg formula) ++ after))
                  ⟨before.length, formula.size⟩ =
                    barringtonTokensLastOccupiedSlot? fuel
                      (FormulaCode.tokens formula) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchild
          simp [FormulaCode.tokens, List.append_assoc] at hchild'
          simp [barringtonBitsFirstOccupiedSlot?,
            barringtonBitsLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot,
            hchild'.1, hchild'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.encodedBinaryChildren?_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj
          have hchildren' :
              FormulaCode.encodedBinaryChildren?
                (FormulaCode.encodeTokenStream
                  (before ++ FormulaCode.tokens (.conj left right) ++ after))
                ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
            left
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.conj :: after) right
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          simp [barringtonBitsFirstOccupiedSlot?,
            barringtonBitsLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleft'.1, hright'.1]
          exact ⟨rfl, rfl⟩
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.encodedBinaryChildren?_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj
          have hchildren' :
              FormulaCode.encodedBinaryChildren?
                (FormulaCode.encodeTokenStream
                  (before ++ FormulaCode.tokens (.disj left right) ++ after))
                ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleft := ih before
            (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
            left
          have hright := ih (before ++ FormulaCode.tokens left)
            (FormulaCode.Token.disj :: after) right
          have hleft' := hleft
          have hright' := hright
          simp [List.append_assoc] at hleft' hright'
          simp [barringtonBitsFirstOccupiedSlot?,
            barringtonBitsLastOccupiedSlot?,
            barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleft'.1, hright'.1]

theorem barringtonCompileBitsSlot?_correct_context_internal (fuel : ℕ)
    (before after : List FormulaCode.Token) (formula : BoolFormula)
    (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileBitsSlot? fuel
        (FormulaCode.encodeTokenStream
          (before ++ FormulaCode.tokens formula ++ after))
        ⟨before.length, formula.size⟩ target slot =
      barringtonCompileTokensSlot? fuel
        (FormulaCode.tokens formula) target slot := by
  induction fuel generalizing before after formula target slot with
  | zero =>
      have hroot :=
        FormulaCode.segmentRootToken?_encodeTokenStream_context_internal
          before after formula
      cases formula <;>
        simp [FormulaCode.tokens, BoolFormula.size,
          List.append_assoc] at hroot ⊢ <;>
        simp [barringtonCompileBitsSlot?,
          barringtonCompileTokensSlot?, hroot]
  | succ fuel ih =>
      have hroot :=
        FormulaCode.segmentRootToken?_encodeTokenStream_context_internal
          before after formula
      cases formula with
      | var index =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileBitsSlot?,
            barringtonCompileTokensSlot?, hroot]
      | tru =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileBitsSlot?,
            barringtonCompileTokensSlot?, hroot]
      | fls =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot ⊢
          simp [barringtonCompileBitsSlot?,
            barringtonCompileTokensSlot?, hroot]
      | neg formula =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hoccupied :=
            barringtonBitsOccupiedSlots_correct_context_internal fuel before
              (FormulaCode.Token.neg :: after) formula
          have hquery :
              barringtonCompileBitsSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.neg formula) ++ after))
                  ⟨before.length, formula.size⟩ target⁻¹ =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens formula) target⁻¹ := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before (FormulaCode.Token.neg :: after) formula target⁻¹
                querySlot
          simp [FormulaCode.tokens, List.append_assoc] at hquery
          have hoccupied' := hoccupied
          simp [List.append_assoc] at hoccupied'
          simp [barringtonCompileBitsSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.TokenSegment.dropRoot?, hroot, hquery,
            hoccupied'.2]
      | conj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.encodedBinaryChildren?_encodeTokenStream_internal
              before after left right FormulaCode.Token.conj
          have hchildren' :
              FormulaCode.encodedBinaryChildren?
                (FormulaCode.encodeTokenStream
                  (before ++ FormulaCode.tokens (.conj left right) ++ after))
                ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftQuery :
              barringtonCompileBitsSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++ after))
                  ⟨before.length, left.size⟩ (barringtonLeft target) =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens left) (barringtonLeft target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.conj :: after)
                left (barringtonLeft target) querySlot
          have hrightQuery :
              barringtonCompileBitsSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.conj left right) ++ after))
                  ⟨before.length + left.size, right.size⟩
                  (barringtonRight target) =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens right) (barringtonRight target) := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.conj :: after) right
                (barringtonRight target) querySlot
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileBitsSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleftQuery, hrightQuery]
      | disj left right =>
          simp [FormulaCode.tokens, BoolFormula.size,
            List.append_assoc] at hroot
          have hchildren :=
            FormulaCode.encodedBinaryChildren?_encodeTokenStream_internal
              before after left right FormulaCode.Token.disj
          have hchildren' :
              FormulaCode.encodedBinaryChildren?
                (FormulaCode.encodeTokenStream
                  (before ++ FormulaCode.tokens (.disj left right) ++ after))
                ⟨before.length, left.size + right.size + 1⟩ =
                some (⟨before.length, left.size⟩,
                  ⟨before.length + left.size, right.size⟩) := by
            simpa [FormulaCode.tokens, List.append_assoc] using hchildren
          simp [FormulaCode.tokens, List.append_assoc] at hchildren'
          have hleftOccupied :=
            barringtonBitsOccupiedSlots_correct_context_internal fuel before
              (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
              left
          have hrightOccupied :=
            barringtonBitsOccupiedSlots_correct_context_internal fuel
              (before ++ FormulaCode.tokens left)
              (FormulaCode.Token.disj :: after) right
          have hleftOccupied' := hleftOccupied
          have hrightOccupied' := hrightOccupied
          simp [List.append_assoc] at hleftOccupied' hrightOccupied'
          have hleftQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileBitsSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++ after))
                  ⟨before.length, left.size⟩ childTarget =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens left) childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih before
                (FormulaCode.tokens right ++ FormulaCode.Token.disj :: after)
                left childTarget querySlot
          have hrightQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileBitsSlot? fuel
                  (FormulaCode.encodeTokenStream
                    (before ++ FormulaCode.tokens (.disj left right) ++ after))
                  ⟨before.length + left.size, right.size⟩ childTarget =
                barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens right) childTarget := by
            funext querySlot
            simpa [FormulaCode.tokens, List.append_assoc] using
              ih (before ++ FormulaCode.tokens left)
                (FormulaCode.Token.disj :: after) right childTarget querySlot
          simp [FormulaCode.tokens, List.append_assoc] at hleftQuery hrightQuery
          simp [barringtonCompileBitsSlot?,
            barringtonCompileTokensSlot?, FormulaCode.tokens,
            BoolFormula.size, List.append_assoc,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hroot, hchildren', hleftOccupied'.2,
            hrightOccupied'.1, hrightOccupied'.2,
            hleftQuery, hrightQuery]

end Complexity
