/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlotQuery.Internal
import Complexitylib.Circuits.BarringtonTokenQuery.Defs
import Complexitylib.Circuits.FormulaEncoding.Navigation.Internal

/-!
# Direct Barrington queries over postfix token streams -- proof internals
-/

namespace Complexity

namespace FormulaCode

theorem postfixBinaryChildren?_tokens_internal
    (left right : BoolFormula) (op : Token) :
    postfixBinaryChildren? (tokens left ++ tokens right ++ [op]) =
      some (tokens left, tokens right) := by
  rw [postfixBinaryChildren?]
  simp only [List.dropLast_concat, List.length_append,
    List.length_singleton, length_tokens_internal]
  rw [show left.size + right.size + 1 - 2 =
    left.size + right.size - 1 by omega]
  rw [subtreeWidth?_tokens_binary_right_internal]
  change (if right.size ≤ left.size + right.size then
      some
        ((tokens left ++ tokens right).take
          (left.size + right.size - right.size),
        (tokens left ++ tokens right).drop
          (left.size + right.size - right.size))
    else none) = some (tokens left, tokens right)
  rw [if_pos (by omega)]
  rw [show left.size + right.size - right.size = left.size by omega]
  rw [← length_tokens_internal left]
  simp

theorem postfixBinaryChildren?_tokens_assoc_internal
    (left right : BoolFormula) (op : Token) :
    postfixBinaryChildren? (tokens left ++ (tokens right ++ [op])) =
      some (tokens left, tokens right) := by
  rw [← List.append_assoc]
  exact postfixBinaryChildren?_tokens_internal left right op

end FormulaCode

theorem barringtonTokensOccupiedSlots_correct_internal (fuel : ℕ)
    (formula : BoolFormula) :
    barringtonTokensFirstOccupiedSlot? fuel (FormulaCode.tokens formula) =
        barringtonFirstOccupiedSlot? fuel formula ∧
      barringtonTokensLastOccupiedSlot? fuel (FormulaCode.tokens formula) =
        barringtonLastOccupiedSlot? fuel formula := by
  induction fuel generalizing formula with
  | zero =>
      cases formula <;>
        simp [barringtonTokensFirstOccupiedSlot?,
          barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
          barringtonLastOccupiedSlot?, FormulaCode.tokens]
  | succ fuel ih =>
      cases formula with
      | var index =>
          simp [barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
            barringtonLastOccupiedSlot?, FormulaCode.tokens]
      | tru =>
          simp [barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
            barringtonLastOccupiedSlot?, FormulaCode.tokens]
      | fls =>
          simp [barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
            barringtonLastOccupiedSlot?, FormulaCode.tokens]
      | neg formula =>
          obtain ⟨hfirst, hlast⟩ := ih formula
          simp [barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
            barringtonLastOccupiedSlot?, FormulaCode.tokens, hfirst, hlast]
      | conj left right =>
          obtain ⟨hleftFirst, _⟩ := ih left
          obtain ⟨hrightFirst, _⟩ := ih right
          simp only [barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
            barringtonLastOccupiedSlot?, FormulaCode.tokens,
            List.getLast?_concat]
          rw [FormulaCode.postfixBinaryChildren?_tokens_internal]
          simp only [hleftFirst, hrightFirst]
          exact ⟨rfl, rfl⟩
      | disj left right =>
          obtain ⟨hleftFirst, _⟩ := ih left
          obtain ⟨hrightFirst, _⟩ := ih right
          simp only [barringtonTokensFirstOccupiedSlot?,
            barringtonTokensLastOccupiedSlot?, barringtonFirstOccupiedSlot?,
            barringtonLastOccupiedSlot?, FormulaCode.tokens,
            List.getLast?_concat]
          rw [FormulaCode.postfixBinaryChildren?_tokens_internal]
          simp only [hleftFirst, hrightFirst]
          exact ⟨True.intro, True.intro⟩

theorem barringtonCompileTokensSlot?_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileTokensSlot? fuel (FormulaCode.tokens formula)
      target slot = barringtonCompileSlot? fuel formula target slot := by
  induction fuel generalizing formula target slot with
  | zero =>
      cases formula <;>
        simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
          FormulaCode.tokens]
  | succ fuel ih =>
      cases formula with
      | var index =>
          simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
            FormulaCode.tokens]
      | tru =>
          simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
            FormulaCode.tokens]
      | fls =>
          simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
            FormulaCode.tokens]
      | neg formula =>
          have hlast :=
            (barringtonTokensOccupiedSlots_correct_internal fuel formula).2
          have hquery :
              barringtonCompileTokensSlot? fuel
                  (FormulaCode.tokens formula) target⁻¹ =
                barringtonCompileSlot? fuel formula target⁻¹ := by
            funext querySlot
            exact ih formula target⁻¹ querySlot
          simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
            FormulaCode.tokens, hquery, hlast]
      | conj left right =>
          have hleftQuery :
              barringtonCompileTokensSlot? fuel (FormulaCode.tokens left)
                  (barringtonLeft target) =
                barringtonCompileSlot? fuel left
                  (barringtonLeft target) := by
            funext querySlot
            exact ih left (barringtonLeft target) querySlot
          have hrightQuery :
              barringtonCompileTokensSlot? fuel (FormulaCode.tokens right)
                  (barringtonRight target) =
                barringtonCompileSlot? fuel right
                  (barringtonRight target) := by
            funext querySlot
            exact ih right (barringtonRight target) querySlot
          simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
            FormulaCode.tokens,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hleftQuery, hrightQuery]
      | disj left right =>
          have hleftLast :=
            (barringtonTokensOccupiedSlots_correct_internal fuel left).2
          have hrightFirst :=
            (barringtonTokensOccupiedSlots_correct_internal fuel right).1
          have hrightLast :=
            (barringtonTokensOccupiedSlots_correct_internal fuel right).2
          have hleftQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileTokensSlot? fuel (FormulaCode.tokens left)
                  childTarget =
                barringtonCompileSlot? fuel left childTarget := by
            funext querySlot
            exact ih left childTarget querySlot
          have hrightQuery (childTarget : Equiv.Perm (Fin 5)) :
              barringtonCompileTokensSlot? fuel (FormulaCode.tokens right)
                  childTarget =
                barringtonCompileSlot? fuel right childTarget := by
            funext querySlot
            exact ih right childTarget querySlot
          simp [barringtonCompileTokensSlot?, barringtonCompileSlot?,
            FormulaCode.tokens,
            FormulaCode.postfixBinaryChildren?_tokens_assoc_internal,
            hleftLast, hrightFirst, hrightLast,
            hleftQuery, hrightQuery]

end Complexity
