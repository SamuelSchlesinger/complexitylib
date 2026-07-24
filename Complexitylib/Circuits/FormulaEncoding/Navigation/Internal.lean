/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.Internal
import Complexitylib.Circuits.FormulaEncoding.Navigation.Defs

/-!
# Navigation in postfix formula codes -- proof internals
-/

namespace Complexity

namespace FormulaCode

/-- Scanning one complete canonical subtree reduces the owed count by exactly
one and then continues into the supplied suffix. -/
theorem backwardScan_tokens_reverse_append_internal
    (formula : BoolFormula) (suffix : List Token) (owed : ℕ) :
    backwardScan ((tokens formula).reverse ++ suffix) (owed + 1) =
      (backwardScan suffix owed).map fun consumed =>
        formula.size + consumed := by
  induction formula generalizing suffix owed with
  | var index =>
      change (backwardScan suffix owed).map (· + 1) =
        (backwardScan suffix owed).map fun consumed => 1 + consumed
      cases backwardScan suffix owed with
      | none => rfl
      | some consumed => simp; omega
  | tru =>
      change (backwardScan suffix owed).map (· + 1) =
        (backwardScan suffix owed).map fun consumed => 1 + consumed
      cases backwardScan suffix owed with
      | none => rfl
      | some consumed => simp; omega
  | fls =>
      change (backwardScan suffix owed).map (· + 1) =
        (backwardScan suffix owed).map fun consumed => 1 + consumed
      cases backwardScan suffix owed with
      | none => rfl
      | some consumed => simp; omega
  | neg formula ih =>
      simp only [tokens, List.reverse_append, List.reverse_singleton,
        List.singleton_append, BoolFormula.size]
      change (backwardScan ((tokens formula).reverse ++ suffix)
        (owed + 1)).map (· + 1) = _
      rw [ih]
      cases backwardScan suffix owed with
      | none => rfl
      | some consumed => simp; omega
  | conj left right ihLeft ihRight =>
      simp only [tokens, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.append_assoc, BoolFormula.size]
      change (backwardScan ((tokens right).reverse ++
        ((tokens left).reverse ++ suffix)) (owed + 2)).map (· + 1) = _
      rw [show owed + 2 = (owed + 1) + 1 by omega]
      rw [ihRight, ihLeft]
      cases backwardScan suffix owed with
      | none => rfl
      | some consumed => simp; omega
  | disj left right ihLeft ihRight =>
      simp only [tokens, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.append_assoc, BoolFormula.size]
      change (backwardScan ((tokens right).reverse ++
        ((tokens left).reverse ++ suffix)) (owed + 2)).map (· + 1) = _
      rw [show owed + 2 = (owed + 1) + 1 by omega]
      rw [ihRight, ihLeft]
      cases backwardScan suffix owed with
      | none => rfl
      | some consumed => simp; omega

private theorem formula_size_pos_internal (formula : BoolFormula) :
    0 < formula.size := by
  cases formula <;> simp [BoolFormula.size]

theorem backwardScan_tokens_reverse_internal (formula : BoolFormula) :
    backwardScan (tokens formula).reverse 1 = some formula.size := by
  simpa using backwardScan_tokens_reverse_append_internal formula [] 0

theorem subtreeWidth?_tokens_root_internal (formula : BoolFormula) :
    subtreeWidth? (tokens formula) (formula.size - 1) = some formula.size := by
  rw [subtreeWidth?]
  have hpositive := formula_size_pos_internal formula
  have htake : (tokens formula).take (formula.size - 1 + 1) =
      tokens formula := by
    rw [show formula.size - 1 + 1 = formula.size by omega]
    rw [← length_tokens_internal formula, List.take_length]
  rw [htake]
  exact backwardScan_tokens_reverse_internal formula

theorem subtreeStart?_tokens_root_internal (formula : BoolFormula) :
    subtreeStart? (tokens formula) (formula.size - 1) = some 0 := by
  rw [subtreeStart?, subtreeWidth?_tokens_root_internal]
  change (if formula.size ≤ formula.size - 1 + 1 then
    some (formula.size - 1 + 1 - formula.size) else none) = some 0
  rw [if_pos (by
    have hpositive := formula_size_pos_internal formula
    omega)]
  congr
  have hpositive := formula_size_pos_internal formula
  omega

theorem subtreeWidth?_tokens_neg_child_internal (formula : BoolFormula) :
    subtreeWidth? (tokens (.neg formula)) (formula.size - 1) =
      some formula.size := by
  rw [subtreeWidth?, tokens]
  have hpositive := formula_size_pos_internal formula
  have htake : (tokens formula ++ [Token.neg]).take
      (formula.size - 1 + 1) = tokens formula := by
    rw [show formula.size - 1 + 1 = formula.size by omega]
    rw [← length_tokens_internal formula]
    simp
  rw [htake]
  exact backwardScan_tokens_reverse_internal formula

theorem subtreeStart?_tokens_neg_child_internal (formula : BoolFormula) :
    subtreeStart? (tokens (.neg formula)) (formula.size - 1) = some 0 := by
  rw [subtreeStart?, subtreeWidth?_tokens_neg_child_internal]
  change (if formula.size ≤ formula.size - 1 + 1 then
    some (formula.size - 1 + 1 - formula.size) else none) = some 0
  have hpositive := formula_size_pos_internal formula
  rw [if_pos (by omega)]
  congr
  omega

theorem subtreeWidth?_tokens_binary_right_internal
    (left right : BoolFormula) (op : Token) :
    subtreeWidth? (tokens left ++ tokens right ++ [op])
      (left.size + right.size - 1) = some right.size := by
  rw [subtreeWidth?]
  have hleftPositive := formula_size_pos_internal left
  have hrightPositive := formula_size_pos_internal right
  rw [show left.size + right.size - 1 + 1 = left.size + right.size by omega]
  have hprefixLength : (tokens left ++ tokens right).length =
      left.size + right.size := by
    simp [length_tokens_internal]
  have htake : (tokens left ++ tokens right ++ [op]).take
      (left.size + right.size) = tokens left ++ tokens right := by
    rw [← hprefixLength]
    exact List.take_left
  rw [htake]
  rw [List.reverse_append]
  have hscan := backwardScan_tokens_reverse_append_internal
    right (tokens left).reverse 0
  simpa [backwardScan] using hscan

theorem subtreeWidth?_tokens_binary_left_internal
    (left right : BoolFormula) (op : Token) :
    subtreeWidth? (tokens left ++ tokens right ++ [op])
      (left.size - 1) = some left.size := by
  rw [subtreeWidth?]
  have hleftPositive := formula_size_pos_internal left
  have htake : (tokens left ++ tokens right ++ [op]).take
      (left.size - 1 + 1) = tokens left := by
    rw [show left.size - 1 + 1 = left.size by omega]
    rw [← length_tokens_internal left]
    simp
  rw [htake]
  exact backwardScan_tokens_reverse_internal left

theorem subtreeStart?_tokens_binary_right_internal
    (left right : BoolFormula) (op : Token) :
    subtreeStart? (tokens left ++ tokens right ++ [op])
      (left.size + right.size - 1) = some left.size := by
  rw [subtreeStart?, subtreeWidth?_tokens_binary_right_internal]
  change (if right.size ≤ left.size + right.size - 1 + 1 then
    some (left.size + right.size - 1 + 1 - right.size) else none) =
      some left.size
  have hleftPositive := formula_size_pos_internal left
  have hrightPositive := formula_size_pos_internal right
  rw [if_pos (by omega)]
  congr
  omega

theorem subtreeStart?_tokens_binary_left_internal
    (left right : BoolFormula) (op : Token) :
    subtreeStart? (tokens left ++ tokens right ++ [op])
      (left.size - 1) = some 0 := by
  rw [subtreeStart?, subtreeWidth?_tokens_binary_left_internal]
  change (if left.size ≤ left.size - 1 + 1 then
    some (left.size - 1 + 1 - left.size) else none) = some 0
  have hleftPositive := formula_size_pos_internal left
  rw [if_pos (by omega)]
  congr
  omega

end FormulaCode

end Complexity
