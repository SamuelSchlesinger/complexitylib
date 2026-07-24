/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.Navigation.Defs
import Complexitylib.Circuits.FormulaEncoding.Navigation.Internal

/-!
# Navigation in postfix formula codes

The backward scan finds canonical subtree boundaries using only a token cursor
and one owed-subtree counter. These results supply the stack-free navigation
primitive used by streaming Barrington compilation.

## Main results

- `FormulaCode.backwardScan_tokens_reverse` -- a canonical subtree consumes
  exactly one owed obligation.
- `FormulaCode.subtreeWidth?_tokens_root` -- exact whole-tree width.
- `FormulaCode.subtreeWidth?_tokens_neg_child` -- exact unary-child width.
- `FormulaCode.subtreeWidth?_tokens_binary_right` -- exact right-child width.
- `FormulaCode.subtreeWidth?_tokens_binary_left` -- exact left-child width.
- `FormulaCode.subtreeStart?_tokens_binary_right` -- exact right-child start.
- `FormulaCode.subtreeStart?_tokens_binary_left` -- exact left-child start.
-/

namespace Complexity

namespace FormulaCode

/-- Scanning a canonical subtree backwards consumes exactly its token count
and then resumes with one fewer owed subtree. -/
theorem backwardScan_tokens_reverse (formula : BoolFormula)
    (suffix : List Token) (owed : ℕ) :
    backwardScan ((tokens formula).reverse ++ suffix) (owed + 1) =
      (backwardScan suffix owed).map fun consumed =>
        formula.size + consumed :=
  backwardScan_tokens_reverse_append_internal formula suffix owed

/-- The whole canonical token stream is one subtree of width `formula.size`. -/
theorem subtreeWidth?_tokens_root (formula : BoolFormula) :
    subtreeWidth? (tokens formula) (formula.size - 1) = some formula.size :=
  subtreeWidth?_tokens_root_internal formula

/-- The only child of a postfix negation has its formula's exact width. -/
theorem subtreeWidth?_tokens_neg_child (formula : BoolFormula) :
    subtreeWidth? (tokens (.neg formula)) (formula.size - 1) =
      some formula.size :=
  subtreeWidth?_tokens_neg_child_internal formula

/-- The only child of a canonical postfix negation starts at index zero. -/
theorem subtreeStart?_tokens_neg_child (formula : BoolFormula) :
    subtreeStart? (tokens (.neg formula)) (formula.size - 1) = some 0 :=
  subtreeStart?_tokens_neg_child_internal formula

/-- In a canonical binary postfix stream, the right child ends immediately
before the operator and has its formula's exact width. -/
theorem subtreeWidth?_tokens_binary_right
    (left right : BoolFormula) (op : Token) :
    subtreeWidth? (tokens left ++ tokens right ++ [op])
      (left.size + right.size - 1) = some right.size :=
  subtreeWidth?_tokens_binary_right_internal left right op

/-- In a canonical binary postfix stream, the left child's own root query
recovers its exact width independently of the following right subtree. -/
theorem subtreeWidth?_tokens_binary_left
    (left right : BoolFormula) (op : Token) :
    subtreeWidth? (tokens left ++ tokens right ++ [op])
      (left.size - 1) = some left.size :=
  subtreeWidth?_tokens_binary_left_internal left right op

/-- The right subtree in a canonical binary postfix stream begins immediately
after the complete left subtree. -/
theorem subtreeStart?_tokens_binary_right
    (left right : BoolFormula) (op : Token) :
    subtreeStart? (tokens left ++ tokens right ++ [op])
      (left.size + right.size - 1) = some left.size :=
  subtreeStart?_tokens_binary_right_internal left right op

/-- The left subtree in a canonical binary postfix stream starts at zero. -/
theorem subtreeStart?_tokens_binary_left
    (left right : BoolFormula) (op : Token) :
    subtreeStart? (tokens left ++ tokens right ++ [op])
      (left.size - 1) = some 0 :=
  subtreeStart?_tokens_binary_left_internal left right op

end FormulaCode

end Complexity
