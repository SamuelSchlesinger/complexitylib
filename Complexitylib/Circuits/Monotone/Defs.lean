/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Formula

/-!
# Monotone Boolean formulas -- definitions

This file defines a typed formula tree containing variables, conjunctions, and
disjunctions only. Constants and negations are deliberately absent: this is the
standard syntax used by the Karchmer--Wigderson correspondence.
-/

@[expose] public section

namespace Complexity

/-- A monotone Boolean formula over exactly `N` input variables. -/
inductive MonotoneFormula (N : ℕ) where
  /-- An input variable. -/
  | var (index : Fin N)
  /-- Conjunction. -/
  | conj (left right : MonotoneFormula N)
  /-- Disjunction. -/
  | disj (left right : MonotoneFormula N)
  deriving Repr, DecidableEq

namespace MonotoneFormula

/-- Evaluate a monotone formula. -/
def eval (input : BitString N) : MonotoneFormula N → Bool
  | .var index => input index
  | .conj left right => left.eval input && right.eval input
  | .disj left right => left.eval input || right.eval input

/-- Total tree-node count. -/
def size : MonotoneFormula N → ℕ
  | .var _ => 1
  | .conj left right => left.size + right.size + 1
  | .disj left right => left.size + right.size + 1

/-- Number of variable leaves, counting repeated occurrences. -/
def leaves : MonotoneFormula N → ℕ
  | .var _ => 1
  | .conj left right => left.leaves + right.leaves
  | .disj left right => left.leaves + right.leaves

/-- Longest root-to-leaf path, with variables at depth zero. -/
def depth : MonotoneFormula N → ℕ
  | .var _ => 0
  | .conj left right => max left.depth right.depth + 1
  | .disj left right => max left.depth right.depth + 1

/-- The set of variables occurring in the formula. -/
def vars : MonotoneFormula N → Finset (Fin N)
  | .var index => {index}
  | .conj left right => left.vars ∪ right.vars
  | .disj left right => left.vars ∪ right.vars

/-- Whether a formula computes a given single-output Boolean function. -/
def Computes (formula : MonotoneFormula N)
    (function : BitString N → Bool) : Prop :=
  ∀ input, formula.eval input = function input

/-- Erase finite-index proofs and view a monotone formula as a general
`BoolFormula`. -/
def toBoolFormula : MonotoneFormula N → BoolFormula
  | .var index => .var index.val
  | .conj left right => .conj left.toBoolFormula right.toBoolFormula
  | .disj left right => .disj left.toBoolFormula right.toBoolFormula

end MonotoneFormula

namespace BitString

/-- Pointwise Boolean order, written as the implication `x_i = 1 → y_i = 1`
at every coordinate. -/
def PointwiseLE (x y : BitString N) : Prop :=
  ∀ index, x index = true → y index = true

end BitString

/-- A single-output Boolean function is monotone in the pointwise Boolean
order. -/
def IsMonotoneBoolFun (function : BitString N → Bool) : Prop :=
  ∀ ⦃x y⦄, x.PointwiseLE y →
    function x = true → function y = true

end Complexity
