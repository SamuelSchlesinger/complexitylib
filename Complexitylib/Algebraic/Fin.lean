/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Basic

/-!
# Finite folds

Small order-theoretic facts about folds indexed by `Fin`.
-/

@[expose] public section

namespace Algebraic.Fin

/-- Every folded value is at most the maximum accumulated by `Fin.foldl`. -/
theorem le_foldl_max [LinearOrder α]
    (values : Fin n → α)
    (initial : α)
    (i : Fin n) :
    values i ≤ Fin.foldl n (fun result j => max result (values j)) initial := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.foldl_succ_last]
        exact le_max_right _ _
      · rw [Fin.foldl_succ_last]
        exact (ih (fun i => values i.castSucc) i).trans (le_max_left _ _)

/-- A finite maximum is bounded above when its initial value and every folded
value are bounded above. -/
theorem foldl_max_le [LinearOrder α]
    (values : Fin n -> α)
    (initial bound : α)
    (initial_le : initial <= bound)
    (values_le : forall i, values i <= bound) :
    Fin.foldl n (fun result i => max result (values i)) initial <= bound := by
  induction n with
  | zero => simpa using initial_le
  | succ n inductionHypothesis =>
      rw [Fin.foldl_succ_last]
      apply max_le
      · apply inductionHypothesis
        intro i
        exact values_le i.castSucc
      · exact values_le (Fin.last n)

end Algebraic.Fin
