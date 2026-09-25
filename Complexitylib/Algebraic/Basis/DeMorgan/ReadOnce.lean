/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.Support
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Card

/-!
# Read-once De Morgan formulas and unateness

A read-once formula uses each input at most once, including through negation.
It is unate: each input has a fixed direction of influence over all contexts.
The substitution API is used to recover read-once formulas from tight shared circuits.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- A Boolean function has a fixed increasing or decreasing direction at a coordinate. -/
def UnateAt (function : ScalarFunction Bool n) (i : Fin n) : Prop :=
  (∀ input, function (Function.update input i false) ≤ function (Function.update input i true)) ∨
  (∀ input, function (Function.update input i true) ≤ function (Function.update input i false))

/-- Every input has a fixed direction of influence, possibly a different direction for each input. -/
def Unate (function : ScalarFunction Bool n) : Prop := ∀ i, UnateAt function i

/-- Every monotone Boolean function is unate. -/
theorem unate_of_monotone {function : ScalarFunction Bool n} (monotone : Monotone function) :
    Unate function := by
  intro i
  left
  intro input
  apply monotone
  intro j
  by_cases same : j = i <;> simp [same]

private theorem not_le_not {left right : Bool} (h : left ≤ right) : (!right) ≤ (!left) := by
  cases left <;> cases right <;> simp_all

/-- Output complementation preserves unateness. -/
theorem UnateAt.not {function : ScalarFunction Bool n} {i : Fin n} (h : UnateAt function i) :
    UnateAt (fun input => !(function input)) i := by
  rcases h with positive | negative
  · exact Or.inr (fun input => not_le_not (positive input))
  · exact Or.inl (fun input => not_le_not (negative input))

/-- A function and its complement are unate at exactly the same coordinates. -/
theorem unateAt_not_iff (function : ScalarFunction Bool n) (i : Fin n) :
    UnateAt (fun input => !(function input)) i ↔ UnateAt function i := by
  constructor
  · intro h
    simpa using h.not
  · exact UnateAt.not

private def combine (useOr : Bool) (left right : Bool) : Bool :=
  if useOr then left || right else left && right

private theorem combine_le (useOr : Bool) {a b c d : Bool} (left : a ≤ b) (right : c ≤ d) :
    combine useOr a c ≤ combine useOr b d := by
  cases useOr <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [combine]

private theorem combine_unate_left (useOr : Bool) {left right : ScalarFunction Bool n}
    {i : Fin n} (unate : UnateAt left i)
    (independent : ∀ input, right (Function.update input i false) =
      right (Function.update input i true)) :
    UnateAt (fun input => combine useOr (left input) (right input)) i := by
  rcases unate with positive | negative
  · exact Or.inl (fun input => combine_le useOr (positive input) (le_of_eq (independent input)))
  · exact Or.inr (fun input => combine_le useOr (negative input) (le_of_eq (independent input).symm))

namespace Expression

/-- Input occurrences in a formula, preserving repetitions and their order. -/
def inputList : Expression n → List (Fin n)
  | .input i => [i]
  | .constant _ => []
  | .not child => child.inputList
  | .and left right | .or left right => left.inputList ++ right.inputList

/-- A formula is read-once when no input occurrence is repeated. -/
def ReadOnce (expression : Expression n) : Prop := expression.inputList.Nodup

/-- Substitute an arbitrary formula for each input. -/
def substitute (expression : Expression n) (replacement : Fin n → Expression m) : Expression m :=
  match expression with
  | .input i => replacement i
  | .constant value => .constant value
  | .not child => .not (child.substitute replacement)
  | .and left right => .and (left.substitute replacement) (right.substitute replacement)
  | .or left right => .or (left.substitute replacement) (right.substitute replacement)

/-- Formula substitution composes the corresponding Boolean functions. -/
theorem eval_substitute (expression : Expression n) (replacement : Fin n → Expression m)
    (input : Fin m → Bool) :
    (expression.substitute replacement).eval input =
      expression.eval (fun i => (replacement i).eval input) := by
  induction expression <;> simp_all [substitute, eval]

/-- Substitution replaces each input occurrence by the occurrences of its replacement. -/
theorem inputList_substitute (expression : Expression n) (replacement : Fin n → Expression m) :
    (expression.substitute replacement).inputList =
      expression.inputList.flatMap (fun i => (replacement i).inputList) := by
  induction expression <;> simp_all [substitute, inputList]

/-- Formula semantics depend only on the inputs occurring in the formula. -/
theorem eval_congr_inputList (expression : Expression n) (left right : Fin n → Bool)
    (agree : ∀ i ∈ expression.inputList, left i = right i) : expression.eval left = expression.eval right := by
  induction expression with
  | input i => exact agree i (by simp [inputList])
  | constant _ => rfl
  | not child ih => exact congrArg Bool.not (ih agree)
  | and left right leftIH rightIH =>
    exact congrArg₂ Bool.and (leftIH (fun i hi => agree i (List.mem_append_left _ hi)))
      (rightIH (fun i hi => agree i (List.mem_append_right _ hi)))
  | or left right leftIH rightIH =>
    exact congrArg₂ Bool.or (leftIH (fun i hi => agree i (List.mem_append_left _ hi)))
      (rightIH (fun i hi => agree i (List.mem_append_right _ hi)))

/-- Changing an absent input leaves the formula value unchanged. -/
theorem eval_update_eq_of_not_mem (expression : Expression n) {i : Fin n}
    (absent : i ∉ expression.inputList) (input : Fin n → Bool) (value : Bool) :
    expression.eval (Function.update input i value) = expression.eval input := by
  apply eval_congr_inputList
  intro j present
  have different : j ≠ i := by
    intro equal
    exact absent (equal ▸ present)
  simp [different]

private theorem binary_unate (useOr : Bool) (left right : Expression n)
    (leftUnate : Unate left.eval) (rightUnate : Unate right.eval)
    (disjoint : List.Disjoint left.inputList right.inputList) :
    Unate (fun input => combine useOr (left.eval input) (right.eval input)) := by
  intro i
  by_cases present : i ∈ left.inputList
  · have absent : i ∉ right.inputList := fun member => disjoint present member
    apply combine_unate_left useOr (leftUnate i)
    intro input
    rw [eval_update_eq_of_not_mem _ absent, eval_update_eq_of_not_mem _ absent]
  · have h := combine_unate_left useOr (rightUnate i) (right := left.eval) (by
      intro input
      rw [eval_update_eq_of_not_mem _ present, eval_update_eq_of_not_mem _ present])
    cases useOr <;> simpa [combine, Bool.and_comm, Bool.or_comm] using h

/-- A read-once De Morgan formula is unate, including formulas with internal negations. -/
theorem ReadOnce.unate {expression : Expression n} (once : expression.ReadOnce) :
    Unate expression.eval := by
  induction expression with
  | input i =>
    apply unate_of_monotone
    exact fun _ _ h => h i
  | constant value => exact fun _ => Or.inl (fun _ => le_refl _)
  | not child ih => exact fun i => (ih once i).not
  | and left right leftIH rightIH =>
    obtain ⟨hl, hr, disjoint⟩ := List.nodup_append'.mp once
    exact binary_unate false left right (leftIH hl) (rightIH hr) disjoint
  | or left right leftIH rightIH =>
    obtain ⟨hl, hr, disjoint⟩ := List.nodup_append'.mp once
    exact binary_unate true left right (leftIH hl) (rightIH hr) disjoint

end Expression

end Algebraic.DeMorgan
