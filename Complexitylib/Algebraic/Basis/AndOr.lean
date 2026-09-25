/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# The binary AND/OR basis

This basis is the common syntax for Boolean AND/OR circuits and set-theoretic
intersection/union constructions.  Separate operation costs can charge either
kind of binary gate; `andCost` is the intersection-complexity convention used
by the set-theoretic fusion method.
-/

@[expose] public section

namespace Algebraic
namespace AndOr

/-- Operation symbols in the binary AND/OR basis. -/
inductive Op
  | and
  | or
  deriving DecidableEq

/-- The AND/OR basis has two operation symbols. -/
instance : Fintype Op :=
  Fintype.ofList [.and, .or] (by
    intro op
    cases op <;> simp)

/-- Both AND/OR operations have arity two. -/
@[reducible] def arity (_ : Op) : Nat := 2

@[simp] theorem arity_and : arity .and = 2 := rfl
@[simp] theorem arity_or : arity .or = 2 := rfl

/-- Signature of the binary AND/OR basis. -/
abbrev signature : Signature where
  Op := Op
  Arity := arity

/-- Standard Boolean interpretation of AND and OR. -/
def boolInterpretation : Interpretation signature Bool
  | .and, input =>
      input ⟨0, by decide⟩ && input ⟨1, by decide⟩
  | .or, input =>
      input ⟨0, by decide⟩ || input ⟨1, by decide⟩

/-- Interpret AND as intersection and OR as union. -/
def setInterpretation (Γ : Type u) : Interpretation signature (Set Γ)
  | .and, input =>
      input ⟨0, by decide⟩ ∩ input ⟨1, by decide⟩
  | .or, input =>
      input ⟨0, by decide⟩ ∪ input ⟨1, by decide⟩

/-- Charge AND gates and treat OR gates as free. -/
def andCost : OperationCost signature
  | .and => 1
  | .or => 0

/-- Charge OR gates and treat AND gates as free. -/
def orCost : OperationCost signature
  | .and => 0
  | .or => 1

@[simp] theorem andCost_and : andCost .and = 1 := rfl
@[simp] theorem andCost_or : andCost .or = 0 := rfl
@[simp] theorem orCost_and : orCost .and = 0 := rfl
@[simp] theorem orCost_or : orCost .or = 1 := rfl

/-- Boolean characteristic value of membership in a set. -/
noncomputable def membership (point : Γ) (set : Set Γ) : Bool := by
  classical
  exact decide (point ∈ set)

@[simp] theorem membership_eq_true
    (point : Γ)
    (set : Set Γ) :
    membership point set = true ↔ point ∈ set := by
  classical
  simp [membership]

@[simp] theorem membership_eq_false
    (point : Γ)
    (set : Set Γ) :
    membership point set = false ↔ point ∉ set := by
  classical
  simp [membership]

/-- Equality of characteristic values is pointwise equivalence of membership. -/
theorem membership_eq_iff
    (point : Γ)
    (left right : Set Γ) :
    membership point left = membership point right ↔
      (point ∈ left ↔ point ∈ right) := by
  classical
  simp [membership]

/-- Equality of characteristic values at two points is equivalence of their
membership in the set. -/
theorem membership_points_eq_iff
    (left right : Γ)
    (set : Set Γ) :
    membership left set = membership right set ↔
      (left ∈ set ↔ right ∈ set) := by
  classical
  simp [membership]

@[simp] theorem membership_setOf_bool_eq_true
    (point : Γ)
    (value : Γ → Bool) :
    membership point { candidate | value candidate = true } = value point := by
  classical
  simp [membership]

@[simp] theorem membership_setOf_bool_eq_false
    (point : Γ)
    (value : Γ → Bool) :
    membership point { candidate | value candidate = false } = !value point := by
  classical
  simp [membership]

/-- Membership at a fixed point is a homomorphism from sets to Booleans. -/
noncomputable def membershipHomomorphism
    (point : Γ) :
    Homomorphism (setInterpretation Γ) boolInterpretation := by
  classical
  exact
    { map := membership point
      homomorphic := by
        intro op input
        cases op <;>
          simp [membership, setInterpretation, boolInterpretation] }

@[simp] theorem membershipHomomorphism_map
    (point : Γ)
    (set : Set Γ) :
    (membershipHomomorphism point).map set = membership point set := rfl

end AndOr
end Algebraic
