/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Mathlib.Data.Fintype.OfMap

/-!
# The De Morgan basis

The basis contains Boolean constants, a structural identity gate, unary
negation, and binary conjunction and disjunction. The circuit representation
has free wire outputs; identity remains useful only when a proof explicitly
materializes an output as a final program gate. `binaryCost` implements the
standard gate-elimination cost model in which only the binary gates are
charged.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-- Operation symbols in the De Morgan basis. -/
inductive Op
  | false
  | true
  | id
  | not
  | and
  | or
  deriving DecidableEq

/-- The De Morgan basis has six operation symbols. -/
instance : Fintype Op :=
  Fintype.ofList [.false, .true, .id, .not, .and, .or] (by
    intro op
    cases op <;> simp)

/-- Arity of an operation in the De Morgan basis. -/
def arity : Op → Nat
  | .false | .true => 0
  | .id | .not => 1
  | .and | .or => 2

@[simp] theorem arity_false : arity .false = 0 := rfl
@[simp] theorem arity_true : arity .true = 0 := rfl
@[simp] theorem arity_id : arity .id = 1 := rfl
@[simp] theorem arity_not : arity .not = 1 := rfl
@[simp] theorem arity_and : arity .and = 2 := rfl
@[simp] theorem arity_or : arity .or = 2 := rfl

/-- Signature of the De Morgan basis. -/
abbrev signature : Signature where
  Op := Op
  Arity := arity

/-- Standard Boolean interpretation of the De Morgan basis. -/
def interpretation : (op : Op) → (Fin (arity op) → Bool) → Bool
  | .false, _ => false
  | .true, _ => true
  | .id, input => input ⟨0, by decide⟩
  | .not, input => !(input ⟨0, by decide⟩)
  | .and, input => input ⟨0, by decide⟩ && input ⟨1, by decide⟩
  | .or, input => input ⟨0, by decide⟩ || input ⟨1, by decide⟩

/-- Cost model charging exactly the binary gates. This is the convention used
by the gate-elimination lower bounds, not the mass-production manuscript. -/
def binaryCost : OperationCost signature
  | .and | .or => 1
  | .false | .true | .id | .not => 0

@[simp] theorem binaryCost_false : binaryCost .false = 0 := rfl
@[simp] theorem binaryCost_true : binaryCost .true = 0 := rfl
@[simp] theorem binaryCost_id : binaryCost .id = 0 := rfl
@[simp] theorem binaryCost_not : binaryCost .not = 0 := rfl
@[simp] theorem binaryCost_and : binaryCost .and = 1 := rfl
@[simp] theorem binaryCost_or : binaryCost .or = 1 := rfl

/-- The manuscript's standard circuit-size convention: constants and
structural identities are free, while NOT, AND, and OR each cost one gate. -/
def standardCost : OperationCost signature
  | .false | .true | .id => 0
  | .not | .and | .or => 1

@[simp] theorem standardCost_false : standardCost .false = 0 := rfl
@[simp] theorem standardCost_true : standardCost .true = 0 := rfl
@[simp] theorem standardCost_id : standardCost .id = 0 := rfl
@[simp] theorem standardCost_not : standardCost .not = 1 := rfl
@[simp] theorem standardCost_and : standardCost .and = 1 := rfl
@[simp] theorem standardCost_or : standardCost .or = 1 := rfl

end DeMorgan
end Algebraic
