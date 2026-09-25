/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order

/-!
# Binary meet and finite join basis

This basis has one binary meet operation and a finite-arity join operation for
every arity.  Nullary join supplies the bottom element.  It is convenient for
cyclic discrete constructions, where joins are free and only binary meets are
counted; finite joins can subsequently be expanded into binary joins without
changing meet cost.
-/

@[expose] public section

namespace Algebraic
namespace JoinMeet

/-- Binary meet or a join with a specified finite arity. -/
inductive Op
  | meet
  | join (arity : Nat)
  deriving DecidableEq

/-- Arity of a meet/join operation. -/
@[reducible] def arity : Op → Nat
  | .meet => 2
  | .join count => count

@[simp] theorem arity_meet : arity .meet = 2 := rfl

theorem arity_join (count : Nat) :
    arity (.join count) = count := rfl

/-- Signature with binary meet and every finite join. -/
abbrev signature : Signature where
  Op := Op
  Arity := arity

/-- Interpret meet as intersection and finite join as indexed union. -/
def setInterpretation (Γ : Type u) :
    Interpretation signature (Set Γ)
  | .meet, input => input (0 : Fin 2) ∩ input (1 : Fin 2)
  | .join _, input => { point | ∃ index, point ∈ input index }

/-- Charge meets and treat all finite joins as free. -/
def meetCost : OperationCost signature
  | .meet => 1
  | .join _ => 0

@[simp] theorem meetCost_meet : meetCost .meet = 1 := rfl

@[simp] theorem meetCost_join (count : Nat) :
    meetCost (.join count) = 0 := rfl

end JoinMeet
end Algebraic
