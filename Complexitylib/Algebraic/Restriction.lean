/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Semantic input substitutions

An input substitution expresses every old input as a scalar function of a new
input vector. It covers ordinary restrictions, variable identifications, and
affine or higher-degree substitutions without imposing basis-specific syntax.
-/

@[expose] public section

namespace Algebraic

/-- A substitution of `n` old inputs by scalar functions of `k` new inputs. -/
abbrev InputSubstitution (U : Type u) (n k : Nat) :=
  Fin n → ScalarFunction U k

namespace InputSubstitution

/-- Evaluate an input substitution on a new input vector. -/
def apply
    (substitution : InputSubstitution U n k)
    (input : Fin k → U) : Fin n → U :=
  fun oldInput => substitution oldInput input

/-- The identity input substitution. -/
def id : InputSubstitution U n n :=
  fun input values => values input

@[simp] theorem id_apply (input : Fin n → U) :
    (id : InputSubstitution U n n).apply input = input := rfl

/-- Compose input substitutions, applying `inner` before `outer`. -/
def comp
    (outer : InputSubstitution U n k)
    (inner : InputSubstitution U k l) : InputSubstitution U n l :=
  fun oldInput input => outer oldInput (inner.apply input)

@[simp] theorem comp_apply
    (outer : InputSubstitution U n k)
    (inner : InputSubstitution U k l)
    (input : Fin l → U) :
    (outer.comp inner).apply input = outer.apply (inner.apply input) := rfl

@[simp] theorem comp_id
    (substitution : InputSubstitution U n k) :
    substitution.comp id = substitution := rfl

@[simp] theorem id_comp
    (substitution : InputSubstitution U n k) :
    id.comp substitution = substitution := rfl

theorem comp_assoc
    (first : InputSubstitution U n k)
    (second : InputSubstitution U k l)
    (third : InputSubstitution U l r) :
    (first.comp second).comp third = first.comp (second.comp third) := rfl

/-- Fix one input of an `(n + 1)`-input function and reindex the others. -/
def fix
    (selected : Fin (n + 1))
    (value : U) : InputSubstitution U (n + 1) n :=
  fun oldInput input =>
    Fin.insertNth (α := fun _ => U) selected value input oldInput

@[simp] theorem fix_selected
    (selected : Fin (n + 1))
    (value : U)
    (input : Fin n → U) :
    (fix selected value).apply input selected = value := by
  simp [fix, apply]

@[simp] theorem fix_succAbove
    (selected : Fin (n + 1))
    (value : U)
    (input : Fin n → U)
    (remaining : Fin n) :
    (fix selected value).apply input (selected.succAbove remaining) =
      input remaining := by
  simp [fix, apply]

end InputSubstitution

namespace Target

/-- Restrict a target along an input substitution. -/
def substitute
    (target : Target U n m)
    (substitution : InputSubstitution U n k) : Target U k m :=
  fun input => target (substitution.apply input)

@[simp] theorem substitute_apply
    (target : Target U n m)
    (substitution : InputSubstitution U n k)
    (input : Fin k → U) :
    target.substitute substitution input =
      target (substitution.apply input) := rfl

@[simp] theorem substitute_id (target : Target U n m) :
    target.substitute InputSubstitution.id = target := rfl

theorem substitute_comp
    (target : Target U n m)
    (outer : InputSubstitution U n k)
    (inner : InputSubstitution U k l) :
    (target.substitute outer).substitute inner =
      target.substitute (outer.comp inner) := rfl

end Target

end Algebraic
