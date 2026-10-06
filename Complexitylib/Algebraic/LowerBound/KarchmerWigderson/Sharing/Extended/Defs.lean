/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Semantics

/-!
# The De Morgan basis extended by XOR and EQUIV gates

This file defines the circuit basis of `Extended.signature`: the De Morgan operations (Boolean
constants, identity, NOT, binary AND and OR) together with binary XOR and EQUIV gates, its
standard interpretation `Extended.interpretation`, and three cost models: `Extended.deMorganCost`
counts the AND and OR gates, `Extended.xorCost` the XOR and EQUIV gates, and
`Extended.binaryCost` all binary gates.

It also defines the four-leaf De Morgan formulas `Formula.xorGadget z₁ z₂` and
`Formula.equivGadget z₁ z₂` computing `z₁ ⊕ z₂` and `z₁ ↔ z₂`. When both variables are shared
values (indices at least `m`), the gadgets have no input leaves below `m`; this is what lets an
XOR or EQUIV gate of any fan-out be charged only two shared values in the Khrapchenko bound of
`Complexitylib.Algebraic.LowerBound.KarchmerWigderson.Sharing.Extended`.
-/

@[expose] public section

namespace Algebraic
namespace KW

/-! ### XOR and EQUIV gadgets -/

namespace Formula

variable {N : Nat}

/-- The De Morgan formula `(z₁ ∧ ¬z₂) ∨ (¬z₁ ∧ z₂)` computing `z₁ ⊕ z₂` on two variables. -/
def xorGadget (z₁ z₂ : Fin N) : Formula N :=
  .or (.and (.lit z₁ true) (.lit z₂ false)) (.and (.lit z₁ false) (.lit z₂ true))

/-- The De Morgan formula `(z₁ ∧ z₂) ∨ (¬z₁ ∧ ¬z₂)` computing `z₁ ↔ z₂` on two variables. -/
def equivGadget (z₁ z₂ : Fin N) : Formula N :=
  .or (.and (.lit z₁ true) (.lit z₂ true)) (.and (.lit z₁ false) (.lit z₂ false))

@[simp] theorem eval_xorGadget (z₁ z₂ : Fin N) (x : Fin N → Bool) :
    (xorGadget z₁ z₂).eval x = (x z₁ ^^ x z₂) := by
  simp only [xorGadget, eval]
  cases x z₁ <;> cases x z₂ <;> rfl

@[simp] theorem eval_equivGadget (z₁ z₂ : Fin N) (x : Fin N → Bool) :
    (equivGadget z₁ z₂).eval x = (x z₁ == x z₂) := by
  simp only [equivGadget, eval]
  cases x z₁ <;> cases x z₂ <;> rfl

/-- When both variables `z₁, z₂` are shared variables (`≥ m`), `xorGadget z₁ z₂` contributes zero
input leaves below `m`. -/
theorem inputLeaves_xorGadget_of_ge {m : Nat} {z₁ z₂ : Fin N} (h₁ : m ≤ z₁.val) (h₂ : m ≤ z₂.val) :
    (xorGadget z₁ z₂).inputLeaves m = 0 := by
  simp only [xorGadget, inputLeaves]
  split_ifs <;> omega

/-- When both variables `z₁, z₂` are shared variables (`≥ m`), `equivGadget z₁ z₂` contributes zero
input leaves below `m`. -/
theorem inputLeaves_equivGadget_of_ge {m : Nat} {z₁ z₂ : Fin N}
    (h₁ : m ≤ z₁.val) (h₂ : m ≤ z₂.val) :
    (equivGadget z₁ z₂).inputLeaves m = 0 := by
  simp only [equivGadget, inputLeaves]
  split_ifs <;> omega

end Formula

/-! ### The extended basis -/

namespace Extended

/-- Operation symbols of the extended De Morgan basis with binary `xor` and `equiv` gates. -/
inductive Op
  | false
  | true
  | id
  | not
  | and
  | or
  | xor
  | equiv
  deriving DecidableEq

instance : Fintype Op :=
  Fintype.ofList [.false, .true, .id, .not, .and, .or, .xor, .equiv] (by
    intro op
    cases op <;> simp)

/-- Arity of an operation in the extended basis. -/
def arity : Op → Nat
  | .false | .true => 0
  | .id | .not => 1
  | .and | .or | .xor | .equiv => 2

@[simp] theorem arity_false : arity .false = 0 := rfl
@[simp] theorem arity_true : arity .true = 0 := rfl
@[simp] theorem arity_id : arity .id = 1 := rfl
@[simp] theorem arity_not : arity .not = 1 := rfl
@[simp] theorem arity_and : arity .and = 2 := rfl
@[simp] theorem arity_or : arity .or = 2 := rfl
@[simp] theorem arity_xor : arity .xor = 2 := rfl
@[simp] theorem arity_equiv : arity .equiv = 2 := rfl

/-- Signature of the extended De Morgan + XOR/EQUIV basis. -/
abbrev signature : Signature where
  Op := Op
  Arity := arity

/-- Standard Boolean interpretation of the extended basis. -/
def interpretation : (op : Op) → (Fin (arity op) → Bool) → Bool
  | .false, _ => false
  | .true, _ => true
  | .id, input => input ⟨0, by decide⟩
  | .not, input => !(input ⟨0, by decide⟩)
  | .and, input => input ⟨0, by decide⟩ && input ⟨1, by decide⟩
  | .or, input => input ⟨0, by decide⟩ || input ⟨1, by decide⟩
  | .xor, input => (input ⟨0, by decide⟩ ^^ input ⟨1, by decide⟩)
  | .equiv, input => (input ⟨0, by decide⟩ == input ⟨1, by decide⟩)

/-- Cost model charging 1 for binary De Morgan gates (`and`, `or`) and 0 for all other gates. -/
def deMorganCost : OperationCost signature
  | .and | .or => 1
  | .false | .true | .id | .not | .xor | .equiv => 0

/-- Cost model charging 1 for binary XOR/EQUIV gates (`xor`, `equiv`) and 0 for all other gates. -/
def xorCost : OperationCost signature
  | .xor | .equiv => 1
  | .false | .true | .id | .not | .and | .or => 0

/-- Cost model charging 1 for all binary gates (`and`, `or`, `xor`, `equiv`). -/
def binaryCost : OperationCost signature
  | .and | .or | .xor | .equiv => 1
  | .false | .true | .id | .not => 0

/-- Whether an operation is in the De Morgan fragment (`false`, `true`, `id`, `not`, `and`, `or`). -/
def isDeMorgan : Op → Bool
  | .false | .true | .id | .not | .and | .or => true
  | .xor | .equiv => false

end Extended

end KW
end Algebraic
