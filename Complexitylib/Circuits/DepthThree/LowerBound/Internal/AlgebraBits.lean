/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Logic.Equiv.Defs

/-!
# Unrestricted depth-three lower bound: algebra bits

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/AlgebraBits.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3

namespace DepthThreeLowerBound
namespace BinaryAlgebra

/-- The two-element field. -/
abbrev F2 := ZMod 2

/-- Identify Boolean bits with the two elements of the field. -/
def boolEquivF2 : Bool ≃ F2 := finTwoEquiv.symm

/-- View a Boolean bit as an element of the two-element field. -/
def bitValue (b : Bool) : F2 := boolEquivF2 b

/-- Read an element of the two-element field as a Boolean bit. -/
def fieldBit (a : F2) : Bool := boolEquivF2.symm a

@[simp] theorem bitValue_false : bitValue false = 0 := rfl

@[simp] theorem bitValue_true : bitValue true = 1 := rfl

@[simp] theorem fieldBit_zero : fieldBit 0 = false := rfl

@[simp] theorem fieldBit_one : fieldBit 1 = true := rfl

@[simp] theorem fieldBit_bitValue (b : Bool) : fieldBit (bitValue b) = b :=
  boolEquivF2.symm_apply_apply b

@[simp] theorem bitValue_fieldBit (a : F2) : bitValue (fieldBit a) = a :=
  boolEquivF2.apply_symm_apply a

theorem bitValue_injective : Function.Injective bitValue :=
  boolEquivF2.injective

theorem bitValue_surjective : Function.Surjective bitValue :=
  boolEquivF2.surjective

theorem bitValue_xor (a b : Bool) :
    bitValue (Bool.xor a b) = bitValue a + bitValue b := by
  cases a <;> cases b <;> decide

theorem bitValue_and (a b : Bool) :
    bitValue (a && b) = bitValue a * bitValue b := by
  cases a <;> cases b <;> decide

theorem bitValue_not (a : Bool) : bitValue (!a) = 1 + bitValue a := by
  cases a <;> decide

@[simp] theorem bitValue_eq_zero_iff (b : Bool) : bitValue b = 0 ↔ b = false := by
  cases b <;> decide

@[simp] theorem bitValue_eq_one_iff (b : Bool) : bitValue b = 1 ↔ b = true := by
  cases b <;> decide

theorem eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  obtain ⟨b, rfl⟩ := boolEquivF2.surjective a
  cases b <;> decide

@[simp] theorem fieldBit_eq_false_iff (a : F2) : fieldBit a = false ↔ a = 0 := by
  obtain ⟨b, rfl⟩ := boolEquivF2.surjective a
  cases b <;> decide

@[simp] theorem fieldBit_eq_true_iff (a : F2) : fieldBit a = true ↔ a = 1 := by
  obtain ⟨b, rfl⟩ := boolEquivF2.surjective a
  cases b <;> decide

/-- Coordinatewise identification of bit vectors with field vectors. -/
def bitsEquivF2 (V : Type uDepth1) : (V → Bool) ≃ (V → F2) where
  toFun x i := bitValue (x i)
  invFun x i := fieldBit (x i)
  left_inv x := funext fun i => fieldBit_bitValue (x i)
  right_inv x := funext fun i => bitValue_fieldBit (x i)

@[simp] theorem bitsEquivF2_apply (V : Type uDepth2) (x : V → Bool) (i : V) :
    bitsEquivF2 V x i = bitValue (x i) := rfl

@[simp] theorem bitsEquivF2_symm_apply (V : Type uDepth3) (x : V → F2) (i : V) :
    (bitsEquivF2 V).symm x i = fieldBit (x i) := rfl

end BinaryAlgebra
end DepthThreeLowerBound

end Complexity
