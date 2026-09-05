/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Gate.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Lookup
import Complexitylib.Circuits.Encoding.FixedWidth.Validity.Internal

/-!
# Fixed-width encoded-gate evaluation formulas -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace GateFormula

theorem eval_negateIf_internal (flag value : BoolFormula)
    (assignment : Nat → Bool) :
    (negateIf flag value).eval assignment =
      (flag.eval assignment).xor (value.eval assignment) := by
  simp only [negateIf, BoolFormula.eval]
  cases flag.eval assignment <;> cases value.eval assignment <;> rfl

theorem size_negateIf_internal (flag value : BoolFormula) :
    (negateIf flag value).size =
      2 * flag.size + 2 * value.size + 4 := by
  simp only [negateIf, BoolFormula.size]
  omega

theorem vars_negateIf_lt_internal (flag value : BoolFormula)
    (available : Nat)
    (hflag : ∀ wire ∈ flag.vars, wire < available)
    (hvalue : ∀ wire ∈ value.vars, wire < available) :
    ∀ wire ∈ (negateIf flag value).vars, wire < available := by
  intro wire hwire
  simp only [negateIf, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with (hwire | hwire) | (hwire | hwire)
  · exact hflag wire hwire
  · exact hvalue wire hwire
  · exact hflag wire hwire
  · exact hvalue wire hwire

theorem eval_applyOperation_internal (operation left right : BoolFormula)
    (assignment : Nat → Bool) :
    (applyOperation operation left right).eval assignment =
      match operation.eval assignment with
      | true => left.eval assignment && right.eval assignment
      | false => left.eval assignment || right.eval assignment := by
  simp only [applyOperation, BoolFormula.eval]
  cases operation.eval assignment <;>
    cases left.eval assignment <;>
    cases right.eval assignment <;> rfl

theorem size_applyOperation_internal (operation left right : BoolFormula) :
    (applyOperation operation left right).size =
      operation.size + 2 * left.size + 2 * right.size + 5 := by
  simp only [applyOperation, BoolFormula.size]
  omega

theorem vars_applyOperation_lt_internal (operation left right : BoolFormula)
    (available : Nat)
    (hoperation : ∀ wire ∈ operation.vars, wire < available)
    (hleft : ∀ wire ∈ left.vars, wire < available)
    (hright : ∀ wire ∈ right.vars, wire < available) :
    ∀ wire ∈ (applyOperation operation left right).vars,
      wire < available := by
  intro wire hwire
  simp only [applyOperation, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with (hwire | hwire) | (hwire | (hwire | hwire))
  · exact hleft wire hwire
  · exact hright wire hwire
  · exact hoperation wire hwire
  · exact hleft wire hwire
  · exact hright wire hwire

private theorem eval_slotBit_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (coordinate : Fin (gateSlotWidth inputWidth gateBound))
    (assignment : Nat → Bool) :
    (ValidityFormula.slotBit inputWidth gateBound slot coordinate).eval
        assignment =
      slotBits (codeOfAssignment inputWidth gateBound assignment) slot
        coordinate := by
  simp only [ValidityFormula.slotBit, BoolFormula.eval]
  exact ValidityFormula.code_apply_slotCoordinate_internal
    (codeOfAssignment inputWidth gateBound assignment) slot coordinate

private theorem eval_operationBit_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (assignment : Nat → Bool) :
    (operationBit inputWidth gateBound slot).eval assignment =
      (decodedSlot inputWidth gateBound slot assignment).op := by
  rw [operationBit, eval_slotBit_internal]
  simp [decodedSlot, GateSlot.decode, Fin.appendEquiv]
  apply congrArg
  apply Fin.ext
  rfl

private theorem eval_negated0Bit_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (assignment : Nat → Bool) :
    (negated0Bit inputWidth gateBound slot).eval assignment =
      (decodedSlot inputWidth gateBound slot assignment).negated0 := by
  rw [negated0Bit, eval_slotBit_internal]
  simp [decodedSlot, GateSlot.decode, Fin.appendEquiv]
  apply congrArg
  apply Fin.ext
  rfl

private theorem eval_negated1Bit_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (assignment : Nat → Bool) :
    (negated1Bit inputWidth gateBound slot).eval assignment =
      (decodedSlot inputWidth gateBound slot assignment).negated1 := by
  rw [negated1Bit, eval_slotBit_internal]
  simp [decodedSlot, GateSlot.decode, Fin.appendEquiv]
  apply congrArg
  apply Fin.ext
  rfl

private theorem evaluated_input0_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (assignment : Nat → Bool) :
    LookupFormula.evaluatedWord
        (ValidityFormula.input0Bit inputWidth gateBound slot) assignment =
      (decodedSlot inputWidth gateBound slot assignment).input0 := by
  funext coordinate
  simp only [LookupFormula.evaluatedWord, ValidityFormula.input0Bit]
  rw [eval_slotBit_internal]
  exact (ValidityFormula.decode_input0_internal
    (slotBits (codeOfAssignment inputWidth gateBound assignment) slot)
    coordinate).symm

private theorem evaluated_input1_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (assignment : Nat → Bool) :
    LookupFormula.evaluatedWord
        (ValidityFormula.input1Bit inputWidth gateBound slot) assignment =
      (decodedSlot inputWidth gateBound slot assignment).input1 := by
  funext coordinate
  simp only [LookupFormula.evaluatedWord, ValidityFormula.input1Bit]
  rw [eval_slotBit_internal]
  exact (ValidityFormula.decode_input1_internal
    (slotBits (codeOfAssignment inputWidth gateBound assignment) slot)
    coordinate).symm

private theorem sourceCount_le_capacity {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    inputWidth + slot.val ≤
      2 ^ referenceWidth inputWidth gateBound := by
  apply le_trans _
    (inputWidth_add_gateBound_le_two_pow_referenceWidth
      inputWidth gateBound)
  exact Nat.add_le_add_left (Nat.le_of_lt slot.isLt) inputWidth

private theorem eval_selected0_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (assignment : Nat → Bool)
    (hinput :
      (decodedSlot inputWidth gateBound slot assignment).input0Value <
        inputWidth + slot.val) :
    (selected0 inputWidth gateBound slot sources).eval assignment =
      (sources ⟨(decodedSlot inputWidth gateBound slot assignment).input0Value,
        hinput⟩).eval assignment := by
  rw [selected0, LookupFormula.eval_select _ _ assignment
    (sourceCount_le_capacity slot), evaluated_input0_internal]
  have hvalue :
      (decodedSlot inputWidth gateBound slot assignment).input0.unsignedValue <
        inputWidth + slot.val := by
    simpa [GateSlot.input0Value, BitString.unsignedValue] using hinput
  rw [dite_eq_left hvalue]
  rfl

private theorem eval_selected1_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (assignment : Nat → Bool)
    (hinput :
      (decodedSlot inputWidth gateBound slot assignment).input1Value <
        inputWidth + slot.val) :
    (selected1 inputWidth gateBound slot sources).eval assignment =
      (sources ⟨(decodedSlot inputWidth gateBound slot assignment).input1Value,
        hinput⟩).eval assignment := by
  rw [selected1, LookupFormula.eval_select _ _ assignment
    (sourceCount_le_capacity slot), evaluated_input1_internal]
  have hvalue :
      (decodedSlot inputWidth gateBound slot assignment).input1.unsignedValue <
        inputWidth + slot.val := by
    simpa [GateSlot.input1Value, BitString.unsignedValue] using hinput
  rw [dite_eq_left hvalue]
  rfl

theorem eval_gate_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (assignment : Nat → Bool)
    (hslot :
      (decodedSlot inputWidth gateBound slot assignment).WellFormedAt
        (inputWidth + slot.val)) :
    (gate inputWidth gateBound slot sources).eval assignment =
      (decodedSlot inputWidth gateBound slot assignment).toRawGate.eval
        ((sources ⟨(decodedSlot inputWidth gateBound slot assignment).input0Value,
          hslot.1⟩).eval assignment)
        ((sources ⟨(decodedSlot inputWidth gateBound slot assignment).input1Value,
          hslot.2⟩).eval assignment) := by
  rw [gate, eval_applyOperation_internal,
    eval_negateIf_internal, eval_negateIf_internal,
    eval_operationBit_internal, eval_negated0Bit_internal,
    eval_negated1Bit_internal,
    eval_selected0_internal slot sources assignment hslot.1,
    eval_selected1_internal slot sources assignment hslot.2]
  unfold GateSlot.toRawGate RawGate.eval
  cases (decodedSlot inputWidth gateBound slot assignment).op <;> rfl

theorem size_gate_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (hsources : ∀ source, (sources source).size = 1) :
    (gate inputWidth gateBound slot sources).size =
      gateSize inputWidth gateBound slot := by
  have hselected0 :
      (selected0 inputWidth gateBound slot sources).size =
        LookupFormula.selectSize
          (referenceWidth inputWidth gateBound)
          (inputWidth + slot.val) := by
    rw [selected0]
    apply LookupFormula.size_select
    · intro coordinate
      rfl
    · exact hsources
  have hselected1 :
      (selected1 inputWidth gateBound slot sources).size =
        LookupFormula.selectSize
          (referenceWidth inputWidth gateBound)
          (inputWidth + slot.val) := by
    rw [selected1]
    apply LookupFormula.size_select
    · intro coordinate
      rfl
    · exact hsources
  simp only [gate, size_applyOperation_internal,
    size_negateIf_internal, hselected0, hselected1,
    operationBit, negated0Bit, negated1Bit,
    ValidityFormula.slotBit, BoolFormula.size, gateSize]
  omega

private theorem vars_slotBit_lt_internal {inputWidth gateBound available : Nat}
    (slot : Fin gateBound)
    (coordinate : Fin (gateSlotWidth inputWidth gateBound))
    (hcode : codeWidth inputWidth gateBound ≤ available) :
    ∀ wire ∈
      (ValidityFormula.slotBit inputWidth gateBound slot coordinate).vars,
      wire < available := by
  intro wire hwire
  simp only [ValidityFormula.slotBit, BoolFormula.vars,
    Finset.mem_singleton] at hwire
  subst wire
  exact lt_of_lt_of_le
    (ValidityFormula.slotCoordinate inputWidth gateBound slot coordinate).isLt
    hcode

private theorem vars_operationBit_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (hcode : codeWidth inputWidth gateBound ≤ available) :
    ∀ wire ∈ (operationBit inputWidth gateBound slot).vars,
      wire < available := by
  unfold operationBit
  exact vars_slotBit_lt_internal slot _ hcode

private theorem vars_negated0Bit_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (hcode : codeWidth inputWidth gateBound ≤ available) :
    ∀ wire ∈ (negated0Bit inputWidth gateBound slot).vars,
      wire < available := by
  unfold negated0Bit
  exact vars_slotBit_lt_internal slot _ hcode

private theorem vars_negated1Bit_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (hcode : codeWidth inputWidth gateBound ≤ available) :
    ∀ wire ∈ (negated1Bit inputWidth gateBound slot).vars,
      wire < available := by
  unfold negated1Bit
  exact vars_slotBit_lt_internal slot _ hcode

private theorem vars_input0Bit_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (hcode : codeWidth inputWidth gateBound ≤ available) :
    ∀ coordinate wire,
      wire ∈
        (ValidityFormula.input0Bit inputWidth gateBound slot coordinate).vars →
      wire < available := by
  intro coordinate
  unfold ValidityFormula.input0Bit
  exact vars_slotBit_lt_internal slot _ hcode

private theorem vars_input1Bit_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (hcode : codeWidth inputWidth gateBound ≤ available) :
    ∀ coordinate wire,
      wire ∈
        (ValidityFormula.input1Bit inputWidth gateBound slot coordinate).vars →
      wire < available := by
  intro coordinate
  unfold ValidityFormula.input1Bit
  exact vars_slotBit_lt_internal slot _ hcode

private theorem vars_selected0_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (hcode : codeWidth inputWidth gateBound ≤ available)
    (hsources : ∀ source wire,
      wire ∈ (sources source).vars → wire < available) :
    ∀ wire ∈ (selected0 inputWidth gateBound slot sources).vars,
      wire < available := by
  unfold selected0
  exact LookupFormula.vars_select_lt _ _
    (vars_input0Bit_lt_internal slot hcode) hsources

private theorem vars_selected1_lt_internal
    {inputWidth gateBound available : Nat} (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (hcode : codeWidth inputWidth gateBound ≤ available)
    (hsources : ∀ source wire,
      wire ∈ (sources source).vars → wire < available) :
    ∀ wire ∈ (selected1 inputWidth gateBound slot sources).vars,
      wire < available := by
  unfold selected1
  exact LookupFormula.vars_select_lt _ _
    (vars_input1Bit_lt_internal slot hcode) hsources

theorem vars_gate_lt_internal {inputWidth gateBound available : Nat}
    (slot : Fin gateBound)
    (sources : Fin (inputWidth + slot.val) → BoolFormula)
    (hcode : codeWidth inputWidth gateBound ≤ available)
    (hsources : ∀ source wire,
      wire ∈ (sources source).vars → wire < available) :
    ∀ wire ∈ (gate inputWidth gateBound slot sources).vars,
      wire < available := by
  unfold gate
  apply vars_applyOperation_lt_internal
  · exact vars_operationBit_lt_internal slot hcode
  · apply vars_negateIf_lt_internal
    · exact vars_negated0Bit_lt_internal slot hcode
    · exact vars_selected0_lt_internal slot sources hcode hsources
  · apply vars_negateIf_lt_internal
    · exact vars_negated1Bit_lt_internal slot hcode
    · exact vars_selected1_lt_internal slot sources hcode hsources

end GateFormula

end Description

end FixedWidth

end CircuitCode

end Complexity
