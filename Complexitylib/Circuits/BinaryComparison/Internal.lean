/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison.Defs
import Complexitylib.Circuits.Encoding.Formula.Internal

/-!
# Little-endian binary comparison -- proof internals
-/


public section

namespace Complexity

private theorem fromBitsLE_concat (bits : List Bool) (bit : Bool) :
    Nat.fromBitsLE (bits.concat bit) =
      Nat.fromBitsLE bits + if bit then 2 ^ bits.length else 0 := by
  cases bit with
  | false => simp [Nat.fromBitsLE, Nat.fromBits]
  | true =>
      simp [Nat.fromBitsLE, Nat.fromBits]
      omega

namespace BitString

theorem unsignedLE_eq_decide_internal {width : ℕ}
    (left right : BitString width) :
    unsignedLE left right =
      decide (left.unsignedValue ≤ right.unsignedValue) := by
  induction width with
  | zero =>
      simp [unsignedLE, unsignedValue, BitString.toList,
        Nat.fromBitsLE, Nat.fromBits]
  | succ width ih =>
      let leftLow : BitString width := fun i => left i.castSucc
      let rightLow : BitString width := fun i => right i.castSucc
      have hleftBound : leftLow.unsignedValue < 2 ^ width := by
        unfold unsignedValue
        simpa using Nat.fromBitsLE_lt_pow_length leftLow.toList
      have hrightBound : rightLow.unsignedValue < 2 ^ width := by
        unfold unsignedValue
        simpa using Nat.fromBitsLE_lt_pow_length rightLow.toList
      change Nat.fromBitsLE leftLow.toList < 2 ^ width at hleftBound
      change Nat.fromBitsLE rightLow.toList < 2 ^ width at hrightBound
      have hleftList : left.toList = leftLow.toList.concat (left (Fin.last width)) := by
        simpa [leftLow, BitString.toList] using List.ofFn_succ' left
      have hrightList : right.toList =
          rightLow.toList.concat (right (Fin.last width)) := by
        simpa [rightLow, BitString.toList] using List.ofFn_succ' right
      rw [unsignedValue, unsignedValue, hleftList, hrightList,
        fromBitsLE_concat, fromBitsLE_concat]
      change
        ((!left (Fin.last width) && right (Fin.last width)) ||
          ((left (Fin.last width) == right (Fin.last width)) &&
            unsignedLE leftLow rightLow)) = _
      rw [ih leftLow rightLow]
      cases hleft : left (Fin.last width) <;>
        cases hright : right (Fin.last width)
      · simp [BitString.unsignedValue]
        rfl
      · simp [BitString.unsignedValue]
        omega
      · simp [BitString.unsignedValue]
        omega
      · simp [BitString.unsignedValue]
        rfl

end BitString

namespace BoolFormula

theorem eval_ofBool_internal (value : Bool)
    (assignment : ℕ → Bool) :
    (ofBool value).eval assignment = value := by
  cases value <;> rfl

@[simp] theorem size_ofBool_internal (value : Bool) :
    (ofBool value).size = 1 := by
  cases value <;> rfl

theorem eval_unsignedLEOf_internal : ∀ {width : ℕ}
    (left right : Fin width → BoolFormula) (assignment : ℕ → Bool),
    (unsignedLEOf left right).eval assignment =
      BitString.unsignedLE
        (fun i => (left i).eval assignment)
        (fun i => (right i).eval assignment) := by
  intro width
  induction width with
  | zero =>
      intro left right assignment
      rfl
  | succ width ih =>
      intro left right assignment
      simp only [unsignedLEOf, BoolFormula.eval]
      rw [ih (fun i => left i.castSucc)
        (fun i => right i.castSucc) assignment]
      change
        ((!(left (Fin.last width)).eval assignment &&
            (right (Fin.last width)).eval assignment) ||
          ((((left (Fin.last width)).eval assignment &&
              (right (Fin.last width)).eval assignment) ||
            (!(left (Fin.last width)).eval assignment &&
              !(right (Fin.last width)).eval assignment)) &&
            BitString.unsignedLE
              (fun i => (left i.castSucc).eval assignment)
              (fun i => (right i.castSucc).eval assignment))) =
          ((!(left (Fin.last width)).eval assignment &&
              (right (Fin.last width)).eval assignment) ||
            (((left (Fin.last width)).eval assignment ==
                (right (Fin.last width)).eval assignment) &&
              BitString.unsignedLE
                (fun i => (left i.castSucc).eval assignment)
                (fun i => (right i.castSucc).eval assignment)))
      cases (left (Fin.last width)).eval assignment <;>
        cases (right (Fin.last width)).eval assignment <;> rfl

theorem size_unsignedLEOf_internal : ∀ {width : ℕ}
    (left right : Fin width → BoolFormula),
    (∀ i, (left i).size = 1) →
    (∀ i, (right i).size = 1) →
    (unsignedLEOf left right).size = 15 * width + 1 := by
  intro width
  induction width with
  | zero =>
      intro left right hleft hright
      rfl
  | succ width ih =>
      intro left right hleft hright
      have htail := ih (fun i => left i.castSucc)
        (fun i => right i.castSucc)
        (fun i => hleft i.castSucc) (fun i => hright i.castSucc)
      simp only [unsignedLEOf, BoolFormula.size,
        hleft (Fin.last width), hright (Fin.last width), htail]
      omega

theorem vars_unsignedLEOf_lt_internal : ∀ {width : ℕ}
    (left right : Fin width → BoolFormula) (available : ℕ),
    (∀ i j, j ∈ (left i).vars → j < available) →
    (∀ i j, j ∈ (right i).vars → j < available) →
    ∀ j ∈ (unsignedLEOf left right).vars, j < available := by
  intro width
  induction width with
  | zero =>
      intro left right available hleft hright j hj
      simp [unsignedLEOf, BoolFormula.vars] at hj
  | succ width ih =>
      intro left right available hleft hright j hj
      simp only [unsignedLEOf, BoolFormula.vars, Finset.mem_union] at hj
      rcases hj with (hj | hj) | (((hj | hj) | (hj | hj)) | hj)
      · exact hleft (Fin.last width) j hj
      · exact hright (Fin.last width) j hj
      · exact hleft (Fin.last width) j hj
      · exact hright (Fin.last width) j hj
      · exact hleft (Fin.last width) j hj
      · exact hright (Fin.last width) j hj
      · exact ih (fun i => left i.castSucc)
          (fun i => right i.castSucc) available
          (fun i => hleft i.castSucc) (fun i => hright i.castSucc) j hj

theorem eval_unsignedLELeftConstant_internal {width : ℕ}
    (left : BitString width) (rightBase : ℕ)
    (assignment : ℕ → Bool) :
    (unsignedLELeftConstant left rightBase).eval assignment =
      decide (left.unsignedValue ≤
        BitString.unsignedValue
          (fun i : Fin width => assignment (rightBase + i.val))) := by
  rw [unsignedLELeftConstant, eval_unsignedLEOf_internal,
    BitString.unsignedLE_eq_decide_internal]
  simp only [eval_ofBool_internal, BoolFormula.eval]

theorem eval_unsignedLERightConstant_internal {width : ℕ}
    (leftBase : ℕ) (right : BitString width)
    (assignment : ℕ → Bool) :
    (unsignedLERightConstant leftBase right).eval assignment =
      decide (BitString.unsignedValue
          (fun i : Fin width => assignment (leftBase + i.val)) ≤
        right.unsignedValue) := by
  rw [unsignedLERightConstant, eval_unsignedLEOf_internal,
    BitString.unsignedLE_eq_decide_internal]
  simp only [eval_ofBool_internal, BoolFormula.eval]

theorem size_unsignedLELeftConstant_internal {width : ℕ}
    (left : BitString width) (rightBase : ℕ) :
    (unsignedLELeftConstant left rightBase).size = 15 * width + 1 := by
  apply size_unsignedLEOf_internal
  · intro i
    exact size_ofBool_internal (left i)
  · intro i
    rfl

theorem size_unsignedLERightConstant_internal {width : ℕ}
    (leftBase : ℕ) (right : BitString width) :
    (unsignedLERightConstant leftBase right).size = 15 * width + 1 := by
  apply size_unsignedLEOf_internal
  · intro i
    rfl
  · intro i
    exact size_ofBool_internal (right i)

theorem vars_unsignedLELeftConstant_lt_internal {width : ℕ}
    (left : BitString width) (rightBase available : ℕ)
    (hright : rightBase + width ≤ available) :
    ∀ j ∈ (unsignedLELeftConstant left rightBase).vars, j < available := by
  apply vars_unsignedLEOf_lt_internal
  · intro i j hj
    cases hbit : left i <;> simp [ofBool, hbit, BoolFormula.vars] at hj
  · intro i j hj
    simp only [BoolFormula.vars, Finset.mem_singleton] at hj
    omega

theorem vars_unsignedLERightConstant_lt_internal {width : ℕ}
    (leftBase : ℕ) (right : BitString width) (available : ℕ)
    (hleft : leftBase + width ≤ available) :
    ∀ j ∈ (unsignedLERightConstant leftBase right).vars, j < available := by
  apply vars_unsignedLEOf_lt_internal
  · intro i j hj
    simp only [BoolFormula.vars, Finset.mem_singleton] at hj
    omega
  · intro i j hj
    cases hbit : right i <;> simp [ofBool, hbit, BoolFormula.vars] at hj

theorem size_unsignedLEAux_internal (width leftBase rightBase : ℕ) :
    (unsignedLEAux width leftBase rightBase).size = 15 * width + 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      simp only [unsignedLEAux, BoolFormula.size, ih]
      omega

theorem size_unsignedLE_internal (width : ℕ) :
    (unsignedLE width).size = 15 * width + 1 :=
  size_unsignedLEAux_internal width 0 width

theorem eval_unsignedLEAux_internal (width leftBase rightBase : ℕ)
    (assignment : ℕ → Bool) (left right : BitString width)
    (hleft : ∀ i, assignment (leftBase + i.val) = left i)
    (hright : ∀ i, assignment (rightBase + i.val) = right i) :
    (unsignedLEAux width leftBase rightBase).eval assignment =
      BitString.unsignedLE left right := by
  induction width with
  | zero => rfl
  | succ width ih =>
      let leftLow : BitString width := fun i => left i.castSucc
      let rightLow : BitString width := fun i => right i.castSucc
      have hleftHigh := hleft (Fin.last width)
      have hrightHigh := hright (Fin.last width)
      have hleftHigh' :
          assignment (leftBase + width) = left (Fin.last width) := by
        simpa using hleftHigh
      have hrightHigh' :
          assignment (rightBase + width) = right (Fin.last width) := by
        simpa using hrightHigh
      have hlow := ih leftLow rightLow
        (fun i => hleft i.castSucc) (fun i => hright i.castSucc)
      simp only [unsignedLEAux, BoolFormula.eval]
      change
        ((!assignment (leftBase + width) &&
            assignment (rightBase + width)) ||
          (((assignment (leftBase + width) &&
              assignment (rightBase + width)) ||
            (!assignment (leftBase + width) &&
              !assignment (rightBase + width))) &&
            (unsignedLEAux width leftBase rightBase).eval assignment)) = _
      rw [hleftHigh', hrightHigh', hlow]
      change
        ((!left (Fin.last width) && right (Fin.last width)) ||
          (((left (Fin.last width) && right (Fin.last width)) ||
            (!left (Fin.last width) && !right (Fin.last width))) &&
            BitString.unsignedLE leftLow rightLow)) =
          ((!left (Fin.last width) && right (Fin.last width)) ||
            ((left (Fin.last width) == right (Fin.last width)) &&
              BitString.unsignedLE leftLow rightLow))
      cases left (Fin.last width) <;> cases right (Fin.last width) <;>
        rfl

theorem eval_unsignedLE_internal (width : ℕ)
    (left right : BitString width) :
    (unsignedLE width).eval
        (BitString.toTotal (Fin.append left right)) =
      decide (left.unsignedValue ≤ right.unsignedValue) := by
  rw [unsignedLE]
  rw [eval_unsignedLEAux_internal width 0 width
    (BitString.toTotal (Fin.append left right)) left right]
  · exact BitString.unsignedLE_eq_decide_internal left right
  · intro i
    simp only [Nat.zero_add]
    rw [BitString.toTotal_of_lt _ i.val (by omega)]
    have hindex :
        (⟨i.val, by omega⟩ : Fin (width + width)) =
          Fin.castAdd width i := by
      apply Fin.ext
      rfl
    rw [hindex, Fin.append_left]
  · intro i
    rw [BitString.toTotal_of_lt _ (width + i.val) (by omega)]
    have hindex :
        (⟨width + i.val, by omega⟩ : Fin (width + width)) =
          Fin.natAdd width i := by
      apply Fin.ext
      rfl
    rw [hindex, Fin.append_right]

theorem vars_unsignedLEAux_lt_internal (width leftBase rightBase available : ℕ)
    (hleft : leftBase + width ≤ available)
    (hright : rightBase + width ≤ available) :
    ∀ i ∈ (unsignedLEAux width leftBase rightBase).vars, i < available := by
  induction width with
  | zero =>
      simp [unsignedLEAux, BoolFormula.vars]
  | succ width ih =>
      intro i hi
      simp only [unsignedLEAux, BoolFormula.vars, Finset.mem_union,
        Finset.mem_singleton] at hi
      rcases hi with (hi | hi) | (((hi | hi) | (hi | hi)) | hi)
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact ih (by omega) (by omega) i hi

theorem vars_unsignedLE_lt_internal (width : ℕ) :
    ∀ i ∈ (unsignedLE width).vars, i < width + width := by
  rw [unsignedLE]
  exact vars_unsignedLEAux_lt_internal width 0 width (width + width)
    (by omega) (by omega)

end BoolFormula

namespace CircuitCode

theorem length_unsignedLERawCircuit_internal (width : ℕ) :
    (unsignedLERawCircuit width).length = 15 * width + 1 := by
  rw [unsignedLERawCircuit, BoolFormula.length_compileRaw_internal,
    BoolFormula.size_unsignedLE_internal]

theorem unsignedLERawCircuit_wellFormed_internal (width : ℕ)
    [NeZero width] :
    (unsignedLERawCircuit width).WellFormed (width + width) := by
  have hwidth := NeZero.ne width
  let : NeZero (width + width) := ⟨by omega⟩
  constructor
  · intro hempty
    have hlength := length_unsignedLERawCircuit_internal width
    rw [hempty] at hlength
    simp at hlength
  · apply BoolFormula.topologicallyWellFormed_compileRaw_internal
    exact BoolFormula.vars_unsignedLE_lt_internal width

theorem eval?_unsignedLERawCircuit_internal (width : ℕ) [NeZero width]
    (left right : BitString width) :
    (unsignedLERawCircuit width).eval?
        (BitString.toList (Fin.append left right)) =
      some (decide (left.unsignedValue ≤ right.unsignedValue)) := by
  have hwidth := NeZero.ne width
  let : NeZero (width + width) := ⟨by omega⟩
  let input := Fin.append left right
  let wires := (BitString.toList input).toArray
  have hwiresSize : wires.size = width + width := by
    simp [wires, input]
  have hwiresInput : ∀ i < width + width,
      wires[i]? = some (BitString.toTotal input i) := by
    intro i hi
    simp [wires, BitString.toList, BitString.toTotal, hi]
  obtain ⟨result, heval, _hresultSize, _hprefix, houtput⟩ :=
    BoolFormula.evalAux?_compileRaw_internal (width + width)
      (BoolFormula.unsignedLE width) (BitString.toTotal input) wires
      hwiresSize hwiresInput (BoolFormula.vars_unsignedLE_lt_internal width)
  have heval' :
      RawCircuit.evalAux? (unsignedLERawCircuit width)
          (BitString.toList (Fin.append left right)).toArray = some result := by
    simpa [unsignedLERawCircuit, wires, input] using heval
  have hwell := unsignedLERawCircuit_wellFormed_internal width
  have hnonempty : (unsignedLERawCircuit width).isEmpty = false := by
    cases hraw : unsignedLERawCircuit width with
    | nil => exact (hwell.1 hraw).elim
    | cons gate gates => rfl
  have houtputIndex :
      (BitString.toList input).length +
          (unsignedLERawCircuit width).length - 1 =
        BoolFormula.rawOutputWire (width + width)
          (BoolFormula.unsignedLE width) := by
    simp [BoolFormula.rawOutputWire, length_unsignedLERawCircuit_internal,
      BoolFormula.size_unsignedLE_internal]
  rw [RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false, heval']
  rw [houtputIndex]
  change result[BoolFormula.rawOutputWire (width + width)
      (BoolFormula.unsignedLE width)]? =
    some (decide (left.unsignedValue ≤ right.unsignedValue))
  rw [houtput]
  simpa [input] using congrArg some
    (BoolFormula.eval_unsignedLE_internal width left right)

end CircuitCode

end Complexity
