/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Defs
import Complexitylib.Circuits.Encoding.FixedWidth

/-!
# Conversion between raw circuits and fixed-width descriptions -- internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace GateSlot

theorem toList_referenceBits_internal (width value : Nat) :
    (referenceBits width value).toList = Nat.toBitsLE width value := by
  simp [referenceBits]

theorem referenceBits_fromBitsLE_internal {width : Nat}
    (bits : BitString width) :
    referenceBits width (Nat.fromBitsLE bits.toList) = bits := by
  apply BitString.toList_inj.mp
  rw [toList_referenceBits_internal]
  simpa only [BitString.length_toList] using
    Nat.toBitsLE_fromBitsLE bits.toList

theorem input0Value_ofRawGate_internal (width : Nat) (gate : RawGate) :
    (ofRawGate width gate).input0Value = gate.input₀ % 2 ^ width := by
  simp only [ofRawGate, input0Value]
  rw [toList_referenceBits_internal, Nat.fromBitsLE_toBitsLE_mod]

theorem input1Value_ofRawGate_internal (width : Nat) (gate : RawGate) :
    (ofRawGate width gate).input1Value = gate.input₁ % 2 ^ width := by
  simp only [ofRawGate, input1Value]
  rw [toList_referenceBits_internal, Nat.fromBitsLE_toBitsLE_mod]

theorem toRawGate_ofRawGate_internal {width : Nat} {gate : RawGate}
    (hinput0 : gate.input₀ < 2 ^ width)
    (hinput1 : gate.input₁ < 2 ^ width) :
    (ofRawGate width gate).toRawGate = gate := by
  have hvalue0 : (ofRawGate width gate).input0Value = gate.input₀ := by
    rw [input0Value_ofRawGate_internal, Nat.mod_eq_of_lt hinput0]
  have hvalue1 : (ofRawGate width gate).input1Value = gate.input₁ := by
    rw [input1Value_ofRawGate_internal, Nat.mod_eq_of_lt hinput1]
  change RawGate.mk (RawGate.opOfBit gate.opBit)
    (ofRawGate width gate).input0Value
    (ofRawGate width gate).input1Value gate.negated₀ gate.negated₁ = gate
  cases gate with
  | mk op input0 input1 negated0 negated1 =>
      rw [RawGate.mk.injEq]
      refine ⟨?_, hvalue0, hvalue1, rfl, rfl⟩
      cases op <;> rfl

theorem ofRawGate_toRawGate_internal {width : Nat}
    (slot : GateSlot width) :
    ofRawGate width slot.toRawGate = slot := by
  cases slot with
  | mk op negated0 negated1 input0 input1 =>
      cases op <;>
        simp [ofRawGate, toRawGate, RawGate.opBit, RawGate.opOfBit,
          input0Value, input1Value, referenceBits_fromBitsLE_internal]

end GateSlot

namespace Description

@[simp] theorem gateCountNat_ofRawCircuit_internal
    {inputWidth gateBound : Nat} (circuit : RawCircuit)
    (hbound : circuit.length ≤ gateBound) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).gateCountNat =
      circuit.length :=
  rfl

@[simp] theorem slot_ofRawCircuit_of_lt_internal
    {inputWidth gateBound : Nat} (circuit : RawCircuit)
    (hbound : circuit.length ≤ gateBound) (index : Fin gateBound)
    (hindex : index.val < circuit.length) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).slots index =
      GateSlot.ofRawGate (referenceWidth inputWidth gateBound)
        circuit[index.val] := by
  simp [ofRawCircuit, hindex]

@[simp] theorem slot_ofRawCircuit_of_le_internal
    {inputWidth gateBound : Nat} (circuit : RawCircuit)
    (hbound : circuit.length ≤ gateBound) (index : Fin gateBound)
    (hindex : circuit.length ≤ index.val) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).slots index =
      GateSlot.zero _ := by
  simp [ofRawCircuit, Nat.not_lt.mpr hindex]

private theorem rawGate_references_fit
    {inputWidth gateBound : Nat} {circuit : RawCircuit}
    (htopological : circuit.TopologicallyWellFormed inputWidth)
    (hbound : circuit.length ≤ gateBound) (index : Fin circuit.length) :
    (circuit.get index).input₀ <
        2 ^ referenceWidth inputWidth gateBound ∧
      (circuit.get index).input₁ <
        2 ^ referenceWidth inputWidth gateBound := by
  have hgate := htopological index
  have hcapacity :=
    inputWidth_add_gateBound_le_two_pow_referenceWidth inputWidth gateBound
  have hindexBound : index.val ≤ gateBound :=
    le_trans (Nat.le_of_lt index.isLt) hbound
  have havailable : inputWidth + index.val ≤ inputWidth + gateBound :=
    Nat.add_le_add_left hindexBound inputWidth
  exact ⟨lt_of_lt_of_le hgate.1 (le_trans havailable hcapacity),
    lt_of_lt_of_le hgate.2 (le_trans havailable hcapacity)⟩

theorem toRawCircuit_ofRawCircuit_internal
    {inputWidth gateBound : Nat} {circuit : RawCircuit}
    (htopological : circuit.TopologicallyWellFormed inputWidth)
    (hbound : circuit.length ≤ gateBound) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).toRawCircuit =
      circuit := by
  apply List.ext_get
  · simp
  · intro index hleft hright
    have hfit := rawGate_references_fit htopological hbound
      ⟨index, hright⟩
    simp only [toRawCircuit, List.get_ofFn, activeSlot, ofRawCircuit]
    change
      (if hindex : index < circuit.length then
        GateSlot.ofRawGate (referenceWidth inputWidth gateBound)
          circuit[index]
      else GateSlot.zero _).toRawGate = circuit[index]
    rw [dite_eq_left hright]
    exact GateSlot.toRawGate_ofRawGate_internal hfit.1 hfit.2

theorem ofRawCircuit_wellFormed_internal
    {inputWidth gateBound : Nat} {circuit : RawCircuit}
    (hcircuit : circuit.WellFormed inputWidth)
    (hbound : circuit.length ≤ gateBound) :
    (ofRawCircuit (inputWidth := inputWidth) circuit hbound).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · have hnonempty := hcircuit.1
    have hpositive : 0 < circuit.length :=
      List.length_pos_iff.mpr hnonempty
    exact hpositive
  · rw [← topologicallyWellFormed_toRawCircuit_iff]
    rw [toRawCircuit_ofRawCircuit_internal hcircuit.2 hbound]
    exact hcircuit.2
  · intro index hindex
    exact slot_ofRawCircuit_of_le_internal circuit hbound index hindex

theorem ofRawCircuit_toRawCircuit_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hcanonical : description.CanonicallyPadded) :
    ofRawCircuit description.toRawCircuit
        (by
          rw [Description.length_toRawCircuit]
          exact Description.gateCountNat_le_gateBound description) =
      description := by
  cases description with
  | mk gateCount slots =>
      rw [Description.mk.injEq]
      constructor
      · apply Fin.ext
        simp [ofRawCircuit, gateCountNat]
      · funext index
        by_cases hactive : index.val < gateCount.val
        · let active : Fin gateCount.val := ⟨index.val, hactive⟩
          have hslot := GateSlot.ofRawGate_toRawGate_internal (slots index)
          simpa [ofRawCircuit, toRawCircuit, activeSlot, gateCountNat,
            hactive, active] using hslot
        · have hpadding := hcanonical index (Nat.le_of_not_gt hactive)
          simpa [ofRawCircuit, toRawCircuit, gateCountNat, hactive]
            using hpadding.symm

end Description

/-- Internal exact equivalence between valid fixed descriptions and bounded
raw circuits. -/
@[expose] def wellFormedEquivInternal (inputWidth gateBound : Nat) :
    Equiv (ValidDescription inputWidth gateBound)
      (BoundedRawCircuit inputWidth gateBound) where
  toFun description :=
    ⟨description.val.toRawCircuit,
      description.val.wellFormed_toRawCircuit description.property,
      by simpa using description.val.gateCountNat_le_gateBound⟩
  invFun circuit :=
    ⟨Description.ofRawCircuit circuit.val circuit.property.2,
      Description.ofRawCircuit_wellFormed_internal
        circuit.property.1 circuit.property.2⟩
  left_inv description := by
    apply Subtype.ext
    exact Description.ofRawCircuit_toRawCircuit_internal
      description.property.2.2
  right_inv circuit := by
    apply Subtype.ext
    exact Description.toRawCircuit_ofRawCircuit_internal
      circuit.property.1.2 circuit.property.2

theorem wellFormedEquiv_apply_val_internal
    {inputWidth gateBound : Nat}
    (description : ValidDescription inputWidth gateBound) :
    (wellFormedEquivInternal inputWidth gateBound description).val =
      description.val.toRawCircuit :=
  rfl

theorem wellFormedEquiv_symm_val_internal
    {inputWidth gateBound : Nat}
    (circuit : BoundedRawCircuit inputWidth gateBound) :
    ((wellFormedEquivInternal inputWidth gateBound).symm circuit).val =
      Description.ofRawCircuit circuit.val circuit.property.2 :=
  rfl

end FixedWidth

end CircuitCode

end Complexity
