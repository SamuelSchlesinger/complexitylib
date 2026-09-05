/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Shift.Defs

/-!
# Relocating raw circuit fragments -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace RawGate

theorem eval_shift_internal (offset : Nat) (gate : RawGate)
    (value₀ value₁ : Bool) :
    (gate.shift offset).eval value₀ value₁ = gate.eval value₀ value₁ := by
  rfl

theorem wellFormedAt_shift_iff_internal (offset available : Nat)
    (gate : RawGate) :
    (gate.shift offset).WellFormedAt (offset + available) ↔
      gate.WellFormedAt available := by
  simp [shift, WellFormedAt]

end RawGate

namespace RawCircuit

theorem length_shift_internal (offset : Nat) (circuit : RawCircuit) :
    (circuit.shift offset).length = circuit.length := by
  simp [shift]

theorem topologicallyWellFormed_shift_iff_internal
    (offset available : Nat) (circuit : RawCircuit) :
    (circuit.shift offset).TopologicallyWellFormed (offset + available) ↔
      circuit.TopologicallyWellFormed available := by
  constructor
  · intro h index
    have hshifted := h ⟨index.val, by
      rw [length_shift_internal]
      exact index.isLt⟩
    simp only [List.get_eq_getElem] at hshifted ⊢
    simpa [shift, RawGate.shift, RawGate.WellFormedAt, Nat.add_assoc]
      using hshifted
  · intro h index
    have hlength := length_shift_internal offset circuit
    have hindex : index.val < circuit.length := by
      have := index.isLt
      omega
    have hlocal := h ⟨index.val, hindex⟩
    simp only [List.get_eq_getElem] at hlocal ⊢
    simpa [shift, RawGate.shift, RawGate.WellFormedAt, Nat.add_assoc]
      using hlocal

private theorem getElem?_append_offset {offset index : Nat}
    (leading wires : Array Bool) (hleading : leading.size = offset) :
    (leading ++ wires)[offset + index]? = wires[index]? := by
  rw [Array.getElem?_append, ite_eq_right]
  · rw [hleading, Nat.add_sub_cancel_left]
  · rw [hleading]
    omega

theorem evalAux?_shift_internal (offset : Nat) (circuit : RawCircuit)
    (leading wires : Array Bool) (hleading : leading.size = offset) :
    evalAux? (circuit.shift offset) (leading ++ wires) =
      (evalAux? circuit wires).map fun result => leading ++ result := by
  induction circuit generalizing wires with
  | nil => rfl
  | cons gate gates ih =>
      simp only [shift, List.map_cons, evalAux?, RawGate.shift]
      rw [getElem?_append_offset leading wires hleading,
        getElem?_append_offset leading wires hleading]
      cases hvalue₀ : wires[gate.input₀]? with
      | none => rfl
      | some value₀ =>
          cases hvalue₁ : wires[gate.input₁]? with
          | none => rfl
          | some value₁ =>
              have hgateEval :
                  ({ op := gate.op
                     input₀ := offset + gate.input₀
                     input₁ := offset + gate.input₁
                     negated₀ := gate.negated₀
                     negated₁ := gate.negated₁ : RawGate }).eval value₀ value₁ =
                    gate.eval value₀ value₁ := by
                rfl
              change
                evalAux? (List.map (RawGate.shift offset) gates)
                    ((leading ++ wires).push
                      (({ op := gate.op
                          input₀ := offset + gate.input₀
                          input₁ := offset + gate.input₁
                          negated₀ := gate.negated₀
                          negated₁ := gate.negated₁ : RawGate }).eval value₀ value₁)) =
                  (evalAux? gates (wires.push (gate.eval value₀ value₁))).map
                    fun result => leading ++ result
              rw [hgateEval]
              rw [Array.push_append]
              exact ih (wires.push (gate.eval value₀ value₁))

end RawCircuit

end CircuitCode

end Complexity
