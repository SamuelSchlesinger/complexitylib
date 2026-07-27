/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Internal.Semantics
public import Complexitylib.Circuits.Encoding.ToCircuit.Defs

/-!
# Internal correctness of raw-to-typed circuit reconstruction

This proof layer shows that restoring dependent wire bounds and then erasing
them is an exact round trip. Semantic correctness is consequently inherited
from the existing typed-to-raw evaluator theorem rather than reproved.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawGate

/-- Restoring and then erasing a well-formed raw gate is the identity. -/
@[simp] theorem ofGate_toGate_internal {W : ℕ} (gate : RawGate)
    (hwell : gate.WellFormedAt W) :
    RawGate.ofGate (gate.toGate hwell) = gate := by
  obtain ⟨op, input₀, input₁, negated₀, negated₁⟩ := gate
  rfl

end RawGate

namespace RawCircuit

/-- Re-erasing a reconstructed typed circuit returns the original raw list
exactly, including its gate order and designated final output gate. -/
theorem ofCircuit_toCircuit_internal (N : ℕ) [NeZero N]
    (circuit : RawCircuit) (hwell : circuit.WellFormed N) :
    RawCircuit.ofCircuit (circuit.toCircuit N hwell) = circuit := by
  simp only [RawCircuit.ofCircuit, toCircuit, RawGate.ofGate_toGate_internal]
  have hprefix :
      (List.ofFn fun i : Fin (circuit.length - 1) =>
        circuit.get ⟨i.val, by omega⟩) = circuit.dropLast := by
    apply List.ext_getElem
    · simp
    · intro i hleft hright
      simp only [List.getElem_ofFn]
      exact (List.getElem_dropLast hright).symm
  have hlast :
      circuit.get ⟨circuit.length - 1, by
        have hpos : circuit.length ≠ 0 := by
          intro hzero
          exact hwell.1 (List.eq_nil_of_length_eq_zero hzero)
        omega⟩ = circuit.getLast hwell.1 :=
    List.get_length_sub_one _
  calc
    _ = circuit.dropLast ++ [circuit.getLast hwell.1] := by
      rw [hprefix, hlast]
    _ = circuit := List.dropLast_append_getLast hwell.1

/-- Raw iterative evaluation agrees exactly with evaluation of the
reconstructed typed circuit. -/
theorem eval?_toCircuit_internal (N : ℕ) [NeZero N]
    (circuit : RawCircuit) (hwell : circuit.WellFormed N)
    (input : BitString N) :
    circuit.eval? input.toList =
      some (((circuit.toCircuit N hwell).eval input) 0) := by
  have hraw := congrArg (fun raw : RawCircuit => raw.eval? input.toList)
    (ofCircuit_toCircuit_internal N circuit hwell)
  calc
    circuit.eval? input.toList =
        (RawCircuit.ofCircuit (circuit.toCircuit N hwell)).eval? input.toList :=
      hraw.symm
    _ = some (((circuit.toCircuit N hwell).eval input) 0) :=
      RawCircuit.eval?_ofCircuit (circuit.toCircuit N hwell) input

/-- Reconstruction preserves the raw gate count under the library's circuit
size convention, which counts internal and output gates. -/
theorem size_toCircuit_internal (N : ℕ) [NeZero N]
    (circuit : RawCircuit) (hwell : circuit.WellFormed N) :
    (circuit.toCircuit N hwell).size = circuit.length := by
  simp only [Circuit.size]
  have hpos : circuit.length ≠ 0 := by
    intro hzero
    exact hwell.1 (List.eq_nil_of_length_eq_zero hzero)
  omega

end RawCircuit

end CircuitCode

end Complexity
