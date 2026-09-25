/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.CircuitRestriction
public import Complexitylib.Algebraic.Basis.DeMorgan.Dependency

/-!
# Structural analysis of one-output De Morgan circuits

The contracted origin of the circuit's designated output wire lies in the
original program. For a function depending on at least two inputs, this origin
must be a charged gate rather than a constant or a single literal.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-- The charged origin of a one-output circuit's terminal value. -/
structure OutputRoot (circuit : Circuit signature n 1) where
  /-- Charged gate carrying the output, after contracting free gates. -/
  gate : Fin circuit.size
  /-- Whether the terminal free chain negates the charged gate. -/
  negated : Bool
  /-- Exact contracted-origin equation for the output wire. -/
  origin_eq : origins circuit.program (circuit.outputs 0) =
    .wire negated (Wire.gate gate)
  /-- The selected origin is charged. -/
  charged : ChargedGate circuit.program gate

/-- Equality at the charged root implies equality of the circuit output. -/
theorem OutputRoot.output_eq_of_gate_eq
    {circuit : Circuit signature n 1}
    (root : OutputRoot circuit)
    (left right : Fin n → Bool)
    (gate_eq : circuit.program.gateFunction interpretation root.gate left =
      circuit.program.gateFunction interpretation root.gate right) :
    circuit.eval interpretation left 0 = circuit.eval interpretation right 0 := by
  let program := circuit.program
  let outputWire := circuit.outputs 0
  calc
    circuit.eval interpretation left 0 =
        program.trace interpretation left outputWire :=
      rfl
    _ = (origins program outputWire).eval program left :=
      (origins_eval program left outputWire).symm
    _ = (ResidualValue.wire root.negated (Wire.gate root.gate)).eval
          program left := by rw [root.origin_eq]
    _ = (ResidualValue.wire root.negated (Wire.gate root.gate)).eval
          program right := by
      cases root.negated <;> simpa [program] using gate_eq
    _ = (origins program outputWire).eval program right := by rw [root.origin_eq]
    _ = program.trace interpretation right outputWire :=
      origins_eval program right outputWire
    _ = circuit.eval interpretation right 0 :=
      rfl

/-- A changed circuit output forces its charged root to change. -/
theorem OutputRoot.gate_ne_of_output_ne
    {circuit : Circuit signature n 1}
    (root : OutputRoot circuit)
    (left right : Fin n → Bool)
    (different : circuit.eval interpretation left 0 ≠
      circuit.eval interpretation right 0) :
    circuit.program.gateFunction interpretation root.gate left ≠
      circuit.program.gateFunction interpretation root.gate right := by
  intro equal
  exact different (root.output_eq_of_gate_eq left right equal)

/--
A one-output circuit structurally supported by every one of at least two inputs
has a charged output root.
-/
theorem exists_outputRoot
    (circuit : Circuit signature (n + 1) 1)
    (positive : 0 < n)
    (allSupported : ∀ input, input ∈ circuit.inputSupport) :
    Nonempty (OutputRoot circuit) := by
  let program := circuit.program
  let outputWire := circuit.outputs 0
  have everyInputInOrigin (input : Fin (n + 1)) :
      input ∈ originSupport program (origins program outputWire) := by
    rw [origins_support]
    obtain ⟨output, present⟩ := Circuit.mem_inputSupport.mp (allSupported input)
    have equal : output = 0 := Fin.eq_zero output
    simpa [program, outputWire, equal] using present
  have valid := origins_valid program outputWire
  generalize origin_eq : origins program outputWire = origin at valid everyInputInOrigin
  cases origin with
  | constant value =>
      have impossible := everyInputInOrigin (0 : Fin (n + 1))
      simp [originSupport] at impossible
  | wire negated originWire =>
      rcases valid with ⟨input, wire_eq⟩ | ⟨gate, wire_eq, charged⟩
      · subst originWire
        let other : Fin (n + 1) := input.succAbove ⟨0, positive⟩
        have supported := everyInputInOrigin other
        have other_eq : other = input := by
          simpa [originSupport] using supported
        exact False.elim (Fin.succAbove_ne input ⟨0, positive⟩ other_eq)
      · subst originWire
        exact ⟨
          { gate := gate
            negated := negated
            origin_eq := origin_eq
            charged := charged }⟩

end DeMorgan
end Algebraic
