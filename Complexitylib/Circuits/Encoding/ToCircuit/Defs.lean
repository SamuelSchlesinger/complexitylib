/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Defs

/-!
# Reconstructing typed circuits from raw circuit syntax

This definitions layer packages a nonempty, topologically ordered
`CircuitCode.RawCircuit` as a typed fan-in-two AND/OR circuit. The final raw
gate becomes the sole output gate; every preceding raw gate becomes an
internal gate in the same order.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawGate

/-- Restore the dependent wire bounds of a well-formed raw gate. -/
def toGate {W : ℕ} (gate : RawGate) (hwell : gate.WellFormedAt W) :
    Gate Basis.andOr2 W where
  op := gate.op
  fanIn := 2
  arityOk := rfl
  inputs i :=
    if i.val = 0 then
      ⟨gate.input₀, hwell.1⟩
    else
      ⟨gate.input₁, hwell.2⟩
  negated i :=
    if i.val = 0 then gate.negated₀ else gate.negated₁

end RawGate

namespace RawCircuit

/-- Restore the dependent type of a valid raw single-output circuit.

The circuit has one typed gate for each raw gate: the first `length - 1` are
internal gates and the final gate is the sole output gate. -/
def toCircuit (N : ℕ) [NeZero N] (circuit : RawCircuit)
    (hwell : circuit.WellFormed N) :
    Circuit Basis.andOr2 N 1 (circuit.length - 1) where
  gates i := by
    let j : Fin circuit.length := ⟨i.val, by omega⟩
    exact (circuit.get j).toGate (by
      have hgate := hwell.2 j
      dsimp only [j] at hgate
      have hle : N + i.val ≤ N + (circuit.length - 1) :=
        Nat.add_le_add_left (Nat.le_of_lt i.isLt) N
      exact ⟨hgate.1.trans_le hle, hgate.2.trans_le hle⟩)
  outputs _ := by
    let j : Fin circuit.length := ⟨circuit.length - 1, by
      have hpos : circuit.length ≠ 0 := by
        intro hzero
        exact hwell.1 (List.eq_nil_of_length_eq_zero hzero)
      omega⟩
    exact (circuit.get j).toGate (by
      simpa using hwell.2 j)
  acyclic i k := by
    let j : Fin circuit.length := ⟨i.val, by omega⟩
    have hgate := hwell.2 j
    dsimp only [j] at hgate
    simp only [RawGate.toGate]
    split_ifs
    · exact hgate.1
    · exact hgate.2

end RawCircuit

end CircuitCode

end Complexity
