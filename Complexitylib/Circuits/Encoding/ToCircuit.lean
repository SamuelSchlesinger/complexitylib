/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Internal.ToCircuit

/-!
# Typed circuits reconstructed from raw circuit syntax

This module exposes the reverse direction of the canonical fan-in-two circuit
encoding bridge. A valid raw circuit at positive input arity becomes a typed
`Circuit Basis.andOr2`; reconstruction preserves its ordered raw syntax,
Boolean evaluation, and exact gate count.

## Main definitions

- `CircuitCode.RawGate.toGate`: restore a raw gate's dependent wire bounds.
- `CircuitCode.RawCircuit.toCircuit`: restore a valid raw circuit's dependent
  circuit type.

## Main results

- `RawCircuit.ofCircuit_toCircuit`: reconstruction is a right inverse to
  erasure.
- `RawCircuit.eval?_toCircuit`: iterative raw and typed evaluation agree.
- `RawCircuit.size_toCircuit`: typed size equals the raw gate count.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawCircuit

/-- Re-erasing a reconstructed typed circuit returns the original raw circuit. -/
theorem ofCircuit_toCircuit (N : ℕ) [NeZero N] (circuit : RawCircuit)
    (hwell : circuit.WellFormed N) :
    RawCircuit.ofCircuit (circuit.toCircuit N hwell) = circuit :=
  ofCircuit_toCircuit_internal N circuit hwell

/-- Raw iterative evaluation agrees with the reconstructed typed circuit. -/
theorem eval?_toCircuit (N : ℕ) [NeZero N] (circuit : RawCircuit)
    (hwell : circuit.WellFormed N) (input : BitString N) :
    circuit.eval? input.toList =
      some (((circuit.toCircuit N hwell).eval input) 0) :=
  eval?_toCircuit_internal N circuit hwell input

/-- Reconstructed typed size is exactly the raw gate count. -/
theorem size_toCircuit (N : ℕ) [NeZero N] (circuit : RawCircuit)
    (hwell : circuit.WellFormed N) :
    (circuit.toCircuit N hwell).size = circuit.length :=
  size_toCircuit_internal N circuit hwell

end RawCircuit

end CircuitCode

end Complexity
