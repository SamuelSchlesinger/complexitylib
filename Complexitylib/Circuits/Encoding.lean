/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Circuits.Encoding.Fragment
public import Complexitylib.Circuits.Encoding.Formula
public import Complexitylib.Circuits.Encoding.Formula.Batch
public import Complexitylib.Circuits.Encoding.Formula.Stream
public import Complexitylib.Circuits.Encoding.Internal
public import Complexitylib.Circuits.Encoding.Threshold
public import Complexitylib.Circuits.Encoding.ToCircuit

/-!
# Encoded fan-in-two circuits

This module exposes the machine-facing representation of
`Basis.andOr2` circuits and its correctness theorems.

## Main definitions

- `CircuitCode.RawGate` and `RawCircuit`: proof-free ordered syntax.
- `RawCircuit.WellFormed`: nonempty, strictly backward-pointing gate lists.
- `RawCircuit.encode` / `decode?`: canonical terminated-unary bit codec.
- `RawCircuit.eval?`: array-backed iterative evaluation.
- `CircuitCode.encodeCircuit`: serialization of a typed circuit.
- `CircuitCode.evalCode`: decode and evaluate with an exact arity check.
- `RawCircuit.toCircuit`: package well-formed raw syntax as a typed circuit.
- `RawCircuit.evalAux?_append`: compose appendable raw fragments.
- `BoolFormula.compileRaw`: compile formulas into appendable raw fragments.
- `BoolFormula.compileRawBatch`: compile many formulas and pack their outputs.
- `BoolFormula.compileRawRightFold`: expose finite folds as forward members,
  one identity gate, and reverse connectors.
- `Threshold.compileRaw`: append a unary dynamic-programming threshold test.

## Main results

- `RawCircuit.decode?_eq_some_iff`: exact decoder soundness and completeness.
- `RawCircuit.eval?_isSome_iff`: executable success exactly matches
  well-formedness.
- `CircuitCode.evalCode_encodeCircuit`: encoded evaluation agrees with
  `Circuit.eval`.
- `CircuitCode.evalCode_encodeCircuit_of_length`: the corresponding
  list-native theorem for machine-facing clients.
- `CircuitCode.encodeCircuit_length_le_size`: concrete polynomial bit-length
  bound for the unary encoding.
- `RawCircuit.ofCircuit_toCircuit`, `RawCircuit.eval?_toCircuit`, and
  `RawCircuit.size_toCircuit`: exact reconstruction, semantics, and size.
- `BoolFormula.evalAux?_compileRaw`: exact formula-fragment evaluation.
- `BoolFormula.evalAux?_compileRawBatch`: exact contiguous batch-output semantics.
- `Threshold.evalAux?_compileRaw`: exact threshold-fragment evaluation.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace RawCircuit

/-- Exact decoding succeeds precisely on canonical raw-circuit encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (circuit : RawCircuit) :
    decode? bits = some circuit ↔ bits = circuit.encode :=
  decode?_eq_some_iff_internal bits circuit

/-- Raw evaluation succeeds precisely for nonempty topologically ordered
circuits at the supplied input arity. -/
theorem eval?_isSome_iff (circuit : RawCircuit) (input : List Bool) :
    (circuit.eval? input).isSome ↔ circuit.WellFormed input.length :=
  eval?_isSome_iff_internal circuit input

end RawCircuit

/-- Decoding and iteratively evaluating the canonical encoding of a typed
fan-in-two circuit returns its typed output. -/
theorem evalCode_encodeCircuit {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : BitString N) :
    evalCode N (encodeCircuit c) input.toList = some ((c.eval input) 0) :=
  evalCode_encodeCircuit_internal c input

/-- List-native semantic correctness for an input of the declared arity. -/
theorem evalCode_encodeCircuit_of_length {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : List Bool)
    (hinput : input.length = N) :
    evalCode N (encodeCircuit c) input =
      some ((c.eval (BitString.ofList input hinput)) 0) :=
  evalCode_encodeCircuit_of_length_internal c input hinput

/-- In the library's size convention, which counts internal and output gates
but not primary inputs or free negations, unary circuit codes have quadratic
length in the input arity and circuit size. -/
theorem encodeCircuit_length_le_size {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (encodeCircuit c).length ≤
      1 + c.size * (2 * (N + c.size) + 6) :=
  encodeCircuit_length_le_size_internal c

end CircuitCode

end Complexity
