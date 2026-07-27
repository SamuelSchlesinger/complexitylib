/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Threshold.Internal

/-!
# Correctness of raw threshold-circuit fragments

This module exposes an appendable unary dynamic-programming circuit for testing
whether at least `threshold` referenced wires are true. For `k` references it
uses exactly `3 + 2 * k * threshold` gates: two Boolean constants, two gates per
table cell, and one final output copy.

The core semantic statement uses Mathlib's dependency-light `Fin.countP` rather
than importing the complexity-class counting layer into the circuit library.
A majority adapter can rewrite this count to the library's `popCount` at the
higher layer where both APIs are already available.

## Main definitions and results

- `Threshold.compileRaw`: compile an at-least-threshold test over absolute wires.
- `Threshold.length_compileRaw`: exact gate count.
- `Threshold.topologicallyWellFormed_compileRaw`: every emitted reference points
  to the existing prefix or an earlier emitted gate.
- `Threshold.evalAux?_compileRaw`: exact size, prefix preservation, and semantic
  correctness of iterative evaluation.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Threshold

/-- Threshold compilation emits two gates per table cell, two constants, and
one final copy gate. -/
@[simp] theorem length_compileRaw (available threshold : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    (compileRaw available threshold refs).length =
      3 + 2 * inputCount * threshold :=
  length_compileRaw_internal available threshold refs

/-- When the requested threshold is at most the input count, the threshold
fragment has the advertised quadratic gate bound. -/
theorem length_compileRaw_le_quadratic (available threshold : ℕ)
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hthreshold : threshold ≤ inputCount) :
    (compileRaw available threshold refs).length ≤
      3 + 2 * inputCount * inputCount := by
  rw [length_compileRaw]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left (2 * inputCount) hthreshold) 3

/-- The designated output lies inside the newly emitted fragment. -/
theorem outputWire_lt (available threshold : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    outputWire available inputCount threshold <
      available + (compileRaw available threshold refs).length := by
  rw [length_compileRaw]
  simp only [outputWire]
  omega

/-- A threshold fragment's designated output is never before its existing-wire
prefix. -/
theorem le_outputWire (available inputCount threshold : ℕ) :
    available ≤ outputWire available inputCount threshold := by
  simp only [outputWire]
  omega

/-- The designated threshold output is the final emitted wire. -/
theorem outputWire_eq (available threshold : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    outputWire available inputCount threshold =
      available + (compileRaw available threshold refs).length - 1 :=
  outputWire_eq_internal available threshold refs

/-- If every requested input names an existing wire, the threshold fragment
only references the existing prefix or earlier gates in the same fragment. -/
theorem topologicallyWellFormed_compileRaw (available threshold : ℕ)
    [NeZero available] {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) :
    (compileRaw available threshold refs).TopologicallyWellFormed available :=
  topologicallyWellFormed_compileRaw_internal available threshold refs hrefs

/-- Successful threshold evaluation appends its exact gate count, preserves
the existing memo array, and returns true exactly when at least `threshold` of
the referenced input values are true. -/
theorem evalAux?_compileRaw (available threshold : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (bits : Fin inputCount → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hrefs : ∀ i, refs i < available)
    (hinputs : ∀ i, wires[refs i]? = some (bits i)) :
    ∃ result,
      RawCircuit.evalAux? (compileRaw available threshold refs) wires = some result ∧
      result.size = wires.size + (3 + 2 * inputCount * threshold) ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[outputWire available inputCount threshold]? =
        some (decide (threshold ≤ Fin.countP bits)) :=
  evalAux?_compileRaw_internal available threshold refs bits wires
    hsize hrefs hinputs

end Threshold

end CircuitCode

end Complexity
