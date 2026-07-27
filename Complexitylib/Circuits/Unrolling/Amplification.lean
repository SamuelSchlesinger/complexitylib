/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.ToCircuit
public import Complexitylib.Circuits.Unrolling.Amplification.Defs
public import Complexitylib.Circuits.Unrolling.Amplification.Internal.Evaluation
public import Complexitylib.Circuits.Unrolling.Amplification.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Amplification.Internal.Topology

/-!
# Parallel amplification circuits

This module exposes a circuit that runs several independent bounded traces of
one nondeterministic machine on shared input data and returns their strict
majority verdict. The implementation serializes the copies in raw gate order,
but every copy reads only its own choice block and the common data block.

The circuit layer deliberately stops at `Fin.countP`. Its interpretation as
the randomized layer's `blockMajority` is supplied by
`Complexitylib.Classes.Randomized.CircuitAmplification`.

## Main results

- `amplifiedAcceptanceRawCircuit_wellFormed`: the raw circuit is valid.
- `eval?_amplifiedAcceptanceRawCircuit`: raw evaluation returns the threshold
  of the independent bounded acceptance bits.
- `amplifiedAcceptanceCircuit_eval`: typed reconstruction has the same semantics.
- `canonicalAmplifiedAcceptanceCircuit_eval`: choices-first canonical semantics.
- `amplifiedAcceptanceCircuit_size_le`: one cubic unrolling per run plus a
  quadratic threshold circuit.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Exact gate count: all acceptance copies followed by the threshold fragment. -/
@[simp] theorem length_amplifiedAcceptanceRawCircuit (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout).length =
      acceptanceCopiesSize tm runs T n primaryAvailable layout +
        (3 + 2 * runs * strictMajorityThreshold runs) :=
  length_amplifiedAcceptanceRawCircuit_internal tm runs T n primaryAvailable
    layout

/-- Every reference in the amplified raw circuit points backward. -/
theorem amplifiedAcceptanceRawCircuit_topologicallyWellFormed
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
      layout).TopologicallyWellFormed primaryAvailable :=
  amplifiedAcceptanceRawCircuit_topologicallyWellFormed_internal tm runs T n
    primaryAvailable layout

/-- The amplified raw circuit is nonempty and topologically ordered. -/
theorem amplifiedAcceptanceRawCircuit_wellFormed
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
      layout).WellFormed primaryAvailable :=
  amplifiedAcceptanceRawCircuit_wellFormed_internal tm runs T n
    primaryAvailable layout

/-- Parallel amplification uses one cubic trace circuit per run and one
quadratic threshold circuit. -/
theorem length_amplifiedAcceptanceRawCircuit_le (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout).length ≤
      runs * (acceptanceSizeCoeff tm * (T + 2) ^ 3) + 3 +
        2 * runs * runs :=
  length_amplifiedAcceptanceRawCircuit_le_internal tm runs T n
    primaryAvailable layout

/-- Array-native evaluation appends the exact raw gate count, preserves the
primary inputs, and records the threshold value at the designated output. -/
theorem evalAux?_amplifiedAcceptanceRawCircuit
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (wires : Array Bool) (hsize : wires.size = primaryAvailable)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j t, wires[(layout.choice j t).val]? = some (choices j t)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout)
          wires = some result ∧
        result.size = wires.size +
          (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
            layout).length ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        result[(amplifiedAcceptanceOutputWire tm runs T n primaryAvailable
          layout)]? = some (decide (strictMajorityThreshold runs ≤
            Fin.countP (parallelAcceptanceBits tm T x choices))) :=
  evalAux?_amplifiedAcceptanceRawCircuit_internal tm runs T n primaryAvailable
    layout x choices wires hsize hdata hchoices

/-- Raw single-output evaluation returns the strict-threshold predicate over
the independent bounded acceptance bits. -/
theorem eval?_amplifiedAcceptanceRawCircuit
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (input : BitString primaryAvailable)
    (hdata : ∀ j, input (layout.data j) = x j)
    (hchoices : ∀ j t, input (layout.choice j t) = choices j t) :
    CircuitCode.RawCircuit.eval?
        (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout)
        (BitString.toList input) = some (decide (strictMajorityThreshold runs ≤
          Fin.countP (parallelAcceptanceBits tm T x choices))) :=
  eval?_amplifiedAcceptanceRawCircuit_internal tm runs T n primaryAvailable
    layout x choices input hdata hchoices

/-- Reconstruct a valid amplified raw circuit as a typed single-output circuit. -/
noncomputable def amplifiedAcceptanceCircuit
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    Circuit Basis.andOr2 primaryAvailable 1
      ((amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
        layout).length - 1) :=
  (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout).toCircuit
    primaryAvailable
    (amplifiedAcceptanceRawCircuit_wellFormed tm runs T n primaryAvailable
      layout)

/-- Typed reconstruction preserves the exact amplified raw gate count. -/
@[simp] theorem amplifiedAcceptanceCircuit_size
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceCircuit tm runs T n primaryAvailable layout).size =
      acceptanceCopiesSize tm runs T n primaryAvailable layout +
        (3 + 2 * runs * strictMajorityThreshold runs) := by
  rw [amplifiedAcceptanceCircuit,
    CircuitCode.RawCircuit.size_toCircuit,
    length_amplifiedAcceptanceRawCircuit]

/-- The typed amplified circuit satisfies the same explicit polynomial bound. -/
theorem amplifiedAcceptanceCircuit_size_le
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceCircuit tm runs T n primaryAvailable layout).size ≤
      runs * (acceptanceSizeCoeff tm * (T + 2) ^ 3) + 3 +
        2 * runs * runs := by
  rw [amplifiedAcceptanceCircuit,
    CircuitCode.RawCircuit.size_toCircuit]
  exact length_amplifiedAcceptanceRawCircuit_le tm runs T n primaryAvailable
    layout

/-- Typed evaluation computes the threshold of the independent bounded runs. -/
theorem amplifiedAcceptanceCircuit_eval
    (tm : NTM k) (runs T n primaryAvailable : ℕ) [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (x : BitString n) (choices : Fin runs → BitString T)
    (input : BitString primaryAvailable)
    (hdata : ∀ j, input (layout.data j) = x j)
    (hchoices : ∀ j t, input (layout.choice j t) = choices j t) :
    ((amplifiedAcceptanceCircuit tm runs T n primaryAvailable layout).eval
      input) 0 = decide (strictMajorityThreshold runs ≤
        Fin.countP (parallelAcceptanceBits tm T x choices)) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit primaryAvailable
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout)
    (amplifiedAcceptanceRawCircuit_wellFormed tm runs T n primaryAvailable
      layout) input
  rw [eval?_amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout
    x choices input hdata hchoices] at hbridge
  exact (Option.some.inj hbridge).symm

/-- Canonical choices-first, shared-data-second amplified circuit. -/
noncomputable def canonicalAmplifiedAcceptanceCircuit
    (tm : NTM k) (runs T n : ℕ) [NeZero (runs * T + n)] :
    Circuit Basis.andOr2 (runs * T + n) 1
      ((canonicalAmplifiedAcceptanceRawCircuit tm runs T n).length - 1) :=
  amplifiedAcceptanceCircuit tm runs T n (runs * T + n)
    (prefixParallelInputWires runs T n)

/-- Under the canonical layout, typed evaluation consumes the flat seed before
the shared input and returns the threshold of the named acceptance-bit vector. -/
theorem canonicalAmplifiedAcceptanceCircuit_eval
    (tm : NTM k) (runs T n : ℕ) [NeZero (runs * T + n)]
    (seed : BitString (runs * T)) (x : BitString n) :
    ((canonicalAmplifiedAcceptanceCircuit tm runs T n).eval
      (Fin.append seed x)) 0 = decide (strictMajorityThreshold runs ≤
        Fin.countP (canonicalAcceptanceBits tm runs T x seed)) := by
  have hbridge := CircuitCode.RawCircuit.eval?_toCircuit (runs * T + n)
    (canonicalAmplifiedAcceptanceRawCircuit tm runs T n)
    (amplifiedAcceptanceRawCircuit_wellFormed tm runs T n (runs * T + n)
      (prefixParallelInputWires runs T n)) (Fin.append seed x)
  rw [eval?_canonicalAmplifiedAcceptanceRawCircuit_internal tm runs T n
    seed x] at hbridge
  exact (Option.some.inj hbridge).symm

/-- The canonical typed circuit inherits the generic amplified size bound. -/
theorem canonicalAmplifiedAcceptanceCircuit_size_le
    (tm : NTM k) (runs T n : ℕ) [NeZero (runs * T + n)] :
    (canonicalAmplifiedAcceptanceCircuit tm runs T n).size ≤
      runs * (acceptanceSizeCoeff tm * (T + 2) ^ 3) + 3 +
        2 * runs * runs :=
  amplifiedAcceptanceCircuit_size_le tm runs T n (runs * T + n)
    (prefixParallelInputWires runs T n)

end CircuitUnrolling

end Complexity
