/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Threshold.Defs
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Unrolling.Acceptance.Defs
public import Mathlib.Data.List.FinRange

/-!
# Parallel amplification circuits -- definitions

This definitions layer emits several independent copies of a bounded-trace
acceptance circuit. Every copy reads the same data wires and its own block of
choice wires. The copies are serialized consecutively in the raw code, but
their semantics are parallel: each copy receives only the shared primary
inputs assigned to it and records one verdict wire.

After all copies have been emitted, a unary threshold fragment computes their
strict majority. The construction is proof-free. Later modules establish the
exact gate count, topological ordering, and evaluation semantics.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace InputWires

/-- Regard an input layout as living in a larger prefix obtained by appending
`extra` wires. The absolute locations of every existing input are unchanged. -/
def weaken {T n available : ℕ} (layout : InputWires T n available)
    (extra : ℕ) : InputWires T n (available + extra) where
  choice i := Fin.castLE (Nat.le_add_right available extra) (layout.choice i)
  data i := Fin.castLE (Nat.le_add_right available extra) (layout.data i)

/-- Weakening an input layout does not change a choice wire's absolute index. -/
@[simp] theorem weaken_choice_val {T n available : ℕ}
    (layout : InputWires T n available) (extra : ℕ) (i : Fin T) :
    ((layout.weaken extra).choice i).val = (layout.choice i).val := rfl

/-- Weakening an input layout does not change a data wire's absolute index. -/
@[simp] theorem weaken_data_val {T n available : ℕ}
    (layout : InputWires T n available) (extra : ℕ) (i : Fin n) :
    ((layout.weaken extra).data i).val = (layout.data i).val := rfl

end InputWires

/-- Locations of several choice blocks and one shared data block in an
existing wire prefix. Run `j` reads the choice map `choice j` and every run
reads the same `data` map. -/
structure ParallelInputWires (runs T n available : ℕ) where
  /-- Choice wire at a run index and a within-run time index. -/
  choice : Fin runs → Fin T → Fin available
  /-- Shared input-data wires. -/
  data : Fin n → Fin available

namespace ParallelInputWires

/-- Select one run's ordinary bounded-trace input layout. -/
def run {runs T n available : ℕ}
    (layout : ParallelInputWires runs T n available) (j : Fin runs) :
    InputWires T n available where
  choice := layout.choice j
  data := layout.data

/-- Selecting a run recovers that run's choice map. -/
@[simp] theorem run_choice {runs T n available : ℕ}
    (layout : ParallelInputWires runs T n available)
    (j : Fin runs) (t : Fin T) :
    (layout.run j).choice t = layout.choice j t := rfl

/-- Selecting a run retains the shared data map. -/
@[simp] theorem run_data {runs T n available : ℕ}
    (layout : ParallelInputWires runs T n available)
    (j : Fin runs) (i : Fin n) :
    (layout.run j).data i = layout.data i := rfl

end ParallelInputWires

/-- Canonical primary-input order for parallel amplification: all
`runs * T` choice bits in row-major run/time order, followed by the shared
`n` data bits. -/
def prefixParallelInputWires (runs T n : ℕ) :
    ParallelInputWires runs T n (runs * T + n) where
  choice j t := Fin.castAdd n (finProdFinEquiv (j, t))
  data i := Fin.natAdd (runs * T) i

/-- Canonical parallel choice wire `(j, t)` has row-major absolute index
`t + T * j`. -/
@[simp] theorem prefixParallelInputWires_choice_val (runs T n : ℕ)
    (j : Fin runs) (t : Fin T) :
    ((prefixParallelInputWires runs T n).choice j t).val =
      t.val + T * j.val := rfl

/-- Canonical shared data starts immediately after every choice block. -/
@[simp] theorem prefixParallelInputWires_data_val (runs T n : ℕ)
    (i : Fin n) :
    ((prefixParallelInputWires runs T n).data i).val =
      runs * T + i.val := rfl

/-- Accumulated raw code while emitting independent acceptance copies.

`verdictWires` has the final arity from the beginning, avoiding dependent
casts while folding over run indices. Before run `j` is emitted its entry is a
dummy value; prefix invariants only interpret entries for completed runs. -/
structure AcceptanceCopiesBuild (runs : ℕ) where
  /-- Acceptance fragments emitted so far. -/
  circuit : CircuitCode.RawCircuit
  /-- Absolute output wire assigned to each completed run. -/
  verdictWires : Fin runs → ℕ

namespace AcceptanceCopiesBuild

/-- First unused absolute wire after this build and its primary-input prefix. -/
def available {runs : ℕ} (build : AcceptanceCopiesBuild runs)
    (primaryAvailable : ℕ) : ℕ :=
  primaryAvailable + build.circuit.length

end AcceptanceCopiesBuild

/-- Empty acceptance-copy build. Verdict entries are placeholders until their
corresponding runs are emitted. -/
def initialAcceptanceCopiesBuild (runs : ℕ) : AcceptanceCopiesBuild runs :=
  { circuit := []
    verdictWires := fun _ => 0 }

/-- Append one bounded-trace acceptance circuit and record its final wire as
the selected run's verdict. The run layout is weakened across all gates
emitted by earlier copies without changing any primary-input index. -/
noncomputable def acceptanceCopiesBuildStep (tm : NTM k)
    {runs T n primaryAvailable : ℕ}
    (layout : ParallelInputWires runs T n primaryAvailable)
    (build : AcceptanceCopiesBuild runs) (j : Fin runs) :
    AcceptanceCopiesBuild runs :=
  let available := build.available primaryAvailable
  let runLayout := (layout.run j).weaken build.circuit.length
  let fragment := acceptanceRawCircuit tm T n available runLayout
  { circuit := build.circuit ++ fragment
    verdictWires := Function.update build.verdictWires j
      (available + fragment.length - 1) }

/-- Append a listed sequence of acceptance copies to an existing build. -/
noncomputable def acceptanceCopiesBuildFrom (tm : NTM k)
    {runs T n primaryAvailable : ℕ}
    (layout : ParallelInputWires runs T n primaryAvailable)
    (build : AcceptanceCopiesBuild runs) (indices : List (Fin runs)) :
    AcceptanceCopiesBuild runs :=
  indices.foldl (acceptanceCopiesBuildStep tm layout) build

/-- Build the first `i` canonical acceptance copies. List `take` saturates
when `i` exceeds the total number of runs. -/
noncomputable def prefixAcceptanceCopiesBuild (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    AcceptanceCopiesBuild runs :=
  acceptanceCopiesBuildFrom tm layout (initialAcceptanceCopiesBuild runs)
    ((List.finRange runs).take i)

/-- Complete build containing one independent acceptance circuit per run. -/
noncomputable def acceptanceCopiesBuild (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    AcceptanceCopiesBuild runs :=
  acceptanceCopiesBuildFrom tm layout (initialAcceptanceCopiesBuild runs)
    (List.finRange runs)

/-- Raw concatenation of every independent acceptance copy. -/
noncomputable def acceptanceCopiesFragment (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    CircuitCode.RawCircuit :=
  (acceptanceCopiesBuild tm runs T n primaryAvailable layout).circuit

/-- Exact gate count recorded after emitting every acceptance copy. -/
noncomputable def acceptanceCopiesSize (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) : ℕ :=
  (acceptanceCopiesBuild tm runs T n primaryAvailable layout).circuit.length

/-- Absolute wire carrying each run's acceptance verdict. -/
noncomputable def acceptanceCopiesVerdictWires (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) : Fin runs → ℕ :=
  (acceptanceCopiesBuild tm runs T n primaryAvailable layout).verdictWires

/-- Smallest integer count constituting a strict majority of `runs`. -/
def strictMajorityThreshold (runs : ℕ) : ℕ :=
  runs / 2 + 1

/-- Acceptance bits produced by independent bounded runs sharing one input. -/
def parallelAcceptanceBits (tm : NTM k) (T : ℕ) (x : BitString n)
    (choices : Fin runs → BitString T) : BitString runs :=
  fun j => boundedAcceptanceBit tm T x (choices j)

/-- Split a flat row-major seed into one bounded choice block per run. -/
def parallelChoiceBlocks (runs T : ℕ) (seed : BitString (runs * T)) :
    Fin runs → BitString T :=
  fun j t => seed (finProdFinEquiv (j, t))

/-- Reading a flat seed's `(j, t)` entry uses the canonical product index. -/
@[simp] theorem parallelChoiceBlocks_apply (runs T : ℕ)
    (seed : BitString (runs * T)) (j : Fin runs) (t : Fin T) :
    parallelChoiceBlocks runs T seed j t = seed (finProdFinEquiv (j, t)) := rfl

/-- Per-run acceptance bits under the canonical flattened-seed layout. -/
def canonicalAcceptanceBits (tm : NTM k) (runs T : ℕ) (x : BitString n)
    (seed : BitString (runs * T)) : BitString runs :=
  parallelAcceptanceBits tm T x (parallelChoiceBlocks runs T seed)

/-- Independent bounded-trace acceptance copies followed by a strict-majority
threshold over their recorded verdict wires. -/
noncomputable def amplifiedAcceptanceRawCircuit (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    CircuitCode.RawCircuit :=
  let built := acceptanceCopiesBuild tm runs T n primaryAvailable layout
  built.circuit ++
    CircuitCode.Threshold.compileRaw
      (primaryAvailable + built.circuit.length)
      (strictMajorityThreshold runs) built.verdictWires

/-- Absolute wire carrying the amplified circuit's strict-majority output. -/
noncomputable def amplifiedAcceptanceOutputWire (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) : ℕ :=
  let built := acceptanceCopiesBuild tm runs T n primaryAvailable layout
  CircuitCode.Threshold.outputWire
    (primaryAvailable + built.circuit.length) runs (strictMajorityThreshold runs)

/-- Canonical amplified raw circuit with all flattened choice blocks before
the shared input data. -/
noncomputable def canonicalAmplifiedAcceptanceRawCircuit
    (tm : NTM k) (runs T n : ℕ) : CircuitCode.RawCircuit :=
  amplifiedAcceptanceRawCircuit tm runs T n (runs * T + n)
    (prefixParallelInputWires runs T n)

end CircuitUnrolling

end Complexity
