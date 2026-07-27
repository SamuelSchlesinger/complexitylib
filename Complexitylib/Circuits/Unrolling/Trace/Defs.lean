/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Defs
public import Mathlib.Data.List.FinRange

/-!
# Definitions for tiled bounded-trace circuits

This definitions layer concatenates the initial-configuration fragment with
one packed transition fragment for every bounded choice. Every transition is
compiled at the original horizon `T`, reads the preceding packed configuration
block, and uses its corresponding primary choice wire.

The intermediate `TraceBuild` record exposes the current packed block and the
first unused wire. This makes the recursive layout available to later proofs
of topology, evaluation, and polynomial size without introducing dependent
casts into the circuit construction itself.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Accumulated circuit data while tiling a bounded machine trace. -/
structure TraceBuild where
  /-- All initialization and transition gates emitted so far. -/
  circuit : CircuitCode.RawCircuit
  /-- First wire of the most recently packed configuration block. -/
  configBase : ℕ
  /-- First unused absolute wire after the accumulated circuit. -/
  available : ℕ
  /-- Exact number of gates emitted after the original primary-wire prefix. -/
  size : ℕ

/-- Initialize a trace build after `available` primary wires.

Arguments after the machine are the horizon, input length, primary-wire count,
and the locations of choices and input data in that primary prefix. -/
noncomputable def initialTraceBuild (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : TraceBuild :=
  { circuit := initFragment tm T n available layout
    configBase := available
    available := available + configWidth tm T
    size := configWidth tm T }

/-- Append the transition selected by choice index `i` to an accumulated build.

The horizon remains the original `T`; only the incoming configuration base and
the first unused wire advance from one layer to the next. -/
noncomputable def traceBuildStep (tm : NTM k) {T n primaryAvailable : ℕ}
    (layout : InputWires T n primaryAvailable) (build : TraceBuild)
    (i : Fin T) : TraceBuild :=
  let choiceWire := (layout.choice i).val
  let layerSize := stepFragmentSize tm T build.configBase choiceWire
  { circuit := build.circuit ++
      stepFragment tm T build.configBase choiceWire build.available
    configBase :=
      stepOutputBase tm T build.configBase choiceWire build.available
    available := build.available + layerSize
    size := build.size + layerSize }

/-- Append a listed sequence of bounded transition layers to an existing build.

Indices are consumed from left to right. The list interface supports induction
over partial traces while keeping every index in the fixed type `Fin T`. -/
noncomputable def traceBuildFrom (tm : NTM k) {T n primaryAvailable : ℕ}
    (layout : InputWires T n primaryAvailable) (build : TraceBuild)
    (indices : List (Fin T)) : TraceBuild :=
  indices.foldl (traceBuildStep tm layout) build

/-- Partial trace build containing the first `i` canonical choice indices.
When `i ≥ T`, list `take` saturates and this is the complete build. -/
noncomputable def prefixTraceBuild (tm : NTM k) (T n available i : ℕ)
    (layout : InputWires T n available) : TraceBuild :=
  traceBuildFrom tm layout (initialTraceBuild tm T n available layout)
    ((List.finRange T).take i)

/-- Complete bounded-trace build: initialization followed by choices
`0, ..., T - 1` in order. At horizon zero this is just initialization. -/
noncomputable def traceBuild (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : TraceBuild :=
  traceBuildFrom tm layout (initialTraceBuild tm T n available layout)
    (List.finRange T)

/-- Raw circuit for the complete bounded trace. -/
noncomputable def traceFragment (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : CircuitCode.RawCircuit :=
  (traceBuild tm T n available layout).circuit

/-- First wire of the final packed configuration block. -/
noncomputable def traceOutputBase (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : ℕ :=
  (traceBuild tm T n available layout).configBase

/-- Exact recursively accumulated gate count of the complete trace fragment. -/
noncomputable def traceFragmentSize (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) : ℕ :=
  (traceBuild tm T n available layout).size

/-- Machine-dependent coefficient in the cubic bounded-trace size bound. -/
noncomputable def traceSizeCoeff (tm : NTM k) : ℕ :=
  stepSizeCoeff tm + Fintype.card tm.Q + 5 * (k + 2)

end CircuitUnrolling

end Complexity
