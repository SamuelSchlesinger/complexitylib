/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Cslib
public import Complexitylib.Interop.Cslib.MultiTape
public import Complexitylib.Interop.Cslib.FromMultiTape
public import Complexitylib.Interop.Cslib.FromMultiTape.PEquiv
public import Complexitylib.Interop.Cslib.Circuit
public import Complexitylib.Interop.Cslib.CircuitClasses
public import Complexitylib.Interop.Cslib.CircuitDepth

/-!
# Interoperability

Aggregation module for bridges to other libraries, currently CSLib.

- `Complexitylib.Interop.Cslib` connects the machine model to CSLib's step
  relations and, through `Complexitylib.Interop.Cslib.Regular`, to the
  regular-language and automata theory that CSLib builds on Mathlib's
  `Language`: regular languages are in `DSPACE(0)`, hence in `L` and `P`.
- `Complexitylib.Interop.Cslib.MultiTape` runs our machines on CSLib's
  multi-tape machines, transferring `DTIME`, `DTISP`, `P`, and `FP` to CSLib's
  time and space measures. `Complexitylib.Interop.Cslib.FromMultiTape` runs
  CSLib's machines on ours, so `P` is exactly CSLib's polynomial time.
- `Complexitylib.Interop.Cslib.Circuit` translates between our fan-in-two
  circuits and CSLib's De Morgan circuits, transferring CSLib's Shannon and
  Lupanov bounds and characterizing `P/poly` in CSLib's circuit model.
  `Complexitylib.Interop.Cslib.CircuitClasses` lifts these to the `SIZE`
  classes, and `Complexitylib.Interop.Cslib.CircuitDepth` matches circuit
  depth in both directions.
-/
