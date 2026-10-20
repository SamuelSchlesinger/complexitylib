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
public import Complexitylib.Interop.Cslib.Guard
public import Complexitylib.Interop.Mathlib.TM0
public import Complexitylib.Interop.Mathlib.TM0.Guard
public import Complexitylib.Interop.Mathlib.TM0.Marked
public import Complexitylib.Interop.Mathlib.TM0.Alphabet
public import Complexitylib.Interop.Mathlib.TM2
public import Complexitylib.Interop.Mathlib.TM2.FP

/-!
# Interoperability

Aggregation module for bridges to CSLib and Mathlib.

- `Complexitylib.Interop.Cslib` connects the machine model to CSLib's step
  relations and, through `Complexitylib.Interop.Cslib.Regular`, to the
  regular-language and automata theory that CSLib builds on Mathlib's
  `Language`: the finite-state scanner that runs a regular language's automaton
  places it in `DSPACE(0)`, in `L`, and in `P`, each proved separately from
  that scanner (`mem_DSPACE_zero_of_isRegular`, `mem_L_of_isRegular`,
  `mem_P_of_isRegular`).
- `Complexitylib.Interop.Cslib.MultiTape` runs our machines on CSLib's
  multi-tape machines, transferring `DTIME`, `DTISP`, `P`, and `FP` to CSLib's
  time and space measures. `Complexitylib.Interop.Cslib.FromMultiTape` runs
  CSLib's machines on ours, giving equivalences for both `P` and `FP`.
- `Complexitylib.Interop.Cslib.Circuit` translates between our fan-in-two
  circuits and CSLib's De Morgan circuits, transferring CSLib's Shannon and
  Lupanov bounds and characterizing `P/poly` in CSLib's circuit model.
  `Complexitylib.Interop.Cslib.CircuitClasses` lifts these to the `SIZE`
  classes, and `Complexitylib.Interop.Cslib.CircuitDepth` matches circuit
  depth in both directions.
- `Complexitylib.Interop.Mathlib.TM0` simulates finite Mathlib machines with
  binary input and output on CSLib symbol tracks. Polynomial source time and
  output length on every input imply canonical `FP` membership.
  Its `Guard` interface validates regular input formats and returns empty
  output on malformed strings, extending source bounds on valid inputs to `FP`.
- `Complexitylib.Interop.Mathlib.TM2` proves quadratic transition overhead for
  Mathlib's existing stack-to-tape compiler, preserving the complete stack-track
  input and output tapes of bundled `FinTM2` computations.
- `Complexitylib.Interop.Mathlib.TM2.FP` transfers total binary-string TM2
  certificates with finite working alphabets to canonical `FP`, including the
  marked empty-input representation and both reversals of stack order.
  Its DFA-guarded theorem requires source bounds only on valid strings and
  returns empty output on malformed strings.
  Its encoded interface supports independent finite input and output alphabets,
  including empty alphabets, through explicit palindromic symbol codes.
- `Complexitylib.Interop.Mathlib.TM0.Marked` handles distinct input and output
  formats, including first-cell and empty-input markers.
- `Complexitylib.Interop.Mathlib.TM0.Alphabet` parses and emits codes for finite
  source alphabets, rejecting invalid symbol codes before source execution.
- `Complexitylib.Interop.Cslib.Guard` validates regular input domains before
  starting an arbitrary binary CSLib machine.
-/
