/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine
public import Complexitylib.Models.TuringMachine.Trace
public import Complexitylib.Models.TuringMachine.SingleTape
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork
public import Complexitylib.Models.TuringMachine.Combinators.ForInput
public import Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes
public import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
public import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
public import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
public import Complexitylib.Models.TuringMachine.Hoare
public import Complexitylib.Models.TuringMachine.Hoare.Space
public import Complexitylib.Models.TuringMachine.Experimental.Routine
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
public import Complexitylib.Models.TuringMachine.Tape.Encoding
public import Complexitylib.Models.TuringMachine.Subroutines
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
public import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput
public import Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput
public import Complexitylib.Models.TuringMachine.Subroutines.PairEmit
public import Complexitylib.Models.TuringMachine.Subroutines.PairValidate
public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit
public import Complexitylib.Models.TuringMachine.Subroutines.ScanRight
public import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary
public import Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
public import Complexitylib.Models.TuringMachine.Subroutines.UnaryLength
public import Complexitylib.Models.TuringMachine.OutputBounds
public import Complexitylib.Models.TuringMachine.SpaceTime
public import Complexitylib.Models.TuringMachine.Placement
public import Complexitylib.Models.TuringMachine.Composition
public import Complexitylib.Models.TuringMachine.Composition.PairWithInput
public import Complexitylib.Models.TuringMachine.Deterministic
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.Repetition
public import Complexitylib.Models.TuringMachine.Repetition.Correctness
public import Complexitylib.Models.TuringMachine.UTM.Encoding
public import Complexitylib.Models.TuringMachine.UTM.Machine
public import Complexitylib.Models.TuringMachine.UTM.Universal
public import Complexitylib.Models.TuringMachine.UTM.Clock
public import Complexitylib.Models.TuringMachine.UTM.ClockConstructible
public import Complexitylib.Models.TuringMachine.UTM.ClockedUtm
public import Complexitylib.Models.TuringMachine.UTM.HierarchySupport
public import Complexitylib.Models.TuringMachine.UTM.Diagonal
public import Complexitylib.Models.RandomAccessMachine
public import Complexitylib.Models.RoseTreeMachine.Data
public import Complexitylib.Models.RoseTreeMachine.DataEncode
public import Complexitylib.Models.RoseTreeMachine.Prog

/-!
# Computation models

Aggregation module for the machine models: the core Turing-machine
semantics, the single-tape simulation, machine combinators, time- and
space-aware Hoare specifications, direct work-symbol branching, experimental
first-order routine lowering and proof-carrying binary stream routines,
reusable read-only-input and binary-work-tape loops, binary count-up loops,
binary successor,
binary predecessor and length, value-iterating and width-linear canonical binary
addition, fixed-constant addition, copying, multiply-add, and fixed-polynomial
evaluation, framed work-tape clearing,
unary length, and pair-emission subroutines,
computed-value/input fanout, finite space-to-time bounds, determinism results,
the universal machine, and the logarithmic-cost random access machine
(`Complexitylib.Models.RandomAccessMachine`), including its verified structured
imperative frontend and Hamming-weight benchmark with exact steps and explicit
quasilinear logarithmic-time and peak-space bounds, plus a generic verified
typed finite-state scanner compiler with pair-validation, last-bit, and
exact-3-CNF syntax instances. Proof-internal modules
(`…/Internal/…`, register machinery, emitter plumbing) are deliberately not
imported here — they stay in the build through the surface modules and theorem
files that need them.
-/

@[expose] public section
