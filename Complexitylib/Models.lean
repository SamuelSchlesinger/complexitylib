/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine
import Complexitylib.Models.TuringMachine.Trace
import Complexitylib.Models.TuringMachine.SingleTape
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.Combinators.Started
import Complexitylib.Models.TuringMachine.Combinators.ForBinaryWork
import Complexitylib.Models.TuringMachine.Combinators.ForInput
import Complexitylib.Models.TuringMachine.Combinators.ForWorkOnes
import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Experimental.Routine
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
import Complexitylib.Models.TuringMachine.Tape.Encoding
import Complexitylib.Models.TuringMachine.Subroutines
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAddConst
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleSub
import Complexitylib.Models.TuringMachine.Subroutines.BinaryShiftMul
import Complexitylib.Models.TuringMachine.Subroutines.BinaryMulAdd
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefix
import Complexitylib.Models.TuringMachine.Subroutines.BlankWorkPrefixMany
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput
import Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput
import Complexitylib.Models.TuringMachine.Subroutines.PairEmit
import Complexitylib.Models.TuringMachine.Subroutines.PairValidate
import Complexitylib.Models.TuringMachine.Subroutines.PairSplit
import Complexitylib.Models.TuringMachine.Subroutines.ScanRight
import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary
import Complexitylib.Models.TuringMachine.Subroutines.ResetBinaryMany
import Complexitylib.Models.TuringMachine.Subroutines.RewindInputSpace
import Complexitylib.Models.TuringMachine.Subroutines.UnaryLength
import Complexitylib.Models.TuringMachine.OutputBounds
import Complexitylib.Models.TuringMachine.OutputCursor
import Complexitylib.Models.TuringMachine.OutputProbe
import Complexitylib.Models.TuringMachine.OutputProbeConsume
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken
import Complexitylib.Models.TuringMachine.OutputProbeDispatch
import Complexitylib.Models.TuringMachine.OutputProbeLatch
import Complexitylib.Models.TuringMachine.OutputProbeIndexed
import Complexitylib.Models.TuringMachine.OutputProbeScan
import Complexitylib.Models.TuringMachine.OutputProbeCleanup
import Complexitylib.Models.TuringMachine.OutputProbeFrame
import Complexitylib.Models.TuringMachine.RetargetOutputFrame
import Complexitylib.Models.TuringMachine.SpaceTime
import Complexitylib.Models.TuringMachine.SpaceTime.WorkSupport
import Complexitylib.Models.TuringMachine.Placement
import Complexitylib.Models.TuringMachine.Composition
import Complexitylib.Models.TuringMachine.Composition.PairWithInput
import Complexitylib.Models.TuringMachine.Deterministic
import Complexitylib.Models.TuringMachine.Lift
import Complexitylib.Models.TuringMachine.Repetition
import Complexitylib.Models.TuringMachine.Repetition.Correctness
import Complexitylib.Models.TuringMachine.UTM.Encoding
import Complexitylib.Models.TuringMachine.UTM.Machine
import Complexitylib.Models.TuringMachine.UTM.Universal
import Complexitylib.Models.TuringMachine.UTM.Clock
import Complexitylib.Models.TuringMachine.UTM.ClockConstructible
import Complexitylib.Models.TuringMachine.UTM.ClockedUtm
import Complexitylib.Models.TuringMachine.UTM.HierarchySupport
import Complexitylib.Models.TuringMachine.UTM.Diagonal
import Complexitylib.Models.RandomAccessMachine
import Complexitylib.Models.RoseTreeMachine.Data
import Complexitylib.Models.RoseTreeMachine.DataEncode
import Complexitylib.Models.RoseTreeMachine.Prog

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
evaluation, framed work-tape clearing and binary-bounded sparse-prefix reset,
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
