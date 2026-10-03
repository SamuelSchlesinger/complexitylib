/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Parameters.Internal

/-!
# Total polynomial-time initialization of the numerical block schedule

Choose `L=clog 2 (n+1)`, clip depth to `min requested L`, and set the local
error exponent to `e+depth+2`. The independent bound
`4^depth ≤ 4*(n+1)^2` permits bounded-power construction of the initial
entropy. The actual initial compressed width can then be computed without
using a circular capacity assumption.

Every initializer parameter has a uniform unary certificate on all natural
inputs. The selected reserve automatically satisfies the finite capacity
and splitting budgets. These arithmetic choices instantiate the previously
proved finite schedule; the payload evaluator and final statistical
specialization are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Depth clipping bounds the variable power directly by the original input length. -/
theorem scheduledBlockDepth_pow_four_le (n requested : Nat) :
    4 ^ scheduledBlockDepth n requested ≤ 4 * (n + 1) ^ 2 :=
  Internal.scheduledBlockDepth_pow_four_le n requested

/-- The selected initial compressed width contains the entropy and has bounded expansion. -/
theorem scheduledBlockRuntimeInitialWidth_bounds (n requested e : Nat) :
    scheduledBlockInitialEntropy n requested e ≤ scheduledBlockRuntimeInitialWidth n requested e ∧
      scheduledBlockRuntimeInitialWidth n requested e ≤
        64 * scheduledBlockInitialEntropy n requested e :=
  Internal.scheduledBlockRuntimeInitialWidth_bounds n requested e

/-- The total parameter choice supplies the global reserve premise of the finite schedule. -/
theorem scheduledBlockRuntime_reserve_budget (n requested e : Nat) :
    3 * (24 * explicitCondenserBudget (scheduledBlockRuntimeInitialWidth n requested e)
      (scheduledBlockInitialEntropy n requested e) (scheduledBlockErrorExponent n requested e)) +
      6 * scheduledBlockErrorExponent n requested e ≤ 2 * scheduledBlockLeafReserve n requested e :=
  Internal.scheduledBlockRuntime_reserve_budget n requested e

variable {n requested e : List Bool → Nat}

/-- The input logarithm is uniformly polynomial-time in unary. -/
@[polytime] theorem scheduledBlockInputLog_unaryFn (hn : UnaryFn n) :
    UnaryFn fun z => scheduledBlockInputLog (n z) :=
  Internal.scheduledBlockInputLog_unaryFn hn

/-- Clipping a runtime requested depth is uniformly polynomial-time. -/
@[polytime] theorem scheduledBlockDepth_unaryFn (hn : UnaryFn n) (hrequested : UnaryFn requested) :
    UnaryFn fun z => scheduledBlockDepth (n z) (requested z) :=
  Internal.scheduledBlockDepth_unaryFn hn hrequested

/-- Compute the local error exponent from the clipped depth and requested error. -/
@[polytime] theorem scheduledBlockErrorExponent_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockErrorExponent (n z) (requested z) (e z) :=
  Internal.scheduledBlockErrorExponent_unaryFn hn hrequested he

/-- The selected leaf reserve has a uniform unary certificate. -/
@[polytime] theorem scheduledBlockLeafReserve_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockLeafReserve (n z) (requested z) (e z) :=
  Internal.scheduledBlockLeafReserve_unaryFn hn hrequested he

/-- Construct initial entropy using a power bounded independently by the original input. -/
@[polytime] theorem scheduledBlockInitialEntropy_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockInitialEntropy (n z) (requested z) (e z) :=
  Internal.scheduledBlockInitialEntropy_unaryFn hn hrequested he

/-- The actual initial compressed width is uniformly polynomial-time in all runtime inputs. -/
@[polytime] theorem scheduledBlockRuntimeInitialWidth_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockRuntimeInitialWidth (n z) (requested z) (e z) :=
  Internal.scheduledBlockRuntimeInitialWidth_unaryFn hn hrequested he

/-- Initialize the encoded numerical state uniformly, with no validity premise on the inputs. -/
@[polytime] theorem scheduledBlockStateInit_mem_FP
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    (fun z => scheduledBlockStateInit (n z) (requested z) (e z)) ∈ FP :=
  Internal.scheduledBlockStateInit_mem_FP hn hrequested he

/-- Uniformly run the initialized numerical state up to a runtime requested level,
clipped to the scheduled depth so that every intermediate state has its proved bound. -/
theorem scheduledBlockStateInit_iterate_mem_FP {count : List Bool → Nat}
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e)
    (hcount : UnaryFn count) :
    (fun z => scheduledBlockStateStepEval^[min (count z) (scheduledBlockDepth (n z) (requested z))]
      (scheduledBlockStateInit (n z) (requested z) (e z))) ∈ FP :=
  Internal.scheduledBlockStateInit_iterate_mem_FP hn hrequested he hcount

end Algebraic.Cutwidth.Extractor
