/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Defs

/-!
# Total runtime parameters for the numerical block schedule

The source length determines its ceiling binary logarithm. The requested
depth is clipped to that logarithm before selecting the local error exponent,
leaf reserve, and initial entropy. Initial rate-one compression determines
the actual starting width. The encoded initializer uses the standard
numerical state codec; every definition is total on natural inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The input logarithm used by the total numerical initializer. -/
def scheduledBlockInputLog (n : Nat) : Nat := Nat.clog 2 (n + 1)

/-- Clip the requested depth to the source-length logarithm. -/
def scheduledBlockDepth (n requested : Nat) : Nat := min requested (scheduledBlockInputLog n)

/-- Local error exponent paying for the clipped number of levels. -/
def scheduledBlockErrorExponent (n requested e : Nat) : Nat :=
  e + scheduledBlockDepth n requested + 2

/-- The finite leaf reserve selected from the input logarithm and local error. -/
def scheduledBlockLeafReserve (n requested e : Nat) : Nat :=
  recursiveBlockReserve (scheduledBlockInputLog n) (scheduledBlockErrorExponent n requested e)

/-- Initial entropy for the clipped-depth schedule. -/
def scheduledBlockInitialEntropy (n requested e : Nat) : Nat :=
  recursiveBlockEntropy (scheduledBlockDepth n requested)
    (scheduledBlockLeafReserve n requested e) 0

/-- Actual initial compressed width for the total runtime parameter choice. -/
def scheduledBlockRuntimeInitialWidth (n requested e : Nat) : Nat :=
  scheduledBlockInitialWidth n (scheduledBlockDepth n requested)
    (scheduledBlockLeafReserve n requested e) (scheduledBlockErrorExponent n requested e)

/-- Initialize the encoded numerical state from runtime source length, depth, and error. -/
def scheduledBlockStateInit (n requested e : Nat) : List Bool :=
  encodeScheduledBlockState (scheduledBlockErrorExponent n requested e)
    (scheduledBlockRuntimeInitialWidth n requested e, scheduledBlockInitialEntropy n requested e)

end Algebraic.Cutwidth.Extractor
