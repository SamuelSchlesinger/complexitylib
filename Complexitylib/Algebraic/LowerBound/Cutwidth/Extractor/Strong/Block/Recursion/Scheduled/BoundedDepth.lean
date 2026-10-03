/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.BoundedDepth.Internal

/-!
# Finite seed and entropy bounds at fixed recursion depths

Every scheduled extractor of depth at most sixty-four has at most
`2^24 * L` seed bits when its local error exponent and input logarithm fit
the common width `L`. At depths twenty-four and sixty-four, its source
entropy threshold is bounded by `2^62 * L` and `2^142 * L`, respectively.
Together with the actual output length `2^h * L`, these conservative
estimates support matching the seed widths of successive extractor calls.

These constants are our arithmetic deductions from the checked scheduled
construction. The recursive method is credited in `Recursion.Extraction`.
They are intended for the alternating-extraction and flip-flop route of
Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes, with their
Many Tampered Extensions*, Section 6, Algorithms 1--2,
<https://arxiv.org/pdf/1505.00107>. This module proves only finite numerical
bounds, not a correlation-breaker construction or its statistical guarantee.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A common width bounds every actual seed tuple at depth at most sixty-four. -/
theorem scheduledBlockSeedBits_boundedDepth_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L)
    (depth : h ≤ 64) (error : E ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L E) E L ≤ 2 ^ 24 * L :=
  Internal.scheduledBlockSeedBits_boundedDepth_le n L E h length room depth error

/-- The actual depth-twenty-four source entropy is linear in the common width. -/
theorem recursiveBlockEntropy_depth24_le (L E : Nat) (positive : 1 ≤ L) (error : E ≤ L) :
    recursiveBlockEntropy 24 (recursiveBlockReserve L E) 0 ≤ 2 ^ 62 * L :=
  Internal.recursiveBlockEntropy_depth24_le L E positive error

/-- The actual depth-sixty-four source entropy is linear in the common width. -/
theorem recursiveBlockEntropy_depth64_le (L E : Nat) (positive : 1 ≤ L) (error : E ≤ L) :
    recursiveBlockEntropy 64 (recursiveBlockReserve L E) 0 ≤ 2 ^ 142 * L :=
  Internal.recursiveBlockEntropy_depth64_le L E positive error

end Algebraic.Cutwidth.Extractor
