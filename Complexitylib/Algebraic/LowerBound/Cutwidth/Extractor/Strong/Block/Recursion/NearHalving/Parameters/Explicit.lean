/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Internal

/-!
# Finite bounds for the rounded near-halving parameters

Under the explicit size guard, the selected schedule accepts source entropy
at most `2*b`, produces at least `b` output bits, and pays every split with its
actual sparse-field seed width. Its complete seed count, including the final
one-shot pair, is at most `2^27 * (Nat.clog 2 (b+1))^3`.

These are finite parameter estimates for the recursive method of
Chattopadhyay, Goodman, and Liao. The offset and constants account for this
library's explicit rounded fields; eventual validity and runtime are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The size guard excludes the empty target. -/
theorem GammaBlockSizeGuard.pos {b : Nat} (guard : GammaBlockSizeGuard b) : 0 < b :=
  Internal.gammaBlock_pos guard

/-- The selected depth is bounded by the input ceiling logarithm. -/
theorem gammaBlockDepth_le (b : Nat) : gammaBlockDepth b ≤ gammaBlockLog b :=
  Internal.gammaBlockDepth_le b

/-- The output quantum is positive even outside the size guard. -/
theorem gammaBlockOutputQuantum_pos (b : Nat) : 0 < gammaBlockOutputQuantum b :=
  Internal.gammaBlockOutputQuantum_pos b

/-- Rounding the reserve upward covers the desired output length. -/
theorem gammaBlock_output_ge (b : Nat) :
    b ≤ 2 ^ gammaBlockDepth b * gammaBlockLeafLength b :=
  Internal.gammaBlock_output_ge b

/-- The rounding quantum consumes at most half of the target length. -/
theorem gammaBlockOutputQuantum_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    2 * gammaBlockOutputQuantum b ≤ b :=
  Internal.gammaBlockOutputQuantum_le guard

/-- The selected input entropy fits the desired threshold of `2*b` bits. -/
theorem gammaBlockInputEntropy_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockInputEntropy b ≤ 2 * b :=
  Internal.gammaBlockInputEntropy_le guard

/-- The reserve pays quadratic logarithmic sparse-field overhead. -/
theorem gammaBlockReserve_lower {b : Nat} (guard : GammaBlockSizeGuard b) :
    4096 * (gammaBlockLog b + 1) ^ 2 ≤ gammaBlockReserve b :=
  Internal.gammaBlockReserve_lower guard

/-- The guarded reserve is positive. -/
theorem gammaBlockReserve_pos {b : Nat} (guard : GammaBlockSizeGuard b) :
    0 < gammaBlockReserve b :=
  Internal.gammaBlockReserve_pos guard

/-- The common condenser budget is logarithmic in the target length. -/
theorem gammaBlockBudget_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    explicitCondenserBudget (8 * b) (gammaBlockInputEntropy b) (gammaBlockErrorExponent b) ≤
      13 * (gammaBlockLog b + 1) :=
  Internal.gammaBlockBudget_le guard

/-- The selected reserve satisfies the complete generic split budget. -/
theorem gammaBlock_split_budget {b : Nat} (guard : GammaBlockSizeGuard b) :
    12 * (nearHalvingBlockRate (gammaBlockDepth b) + 1) *
        explicitCondenserBudget (8 * b) (gammaBlockInputEntropy b) (gammaBlockErrorExponent b) +
      4 * gammaBlockErrorExponent b ≤ gammaBlockReserve b :=
  Internal.gammaBlock_split_budget guard

/-- Each final leaf has a cubic logarithmic output length. -/
theorem gammaBlockLeafLength_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockLeafLength b ≤ 524296 * (gammaBlockLog b + 1) ^ 3 :=
  Internal.gammaBlockLeafLength_le guard

/-- The explicit threshold equals the initial threshold of the generic schedule. -/
theorem gammaBlockInputEntropy_eq (b : Nat) :
    gammaBlockInputEntropy b =
      nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0 :=
  Internal.gammaBlockInputEntropy_eq b

/-- The explicit leaf length equals the generic schedule's final output length. -/
theorem gammaBlockLeafLength_eq (b : Nat) :
    gammaBlockLeafLength b = nearHalvingBlockLeafLength (gammaBlockDepth b) (gammaBlockReserve b) :=
  Internal.gammaBlockLeafLength_eq b

/-- The actual seed count, including both final one-shot seeds, is polylogarithmic. -/
theorem gammaBlockSeedBits_le {b : Nat} (guard : GammaBlockSizeGuard b) :
    nearHalvingBlockSeedBits (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
        (gammaBlockErrorExponent b) ≤ 2 ^ 27 * gammaBlockLog b ^ 3 :=
  Internal.gammaBlockSeedBits_le guard

end Algebraic.Cutwidth.Extractor
