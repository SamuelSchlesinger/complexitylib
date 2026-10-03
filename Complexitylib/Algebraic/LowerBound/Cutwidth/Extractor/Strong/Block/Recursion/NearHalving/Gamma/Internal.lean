/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Asymptotics
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Quarter-error extraction from the selected actual recursive construction

The finite parameter bounds pay all recursive budgets. Keeping an output
prefix preserves uniformity, and increasing the source threshold to `2^(2*b)`
preserves the same error. Eventual claims use the proved numerical size guard.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem gammaBlock_output_capacity (b : Nat) :
    b ≤ recursiveBlockCount 1 (gammaBlockDepth b) *
      nearHalvingBlockLeafLength (gammaBlockDepth b) (gammaBlockReserve b) := by
  simpa only [recursiveBlockCount_eq, Nat.mul_one, ← gammaBlockLeafLength_eq] using
    gammaBlock_output_ge b

theorem gammaBlockExtractor_ofFn (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBits b) → Bool) :
    List.ofFn (gammaBlockExtractor b x seed) =
      (List.ofFn (nearHalvingBlockBooleanExtractor (8 * b) (gammaBlockDepth b)
        (gammaBlockReserve b) (gammaBlockErrorExponent b) x seed)).take b := by
  exact Fin.ofFn_take_eq_take_ofFn (gammaBlock_output_capacity b)
    (nearHalvingBlockBooleanExtractor (8 * b) (gammaBlockDepth b)
      (gammaBlockReserve b) (gammaBlockErrorExponent b) x seed)

theorem gammaBlockExtractor_weighted {b : Nat} (guard : GammaBlockSizeGuard b) :
    WeightedStrongSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) := by
  have capacity : nearHalvingBlockEntropy (gammaBlockDepth b) (gammaBlockReserve b) 0 ≤
      8 * b := by
    rw [← gammaBlockInputEntropy_eq]
    have := gammaBlockInputEntropy_le guard
    lia
  have error : 2 + gammaBlockDepth b + 2 = gammaBlockErrorExponent b := by
    unfold gammaBlockErrorExponent
    lia
  have extract := nearHalvingBlockBooleanExtractor_dyadic (8 * b) (gammaBlockDepth b)
    (gammaBlockReserve b) 2 capacity (by
      rw [error, ← gammaBlockInputEntropy_eq]
      exact gammaBlock_split_budget guard)
  rw [error] at extract
  norm_num at extract
  exact (extract.truncate (gammaBlock_output_capacity b)).mono_threshold
    (Nat.pow_le_pow_right (by decide) (by
      rw [← gammaBlockInputEntropy_eq]
      exact gammaBlockInputEntropy_le guard))

theorem gammaBlockExtractor_flat {b : Nat} (guard : GammaBlockSizeGuard b) :
    FlatSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  (gammaBlockExtractor_weighted guard).flatStrongSeededExtractor.flatSeededExtractor

theorem gammaBlockSeedBits_bound {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockSeedBits b ≤ 2 ^ 27 * gammaBlockLog b ^ 3 :=
  gammaBlockSeedBits_le guard

theorem eventually_gammaBlockExtractor_weighted :
    ∀ᶠ b : Nat in Filter.atTop,
      WeightedStrongSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  eventually_gammaBlockSizeGuard.mono fun _ guard => gammaBlockExtractor_weighted guard

theorem eventually_gammaBlockExtractor_flat :
    ∀ᶠ b : Nat in Filter.atTop,
      FlatSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  eventually_gammaBlockSizeGuard.mono fun _ guard => gammaBlockExtractor_flat guard

theorem eventually_gammaBlockSeedBits_bound :
    ∀ᶠ b : Nat in Filter.atTop, gammaBlockSeedBits b ≤ 2 ^ 27 * gammaBlockLog b ^ 3 :=
  eventually_gammaBlockSizeGuard.mono fun _ guard => gammaBlockSeedBits_bound guard

end Algebraic.Cutwidth.Extractor.Internal
