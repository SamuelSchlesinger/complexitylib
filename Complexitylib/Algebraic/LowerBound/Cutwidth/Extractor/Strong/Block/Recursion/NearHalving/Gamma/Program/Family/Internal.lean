/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Correctness
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Asymptotics

/-!
# The total Gamma program computes the specified extractor family

The finite size guard selects the full near-halving runtime. Exact complete
program correspondence and output-prefix serialization identify its output
with the Boolean Gamma map. Exact input length also recovers the target
parameter of the paired evaluator. Eventual guard validity transfers these
identities uniformly over all sources, exact-width seeds, and trailing bits.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem gammaBlockExtractorRuntime_append_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool) :
    gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed ++ tail) =
      List.ofFn (gammaBlockExtractor b x seed) := by
  rw [gammaBlockExtractorRuntime_of_guard b _ _ guard, gammaBlockExtractor_ofFn,
    gammaBlockLeafLength_eq]
  exact congrArg (List.take b)
    (nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockBooleanExtractor
      (8 * b) (gammaBlockDepth b) (gammaBlockReserve b) (gammaBlockErrorExponent b) x seed tail)

theorem gammaBlockExtractorRuntime_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) :
    gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed) =
      List.ofFn (gammaBlockExtractor b x seed) := by
  simpa only [List.append_nil] using gammaBlockExtractorRuntime_append_eq b guard x seed []

theorem gammaBlockExtractorEval_pair_append_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool) :
    gammaBlockExtractorEval (Complexity.pair (List.ofFn x) (List.ofFn seed ++ tail)) =
      List.ofFn (gammaBlockExtractor b x seed) := by
  rw [gammaBlockExtractorEval_pair, show (List.ofFn x).length / 8 = b by simp]
  exact gammaBlockExtractorRuntime_append_eq b guard x seed tail

theorem gammaBlockExtractorEval_pair_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) :
    gammaBlockExtractorEval (Complexity.pair (List.ofFn x) (List.ofFn seed)) =
      List.ofFn (gammaBlockExtractor b x seed) := by
  simpa only [List.append_nil] using gammaBlockExtractorEval_pair_append_eq b guard x seed []

theorem eventually_gammaBlockExtractorRuntime :
    ∀ᶠ b : Nat in Filter.atTop,
      ∀ (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool),
        gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed ++ tail) =
          List.ofFn (gammaBlockExtractor b x seed) :=
  eventually_gammaBlockSizeGuard.mono fun b guard x seed tail =>
    gammaBlockExtractorRuntime_append_eq b guard x seed tail

theorem eventually_gammaBlockExtractorEval :
    ∀ᶠ b : Nat in Filter.atTop,
      ∀ (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool),
        gammaBlockExtractorEval (Complexity.pair (List.ofFn x) (List.ofFn seed ++ tail)) =
          List.ofFn (gammaBlockExtractor b x seed) :=
  eventually_gammaBlockSizeGuard.mono fun b guard x seed tail =>
    gammaBlockExtractorEval_pair_append_eq b guard x seed tail

end Algebraic.Cutwidth.Extractor.Internal
