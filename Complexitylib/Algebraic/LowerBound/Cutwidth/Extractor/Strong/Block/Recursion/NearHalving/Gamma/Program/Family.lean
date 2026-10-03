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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Family.Internal

/-!
# Exact uniform evaluation of the Gamma extractor family

Under the finite size guard, the actual total runtime computes the specified
Boolean Gamma extractor on every source and every exact-width seed. The
paired evaluator infers `b` from its `8*b` input bits. Both identities allow
arbitrary bits after the full seed word, which the program ignores.

The guard holds eventually, so a single total string program computes this
family at all sufficiently large sizes. The program's unconditional FP
certificate lives in `Gamma.Program`; the statistical guarantee and actual
seed-length bound live in `Gamma`. Padding to a larger fixed seed budget is
a separate transport layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The guarded runtime computes Gamma and ignores any suffix after the exact seed word. -/
theorem gammaBlockExtractorRuntime_append_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool) :
    gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed ++ tail) =
      List.ofFn (gammaBlockExtractor b x seed) :=
  Internal.gammaBlockExtractorRuntime_append_eq b guard x seed tail

/-- At the exact Boolean seed word, the guarded runtime computes every Gamma output bit. -/
theorem gammaBlockExtractorRuntime_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) :
    gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed) =
      List.ofFn (gammaBlockExtractor b x seed) :=
  Internal.gammaBlockExtractorRuntime_eq b guard x seed

/-- The paired evaluator recovers the target from the source length and ignores seed padding. -/
theorem gammaBlockExtractorEval_pair_append_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool) :
    gammaBlockExtractorEval (Complexity.pair (List.ofFn x) (List.ofFn seed ++ tail)) =
      List.ofFn (gammaBlockExtractor b x seed) :=
  Internal.gammaBlockExtractorEval_pair_append_eq b guard x seed tail

/-- The single paired string evaluator agrees with Gamma on all guarded canonical inputs. -/
theorem gammaBlockExtractorEval_pair_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) :
    gammaBlockExtractorEval (Complexity.pair (List.ofFn x) (List.ofFn seed)) =
      List.ofFn (gammaBlockExtractor b x seed) :=
  Internal.gammaBlockExtractorEval_pair_eq b guard x seed

/-- Eventually the actual runtime computes Gamma uniformly over all sources, seeds, and padding. -/
theorem eventually_gammaBlockExtractorRuntime :
    ∀ᶠ b : Nat in Filter.atTop,
      ∀ (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool),
        gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed ++ tail) =
          List.ofFn (gammaBlockExtractor b x seed) :=
  Internal.eventually_gammaBlockExtractorRuntime

/-- One paired evaluator eventually computes the entire Gamma family, including padded seeds. -/
theorem eventually_gammaBlockExtractorEval :
    ∀ᶠ b : Nat in Filter.atTop,
      ∀ (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBits b) → Bool) (tail : List Bool),
        gammaBlockExtractorEval (Complexity.pair (List.ofFn x) (List.ofFn seed ++ tail)) =
          List.ofFn (gammaBlockExtractor b x seed) :=
  Internal.eventually_gammaBlockExtractorEval

end Algebraic.Cutwidth.Extractor
