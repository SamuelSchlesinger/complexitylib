/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded.Internal

/-!
# A uniform Gamma extractor with an explicit Boolean seed budget

The actual total polynomial-time program takes `8*b` source bits and exactly
`2^27 * (Nat.clog 2 (b+1))^3` seed bits, and emits `b` bits. At every size
satisfying the guard, it extracts with error at most one quarter from sources
of min-entropy at least `2*b`. This holds eventually in `b`.

The stronger weighted theorem retains the entire padded seed, including its
unused suffix. The evaluator equality holds at all sizes; outside the guard
the program's defined output is all false. No field instances or abstract
extractor are supplied by the caller. This interface combines the CGL-based
recursive construction with its proved runtime and seed-padding transport.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The Boolean output vector is exactly the actual runtime's word, at every size. -/
theorem gammaBlockPaddedExtractor_ofFn (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBudget b) → Bool) :
    List.ofFn (gammaBlockPaddedExtractor b x seed) =
      gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed) :=
  Internal.gammaBlockPaddedExtractor_ofFn b x seed

/-- The simple seed budget covers the actual seed tuple whenever the size guard holds. -/
theorem gammaBlockSeedBits_le_budget {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockSeedBits b ≤ gammaBlockSeedBudget b :=
  Internal.gammaBlockSeedBits_le_budget guard

/-- At guarded sizes, the actual padded program uses precisely the required seed prefix. -/
theorem gammaBlockPaddedExtractor_eq (b : Nat) (guard : GammaBlockSizeGuard b)
    (x : Fin (8 * b) → Bool) (seed : Fin (gammaBlockSeedBudget b) → Bool) :
    gammaBlockPaddedExtractor b x seed = gammaBlockExtractor b x
      (fun j => seed (Fin.castLE (gammaBlockSeedBits_le_budget guard) j)) :=
  Internal.gammaBlockPaddedExtractor_eq b guard x seed

/-- The actual program strongly extracts while retaining every padded seed bit. -/
theorem gammaBlockPaddedExtractor_weighted {b : Nat} (guard : GammaBlockSizeGuard b) :
    WeightedStrongSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.gammaBlockPaddedExtractor_weighted guard

/-- The same actual program is an ordinary flat seeded extractor. -/
theorem gammaBlockPaddedExtractor_flat {b : Nat} (guard : GammaBlockSizeGuard b) :
    FlatSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.gammaBlockPaddedExtractor_flat guard

open Complexity in
/-- The existing polynomial-time paired evaluator computes every padded Boolean output. -/
theorem gammaBlockPaddedExtractor_eval (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBudget b) → Bool) :
    gammaBlockExtractorEval (pair (List.ofFn x) (List.ofFn seed)) =
      List.ofFn (gammaBlockPaddedExtractor b x seed) :=
  Internal.gammaBlockPaddedExtractor_eval b x seed

open Complexity in
/-- The complete padded seed budget can be generated in unary in polynomial time. -/
@[polytime] theorem gammaBlockSeedBudget_unaryFn {b : List Bool → Nat} (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockSeedBudget (b z) :=
  Internal.gammaBlockSeedBudget_unaryFn hb

/-- Every sufficiently large target has the full weighted retained-seed guarantee. -/
theorem eventually_gammaBlockPaddedExtractor_weighted :
    ∀ᶠ b : Nat in Filter.atTop,
      WeightedStrongSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.eventually_gammaBlockPaddedExtractor_weighted

/-- Every sufficiently large target gives an actual ordinary seeded extractor. -/
theorem eventually_gammaBlockPaddedExtractor_flat :
    ∀ᶠ b : Nat in Filter.atTop,
      FlatSeededExtractor (gammaBlockPaddedExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.eventually_gammaBlockPaddedExtractor_flat

end Algebraic.Cutwidth.Extractor
