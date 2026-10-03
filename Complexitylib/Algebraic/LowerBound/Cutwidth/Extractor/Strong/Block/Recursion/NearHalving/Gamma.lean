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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Internal

/-!
# An actual quarter-error Gamma extractor with a polylogarithmic seed

For all sufficiently large `b`, the specified map takes `8*b` input bits
with min-entropy at least `2*b` and returns `b` bits with error at most
one quarter. The stronger weighted theorem retains the entire independent
Boolean seed. Its actual length is at most `2^27 * (Nat.clog 2 (b+1))^3`.

The construction instantiates the checked recursive condenser/splitting
method of Chattopadhyay, Goodman, and Liao, Theorem 5.6 of
*Affine Extractors for Almost Logarithmic Entropy*,
<https://eccc.weizmann.ac.il/report/2021/075/>, with this library's
near-halving parameters, then keeps an output prefix. These semantic
guarantees use no supplied extractor or field instances. Polynomial-time
evaluation is a separate layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Listing the selected Gamma output takes the corresponding prefix of the actual output. -/
theorem gammaBlockExtractor_ofFn (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBits b) → Bool) :
    List.ofFn (gammaBlockExtractor b x seed) =
      (List.ofFn (nearHalvingBlockBooleanExtractor (8 * b) (gammaBlockDepth b)
        (gammaBlockReserve b) (gammaBlockErrorExponent b) x seed)).take b :=
  Internal.gammaBlockExtractor_ofFn b x seed

/-- The actual selected map strongly extracts from every capped finite weighted source. -/
theorem gammaBlockExtractor_weighted {b : Nat} (guard : GammaBlockSizeGuard b) :
    WeightedStrongSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.gammaBlockExtractor_weighted guard

/-- Forgetting the retained seed gives the ordinary flat seeded-extractor contract. -/
theorem gammaBlockExtractor_flat {b : Nat} (guard : GammaBlockSizeGuard b) :
    FlatSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.gammaBlockExtractor_flat guard

/-- The selected map's actual complete seed length is bounded by a cubic logarithm. -/
theorem gammaBlockSeedBits_bound {b : Nat} (guard : GammaBlockSizeGuard b) :
    gammaBlockSeedBits b ≤ 2 ^ 27 * gammaBlockLog b ^ 3 :=
  Internal.gammaBlockSeedBits_bound guard

/-- All sufficiently large targets have the weighted retained-seed guarantee. -/
theorem eventually_gammaBlockExtractor_weighted :
    ∀ᶠ b : Nat in Filter.atTop,
      WeightedStrongSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.eventually_gammaBlockExtractor_weighted

/-- All sufficiently large targets give an ordinary flat seeded extractor. -/
theorem eventually_gammaBlockExtractor_flat :
    ∀ᶠ b : Nat in Filter.atTop,
      FlatSeededExtractor (gammaBlockExtractor b) (2 ^ (2 * b)) (1 / 4) :=
  Internal.eventually_gammaBlockExtractor_flat

/-- The actual seed lengths eventually satisfy the explicit polylogarithmic bound. -/
theorem eventually_gammaBlockSeedBits_bound :
    ∀ᶠ b : Nat in Filter.atTop, gammaBlockSeedBits b ≤ 2 ^ 27 * gammaBlockLog b ^ 3 :=
  Internal.eventually_gammaBlockSeedBits_bound

end Algebraic.Cutwidth.Extractor
