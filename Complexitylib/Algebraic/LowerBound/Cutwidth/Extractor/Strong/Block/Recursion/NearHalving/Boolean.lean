/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean.Internal

/-!
# Near-halving strong extraction on ordinary Boolean vectors

The full uniform Boolean seed decodes to the exact retained field-seed
tuple. Outputs use a single Boolean index in block order. Bijections
preserve the strong-extraction guarantee, with no caller-supplied field
enumeration instances. The exact list identity fixes the representation
needed by the separate string evaluator.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Boolean seed and output transport preserves the complete recursive error bound. -/
theorem nearHalvingBlockBooleanExtractor_weighted (n h Q E : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) E + 4 * E ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockBooleanExtractor n h Q E)
      (2 ^ nearHalvingBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) :=
  Internal.nearHalvingBlockBooleanExtractor_weighted n h Q E capacity budget

/-- The Boolean-vector map extracts with error `2^(-e)` at local exponent `e+h+2`. -/
theorem nearHalvingBlockBooleanExtractor_dyadic (n h Q e : Nat)
    (capacity : nearHalvingBlockEntropy h Q 0 ≤ n)
    (budget : 12 * (nearHalvingBlockRate h + 1) *
      explicitCondenserBudget n (nearHalvingBlockEntropy h Q 0) (e + h + 2) +
      4 * (e + h + 2) ≤ Q) :
    WeightedStrongSeededExtractor (nearHalvingBlockBooleanExtractor n h Q (e + h + 2))
      (2 ^ nearHalvingBlockEntropy h Q 0) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.nearHalvingBlockBooleanExtractor_dyadic n h Q e capacity budget

/-- Listing the Boolean output reads the semantic tuple in consecutive block order. -/
theorem nearHalvingBlockBooleanExtractor_ofFn (n h Q E : Nat) (x : Fin n → Bool)
    (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool) :
    List.ofFn (nearHalvingBlockBooleanExtractor n h Q E x seed) =
      (List.ofFn fun i => List.ofFn fun j => decide (nearHalvingBlockExtractor n h Q E x
        (decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed)) i j = 1)).flatten :=
  Internal.nearHalvingBlockBooleanExtractor_ofFn n h Q E x seed

end Algebraic.Cutwidth.Extractor
