/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Weighted.Internal

/-!
# One-shot extraction from nonuniform finite sources

The actual program extracts `ell` bits with error `2^(-e)` from every
normalized source whose point masses are at most `2^(-(ell+2*e))`.
Sources may be represented by any injective encoding into `n`-bit words;
the direct Boolean-vector instance needs no supplied encoding. Both seeds
remain in every statistical test.

Only the statistical guarantee is extended. The program and its previously
checked uniform polynomial-time certificate are the same as for flat
sources. The mixture proof does not require sampling or computing the
source probabilities.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual one-shot program strongly extracts from every capped finite
source with an injective fixed-length bit encoding. -/
theorem decodedOneShotExtractor_weightedStrongSeededExtractor (n ell e : Nat)
    {α : Type*} [Fintype α]
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    (input : α ↪ List Bool) (source : ∀ x, (input x).length = n) :
    WeightedStrongSeededExtractor
      (fun x => decodedOneShotExtractor n ell e (input x))
      (2 ^ (ell + 2 * e)) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.decodedOneShotExtractor_weightedStrongSeededExtractor n ell e input source

/-- In particular, all normalized capped distributions on `n` Boolean
coordinates satisfy the one-shot guarantee at the same parameters. -/
theorem decodedOneShotExtractor_ofFn_weighted (n ell e : Nat)
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))] :
    WeightedStrongSeededExtractor
      (fun x : Fin n → Bool => decodedOneShotExtractor n ell e (List.ofFn x))
      (2 ^ (ell + 2 * e)) (((2 : ℝ) ^ e)⁻¹) :=
  Internal.decodedOneShotExtractor_ofFn_weighted n ell e

end Algebraic.Cutwidth.Extractor
