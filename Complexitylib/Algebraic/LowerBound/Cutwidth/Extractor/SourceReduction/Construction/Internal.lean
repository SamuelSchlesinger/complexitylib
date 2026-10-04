/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Internal.Sampler
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Selection
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Assembling the actual finite sumset extractor

One source reserve supplies both the actual affine test theorem and the
actual amplified sampler. Exact parameter budgets allow the selection
theorem to retain enough coordinates for the checked majority argument.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem sourceReductionExtractor_flat (n L : Nat) (positive : 0 < L)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (gamma : GammaBlockSizeGuard (matchedBlockSeedBits L)) :
    FlatSumsetExtractor (sourceReductionExtractor n L) (2 ^ sourceReductionEntropy n L)
      (35 / 72) := by
  let b := matchedBlockSeedBits L
  have bpos : 0 < b := by dsimp [b, matchedBlockSeedBits]; positivity
  have large : 5 ≤ b := by dsimp [b, matchedBlockSeedBits]; lia
  have sample := sourceReductionSampler_somewhereSampler n L positive base gamma
  apply majority_flatSumsetExtractor_of_parity_fibers (sourceReductionOutput n L)
    (by positivity) (sourceReductionParityBias_nonneg b)
  intro P Q leftSize rightSize
  have leftPositive : 0 < P.card := (by positivity : 0 < 2 ^ sourceReductionEntropy n L).trans_le
    leftSize
  have rightPositive : 0 < Q.card := (by positivity : 0 < 2 ^ sourceReductionEntropy n L).trans_le
    rightSize
  obtain ⟨bad, small, estimate⟩ := affineSourceReduction_exists_tests n
    (sourceReductionOuterCount b) (sourceReductionCandidateCount b)
    (sourceReductionAdviceLength b) (sourceReductionTarget b) (flatWeight P)
    (sourceReductionSampler n L)
    (sourceReductionAdvice (sourceReductionOuterBits b) (sourceReductionCandidateBits b))
    (sourceReductionCandidateCount_pos b) (sourceReductionAdviceLength_pos bpos)
    (sourceReductionBadThreshold_pos b)
    (isProbabilityWeight_flatWeight P (Finset.card_pos.mp leftPositive))
    (sourceReduction_flatWeight_cap n L P leftSize)
    (sourceReductionAdvice_length _ _) (sourceReductionAdvice_injective _ _)
    (sourceReductionSampler_xor n L)
  have budget : (sourceReductionOuterCount b : ℝ) ^ 4 *
      Fintype.card (Fin (sourceReductionCandidateCount b)) *
      (((2 : ℝ) ^ sourceReductionTarget b)⁻¹ / sourceReductionBadThreshold b) ≤
        sourceReductionSamplerError b := by
    simpa only [Fintype.card_fin] using (sourceReduction_union_budget b).le
  obtain ⟨G, subset, mass, fibers⟩ := sample.parity_fibers
    (s := P) (w := fun _ => 1 / (P.card : ℝ)) (β := sourceReductionParityBias b)
    (fun x y i => if sourceReductionOutput n L (xorInput x y) i then (1 : ℝ) else -1)
    Q rightPositive (sourceReduction_sampler_threshold n L Q rightSize)
    bad (div_nonneg (inv_nonneg.mpr (by positivity))
      (sourceReductionBadThreshold_pos b).le) small budget (by
      intro U member
      obtain ⟨j, inside, bound⟩ := estimate U member
      refine ⟨j, inside, ?_⟩
      intro z y _ escapes
      rw [← weightedMean_flatWeight]
      exact bound z y escapes)
  refine ⟨G, subset, ?_, ?_⟩
  · simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using mass
  · intro y member
    obtain ⟨m, good, discarded, parity⟩ := fibers y member
    have size : m ≤ sourceReductionOuterCount b := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective good good.injective
    have guards := sourceReduction_majority_guards large size discarded
    exact ⟨m, good, guards.1, sourceReduction_moment_budget size, parity, guards.2⟩

end Algebraic.Cutwidth.Extractor.Internal
