/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite sampling for the actual Gamma and matched composition

The growing extractor keeps error one sixteenth while Gamma supplies
three-quarter neighbor coverage. The target test density may be much
smaller than that constant error. One extra source-entropy bit makes the
sampler failure probability one half.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem target_error_le (b : Nat) (positive : 0 < b) :
    ((2 : ℝ) ^ (5 * b))⁻¹ ≤ 1 / 16 := by
  have order : (2 : ℝ) ^ 4 ≤ 2 ^ (5 * b) :=
    pow_le_pow_right₀ (by norm_num) (by lia)
  calc
    _ ≤ ((2 : ℝ) ^ 4)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) order
    _ = 1 / 16 := by norm_num

private theorem amplification_budget (b : Nat) :
    ((2 ^ (2 * b) : Nat) : ℝ) ≤
      2 * ((2 : ℝ) ^ (5 * b))⁻¹ * Fintype.card (Fin (8 * b) → Bool) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  have identity : 2 * ((2 : ℝ) ^ (5 * b))⁻¹ * 2 ^ (8 * b) = 2 ^ (3 * b + 1) := by
    rw [show 8 * b = 5 * b + 3 * b by lia, pow_add, pow_succ]
    field_simp
  rw [identity]
  exact pow_le_pow_right₀ (by norm_num) (by lia)

theorem amplifiedMatchedSampler_somewhereSampler (n L d : Nat) (positive : 0 < L)
    (base : GrowingMatchedBlockRuntimeValid n d L 4)
    (gamma : GammaBlockSizeGuard (matchedBlockSeedBits L)) :
    SomewhereSampler (amplifiedMatchedSampler n L d)
      ((2 : ℝ) ^ amplifiedMatchedSamplerEntropy L d)
      (((2 : ℝ) ^ (5 * matchedBlockSeedBits L))⁻¹) (1 / 2) := by
  let h := growingMatchedBlockDepth d
  let E := fun (x : Fin n → Bool) (seed : Fin (matchedBlockSeedBits L) → Bool)
    (j : Fin d) => matchedBlockExtractor n h L 4 x seed
      (Fin.castLE (amplifiedMatchedSampler_output_capacity L d positive) j)
  have extract : FlatSeededExtractor E (2 ^ (2 ^ (2 * h + 14) * L)) (1 / 16) := by
    have strong := (matchedBlockExtractor_growing n h L 4 base.1 base.2.1 base.2.2).truncate
      (amplifiedMatchedSampler_output_capacity L d positive)
    simpa only [E, show ((2 : ℝ) ^ 4)⁻¹ = 1 / 16 by norm_num] using
      strong.flatStrongSeededExtractor.flatSeededExtractor
  have sample : Sampler E ((2 : ℝ) ^ amplifiedMatchedSamplerEntropy L d) (1 / 16) (1 / 2) := by
    apply extract.sampler (by positivity) (by positivity)
    simp only [amplifiedMatchedSamplerEntropy, Nat.cast_pow, Nat.cast_ofNat, pow_succ, h]
    linarith
  have cover := (gammaBlockPaddedExtractor_flat gamma).neighborCoverage (by positivity)
  have small := target_error_le (matchedBlockSeedBits L) (by
    unfold matchedBlockSeedBits
    positivity)
  have result := sample.amplify cover small (by norm_num) (amplification_budget _)
  convert result using 1
  funext x outer candidate
  exact amplifiedMatchedSampler_eq_prefix n L d positive x outer candidate

end Algebraic.Cutwidth.Extractor.Internal
