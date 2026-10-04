/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
import Mathlib.Tactic.NormNum

/-!
# Flat-source bookkeeping for the actual construction

The maximum entropy reserve supplies the original affine point-mass cap
and the sampler support threshold. Restricting the ambient flat-weight
average to its support changes neither its value nor its normalization.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem weightedMean_flatWeight {α : Type*} [Fintype α]
    (P : Finset α) (f : α → ℝ) :
    weightedMean Finset.univ (flatWeight P) f =
      weightedMean P (fun _ => 1 / (P.card : ℝ)) f := by
  simp only [weightedMean, flatWeight, ite_mul, zero_mul, Finset.sum_ite_mem_eq, one_div]

theorem sourceReduction_flatWeight_cap (n L : Nat) (P : Finset (Fin n → Bool))
    (size : 2 ^ sourceReductionEntropy n L ≤ P.card) :
    ∀ x, flatWeight P x ≤
      ((2 : ℝ) ^ affineLeakageSourceEntropy n
        (sourceReductionTamperingCount (matchedBlockSeedBits L))
        (sourceReductionAdviceLength (matchedBlockSeedBits L))
        (sourceReductionTarget (matchedBlockSeedBits L)))⁻¹ := by
  have reserve : affineLeakageSourceEntropy n
      (sourceReductionTamperingCount (matchedBlockSeedBits L))
      (sourceReductionAdviceLength (matchedBlockSeedBits L))
      (sourceReductionTarget (matchedBlockSeedBits L)) ≤ sourceReductionEntropy n L :=
    le_max_left _ _
  have cap := cappedWeight_flatWeight P
    ((Nat.pow_le_pow_right (by decide : 0 < 2) reserve).trans size)
  intro x
  rw [← one_div]
  apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using cap x

theorem sourceReduction_sampler_threshold (n L : Nat) (Q : Finset (Fin n → Bool))
    (size : 2 ^ sourceReductionEntropy n L ≤ Q.card) :
    (2 : ℝ) ^ amplifiedMatchedSamplerEntropy L (sourceReductionSeedBits n L) ≤ Q.card := by
  have reserve : amplifiedMatchedSamplerEntropy L (sourceReductionSeedBits n L) ≤
      sourceReductionEntropy n L := le_max_right _ _
  exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) reserve).trans size

end Algebraic.Cutwidth.Extractor.Internal
