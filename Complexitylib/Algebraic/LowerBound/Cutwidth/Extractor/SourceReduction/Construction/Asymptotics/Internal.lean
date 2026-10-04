/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Asymptotics.Internal.Bounds
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Asymptotics.Internal.Growth
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Asymptotics

/-!
# Eventual validity of the actual sumset-extractor family

Choose the scale to be the input's ceiling binary logarithm. The cubic
iterated-logarithmic bounds on candidate bits and the growing depth make
both sampler guards eventual. The selected entropy exponent is bounded by
an exponential of a cubic iterated logarithm and is therefore sublinear.
All statements concern the fixed actual construction and its unbounded
candidate count.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

private theorem nat_isLittleO_of_eventually_le {f g : Nat → Nat}
    (bound : ∀ᶠ n in atTop, f n ≤ g n)
    (small : (fun n => (g n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun n => (g n : ℝ)) _ small
  apply Asymptotics.IsBigO.of_bound (1 : ℝ)
  filter_upwards [bound] with n hn
  simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul] using
    (show (f n : ℝ) ≤ g n by exact_mod_cast hn)

private theorem eventually_candidates_fit :
    ∀ᶠ n : Nat in atTop,
      sourceReductionCandidateBits (matchedBlockSeedBits (Nat.clog 2 (n + 1))) ≤
        Nat.clog 2 (n + 1) := by
  filter_upwards [sourceReduction_tendsto_clog.eventually
    (sourceReduction_eventually_clog_pow_le (2 ^ 41) 3)] with n bound
  exact (sourceReduction_candidateBits_le _).trans bound

theorem sourceReductionCandidateCount_isLittleO :
    (fun n : Nat =>
      (sourceReductionCandidateCount (matchedBlockSeedBits (Nat.clog 2 (n + 1))) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) := by
  apply nat_isLittleO_of_eventually_le (g := fun n =>
    2 ^ (2 ^ 41 * (Nat.clog 2 (Nat.clog 2 (n + 1) + 1) + 1) ^ 3)) _
    (sourceReduction_iterated_exp_isLittleO (2 ^ 41) 3)
  filter_upwards [] with n
  exact Nat.pow_le_pow_right (by decide) (sourceReduction_candidateBits_le _)

theorem eventually_sourceReductionCandidateCount_le :
    ∀ᶠ n : Nat in atTop,
      sourceReductionCandidateCount (matchedBlockSeedBits (Nat.clog 2 (n + 1))) ≤ n + 1 := by
  filter_upwards [sourceReductionCandidateCount_isLittleO.def
    (by norm_num : (0 : ℝ) < 1)] with n bound
  have cast :
      (sourceReductionCandidateCount (matchedBlockSeedBits (Nat.clog 2 (n + 1))) : ℝ) ≤ n := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul] using bound
  exact (show sourceReductionCandidateCount (matchedBlockSeedBits (Nat.clog 2 (n + 1))) ≤ n
    by exact_mod_cast cast).trans (Nat.le_succ n)

theorem sourceReductionEntropy_isLittleO :
    (fun n : Nat => (sourceReductionEntropy n (Nat.clog 2 (n + 1)) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) := by
  apply nat_isLittleO_of_eventually_le (g := fun n =>
    2 ^ (2 ^ 44 * (Nat.clog 2 (Nat.clog 2 (n + 1) + 1) + 1) ^ 3)) _
    (sourceReduction_iterated_exp_isLittleO (2 ^ 44) 3)
  filter_upwards [eventually_candidates_fit,
    sourceReduction_tendsto_clog.eventually (eventually_ge_atTop 1)] with n candidates positive
  exact sourceReductionEntropy_le_cubic_exp le_rfl positive candidates

theorem eventually_sourceReductionEntropy_le :
    ∀ᶠ n : Nat in atTop, sourceReductionEntropy n (Nat.clog 2 (n + 1)) ≤ n := by
  filter_upwards [sourceReductionEntropy_isLittleO.def (by norm_num : (0 : ℝ) < 1)]
    with n bound
  have cast : (sourceReductionEntropy n (Nat.clog 2 (n + 1)) : ℝ) ≤ n := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul] using bound
  exact_mod_cast cast

theorem eventually_sourceReduction_guards :
    ∀ᶠ n : Nat in atTop,
      let L := Nat.clog 2 (n + 1)
      0 < L ∧ GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4 ∧
        GammaBlockSizeGuard (matchedBlockSeedBits L) := by
  have scaled : Tendsto (fun n : Nat => matchedBlockSeedBits (Nat.clog 2 (n + 1)))
      atTop atTop := by
    apply tendsto_atTop_mono _ sourceReduction_tendsto_clog
    intro n
    change Nat.clog 2 (n + 1) ≤ 2 ^ 24 * Nat.clog 2 (n + 1)
    calc
      _ = 1 * Nat.clog 2 (n + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  filter_upwards [eventually_candidates_fit,
    sourceReduction_tendsto_clog.eventually (eventually_ge_atTop 1),
    sourceReduction_tendsto_clog.eventually (sourceReduction_eventually_clog_pow_le (2 ^ 43) 3),
    sourceReduction_tendsto_clog.eventually (sourceReduction_eventually_clog_pow_le (2 ^ 90) 6),
    scaled.eventually eventually_gammaBlockSizeGuard]
      with n candidates positive error overhead gamma
  refine ⟨positive, ⟨le_rfl, ?_, ?_⟩, gamma⟩
  · exact (sourceReduction_error_overhead_le le_rfl positive candidates).trans error
  · exact (sourceReduction_growing_overhead_le le_rfl positive candidates).trans overhead

theorem eventually_sourceReductionExtractor_flat :
    ∀ᶠ n : Nat in atTop,
      FlatSumsetExtractor (sourceReductionExtractor n (Nat.clog 2 (n + 1)))
        (2 ^ sourceReductionEntropy n (Nat.clog 2 (n + 1))) (35 / 72) := by
  filter_upwards [eventually_sourceReduction_guards] with n guards
  exact sourceReductionExtractor_flat n _ guards.1 guards.2.1 guards.2.2

end Algebraic.Cutwidth.Extractor.Internal
