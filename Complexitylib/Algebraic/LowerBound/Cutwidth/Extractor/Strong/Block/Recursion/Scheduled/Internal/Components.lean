/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Weighted

/-!
# Statistical certificates for the specified recursive components

Recombining the initial pair is injective, each internal map is the actual
rate-three condenser, and a leaf reserve above the one-shot threshold
suffices by monotonicity of the normalized source cap.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem scheduledBlockInitial_weighted (n h Q E : Nat)
    [Fintype (ScheduledInitialSeed n h Q E)] :
    WeightedStrongSeededCondenser (scheduledBlockInitial n h Q E)
      (2 ^ recursiveBlockEntropy h Q 0) (2 ^ recursiveBlockEntropy h Q 0)
      (((2 : ℝ) ^ E)⁻¹) := by
  exact (explicitCondenserPair_weighted n (recursiveBlockEntropy h Q 0) E 1
    (by decide)).map_output_injective (fun _ => Fin.appendEquiv _ _)
      (fun _ => (Fin.appendEquiv _ _).injective)

theorem scheduledBlockStep_weighted (n h Q E i : Nat)
    [Fintype (ScheduledLevelSeed n h Q E i)] :
    WeightedStrongSeededCondenser (scheduledBlockStep n h Q E i)
      (2 ^ recursiveBlockEntropy h Q i) (2 ^ recursiveBlockEntropy h Q i)
      (((2 : ℝ) ^ E)⁻¹) :=
  explicitCondenserPair_weighted
    (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E i)
    (recursiveBlockEntropy h Q i) E 3 (by decide)

theorem scheduledBlockLeaf_weighted (width h Q E ell : Nat)
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent width ell E)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent width ell E)))]
    (reserve : ell + 2 * E ≤ Q) :
    WeightedStrongSeededExtractor
      (fun x : Fin width → Bool => decodedOneShotExtractor width ell E (List.ofFn x))
      (2 ^ recursiveBlockEntropy h Q h) (((2 : ℝ) ^ E)⁻¹) := by
  intro p probability cap T
  apply decodedOneShotExtractor_ofFn_weighted width ell E p probability _ T
  intro x
  have threshold : (2 ^ (ell + 2 * E) : Nat) ≤ 2 ^ recursiveBlockEntropy h Q h := by
    simpa only [recursiveBlockEntropy, Nat.sub_self, pow_zero, one_mul] using
      Nat.pow_le_pow_right (by decide : 0 < 2) reserve
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr threshold) (probability.1 x)).trans (cap x)

end Algebraic.Cutwidth.Extractor.Internal
