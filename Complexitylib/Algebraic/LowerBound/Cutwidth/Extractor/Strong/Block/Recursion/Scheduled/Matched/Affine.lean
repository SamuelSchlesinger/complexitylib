/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Affine.Internal

/-!
# Actual matched extraction with a correlated right mask

The honest source is XORed with a mask carried by the original right state.
Matched extraction retains that full state, with the same finite entropy
budget as the unmasked source and one charge for seed discrepancy. The
actual program's fixed-seed XOR identity discharges the linearity premise.

The depth-sixty-four call seeds the standard correlation breaker in the
first phase of Chattopadhyay--Liao Theorem 6.1; growing depths provide longer
rows for its later independence-merging phase:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual long initial extraction retains the correlated right mask and complete state. -/
theorem matchedBlockExtractor_depth64_affine_dist_le (n L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (room : 64 ≤ L) (error : e + 64 + 2 ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (y : Z → B → Fin (matchedBlockSeedBits L) → Bool) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    let actual := affineExtractionWeight w l r x mask y
      (fun a b i => Bool.xor (a i) (b i)) (matchedBlockExtractor n 64 L e)
    weightDist actual (uniformSecondWeight actual) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ 142 * L) * ∑ z, μ z :=
  Internal.matchedBlockExtractor_depth64_affine_dist_le n L e length room error
    w l r x mask y μ hw hl hr nonnegative cap seed

/-- Growing output rows retain the same strong guarantee under a correlated source mask. -/
theorem matchedBlockExtractor_growing_affine_dist_le (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (y : Z → B → Fin (matchedBlockSeedBits L) → Bool) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    let actual := affineExtractionWeight w l r x mask y
      (fun a b i => Bool.xor (a i) (b i)) (matchedBlockExtractor n h L e)
    weightDist actual (uniformSecondWeight actual) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L) * ∑ z, μ z :=
  Internal.matchedBlockExtractor_growing_affine_dist_le n h L e length error budget
    w l r x mask y μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor
