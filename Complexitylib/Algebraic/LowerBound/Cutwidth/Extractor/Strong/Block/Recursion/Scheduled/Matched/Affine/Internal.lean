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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
import Mathlib.Tactic.Positivity

/-!
# Matched linear extraction on a masked original source

The actual matched program preserves source XOR at every fixed seed.
Consequently its output mask is a permutation within every retained right
state. The actual strong extractor certificates supply the finite error
and entropy thresholds, including the growing-depth row used for merging.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def xorOutputEquiv {ι : Type*} (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := Bool.xor (x i) (mask i)
  invFun x i := Bool.xor (x i) (mask i)
  left_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl
  right_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl

private theorem matched_affine_dist_le (n h L e K : Nat)
    (extract : WeightedStrongSeededExtractor (matchedBlockExtractor n h L e) K
      (((2 : ℝ) ^ e)⁻¹))
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
      ((2 : ℝ) ^ e)⁻¹ + δ + (K : ℝ) * ∑ z, μ z :=
  extract.affine_dist_le (by positivity) (fun a b i => Bool.xor (a i) (b i))
    (fun b seed => xorOutputEquiv (matchedBlockExtractor n h L e b seed))
    (matchedBlockExtractor_xor n h L e) w l r x mask y μ hw hl hr nonnegative cap seed

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
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ 142 * L) * ∑ z, μ z := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using matched_affine_dist_le n 64 L e _
    (matchedBlockExtractor_depth64 n L e length room error)
    w l r x mask y μ hw hl hr nonnegative cap seed

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
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L) * ∑ z, μ z := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using matched_affine_dist_le n h L e _
    (matchedBlockExtractor_growing n h L e length error budget)
    w l r x mask y μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor.Internal
