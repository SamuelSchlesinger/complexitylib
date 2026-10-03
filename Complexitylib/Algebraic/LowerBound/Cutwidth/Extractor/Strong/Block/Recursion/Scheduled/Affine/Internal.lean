/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Affine extraction by the scheduled Boolean program

The actual program's source XOR law expresses a right-source mask as an
output XOR mask. Coordinatewise XOR is an involution on the curried output
blocks, supplying the output equivalence required by retained affine
extraction. The extractor guarantee comes from the checked finite schedule.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def xorOutputEquiv {ι κ : Type*} (mask : ι → κ → Bool) :
    (ι → κ → Bool) ≃ (ι → κ → Bool) where
  toFun x i j := Bool.xor (x i j) (mask i j)
  invFun x i j := Bool.xor (x i j) (mask i j)
  left_inv x := by
    funext i j
    dsimp only
    cases x i j <;> cases mask i j <;> rfl
  right_inv x := by
    funext i j
    dsimp only
    cases x i j <;> cases mask i j <;> rfl

theorem scheduledBlockBooleanExtractor_affine_dist_le
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B] {δ : ℝ}
    (n h Q E ell : Nat)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    (reserve : ell + 2 * E ≤ Q)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (y : Z → B → Fin (scheduledBlockSeedBits n h Q E ell) → Bool) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    weightDist
      (affineExtractionWeight w l r x mask y (fun a b i => Bool.xor (a i) (b i))
        (scheduledBlockBooleanExtractor n h Q E ell))
      (uniformSecondWeight
        (affineExtractionWeight w l r x mask y (fun a b i => Bool.xor (a i) (b i))
          (scheduledBlockBooleanExtractor n h Q E ell))) ≤
      (3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹ + δ +
        (2 ^ recursiveBlockEntropy h Q 0 : Nat) * ∑ z, μ z := by
  have power : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have error : 0 ≤ (3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹ :=
    mul_nonneg (by linarith) (by positivity)
  exact (scheduledBlockBooleanExtractor_weighted n h Q E ell budget reserve).affine_dist_le
    error (fun a b i => Bool.xor (a i) (b i))
    (fun b seed => xorOutputEquiv (scheduledBlockBooleanExtractor n h Q E ell b seed))
    (scheduledBlockBooleanExtractor_xor n h Q E ell)
    w l r x mask y μ hw hl hr nonnegative cap seed

theorem scheduledBlockBooleanExtractor_dyadic_affine_dist_le
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B] {δ : ℝ}
    (n h L e : Nat) (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (y : Z → B → Fin (scheduledBlockSeedBits n h
      (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L) → Bool) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    weightDist
      (affineExtractionWeight w l r x mask y (fun a b i => Bool.xor (a i) (b i))
        (scheduledBlockBooleanExtractor n h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L))
      (uniformSecondWeight
        (affineExtractionWeight w l r x mask y (fun a b i => Bool.xor (a i) (b i))
          (scheduledBlockBooleanExtractor n h
            (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ +
        (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0 : Nat) *
          ∑ z, μ z := by
  exact (scheduledBlockBooleanExtractor_dyadic n h L e length depth).affine_dist_le
    (by positivity) (fun a b i => Bool.xor (a i) (b i))
    (fun b seed => xorOutputEquiv (scheduledBlockBooleanExtractor n h
      (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L b seed))
    (scheduledBlockBooleanExtractor_xor n h
      (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)
    w l r x mask y μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor.Internal
