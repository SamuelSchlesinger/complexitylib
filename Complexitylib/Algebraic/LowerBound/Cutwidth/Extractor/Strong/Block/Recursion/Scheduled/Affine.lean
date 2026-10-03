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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Affine.Internal

/-!
# Actual scheduled extraction from a Boolean affine source

The named Boolean bit program extracts from a left source XOR a right-side
mask while retaining the entire right variable and shared transcript. The
error pays for extraction, the seed's distance from uniform given the
transcript, and an average joint source-mass envelope. Source XOR linearity
and the output translation equivalence are discharged by the implementation.

Both the general finite schedule and its explicit dyadic-error family are
available without caller-supplied extractors or field instances. This is a
finite extraction step for the affine correlation-breaker argument of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1,
<https://arxiv.org/pdf/2110.12652>. The remaining tampering and recursive
correlation-breaker guarantees are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual scheduled extractor tolerates a correlated right mask with its full state retained. -/
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
        (2 ^ recursiveBlockEntropy h Q 0 : Nat) * ∑ z, μ z :=
  Internal.scheduledBlockBooleanExtractor_affine_dist_le n h Q E ell budget reserve
    w l r x mask y μ hw hl hr nonnegative cap seed

/-- Explicit reserve parameters give the same retained affine guarantee with error `2^(-e)`. -/
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
          ∑ z, μ z :=
  Internal.scheduledBlockBooleanExtractor_dyadic_affine_dist_le n h L e length depth
    w l r x mask y μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor
