/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Second.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Internal.Mask

/-!
# Actual final pairwise extraction in the first affine phase

The preceding actual second-seed discrepancy supplies the only intermediate
statistical premise. From the original normalized source factors and its
joint left-source envelope, the actual growing matched extractor gives
pairwise output security while retaining the complete transcript and
original right state. The envelope pays for all first extraction outputs
and one tampered final output. No individual transcript row is required to
have a uniform seed or a capped conditional source.

The left-contribution law supports later merging rounds. The actual masked
pair has the same bound because both masks are determined by the retained
transcript and original right state. This is a local consumer of the
preceding seed bound, not the full affine correlation-breaker theorem or
a simultaneous guarantee against every tampered output.

The construction and pairwise merging step follow Chattopadhyay--Liao,
*Extractors for Sum of Two Sources* (2021), Theorem 6.1, printed p.23,
and Lemma 3.26, printed p.15: <https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Masking both final values does not increase the distance from retained-tag uniformity. -/
theorem affinePhaseOnePair_dist_le_left (n d t h L₀ e₀ L₁ e₁ er : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) :
    weightDist
      (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      weightDist
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
        (uniformSecondWeight
          (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) :=
  Internal.affinePhaseOnePair_dist_le_left n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i

/-- The original normalized factors give a normalized retained left-contribution pair. -/
theorem affinePhaseOneLeftPairWeight_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i) :=
  Internal.affinePhaseOneLeftPairWeight_probability n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
  i hw hl hr

/-- The original normalized factors give a normalized retained actual masked pair. -/
theorem affinePhaseOnePairWeight_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i) :=
  Internal.affinePhaseOnePairWeight_probability n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i hw
  hl hr

/-- The actual growing extractor merges the preceding second-seed pair into left contributions. -/
theorem affinePhaseOneLeftPair_dist_le (n d t h L₀ e₀ L₁ e₁ er : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L₁) (error : er + h + 2 ≤ L₁)
    (budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)) ≤ δ) :
    weightDist
      (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      ((2 : ℝ) ^ er)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁) *
        Fintype.card (Fin (matchedBlockOutputBits h L₁) → Bool) *
        Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) * ∑ z, μ z :=
  Internal.affinePhaseOneLeftPair_dist_le n d t h L₀ e₀ L₁ e₁ er length error budget w l r x mask
  ys advice i μ hw hl hr nonnegative cap seed

/-- The actual masked final pair satisfies the same bound, without an additional masking error. -/
theorem affinePhaseOnePair_dist_le (n d t h L₀ e₀ L₁ e₁ er : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L₁) (error : er + h + 2 ≤ L₁)
    (budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i)) ≤ δ) :
    weightDist
      (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      ((2 : ℝ) ^ er)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁) *
        Fintype.card (Fin (matchedBlockOutputBits h L₁) → Bool) *
        Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) * ∑ z, μ z :=
  Internal.affinePhaseOnePair_dist_le n d t h L₀ e₀ L₁ e₁ er length error budget w l r x mask ys
  advice i μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor
