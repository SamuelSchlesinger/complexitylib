/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Invariant.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Invariant.Internal

/-!
# Actual affine rounds double the retained-subset capacity

The invariant holds for all subsets up to a specified cardinality, including
empty subsets. Splitting a larger set and applying the actual four-call
round proves the same invariant at the new transcript with doubled capacity
and error `2ρ + 8 * 2⁻ᵉ`. The finite entropy reserves are uniform in the set.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Decrease the retained-subset capacity and increase the allowed discrepancy. -/
theorem AffineRowInvariant.mono (h t L : Nat) {Z A : Type*} [Fintype Z] [Fintype A]
    {w : Z → ℝ} {l : Z → A → ℝ}
    {wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)}
    {k k' : Nat} {ρ ρ' : ℝ} (invariant : AffineRowInvariant h t L w l wl k ρ)
    (capacity : k' ≤ k) (error : ρ ≤ ρ') : AffineRowInvariant h t L w l wl k' ρ' :=
  Internal.affineRowInvariant_mono h t L invariant capacity error

/-- One actual four-call round doubles capacity with its explicit dyadic error. -/
theorem affineRound_doubles_invariant (n d h t L e k kx ky : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (μ ν : Z → ℝ) {ρ : ℝ}
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L)
    (right_length : Nat.clog 2 (d + 1) ≤ L)
    (row_length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (short_error : e + 24 + 2 ≤ L)
    (final_length : Nat.clog 2 (n + 1) ≤ L) (final_error : e + h + 2 ≤ L)
    (final_budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ ν z)
    (first : 2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤ ky)
    (merge : 2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits h L)
    (recover : 2 ^ 62 * L + (t + 3 * (t + 1)) * matchedBlockSeedBits L + e ≤ ky)
    (final : 2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + e ≤ kx)
    (left_mass : (∑ z, μ z) ≤ ((2 : ℝ) ^ kx)⁻¹)
    (right_mass : (∑ z, ν z) ≤ ((2 : ℝ) ^ ky)⁻¹)
    (old : AffineRowInvariant h t L w l wl k ρ) :
    AffineRowInvariant h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
      (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x)
      (2 * k) (2 * ρ + 8 * ((2 : ℝ) ^ e)⁻¹) :=
  Internal.affineRound_doubles_invariant n d h t L e k kx ky w l r x wl wr ys μ ν
    size right_length row_length room short_error final_length final_error final_budget
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap first merge recover final
    left_mass right_mass old

end Algebraic.Cutwidth.Extractor
