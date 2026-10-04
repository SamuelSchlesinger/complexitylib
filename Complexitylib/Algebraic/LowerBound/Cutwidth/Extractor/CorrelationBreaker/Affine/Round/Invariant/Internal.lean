/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Invariant.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction.Bounds
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Subset

/-!
# One actual round doubles the retained-subset capacity

Split each requested set into two smaller parts and apply the actual round
union theorem. The four worst-case finite reserves apply uniformly to all
sets of tampering indices. The result is the same conditional left-row
invariant at the new executed transcript, with its explicit next error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRowInvariant_mono (h t L : Nat) {Z A : Type*} [Fintype Z] [Fintype A]
    {w : Z → ℝ} {l : Z → A → ℝ}
    {wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)}
    {k k' : Nat} {ρ ρ' : ℝ} (invariant : AffineRowInvariant h t L w l wl k ρ)
    (capacity : k' ≤ k) (error : ρ ≤ ρ') : AffineRowInvariant h t L w l wl k' ρ' :=
  fun S size => (invariant S (size.trans capacity)).trans error

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
      (2 * k) (2 * ρ + 8 * ((2 : ℝ) ^ e)⁻¹) := by
  intro U cardU
  obtain ⟨S, T, _, _, _, union, cardS, cardT⟩ := exists_union_of_card_le_two_mul U cardU
  have s_le : S.card ≤ t := by simpa only [Fintype.card_fin] using S.card_le_univ
  have u_le : U.card ≤ t := by simpa only [Fintype.card_fin] using U.card_le_univ
  have first_count := Nat.mul_le_mul_right (matchedBlockSeedBits L)
    (show S.card + t + 1 ≤ t + t + 1 by lia)
  have recover_count := Nat.mul_le_mul_right (matchedBlockSeedBits L)
    (show U.card + 3 * (t + 1) ≤ t + 3 * (t + 1) by lia)
  have final_count := Nat.mul_le_mul_right (matchedBlockOutputBits h L) u_le
  have bound := affineRound_next_union_dist_le n d h t L e w l r x wl wr ys S T μ ν
    size right_length row_length room short_error final_length final_error final_budget
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap (old S cardS) (old T cardT)
  rw [union] at bound
  have numerical := affineRoundError_dyadic_le t h L e S.card U.card kx ky ρ ρ
    (by lia) (by lia) (by lia) (by lia) left_mass right_mass
  exact bound.trans (by simpa only [two_mul] using numerical)

end Algebraic.Cutwidth.Extractor.Internal
