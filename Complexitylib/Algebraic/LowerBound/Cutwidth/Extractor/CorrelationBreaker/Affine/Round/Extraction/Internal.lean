/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Recovery
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final
import Mathlib.Tactic.Ring

/-!
# Compose all actual calls of one affine subset-union round

The first old-row guarantee supplies the masked prefix and first right
seed. The second supplies the smooth source for merging the two tampering
sets. Rereading the original right and left sources restores the long
output. Every intermediate statistical hypothesis is discharged by its
actual preceding call. The output retains the entire executed transcript,
original right state, and selected next rows; its marginal supplies the
same left-row invariant for the next round.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem coefficient (t L b c s p : Nat) :
    (2 : ℝ) ^ c * (Fintype.card (Fin b → Bool) : ℝ) ^ s *
        (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ p =
      (2 : ℝ) ^ (c + s * b + p * (t + 1) * matchedBlockSeedBits L) := by
  rw [card_affineRoundShortMessages]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
  congr 1
  ring

private theorem first_coefficient (t L s : Nat) :
    (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ s *
        Fintype.card (AffineRoundShortMessages t L) =
      (2 : ℝ) ^ (2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L) := by
  have result := coefficient t L (matchedBlockSeedBits L) (2 ^ 62 * L) s 1
  rw [pow_one] at result
  convert result using 1
  congr 1
  ring

private theorem recover_coefficient (t L u : Nat) :
    (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ u *
        (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 =
      (2 : ℝ) ^ (2 ^ 62 * L + (u + 3 * (t + 1)) * matchedBlockSeedBits L) := by
  rw [coefficient]
  congr 1
  ring

theorem affineRound_left_union_dist_le (n d h t L e : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) (μ ν : Z → ℝ)
    {ρS ρT : ℝ}
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
    (oldS : weightDist (affineRoundLeftRowsWeight h t L w l wl S)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) ≤ ρS)
    (oldT : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρT) :
    let actual := affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys (S ∪ T)
    weightDist actual (uniformSecondWeight actual) ≤
      affineRoundError t h L e S.card (S ∪ T).card ρS ρT (∑ z, μ z) (∑ z, ν z) := by
  have first := affineRoundMiddleSeed_dist_le d h t L e size right_length room short_error
    w l r wl wr ys S ν hw hl hr right_nonnegative right_cap oldS
  have middle := affineRound_middle_seed_input_dist_le d h t L e w l r wl wr ys S T
    row_length room short_error hw hl hr oldT first
  have recovered := affineRoundFinalSeed_dist_le d h t L e right_length room short_error
    w l r wl wr ys (S ∪ T) ν hw hl hr right_nonnegative right_cap middle
  have final := affineRoundLeftSubset_dist_le n d h t L e
    final_length final_error final_budget w l r x wl wr ys (S ∪ T) μ
    hw hl hr left_nonnegative left_cap recovered
  simp only [first_coefficient, recover_coefficient] at final
  rw [coefficient] at final
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] at final
  convert final using 1
  unfold affineRoundError
  ring

theorem affineRound_union_dist_le (n d h t L e : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) (μ ν : Z → ℝ)
    {ρS ρT : ℝ}
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
    (oldS : weightDist (affineRoundLeftRowsWeight h t L w l wl S)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) ≤ ρS)
    (oldT : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρT) :
    let actual := affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys (S ∪ T)
    weightDist actual (uniformSecondWeight actual) ≤
      affineRoundError t h L e S.card (S ∪ T).card ρS ρT (∑ z, μ z) (∑ z, ν z) := by
  exact (affineRoundSubset_dist_le_left n d h t L e w l r x mask wl wr ys (S ∪ T)).trans
    (affineRound_left_union_dist_le n d h t L e w l r x wl wr ys S T μ ν
      size right_length row_length room short_error final_length final_error final_budget
      hw hl hr left_nonnegative right_nonnegative left_cap right_cap oldS oldT)

theorem affineRound_next_union_dist_le (n d h t L e : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) (μ ν : Z → ℝ)
    {ρS ρT : ℝ}
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
    (oldS : weightDist (affineRoundLeftRowsWeight h t L w l wl S)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) ≤ ρS)
    (oldT : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρT) :
    let actual := affineRoundLeftRowsWeight h t L
      (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
      (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) (S ∪ T)
    weightDist actual (uniformSecondWeight actual) ≤
      affineRoundError t h L e S.card (S ∪ T).card ρS ρT (∑ z, μ z) (∑ z, ν z) := by
  exact (affineRoundNextLeftRows_dist_le n d h t L e w l r x wl wr ys (S ∪ T) hw hl hr).trans
    (affineRound_left_union_dist_le n d h t L e w l r x wl wr ys S T μ ν
      size right_length row_length room short_error final_length final_error final_budget
      hw hl hr left_nonnegative right_nonnegative left_cap right_cap oldS oldT)

end Algebraic.Cutwidth.Extractor.Internal
