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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction.Internal

/-!
# One actual affine round merges two retained-subset guarantees

The old honest left row is nearly uniform against each of two tampering
sets. The actual four-call round produces a long output nearly uniform
against their union, retaining the complete transcript and original right
state. The theorem uses only the two old-row guarantees, original source
envelopes, and finite extractor guards. Every intermediate seed bound is
derived from the actual preceding call.

The next-left-row marginal exposes the same invariant at the new transcript.
The sets may overlap. This is the finite subset-union step of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>. The full iteration and its parameter
schedule are proved in `Affine.Iteration.Extraction`
(`affineCorrelationBreaker_parameters_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The executed next-left row is uniform against the union under the explicit round error. -/
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
      affineRoundError t h L e S.card (S ∪ T).card ρS ρT (∑ z, μ z) (∑ z, ν z) :=
  Internal.affineRound_left_union_dist_le n d h t L e w l r x wl wr ys S T μ ν
    size right_length row_length room short_error final_length final_error final_budget
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap oldS oldT

/-- The actual masked output satisfies the same retained-union guarantee. -/
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
      affineRoundError t h L e S.card (S ∪ T).card ρS ρT (∑ z, μ z) (∑ z, ν z) :=
  Internal.affineRound_union_dist_le n d h t L e w l r x mask wl wr ys S T μ ν
    size right_length row_length room short_error final_length final_error final_budget
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap oldS oldT

/-- The new transcript and left kernel satisfy the next retained-union row invariant. -/
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
      affineRoundError t h L e S.card (S ∪ T).card ρS ρT (∑ z, μ z) (∑ z, ν z) :=
  Internal.affineRound_next_union_dist_le n d h t L e w l r x wl wr ys S T μ ν
    size right_length row_length room short_error final_length final_error final_budget
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap oldS oldT

end Algebraic.Cutwidth.Extractor
