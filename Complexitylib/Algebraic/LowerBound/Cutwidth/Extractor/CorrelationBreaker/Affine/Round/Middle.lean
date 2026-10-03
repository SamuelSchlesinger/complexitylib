/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Internal.Left
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Internal.Mask

/-!
# Actual smooth-source middle extraction in an affine round

The old honest left row need only be close to uniform jointly with the
selected tampered rows in `T`. The first right seed is compared with
uniform using the actual prefix transcript and tampered seeds in `S`.
The actual middle-left extraction then retains the complete middle-right
transcript, original right state, and all tampered outputs in `S ∪ T`.
Overlapping subsets are permitted. Its bound charges the extractor error,
the two old discrepancies, and the exact finite prefix/leakage cost.

The checked XOR identity transfers the same bound to the executed masked
short rows. Dropping the original right state gives the exact next seed
law. These are finite steps in Chattopadhyay--Liao, *Extractors for Sum of
Two Sources*, Theorem 6.1: <https://arxiv.org/abs/2110.12652>.
The complete subset induction and global parameter schedule are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Original normalized factors give normalized unmasked middle rows. -/
theorem affineRoundMiddleLeftRowsWeight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U) :=
  Internal.affineRoundMiddleLeftRowsWeight_probability d h t L e w l r wl wr ys U hw hl hr

/-- The executed masked middle rows define a probability law. -/
theorem affineRoundMiddleRowsWeight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U) :=
  Internal.affineRoundMiddleRowsWeight_probability d h t L e w l r wl wr ys U hw hl hr

/-- The next actual seed-input law is normalized, including null transcript rows. -/
theorem affineRoundMiddleSeedInputWeight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys U) :=
  Internal.affineRoundMiddleSeedInputWeight_probability d h t L e w l r wl wr ys U hw hl hr

/-- Dropping the original right state gives exactly the conditional seed-input law. -/
theorem affineRoundMiddleSeedInputWeight_eq_map (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p => ((p.1.1.1, p.1.2), p.2))
      (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U) =
      affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys U :=
  Internal.affineRoundMiddleSeedInputWeight_eq_map d h t L e w l r wl wr ys U hl hr

/-- Transcript-dependent masking costs no additional uniformity error. -/
theorem affineRound_middle_mask_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t)) :
    weightDist (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U)
      (uniformSecondWeight (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U)) ≤
      weightDist (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U)
        (uniformSecondWeight (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U)) :=
  Internal.affineRound_middle_mask_dist_le d h t L e w l r wl wr ys U

/-- Actual middle-left extraction merges smooth independence on arbitrary overlapping subsets. -/
theorem affineRound_middle_left_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) {ρ δ : ℝ}
    (length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρ)
    (seed : weightDist (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys (S ∪ T))
      (uniformSecondWeight
        (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys (S ∪ T))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) /
            Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) :=
  Internal.affineRound_middle_left_dist_le d h t L e w l r wl wr ys S T
    length room error hw hl hr source seed

/-- The actual masked short rows satisfy the same union bound with the full right state retained. -/
theorem affineRound_middle_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) {ρ δ : ℝ}
    (length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρ)
    (seed : weightDist (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys (S ∪ T))
      (uniformSecondWeight
        (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys (S ∪ T))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) /
            Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) :=
  Internal.affineRound_middle_dist_le d h t L e w l r wl wr ys S T
    length room error hw hl hr source seed

/-- The actual seed-input law for the second right call satisfies the same union bound. -/
theorem affineRound_middle_seed_input_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) {ρ δ : ℝ}
    (length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρ)
    (seed : weightDist (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys (S ∪ T))
      (uniformSecondWeight
        (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys (S ∪ T))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) /
            Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) :=
  Internal.affineRound_middle_seed_input_dist_le d h t L e w l r wl wr ys S T
    length room error hw hl hr source seed

end Algebraic.Cutwidth.Extractor
