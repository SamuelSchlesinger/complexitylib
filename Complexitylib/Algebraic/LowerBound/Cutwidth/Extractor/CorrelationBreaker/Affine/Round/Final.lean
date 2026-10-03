/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal.Mask
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal.Projection

/-!
# Final extraction against a finite set of actual round outputs

The actual honest final seed is close to uniform given the middle transcript
and selected tampered seeds. The original left-source joint envelope then
bounds the actual final growing matched extraction, retaining the complete
round transcript, the entire original right state, and all selected next
rows. The envelope cost is the square of the short-message alphabet size;
the selected outputs cost their tuple's alphabet size. No cap on individual
conditional rows or per-transcript seed-error bound is required.

The actual masked rows have the same bound. Projecting away the original
right state gives the exact left-row law used as the next round's input.
This is the fourth-call consumer in Chattopadhyay--Liao, *Extractors for Sum
of Two Sources* (2021), Theorem 6.1, printed pp.23--25, using Lemma 3.26,
printed p.15: <https://arxiv.org/abs/2110.12652>. Producing its actual seed
discrepancy is a separate extraction step; no complete correlation breaker
is asserted by this local theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The conditional final-seed law is exactly an image of the original source law. -/
theorem affineRoundFinalSeedWeight_eq_map (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    affineRoundFinalSeedWeight d h t L e w l r wl wr ys S =
      mapWeight (fun p : (Z × B) × A =>
        let seeds := fun i => affineRoundFinalSeed d h L e (ys p.1.1 p.1.2 i)
          (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j))
        ((affineRoundMiddleTranscript d h t L e wl wr ys p,
          fun i : S => seeds (some i.val)), seeds none)) (factoredWeight w l r) :=
  Internal.affineRoundFinalSeedWeight_eq_map d h t L e w l r wl wr ys S hl hr

/-- Normalized original factors give normalized actual retained left contributions. -/
theorem affineRoundLeftSubsetWeight_probability (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S) :=
  Internal.affineRoundLeftSubsetWeight_probability n d h t L e w l r x wl wr ys S hw hl hr

/-- Normalized original factors give normalized actual retained masked next rows. -/
theorem affineRoundSubsetWeight_probability (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S) :=
  Internal.affineRoundSubsetWeight_probability n d h t L e w l r x mask wl wr ys S hw hl hr

/-- Applying the actual right masks costs no additional conditional-uniformity error. -/
theorem affineRoundSubset_dist_le_left (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :
    weightDist (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)
      (uniformSecondWeight (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)) ≤
      weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
        (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) :=
  Internal.affineRoundSubset_dist_le_left n d h t L e w l r x mask wl wr ys S

/-- Discarding original B gives exactly the next round's left-row subset law. -/
theorem affineRoundNextLeftRows_eq_map (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    affineRoundLeftRowsWeight h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
      (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) S =
      mapWeight (fun p => ((p.1.1.1, p.1.2), p.2))
        (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S) :=
  Internal.affineRoundNextLeftRows_eq_map n d h t L e w l r x wl wr ys S hw hl hr

/-- The next left-row subset discrepancy is no larger than the retained final-call discrepancy. -/
theorem affineRoundNextLeftRows_dist_le (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist
      (affineRoundLeftRowsWeight h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
        (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) S)
      (uniformSecondWeight
        (affineRoundLeftRowsWeight h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
          (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) S)) ≤
      weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
        (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) :=
  Internal.affineRoundNextLeftRows_dist_le n d h t L e w l r x wl wr ys S hw hl hr

/-- The actual growing extractor preserves uniformity against the selected next left rows. -/
theorem affineRoundLeftSubset_dist_le (n d h t L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
      (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L) *
        (Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) : ℝ) ^ S.card *
        (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z :=
  Internal.affineRoundLeftSubset_dist_le n d h t L e length error budget
    w l r x wl wr ys S μ hw hl hr nonnegative cap seed

/-- The same original-source and actual-seed bounds control the masked next rows. -/
theorem affineRoundSubset_dist_le (n d h t L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)
      (uniformSecondWeight (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L) *
        (Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) : ℝ) ^ S.card *
        (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z :=
  Internal.affineRoundSubset_dist_le n d h t L e length error budget
    w l r x mask wl wr ys S μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor
