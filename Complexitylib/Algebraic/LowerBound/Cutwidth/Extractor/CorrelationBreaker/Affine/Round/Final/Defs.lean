/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# Actual final-seed and selected-output laws of an affine round

The seed law retains the middle transcript and a finite set of tampered
final seeds. The output laws retain the complete executed transcript, the
original right state, and the selected next rows. Left contributions and
actual XOR-masked rows are kept separately. Every law is computed from the
original source factors; no replacement source or security property is
part of a definition.

These are the final-call laws for Chattopadhyay--Liao, *Extractors for Sum
of Two Sources* (2021), Theorem 6.1, printed pp.23--25, using Lemma 3.26:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

/-- The honest final seed with the middle transcript and selected tampered seeds retained. -/
noncomputable def affineRoundFinalSeedWeight (d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :=
  observedSeedWeight (affineRoundMiddleWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (fun z b (i : S) => affineRoundFinalSeedRight d t L e ys z b (some i.val))
    (fun z b => affineRoundFinalSeedRight d t L e ys z b none)

/-- Actual next-row left contributions, retaining the full transcript, original B, and a subset. -/
noncomputable def affineRoundLeftSubsetWeight (n d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :
    ((AffineRoundTranscript Z t L × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) ×
      (Fin (matchedBlockOutputBits h L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let z := affineRoundTranscript d h t L e wl wr ys p
    (((z, p.1.2), fun i : S => affineRoundOutputLeft n h t L e x z p.2 (some i.val)),
      affineRoundOutputLeft n h t L e x z p.2 none)) (factoredWeight w l r)

/-- Actual masked next rows, retaining the full transcript, original B, and the selected rows. -/
noncomputable def affineRoundSubsetWeight (n d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :
    ((AffineRoundTranscript Z t L × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) ×
      (Fin (matchedBlockOutputBits h L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let input := fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j)
    let output := fun i => affineRoundOutput n d h L e input (ys p.1.1 p.1.2 i)
      (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j))
    (((affineRoundTranscript d h t L e wl wr ys p, p.1.2), fun i : S => output (some i.val)),
      output none)) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
