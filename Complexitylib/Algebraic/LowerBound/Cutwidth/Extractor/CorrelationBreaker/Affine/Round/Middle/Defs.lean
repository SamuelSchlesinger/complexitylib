/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs

/-!
# Actual middle-row laws in an affine extraction round

The unmasked law keeps the first right seeds, all right mask contributions,
and the complete original right state. The masked law records the actual
short rows executed by the round. Its seed-input marginal drops the
original right state while retaining the complete middle-right transcript.
All laws use actual original inputs and selected tampering indices.

These definitions isolate the smooth-source merging step in
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>. No replacement source is part of a law.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

/-- Original-left short outputs retain all first right messages and the original right state. -/
noncomputable def affineRoundMiddleLeftRowsWeight (d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t)) :
    ((AffineRoundMiddleRightTranscript Z t L × B) ×
      (U → Fin (matchedBlockSeedBits L) → Bool)) × (Fin (matchedBlockSeedBits L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let z := affineRoundMiddleRightTranscript d h t L e wl wr ys p
    (((z, p.1.2), fun j : U =>
      matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e
        (wl p.1.1 p.2 (some j)) (z.2.1 (some j))),
      matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e
        (wl p.1.1 p.2 none) (z.2.1 none)))
    (factoredWeight w l r)

/-- The actual masked short outputs retain the same transcript and original right state. -/
noncomputable def affineRoundMiddleRowsWeight (d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t)) :
    ((AffineRoundMiddleRightTranscript Z t L × B) ×
      (U → Fin (matchedBlockSeedBits L) → Bool)) × (Fin (matchedBlockSeedBits L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let z := affineRoundMiddleRightTranscript d h t L e wl wr ys p
    (((z, p.1.2), fun j : U => affineRoundMiddleOutput d h L e
      (ys p.1.1 p.1.2 (some j))
      (fun i => Bool.xor (wl p.1.1 p.2 (some j) i) (wr p.1.1 p.1.2 (some j) i))),
      affineRoundMiddleOutput d h L e (ys p.1.1 p.1.2 none)
        (fun i => Bool.xor (wl p.1.1 p.2 none i) (wr p.1.1 p.1.2 none i))))
    (factoredWeight w l r)

/-- The actual short-row seed law at the middle-right observation factors. -/
noncomputable def affineRoundMiddleSeedInputWeight (d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t)) :
    (AffineRoundMiddleRightTranscript Z t L ×
      (U → Fin (matchedBlockSeedBits L) → Bool)) × (Fin (matchedBlockSeedBits L) → Bool) → ℝ :=
  observedSeedWeight (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (fun z a (j : U) => affineRoundMiddleLeftMessage h t L e wl z a (some j))
    (fun z a => affineRoundMiddleLeftMessage h t L e wl z a none)

end Algebraic.Cutwidth.Extractor
