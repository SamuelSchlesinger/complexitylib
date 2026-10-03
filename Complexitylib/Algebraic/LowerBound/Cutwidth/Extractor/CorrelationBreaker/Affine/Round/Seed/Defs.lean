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
# Actual subset laws at the start of an affine round

The old left row is compared with uniform while retaining a chosen set of
old tampered left rows. The prefix law additionally observes the original
right prefix masks. The first right-extraction law retains all actual
prefixes and the selected tampered seeds. All weights use the actual
normalized observation factors of the original sources.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

/-- The old honest left row, retaining the transcript and selected tampered left rows. -/
noncomputable def affineRoundLeftRowsWeight (h t L : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t)) :=
  observedSeedWeight w l (fun z a (j : S) => wl z a (some j)) (fun z a => wl z a none)

/-- Actual masked prefixes after observing the right prefix masks. -/
noncomputable def affineRoundPrefixSeedWeight (h t L : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t)) :=
  observedSeedWeight (affineRoundPrefixMaskWeight h t L w r wr) (fun z => l z.1)
    (fun z a (j : S) => affineRoundPrefixLeftMessage h t L wl z a (some j))
    (fun z a => affineRoundPrefixLeftMessage h t L wl z a none)

/-- The actual first right seeds, retaining every prefix and the selected tampered seeds. -/
noncomputable def affineRoundMiddleSeedWeight (d h t L e : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :=
  observedSeedWeight (affineRoundPrefixWeight h t L w l r wl wr)
    (affineRoundPrefixRight h t L r wr)
    (fun z b (j : S) => affineRoundMiddleSeedRight d t L e ys z b (some j))
    (fun z b => affineRoundMiddleSeedRight d t L e ys z b none)

end Algebraic.Cutwidth.Extractor
