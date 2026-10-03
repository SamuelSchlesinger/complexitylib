/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Transcript.Defs

/-!
# Original-source envelopes through an actual affine round

An observation of a source's own side copies its envelope over the message
alphabet. An opposite-side observation scales the envelope by the actual
message probability. This preserves null rows and keeps the original
source coordinates rather than substituting a repaired or conditioned input.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B : Type*}

/-- Right prefix-mask observation preserves the total original-left envelope. -/
noncomputable def affineRoundPrefixMaskLeftEnvelope (h t L : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptWeight μ r (affineRoundPrefixMask h t L wr)

/-- Actual prefixes copy the previous original-left envelope. -/
noncomputable def affineRoundPrefixLeftEnvelope (h t L : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundPrefixTranscript Z t L) : ℝ :=
  affineRoundPrefixMaskLeftEnvelope h t L μ r wr z.1

/-- Observing actual prefixes scales the original-right envelope by their probability. -/
noncomputable def affineRoundPrefixRightEnvelope (h t L : Nat) [Fintype A]
    (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptWeight (fun z : AffineRoundPrefixMaskTranscript Z t L => ξ z.1)
    (fun z => l z.1) (affineRoundPrefixLeftMessage h t L wl)

/-- The first right seeds and short-row masks scale the original-left envelope. -/
noncomputable def affineRoundMiddleRightLeftEnvelope (d h t L e : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptWeight (affineRoundPrefixLeftEnvelope h t L μ r wr)
    (affineRoundPrefixRight h t L r wr) (affineRoundMiddleRightMessage d h t L e wr ys)

/-- The first right seeds and short-row masks copy the original-right envelope. -/
noncomputable def affineRoundMiddleRightRightEnvelope (h t L : Nat) [Fintype A]
    (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundMiddleRightTranscript Z t L) : ℝ :=
  affineRoundPrefixRightEnvelope h t L ξ l wl z.1

/-- Observing actual short rows copies the preceding original-left envelope. -/
noncomputable def affineRoundMiddleLeftEnvelope (d h t L e : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (z : AffineRoundMiddleTranscript Z t L) : ℝ :=
  affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z.1

/-- Observing actual short rows preserves the preceding original-right envelope total. -/
noncomputable def affineRoundMiddleRightEnvelope (h t L e : Nat) [Fintype A]
    (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptWeight (affineRoundMiddleRightRightEnvelope h t L ξ l wl)
    (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleLeftMessage h t L e wl)

/-- The final right seeds preserve the preceding original-left envelope total. -/
noncomputable def affineRoundTranscriptLeftEnvelope (d h t L e : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptWeight (affineRoundMiddleLeftEnvelope d h t L e μ r wr ys)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (affineRoundFinalSeedRight d t L e ys)

/-- The final right seeds copy the preceding original-right envelope. -/
noncomputable def affineRoundTranscriptRightEnvelope (h t L e : Nat) [Fintype A]
    (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundTranscript Z t L) : ℝ :=
  affineRoundMiddleRightEnvelope h t L e ξ l wl z.1

end Algebraic.Cutwidth.Extractor
