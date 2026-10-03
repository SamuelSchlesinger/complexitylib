/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs

/-!
# Actual alternating observations of one affine extraction round

The transcript observes right prefix masks, actual prefixes, the first
right seeds together with short-row mask contributions, actual short rows,
and the final right seeds. Every coordinate is computed by the actual
round. Original left and right states are retained in all conditional
kernels; null rows use `observedTranscriptKernel`'s normalized completion.

These are exact observation factors for the second-phase round of
Chattopadhyay--Liao, Theorem 6.1, printed pp.23--25, using Lemma 3.25:
<https://arxiv.org/abs/2110.12652>. No security premise is encoded here.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- All honest and tampered short messages in one round. -/
abbrev AffineRoundShortMessages (t L : Nat) :=
  AffinePhaseOneCopies t (matchedBlockSeedBits L)

/-- Original transcript extended by right-side prefix masks. -/
abbrev AffineRoundPrefixMaskTranscript (Z : Type*) (t L : Nat) :=
  Z × AffineRoundShortMessages t L

/-- The right prefix masks followed by the actual previous-row prefixes. -/
abbrev AffineRoundPrefixTranscript (Z : Type*) (t L : Nat) :=
  AffineRoundPrefixMaskTranscript Z t L × AffineRoundShortMessages t L

/-- The first right seeds and short-row mask contributions are observed together. -/
abbrev AffineRoundMiddleRightTranscript (Z : Type*) (t L : Nat) :=
  AffineRoundPrefixTranscript Z t L ×
    (AffineRoundShortMessages t L × AffineRoundShortMessages t L)

/-- Actual short rows are observed after their seed and mask contributions. -/
abbrev AffineRoundMiddleTranscript (Z : Type*) (t L : Nat) :=
  AffineRoundMiddleRightTranscript Z t L × AffineRoundShortMessages t L

/-- The full round transcript additionally retains every final right seed. -/
abbrev AffineRoundTranscript (Z : Type*) (t L : Nat) :=
  AffineRoundMiddleTranscript Z t L × AffineRoundShortMessages t L

variable {Z A B : Type*}

/-- The right-only contribution to every previous-row prefix. -/
def affineRoundPrefixMask (h t L : Nat)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : Z) (b : B) : AffineRoundShortMessages t L :=
  fun i => affineRoundPrefix h L (wr z b i)

/-- Fixing prefix masks makes all actual prefixes left-only. -/
def affineRoundPrefixLeftMessage (h t L : Nat)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundPrefixMaskTranscript Z t L) (a : A) : AffineRoundShortMessages t L :=
  fun i j => Bool.xor (affineRoundPrefix h L (wl z.1 a i) j) (z.2 i j)

/-- The first right extractor is a right-only function once the actual prefixes are fixed. -/
def affineRoundMiddleSeedRight (d t L e : Nat)
    (ys : Z → B → AffinePhaseOneCopies t d)
    (z : AffineRoundPrefixTranscript Z t L) (b : B) : AffineRoundShortMessages t L :=
  fun i => matchedBlockExtractor d 24 L e (ys z.1.1 b i) (z.2 i)

/-- Observe the actual first right seeds and their short-row mask contributions. -/
def affineRoundMiddleRightMessage (d h t L e : Nat)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (z : AffineRoundPrefixTranscript Z t L) (b : B) :
    AffineRoundShortMessages t L × AffineRoundShortMessages t L :=
  (affineRoundMiddleSeedRight d t L e ys z b,
    fun i => matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e (wr z.1.1 b i)
      (affineRoundMiddleSeedRight d t L e ys z b i))

/-- Fixing the first right seeds and mask contributions makes actual short rows left-only. -/
def affineRoundMiddleLeftMessage (h t L e : Nat)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundMiddleRightTranscript Z t L) (a : A) : AffineRoundShortMessages t L :=
  fun i j => Bool.xor
    (matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e (wl z.1.1.1 a i) (z.2.1 i) j)
    (z.2.2 i j)

/-- The second right extractor rereads each original right word using its actual short row. -/
def affineRoundFinalSeedRight (d t L e : Nat)
    (ys : Z → B → AffinePhaseOneCopies t d)
    (z : AffineRoundMiddleTranscript Z t L) (b : B) : AffineRoundShortMessages t L :=
  fun i => matchedBlockExtractor d 24 L e (ys z.1.1.1.1 b i) (z.2 i)

/-- The actual first observation retains the original tag and right prefix masks. -/
def affineRoundPrefixMaskTranscript (h t L : Nat)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (p : Z × B) : AffineRoundPrefixMaskTranscript Z t L :=
  (p.1, affineRoundPrefixMask h t L wr p.1 p.2)

/-- The actual second observation records the prefixes of the executed masked rows. -/
def affineRoundPrefixTranscript (h t L : Nat)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (p : (Z × B) × A) : AffineRoundPrefixTranscript Z t L :=
  (affineRoundPrefixMaskTranscript h t L wr p.1,
    fun i => affineRoundPrefix h L
      (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)))

/-- The third observation records the actual right seeds and corresponding mask contributions. -/
def affineRoundMiddleRightTranscript (d h t L e : Nat)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    AffineRoundMiddleRightTranscript Z t L :=
  (affineRoundPrefixTranscript h t L wl wr p,
    affineRoundMiddleRightMessage d h t L e wr ys
      (affineRoundPrefixTranscript h t L wl wr p) p.1.2)

/-- The fourth observation records the actual short extraction outputs. -/
def affineRoundMiddleTranscript (d h t L e : Nat)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    AffineRoundMiddleTranscript Z t L :=
  (affineRoundMiddleRightTranscript d h t L e wl wr ys p,
    fun i => affineRoundMiddleOutput d h L e (ys p.1.1 p.1.2 i)
      (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)))

/-- The full actual transcript includes the final right extraction seeds. -/
def affineRoundTranscript (d h t L e : Nat)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    AffineRoundTranscript Z t L :=
  (affineRoundMiddleTranscript d h t L e wl wr ys p,
    fun i => affineRoundFinalSeed d h L e (ys p.1.1 p.1.2 i)
      (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)))

/-- The next rows' original-left contributions after the full transcript is fixed. -/
def affineRoundOutputLeft (n h t L e : Nat) (x : Z → A → Fin n → Bool)
    (z : AffineRoundTranscript Z t L) (a : A) :
    AffinePhaseOneCopies t (matchedBlockOutputBits h L) :=
  fun i => matchedBlockExtractor n h L e (x z.1.1.1.1.1 a) (z.2 i)

/-- The next rows' original-right mask contributions after the full transcript is fixed. -/
def affineRoundOutputRight (n h t L e : Nat) (mask : Z → B → Fin n → Bool)
    (z : AffineRoundTranscript Z t L) (b : B) :
    AffinePhaseOneCopies t (matchedBlockOutputBits h L) :=
  fun i => matchedBlockExtractor n h L e (mask z.1.1.1.1.1 b) (z.2 i)

/-- Transcript mass after observing the right prefix masks. -/
noncomputable def affineRoundPrefixMaskWeight (h t L : Nat) [Fintype B]
    (w : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptWeight w r (affineRoundPrefixMask h t L wr)

/-- Original right states conditioned on their prefix-mask message. -/
noncomputable def affineRoundPrefixMaskRight (h t L : Nat) [Fintype B]
    (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptKernel r (affineRoundPrefixMask h t L wr)

/-- Transcript mass after observing actual prefixes. -/
noncomputable def affineRoundPrefixWeight (h t L : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptWeight (affineRoundPrefixMaskWeight h t L w r wr)
    (fun z => l z.1) (affineRoundPrefixLeftMessage h t L wl)

/-- Original left states conditioned on the actual prefix message. -/
noncomputable def affineRoundPrefixLeft (h t L : Nat) [Fintype A]
    (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptKernel (fun z => l z.1) (affineRoundPrefixLeftMessage h t L wl)

/-- The right kernel is unchanged when actual prefixes are observed on the left. -/
noncomputable def affineRoundPrefixRight (h t L : Nat) [Fintype B]
    (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundPrefixTranscript Z t L) : B → ℝ :=
  affineRoundPrefixMaskRight h t L r wr z.1

/-- Transcript mass after observing the first right seeds and short-row masks. -/
noncomputable def affineRoundMiddleRightWeight (d h t L e : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptWeight (affineRoundPrefixWeight h t L w l r wl wr)
    (affineRoundPrefixRight h t L r wr) (affineRoundMiddleRightMessage d h t L e wr ys)

/-- Original right states conditioned on the first right seeds and short-row masks. -/
noncomputable def affineRoundMiddleRightKernel (d h t L e : Nat) [Fintype B]
    (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptKernel (affineRoundPrefixRight h t L r wr)
    (affineRoundMiddleRightMessage d h t L e wr ys)

/-- Transcript mass after observing the actual short rows. -/
noncomputable def affineRoundMiddleWeight (d h t L e : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptWeight (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleLeftMessage h t L e wl)

/-- Original left states conditioned on the actual short rows. -/
noncomputable def affineRoundMiddleLeft (h t L e : Nat) [Fintype A]
    (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) :=
  observedTranscriptKernel (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleLeftMessage h t L e wl)

/-- The full round's normalized transcript mass. -/
noncomputable def affineRoundTranscriptWeight (d h t L e : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptWeight (affineRoundMiddleWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (affineRoundFinalSeedRight d t L e ys)

/-- The original left kernel at the full round transcript. -/
noncomputable def affineRoundTranscriptLeft (h t L e : Nat) [Fintype A]
    (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (z : AffineRoundTranscript Z t L) : A → ℝ :=
  affineRoundMiddleLeft h t L e l wl z.1

/-- The original right kernel at the full round transcript. -/
noncomputable def affineRoundTranscriptRight (d h t L e : Nat) [Fintype B]
    (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) :=
  observedTranscriptKernel (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (affineRoundFinalSeedRight d t L e ys)

end Algebraic.Cutwidth.Extractor
