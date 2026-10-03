/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs

/-!
# The actual transcript of a pair of advice-bit executions

The transcript records both input states, all four first look-ahead outputs,
both refreshed states, and all four second look-ahead outputs. The two advice
bits are arbitrary. Both final outputs are right-only maps once these messages
are fixed. The tampered final output is not included in this transcript:
before advice first differs, it may equal the honest output.

The factors condition the original sources through two successive instances
of the common look-ahead transcript. No source is resampled. These are the
actual messages in Chattopadhyay--Goyal--Li Algorithm 1, used in the advice
induction of Lemma 6.9: <https://arxiv.org/pdf/1505.00107>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Both initial states and all first-pass look-ahead outputs. -/
abbrev FlipFlopFirstTranscript (Z : Type*) (L : Nat) :=
  LookAheadBaseTranscript Z (Fin (matchedBlockOutputBits 64 L) → Bool)
    (Fin (matchedBlockSeedBits L) → Bool)

/-- Both complete look-ahead histories, before observing either final output. -/
abbrev FlipFlopTranscript (Z : Type*) (L : Nat) :=
  LookAheadBaseTranscript (FlipFlopFirstTranscript Z L)
    (Fin (matchedBlockOutputBits 64 L) → Bool) (Fin (matchedBlockSeedBits L) → Bool)

variable {Z A B : Type*}

/-- The honest first refresh is right-only after fixing the first transcript. -/
def flipFlopHonestRefresh (m L e : Nat) (y : Z → B → Fin m → Bool) (b : Bool)
    (t : FlipFlopFirstTranscript Z L) (u : B) :
    Fin (matchedBlockOutputBits 64 L) → Bool :=
  matchedBlockExtractor m 64 L e (y t.1.1 u) (if b then t.2.1.2 else t.2.1.1)

/-- The tampered first refresh uses its own advice bit and the original right source. -/
def flipFlopTamperedRefresh (m L e : Nat) (y' : Z → B → Fin m → Bool) (b' : Bool)
    (t : FlipFlopFirstTranscript Z L) (u : B) :
    Fin (matchedBlockOutputBits 64 L) → Bool :=
  matchedBlockExtractor m 64 L e (y' t.1.1 u) (if b' then t.2.2.2 else t.2.2.1)

/-- The actual two-pass transcript of arbitrary honest and tampered advice bits. -/
def flipFlopTranscript (n m L e : Nat)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b b' : Bool) (p : (Z × B) × A) : FlipFlopTranscript Z L :=
  let z := p.1.1
  let first := flipFlopLookAhead n L e (x z p.2) (q z p.1.2)
  let first' := flipFlopLookAhead n L e (x' z p.2) (q' z p.1.2)
  let t := ((z, (q z p.1.2, q' z p.1.2)), (first, first'))
  let qbar := flipFlopHonestRefresh m L e y b t p.1.2
  let qbar' := flipFlopTamperedRefresh m L e y' b' t p.1.2
  ((t, (qbar, qbar')),
    (flipFlopLookAhead n L e (x z p.2) qbar,
      flipFlopLookAhead n L e (x' z p.2) qbar'))

/-- The exact first transcript weight from the original factors. -/
noncomputable def flipFlopFirstWeight (n L e : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) :
    FlipFlopFirstTranscript Z L → ℝ :=
  lookAheadBaseWeight (Mid := Fin (matchedBlockSeedBits L) → Bool)
    w l r x x' q q' (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)

/-- The original left-source kernel conditioned on the first transcript. -/
noncomputable def flipFlopFirstLeft (n L e : Nat) [Fintype A]
    (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool) :
    FlipFlopFirstTranscript Z L → A → ℝ :=
  lookAheadBaseLeft (Mid := Fin (matchedBlockSeedBits L) → Bool)
    l x x' (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)

/-- The original right-source kernel conditioned on the first input pair. -/
noncomputable def flipFlopFirstRight (L : Nat) [Fintype B] (r : Z → B → ℝ)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) :
    FlipFlopFirstTranscript Z L → B → ℝ :=
  lookAheadBaseRight (Mid := Fin (matchedBlockSeedBits L) → Bool) r q q'

/-- The actual two-pass transcript weight for arbitrary advice bits. -/
noncomputable def flipFlopTranscriptWeight (n m L e : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    FlipFlopTranscript Z L → ℝ :=
  lookAheadBaseWeight (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (flipFlopFirstWeight n L e w l r x x' q q')
    (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q')
    (fun t => x t.1.1) (fun t => x' t.1.1)
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')
    (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)

/-- The original left-source kernel conditioned on both look-ahead histories. -/
noncomputable def flipFlopTranscriptLeft (n L e : Nat) [Fintype A]
    (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool) :
    FlipFlopTranscript Z L → A → ℝ :=
  lookAheadBaseLeft (Mid := Fin (matchedBlockSeedBits L) → Bool) (flipFlopFirstLeft n L e l x x')
    (fun t => x t.1.1) (fun t => x' t.1.1) (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)

/-- The original right-source kernel conditioned on both pairs of right states. -/
noncomputable def flipFlopTranscriptRight (m L e : Nat) [Fintype B]
    (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    FlipFlopTranscript Z L → B → ℝ :=
  lookAheadBaseRight (Mid := Fin (matchedBlockSeedBits L) → Bool) (flipFlopFirstRight L r q q')
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')

/-- The honest final output is right-only once its final seed is recorded. -/
def flipFlopHonestOutput (m L e : Nat) (y : Z → B → Fin m → Bool) (b : Bool)
    (t : FlipFlopTranscript Z L) (u : B) : Fin (matchedBlockOutputBits 64 L) → Bool :=
  matchedBlockExtractor m 64 L e (y t.1.1.1.1 u) (if b then t.2.1.1 else t.2.1.2)

/-- The tampered final output is right-only once its final seed is recorded. -/
def flipFlopTamperedOutput (m L e : Nat) (y' : Z → B → Fin m → Bool) (b' : Bool)
    (t : FlipFlopTranscript Z L) (u : B) : Fin (matchedBlockOutputBits 64 L) → Bool :=
  matchedBlockExtractor m 64 L e (y' t.1.1.1.1 u) (if b' then t.2.2.1 else t.2.2.2)

/-- The original left envelope updated by the two exact common transcripts. -/
noncomputable def flipFlopTranscriptLeftEnvelope (m L e : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    FlipFlopTranscript Z L → ℝ :=
  lookAheadBaseLeftEnvelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (lookAheadBaseLeftEnvelope (Mid := Fin (matchedBlockSeedBits L) → Bool) μ r q q')
    (flipFlopFirstRight L r q q')
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')

/-- The original right envelope updated by both four-output left messages. -/
noncomputable def flipFlopTranscriptRightEnvelope (n L e : Nat) [Fintype A]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool) :
    FlipFlopTranscript Z L → ℝ :=
  lookAheadBaseRightEnvelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (lookAheadBaseRightEnvelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
      ν l x x' (flipFlopSeedPrefix L)
      (matchedBlockExtractor n 24 L e)
      (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e))
    (flipFlopFirstLeft n L e l x x') (fun t => x t.1.1) (fun t => x' t.1.1)
    (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)

end Algebraic.Cutwidth.Extractor
