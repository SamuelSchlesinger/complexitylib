/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs

/-!
# Actual final outputs and their conditional transcript factors

The unobserved law retains the complete common history and original left
state. The observed law additionally records the actual tampered final
output. Both are direct images of the original source law under the actual
advice-bit programs. Observing the final tampered output conditions only the
original right kernel; the left kernel is unchanged at each common history.

These are the two transcript forms used before and after the first differing
advice bit in Chattopadhyay--Goyal--Li Algorithm 2 and Lemma 6.9:
<https://arxiv.org/pdf/1505.00107>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The common two-pass history followed by the actual tampered final output. -/
abbrev FlipFlopObservedTranscript (Z : Type*) (L : Nat) :=
  FlipFlopTranscript Z L × (Fin (matchedBlockOutputBits 64 L) → Bool)

variable {Z A B : Type*}

/-- Observe the tampered final state after both actual advice-bit executions. -/
def flipFlopObservedTranscript (n m L e : Nat)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b b' : Bool) (p : (Z × B) × A) : FlipFlopObservedTranscript Z L :=
  (flipFlopTranscript n m L e x x' y y' q q' b b' p,
    flipFlopStep n m L e (x' p.1.1 p.2) (y' p.1.1 p.1.2) (q' p.1.1 p.1.2) b')

/-- The honest final state with its common history and the full original left state. -/
noncomputable def flipFlopOutputWeight (n m L e : Nat)
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    (FlipFlopTranscript Z L × A) × (Fin (matchedBlockOutputBits 64 L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((flipFlopTranscript n m L e x x' y y' q q' b b' p, p.2),
      flipFlopStep n m L e (x p.1.1 p.2) (y p.1.1 p.1.2) (q p.1.1 p.1.2) b))
    (factoredWeight w l r)

/-- The actual honest final state, additionally retaining the actual tampered final state. -/
noncomputable def flipFlopObservedOutputWeight (n m L e : Nat)
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    (FlipFlopObservedTranscript Z L × A) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((flipFlopObservedTranscript n m L e x x' y y' q q' b b' p, p.2),
      flipFlopStep n m L e (x p.1.1 p.2) (y p.1.1 p.1.2) (q p.1.1 p.1.2) b))
    (factoredWeight w l r)

/-- The exact transcript weight after observing the tampered final output. -/
noncomputable def flipFlopObservedWeight (n m L e : Nat) [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    FlipFlopObservedTranscript Z L → ℝ :=
  observedTranscriptWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
    (flipFlopTranscriptRight m L e r y y' q q' b b') (flipFlopTamperedOutput m L e y' b')

/-- Observing the final right output preserves the original conditional left kernel. -/
noncomputable def flipFlopObservedLeft (n L e : Nat) [Fintype A]
    (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (t : FlipFlopObservedTranscript Z L) : A → ℝ :=
  flipFlopTranscriptLeft n L e l x x' t.1

/-- The original right kernel conditioned on the final tampered output as well as both histories. -/
noncomputable def flipFlopObservedRight (m L e : Nat) [Fintype B]
    (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    FlipFlopObservedTranscript Z L → B → ℝ :=
  observedTranscriptKernel (flipFlopTranscriptRight m L e r y y' q q' b b')
    (flipFlopTamperedOutput m L e y' b')

/-- The left envelope scaled by the conditional probability of the final right message. -/
noncomputable def flipFlopObservedLeftEnvelope (m L e : Nat) [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool) :
    FlipFlopObservedTranscript Z L → ℝ :=
  observedTranscriptWeight (flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b')
    (flipFlopTranscriptRight m L e r y y' q q' b b') (flipFlopTamperedOutput m L e y' b')

/-- The right envelope copied to every possible final tampered output. -/
noncomputable def flipFlopObservedRightEnvelope (n L e : Nat) [Fintype A]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (t : FlipFlopObservedTranscript Z L) : ℝ :=
  flipFlopTranscriptRightEnvelope n L e ν l x x' t.1

end Algebraic.Cutwidth.Extractor
