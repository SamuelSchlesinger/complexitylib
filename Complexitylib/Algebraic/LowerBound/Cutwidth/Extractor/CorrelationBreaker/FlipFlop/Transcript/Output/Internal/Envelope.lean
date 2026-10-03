/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Mathlib.Tactic.Ring

/-!
# Source envelopes after observing the actual tampered final output

The final right message preserves the left envelope total and multiplies the
right envelope total by the state alphabet size. Thus the complete observed
transcript has exact total growth `D^8` on the left and `C^5` on the right.
All bounds apply to the normalized original-source kernels at every row.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopObservedLeftEnvelope_nonnegative (m L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (t : FlipFlopObservedTranscript Z L) :
    0 ≤ flipFlopObservedLeftEnvelope m L e μ r y y' q q' b b' t :=
  observedTranscriptWeight_nonnegative _ _ _
    (flipFlopTranscriptLeftEnvelope_nonnegative m L e μ r y y' q q' b b' nonnegative hr)
    (fun u => (flipFlopTranscriptRight_probability m L e r y y' q q' b b' hr u).1) t

theorem flipFlopObservedRightEnvelope_nonnegative (n L e : Nat) {Z A : Type*}
    [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (nonnegative : ∀ z, 0 ≤ ν z) (hl : ∀ z, IsProbabilityWeight (l z))
    (t : FlipFlopObservedTranscript Z L) :
    0 ≤ flipFlopObservedRightEnvelope n L e ν l x x' t :=
  flipFlopTranscriptRightEnvelope_nonnegative n L e ν l x x' nonnegative hl t.1

theorem flipFlopObserved_left_envelope (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (t : FlipFlopObservedTranscript Z L) (x₀ : Fin n → Bool) :
    flipFlopObservedWeight n m L e w l r x x' y y' q q' b b' t *
        mapWeight (x t.1.1.1.1.1) (flipFlopObservedLeft n L e l x x' t) x₀ ≤
      flipFlopObservedLeftEnvelope m L e μ r y y' q q' b b' t := by
  exact observedTranscript_right_envelope
    (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
    (flipFlopTranscriptLeft n L e l x x')
    (flipFlopTranscriptRight m L e r y y' q q' b b')
    (fun u => x u.1.1.1.1) (flipFlopTamperedOutput m L e y' b')
    (flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b')
    (fun u => (flipFlopTranscriptRight_probability m L e r y y' q q' b b' hr u).1)
    (flipFlopTranscript_left_envelope n m L e w l r x x' y y' q q' b b' μ hw hl hr cap)
    t x₀

theorem flipFlopObserved_right_envelope (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (ν : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (t : FlipFlopObservedTranscript Z L) (y₀ : Fin m → Bool) :
    flipFlopObservedWeight n m L e w l r x x' y y' q q' b b' t *
        mapWeight (y t.1.1.1.1.1)
          (flipFlopObservedRight m L e r y y' q q' b b' t) y₀ ≤
      flipFlopObservedRightEnvelope n L e ν l x x' t := by
  obtain ⟨hwt, _, hrt⟩ := flipFlopTranscript_probability
    n m L e w l r x x' y y' q q' b b' hw hl hr
  exact observedTranscript_left_envelope
    (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
    (flipFlopTranscriptRight m L e r y y' q q' b b')
    (fun u => y u.1.1.1.1) (flipFlopTamperedOutput m L e y' b')
    (flipFlopTranscriptRightEnvelope n L e ν l x x') hwt.1 (fun u => (hrt u).1)
    (flipFlopTranscript_right_envelope n m L e w l r x x' y y' q q' b b' ν hw hl hr cap)
    t y₀

theorem flipFlopObservedLeftEnvelope_sum (m L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ t, flipFlopObservedLeftEnvelope m L e μ r y y' q q' b b' t) =
      (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * ∑ z, μ z := by
  unfold flipFlopObservedLeftEnvelope
  rw [observedTranscript_right_envelope_sum _ _ _
    (fun u => (flipFlopTranscriptRight_probability m L e r y y' q q' b b' hr u).2)]
  exact flipFlopTranscriptLeftEnvelope_sum m L e μ r y y' q q' b b' hr

theorem flipFlopObservedRightEnvelope_sum (n L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ)
    (x x' : Z → A → Fin n → Bool) (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ t, flipFlopObservedRightEnvelope n L e ν l x x' t) =
      (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 5 * ∑ z, ν z := by
  unfold flipFlopObservedRightEnvelope
  rw [observedTranscript_left_envelope_sum, flipFlopTranscriptRightEnvelope_sum n L e ν l x x' hl]
  ring

end Algebraic.Cutwidth.Extractor.Internal
