/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Internal.Envelope

/-!
# Exact factors for the complete advice-bit transcript

For arbitrary advice bits, the actual pair of eight-call executions admits
normalized conditional kernels for the original sources. Both final outputs
are right-only maps of these kernels. The original source envelopes have
exact total growth `D^8` on the left and `C^4` on the right, where `D` is the
short-output cardinality and `C` the refresh-state cardinality.

This common transcript leaves the final tampered output unobserved. The
opposite-bit identity connects observing that output to the transcript used
by the checked opposite-advice guarantees. These are the factorization and
entropy bookkeeping for the induction in Chattopadhyay--Goyal--Li Lemma 6.9:
<https://arxiv.org/pdf/1505.00107>. The complete advice induction remains a
separate theorem.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The original left kernel is normalized after the first history. -/
theorem flipFlopFirstLeft_probability (n L e : Nat) {Z A : Type*} [Fintype A]
    (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (t : FlipFlopFirstTranscript Z L) :
    IsProbabilityWeight (flipFlopFirstLeft n L e l x x' t) :=
  Internal.flipFlopFirstLeft_probability
    n L e l x x' hl t

/-- The original right kernel is normalized after the first input pair. -/
theorem flipFlopFirstRight_probability (L : Nat) {Z B : Type*} [Fintype B]
    (r : Z → B → ℝ) (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) (t : FlipFlopFirstTranscript Z L) :
    IsProbabilityWeight (flipFlopFirstRight L r q q' t) :=
  Internal.flipFlopFirstRight_probability
    L r q q' hr t

/-- The first actual transcript and both conditional kernels are normalized. -/
theorem flipFlopFirst_probability (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopFirstWeight n L e w l r x x' q q') ∧
      (∀ t, IsProbabilityWeight (flipFlopFirstLeft n L e l x x' t)) ∧
      (∀ t, IsProbabilityWeight (flipFlopFirstRight L r q q' t)) :=
  Internal.flipFlopFirst_probability
    n L e w l r x x' q q' hw hl hr

/-- The complete actual transcript and both original-source kernels are normalized. -/
theorem flipFlopTranscript_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b') ∧
      (∀ t, IsProbabilityWeight (flipFlopTranscriptLeft n L e l x x' t)) ∧
      (∀ t, IsProbabilityWeight (flipFlopTranscriptRight m L e r y y' q q' b b' t)) :=
  Internal.flipFlopTranscript_probability
    n m L e w l r x x' y y' q q' b b' hw hl hr

/-- The actual two-pass transcript factors the original sources exactly. -/
theorem flipFlopTranscript_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((flipFlopTranscript n m L e x x' y y' q q' b b' p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopTranscriptLeft n L e l x x')
        (flipFlopTranscriptRight m L e r y y' q q' b b') :=
  Internal.flipFlopTranscript_factored
    n m L e w l r x x' y y' q q' b b' hl hr

/-- The honest right-only output map recovers the actual advice-bit program. -/
theorem flipFlopHonestOutput_eq_step (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b b' : Bool) (p : (Z × B) × A) :
    flipFlopHonestOutput m L e y b
      (flipFlopTranscript n m L e x x' y y' q q' b b' p) p.1.2 =
      flipFlopStep n m L e (x p.1.1 p.2) (y p.1.1 p.1.2) (q p.1.1 p.1.2) b :=
  Internal.flipFlopHonestOutput_eq_step
    n m L e x x' y y' q q' b b' p

/-- The tampered right-only output map recovers its actual advice-bit program. -/
theorem flipFlopTamperedOutput_eq_step (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b b' : Bool) (p : (Z × B) × A) :
    flipFlopTamperedOutput m L e y' b'
      (flipFlopTranscript n m L e x x' y y' q q' b b' p) p.1.2 =
      flipFlopStep n m L e (x' p.1.1 p.2) (y' p.1.1 p.1.2) (q' p.1.1 p.1.2) b' :=
  Internal.flipFlopTamperedOutput_eq_step
    n m L e x x' y y' q q' b b' p

/-- Observing the tampered output for opposite bits gives the opposite-advice transcript. -/
theorem flipFlopTranscript_opposite (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (p : (Z × B) × A) :
    (flipFlopTranscript n m L e x x' y y' q q' b (!b) p,
      flipFlopTamperedOutput m L e y' (!b)
        (flipFlopTranscript n m L e x x' y y' q q' b (!b) p) p.1.2) =
      flipFlopOppositeTranscript n m L e x x' y y' q q' b p :=
  Internal.flipFlopTranscript_opposite
    n m L e x x' y y' q q' b p

/-- The updated original left-source envelope is nonnegative. -/
theorem flipFlopTranscriptLeftEnvelope_nonnegative (m L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (t : FlipFlopTranscript Z L) :
    0 ≤ flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b' t :=
  Internal.flipFlopTranscriptLeftEnvelope_nonnegative
    m L e μ r y y' q q' b b' nonnegative hr t

/-- The updated original right-source envelope is nonnegative. -/
theorem flipFlopTranscriptRightEnvelope_nonnegative (n L e : Nat) {Z A : Type*}
    [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (nonnegative : ∀ z, 0 ≤ ν z) (hl : ∀ z, IsProbabilityWeight (l z))
    (t : FlipFlopTranscript Z L) :
    0 ≤ flipFlopTranscriptRightEnvelope n L e ν l x x' t :=
  Internal.flipFlopTranscriptRightEnvelope_nonnegative
    n L e ν l x x' nonnegative hl t

/-- The complete actual transcript preserves an explicit original left-source envelope. -/
theorem flipFlopTranscript_left_envelope (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (t : FlipFlopTranscript Z L) (x₀ : Fin n → Bool) :
    flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b' t *
        mapWeight (x t.1.1.1.1) (flipFlopTranscriptLeft n L e l x x' t) x₀ ≤
      flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b' t :=
  Internal.flipFlopTranscript_left_envelope
    n m L e w l r x x' y y' q q' b b' μ hw hl hr cap t x₀

/-- The complete actual transcript preserves an explicit original right-source envelope. -/
theorem flipFlopTranscript_right_envelope (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (ν : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (t : FlipFlopTranscript Z L) (y₀ : Fin m → Bool) :
    flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b' t *
        mapWeight (y t.1.1.1.1) (flipFlopTranscriptRight m L e r y y' q q' b b' t) y₀ ≤
      flipFlopTranscriptRightEnvelope n L e ν l x x' t :=
  Internal.flipFlopTranscript_right_envelope
    n m L e w l r x x' y y' q q' b b' ν hw hl hr cap t y₀

/-- The left envelope pays for all eight short look-ahead messages. -/
theorem flipFlopTranscriptLeftEnvelope_sum (m L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ t, flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b' t) =
      (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * ∑ z, μ z :=
  Internal.flipFlopTranscriptLeftEnvelope_sum
    m L e μ r y y' q q' b b' hr

/-- The right envelope pays for the two pairs of right states. -/
theorem flipFlopTranscriptRightEnvelope_sum (n L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ)
    (x x' : Z → A → Fin n → Bool) (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ t, flipFlopTranscriptRightEnvelope n L e ν l x x' t) =
      (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 4 * ∑ z, ν z :=
  Internal.flipFlopTranscriptRightEnvelope_sum
    n L e ν l x x' hl

end Algebraic.Cutwidth.Extractor
