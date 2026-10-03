/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Internal.Envelope

/-!
# Exact laws before and after observing the final tampered state

The honest final output is right-only after the common transcript. Observing
its tampered counterpart preserves exact conditional independence of the
original sources and gives normalized kernels even on null observations.
The resulting source-envelope totals are `D^8` on the left and `C^5` on the
right. Dropping the original left state identifies the whole honest-state
law needed for the next advice bit. For opposite advice the observed law
is exactly the law in the complete opposite-bit extraction theorem.

These facts support the two-phase induction in Chattopadhyay--Goyal--Li
Algorithm 2 and Lemma 6.9: <https://arxiv.org/pdf/1505.00107>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The original right kernel is normalized after both complete histories. -/
theorem flipFlopTranscriptRight_probability (m L e : Nat) {Z B : Type*} [Fintype B]
    (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) (t : FlipFlopTranscript Z L) :
    IsProbabilityWeight (flipFlopTranscriptRight m L e r y y' q q' b b' t) :=
  Internal.flipFlopTranscriptRight_probability
    m L e r y y' q q' b b' hr t

/-- The actual honest output law with its common history is normalized. -/
theorem flipFlopOutputWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopOutputWeight n m L e w l r x x' y y' q q' b b') :=
  Internal.flipFlopOutputWeight_probability
    n m L e w l r x x' y y' q q' b b' hw hl hr

/-- The actual output law retaining the final tampered state is normalized. -/
theorem flipFlopObservedOutputWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b b') :=
  Internal.flipFlopObservedOutputWeight_probability
    n m L e w l r x x' y y' q q' b b' hw hl hr

/-- The observed transcript and both original-source kernels are normalized. -/
theorem flipFlopObserved_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b') ∧
      (∀ t, IsProbabilityWeight (flipFlopObservedLeft n L e l x x' t)) ∧
      (∀ t, IsProbabilityWeight (flipFlopObservedRight m L e r y y' q q' b b' t)) :=
  Internal.flipFlopObserved_probability
    n m L e w l r x x' y y' q q' b b' hw hl hr

/-- Observing the actual tampered final output gives these exact original-source factors. -/
theorem flipFlopObserved_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((flipFlopObservedTranscript n m L e x x' y y' q q' b b' p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopObservedLeft n L e l x x')
        (flipFlopObservedRight m L e r y y' q q' b b') :=
  Internal.flipFlopObserved_factored
    n m L e w l r x x' y y' q q' b b' hl hr

/-- The actual honest output is right-only over the exact common transcript factors. -/
theorem flipFlopOutputWeight_eq_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    flipFlopOutputWeight n m L e w l r x x' y y' q q' b b' =
      mapWeight (fun p : (FlipFlopTranscript Z L × B) × A =>
        ((p.1.1, p.2), flipFlopHonestOutput m L e y b p.1.1 p.1.2))
        (factoredWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
          (flipFlopTranscriptLeft n L e l x x')
          (flipFlopTranscriptRight m L e r y y' q q' b b')) :=
  Internal.flipFlopOutputWeight_eq_factored
    n m L e w l r x x' y y' q q' b b' hl hr

/-- The actual honest output is right-only over the exact observed transcript factors. -/
theorem flipFlopObservedOutputWeight_eq_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b b' =
      mapWeight (fun p : (FlipFlopObservedTranscript Z L × B) × A =>
        ((p.1.1, p.2), flipFlopHonestOutput m L e y b p.1.1.1 p.1.2))
        (factoredWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
          (flipFlopObservedLeft n L e l x x')
          (flipFlopObservedRight m L e r y y' q q' b b')) :=
  Internal.flipFlopObservedOutputWeight_eq_factored
    n m L e w l r x x' y y' q q' b b' hl hr

/-- Dropping the original left state gives the honest seed law over the common transcript. -/
theorem flipFlopOutputWeight_retainedSeed (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (FlipFlopTranscript Z L × A) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool) => (p.1.1, p.2))
      (flipFlopOutputWeight n m L e w l r x x' y y' q q' b b') =
      retainedSeedWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopTranscriptRight m L e r y y' q q' b b')
        (flipFlopHonestOutput m L e y b) :=
  Internal.flipFlopOutputWeight_retainedSeed
    n m L e w l r x x' y y' q q' b b' hw hl hr

/-- Dropping the original left state gives the honest seed law with tampered output retained. -/
theorem flipFlopObservedOutputWeight_retainedSeed (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (FlipFlopObservedTranscript Z L × A) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool) => (p.1.1, p.2))
      (flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b b') =
      retainedSeedWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopObservedRight m L e r y y' q q' b b')
        (fun t => flipFlopHonestOutput m L e y b t.1) :=
  Internal.flipFlopObservedOutputWeight_retainedSeed
    n m L e w l r x x' y y' q q' b b' hw hl hr

/-- Opposite advice gives exactly the transcript of the checked opposite-advice theorem. -/
theorem flipFlopObservedTranscript_opposite (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (p : (Z × B) × A) :
    flipFlopObservedTranscript n m L e x x' y y' q q' b (!b) p =
      flipFlopOppositeTranscript n m L e x x' y y' q q' b p :=
  Internal.flipFlopObservedTranscript_opposite
    n m L e x x' y y' q q' b p

/-- The observed actual output law specializes to the checked opposite-advice law. -/
theorem flipFlopObservedOutputWeight_opposite (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool)
    : flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b (!b) =
      flipFlopOppositeWeight n m L e w l r x x' y y' q q' b :=
  Internal.flipFlopObservedOutputWeight_opposite
    n m L e w l r x x' y y' q q' b

/-- The observed original left-source envelope is nonnegative. -/
theorem flipFlopObservedLeftEnvelope_nonnegative (m L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (t : FlipFlopObservedTranscript Z L) :
    0 ≤ flipFlopObservedLeftEnvelope m L e μ r y y' q q' b b' t :=
  Internal.flipFlopObservedLeftEnvelope_nonnegative
    m L e μ r y y' q q' b b' nonnegative hr t

/-- The observed original right-source envelope is nonnegative. -/
theorem flipFlopObservedRightEnvelope_nonnegative (n L e : Nat) {Z A : Type*}
    [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (nonnegative : ∀ z, 0 ≤ ν z) (hl : ∀ z, IsProbabilityWeight (l z))
    (t : FlipFlopObservedTranscript Z L) :
    0 ≤ flipFlopObservedRightEnvelope n L e ν l x x' t :=
  Internal.flipFlopObservedRightEnvelope_nonnegative
    n L e ν l x x' nonnegative hl t

/-- The final tampered observation preserves an explicit original left-source envelope. -/
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
      flipFlopObservedLeftEnvelope m L e μ r y y' q q' b b' t :=
  Internal.flipFlopObserved_left_envelope
    n m L e w l r x x' y y' q q' b b' μ hw hl hr cap t x₀

/-- The final tampered observation preserves an explicit original right-source envelope. -/
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
      flipFlopObservedRightEnvelope n L e ν l x x' t :=
  Internal.flipFlopObserved_right_envelope
    n m L e w l r x x' y y' q q' b b' ν hw hl hr cap t y₀

/-- The full observed left envelope pays for exactly eight short outputs. -/
theorem flipFlopObservedLeftEnvelope_sum (m L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ t, flipFlopObservedLeftEnvelope m L e μ r y y' q q' b b' t) =
      (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * ∑ z, μ z :=
  Internal.flipFlopObservedLeftEnvelope_sum
    m L e μ r y y' q q' b b' hr

/-- The full observed right envelope pays for five refresh-width outputs. -/
theorem flipFlopObservedRightEnvelope_sum (n L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ)
    (x x' : Z → A → Fin n → Bool) (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ t, flipFlopObservedRightEnvelope n L e ν l x x' t) =
      (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 5 * ∑ z, ν z :=
  Internal.flipFlopObservedRightEnvelope_sum
    n L e ν l x x' hl

end Algebraic.Cutwidth.Extractor
