/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Mathlib.Tactic.Ring

/-!
# Original source envelopes through the first phase

The original left source pays for the family of first extraction outputs.
The original right source pays for the initial seed-and-mask message and
the family of advice outputs. Opposite-side observations retain their
message probabilities in the envelope and preserve its total exactly.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affinePhaseOneRight_left_envelope (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (μ : Z → ℝ)
    (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffinePhaseOneRightTranscript Z t L₀) (x₀ : Fin n → Bool) :
    affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys z *
        mapWeight (x z.1) (l z.1) x₀ ≤
      affinePhaseOneRightLeftEnvelope n d t L₀ e₀ μ r mask ys z :=
  observedTranscript_right_envelope w l r x _ μ hr cap z x₀

theorem affinePhaseOneRight_right_envelope (n d t L₀ e₀ : Nat) {Z B Y : Type*}
    [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (y : Z → B → Y) (ξ : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffinePhaseOneRightTranscript Z t L₀) (y₀ : Y) :
    affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys z *
        mapWeight (y z.1) (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) y₀ ≤ ξ z.1 :=
  observedTranscript_left_envelope w r y _ ξ hw hr cap z y₀

theorem affinePhaseOneLeft_left_envelope (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffinePhaseOneLeftTranscript Z t L₀) (x₀ : Fin n → Bool) :
    affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys z *
        mapWeight (x z.1.1) (affinePhaseOneLeftKernel n t L₀ e₀ l x z) x₀ ≤
      affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z := by
  have hw₀ := (affinePhaseOneRight_probability n d t L₀ e₀ w r mask ys hw hr).1
  exact observedTranscript_left_envelope
    (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys) (fun z => l z.1) (fun z => x z.1)
    (affinePhaseOneFirstLeft n t L₀ e₀ x)
    (affinePhaseOneRightLeftEnvelope n d t L₀ e₀ μ r mask ys) hw₀.1 (fun z => (hl z.1).1)
    (affinePhaseOneRight_left_envelope n d t L₀ e₀ w l r x mask ys μ
      (fun z => (hr z).1) cap) z x₀

theorem affinePhaseOneLeft_right_envelope (n d t L₀ e₀ : Nat) {Z A B Y : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (y : Z → B → Y) (ξ : Z → ℝ)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffinePhaseOneLeftTranscript Z t L₀) (y₀ : Y) :
    affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys z *
        mapWeight (y z.1.1) (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) y₀ ≤
      affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x z :=
  observedTranscript_right_envelope
    (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys)
    (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys) (fun z => l z.1) (fun z => y z.1)
    (affinePhaseOneFirstLeft n t L₀ e₀ x) (fun z => ξ z.1) (fun z => hl z.1)
    (affinePhaseOneRight_right_envelope n d t L₀ e₀ w r mask ys y ξ hw hr cap) z y₀

theorem affinePhaseOneTranscript_left_envelope (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) (x₀ : Fin n → Bool) :
    affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice z *
        mapWeight (x z.1.1.1) (affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x z) x₀ ≤
      affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice z := by
  have hr₀ : ∀ z, IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) :=
    observedTranscriptKernel_probability _ _ hr
  exact observedTranscript_right_envelope
    (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
    (affinePhaseOneLeftKernel n t L₀ e₀ l x)
    (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) (fun z => x z.1.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice)
    (affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys) (fun z => (hr₀ z.1).1)
    (affinePhaseOneLeft_left_envelope n d t L₀ e₀ w l r x mask ys μ hw hl hr cap) z x₀

theorem affinePhaseOneTranscript_right_envelope (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z A B Y : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (y : Z → B → Y) (ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) (y₀ : Y) :
    affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice z *
        mapWeight (y z.1.1.1)
          (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice z) y₀ ≤
      affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ξ l x z := by
  obtain ⟨hw₁, _, hr₁⟩ := affinePhaseOneLeft_probability n d t L₀ e₀
    w l r x mask ys hw hl hr
  exact observedTranscript_left_envelope
    (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
    (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) (fun z => y z.1.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice)
    (affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x) hw₁.1 (fun z => (hr₁ z).1)
    (affinePhaseOneLeft_right_envelope n d t L₀ e₀ w l r x mask ys y ξ hw.1
      (fun z => (hl z).1) (fun z => (hr z).1) cap) z y₀

theorem affinePhaseOneRightLeftEnvelope_sum (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affinePhaseOneRightLeftEnvelope n d t L₀ e₀ μ r mask ys z) = ∑ z, μ z :=
  observedTranscript_right_envelope_sum μ r _ hr

theorem affinePhaseOneLeftEnvelope_sum (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z) =
      (Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) : ℝ) *
        ∑ z, μ z := by
  unfold affinePhaseOneLeftEnvelope
  rw [observedTranscript_left_envelope_sum,
    affinePhaseOneRightLeftEnvelope_sum n d t L₀ e₀ μ r mask ys hr]

theorem affinePhaseOneRightEnvelope_sum (n t L₀ e₀ : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (x : Z → A → Fin n → Bool) (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x z) =
      (Fintype.card (AffinePhaseOneRightMessage t L₀) : ℝ) * ∑ z, ξ z := by
  unfold affinePhaseOneRightEnvelope
  rw [observedTranscript_right_envelope_sum
    (fun z : AffinePhaseOneRightTranscript Z t L₀ => ξ z.1) (fun z => l z.1)
    (affinePhaseOneFirstLeft n t L₀ e₀ x) (fun z => hl z.1),
    observedTranscript_left_envelope_sum]

theorem affinePhaseOneTranscriptLeftEnvelope_sum (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z B : Type*} [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (advice : Option (Fin t) → List Bool) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice z) =
      (Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) : ℝ) *
        ∑ z, μ z := by
  have hr₀ : ∀ z, IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) :=
    observedTranscriptKernel_probability _ _ hr
  have total := observedTranscript_right_envelope_sum
    (affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys)
    (fun z : AffinePhaseOneLeftTranscript Z t L₀ =>
      affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice) (fun z => (hr₀ z.1).2)
  exact total.trans (affinePhaseOneLeftEnvelope_sum n d t L₀ e₀ μ r mask ys
    (fun z => (hr z).2))

theorem affinePhaseOneTranscriptRightEnvelope_sum (n t L₀ e₀ L₁ : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (x : Z → A → Fin n → Bool) (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ξ l x z) =
      (Fintype.card (AffinePhaseOneCopies t (matchedBlockSeedBits L₁)) : ℝ) *
        Fintype.card (AffinePhaseOneRightMessage t L₀) * ∑ z, ξ z := by
  unfold affinePhaseOneTranscriptRightEnvelope
  rw [observedTranscript_left_envelope_sum,
    affinePhaseOneRightEnvelope_sum n t L₀ e₀ ξ l x hl]
  ring

theorem affinePhaseOneLeftEnvelope_nonnegative (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z b, 0 ≤ r z b)
    (z : AffinePhaseOneLeftTranscript Z t L₀) :
    0 ≤ affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z :=
  observedTranscriptWeight_nonnegative μ r _ nonnegative hr z.1

theorem affinePhaseOneRightEnvelope_nonnegative (n t L₀ e₀ : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → Fin n → Bool)
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffinePhaseOneLeftTranscript Z t L₀) :
    0 ≤ affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x z :=
  observedTranscriptWeight_nonnegative
    (fun z : AffinePhaseOneRightTranscript Z t L₀ => ξ z.1) (fun z => l z.1)
    (affinePhaseOneFirstLeft n t L₀ e₀ x) (fun z => nonnegative z.1) (fun z => hl z.1) z

theorem affinePhaseOneTranscriptLeftEnvelope_nonnegative (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z B : Type*} [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (advice : Option (Fin t) → List Bool) (nonnegative : ∀ z, 0 ≤ μ z)
    (hr : ∀ z, IsProbabilityWeight (r z)) (z : AffinePhaseOneTranscript Z t L₀ L₁) :
    0 ≤ affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice z := by
  have hr₀ : ∀ z, IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) :=
    observedTranscriptKernel_probability _ _ hr
  exact observedTranscriptWeight_nonnegative _ _ _
    (affinePhaseOneLeftEnvelope_nonnegative n d t L₀ e₀ μ r mask ys nonnegative
      (fun z => (hr z).1)) (fun z => (hr₀ z.1).1) z

theorem affinePhaseOneTranscriptRightEnvelope_nonnegative (n t L₀ e₀ L₁ : Nat)
    {Z A : Type*} [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (x : Z → A → Fin n → Bool) (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) :
    0 ≤ affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ξ l x z :=
  affinePhaseOneRightEnvelope_nonnegative n t L₀ e₀ ξ l x nonnegative hl z.1

theorem card_affinePhaseOneCopies (t width : Nat) :
    Fintype.card (AffinePhaseOneCopies t width) = (2 ^ width) ^ (t + 1) := by
  simp only [AffinePhaseOneCopies, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin, Fintype.card_bool]

theorem card_affinePhaseOneRightMessage (t L₀ : Nat) :
    Fintype.card (AffinePhaseOneRightMessage t L₀) =
      (2 ^ (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀)) ^ (t + 1) := by
  unfold AffinePhaseOneRightMessage
  rw [Fintype.card_prod, card_affinePhaseOneCopies,
    card_affinePhaseOneCopies,
    pow_add 2 (matchedBlockSeedBits L₀) (matchedBlockOutputBits 64 L₀), mul_pow]

end Algebraic.Cutwidth.Extractor.Internal
