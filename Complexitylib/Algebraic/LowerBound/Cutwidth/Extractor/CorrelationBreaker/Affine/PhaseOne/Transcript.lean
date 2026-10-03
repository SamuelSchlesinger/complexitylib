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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript.Internal.Envelope

/-!
# Exact first-phase execution factors and source envelopes

The actual prefix, matched extraction, advice construction, and final
matched extraction have an exact alternating transcript over the original
left and right states. All kernels are normalized, including null rows.
The XOR equations connect the executed masked program to the side-local
maps used in that transcript.

The original left envelope pays for all first extraction outputs. The
original right envelope pays for all initial seed-and-mask messages and
all advice outputs. Opposite-side observations preserve envelope totals.
These are exact execution and counting laws, with no statistical premise
or conclusion about the component programs.

The message order follows Chattopadhyay--Liao, *Extractors for Sum of Two
Sources* (2021), first phase of Theorem 6.1, printed p.23, using the
observation rule of Lemma 3.25, printed p.15:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual first extractor splits a masked input into its two XOR contributions. -/
theorem affinePhaseOneFirstOutput_xor (n d L₀ e₀ : Nat) (x mask : Fin n → Bool)
    (y : Fin d → Bool) :
    affinePhaseOneFirstOutput n d L₀ e₀ (fun j => Bool.xor (x j) (mask j)) y =
      fun j => Bool.xor (affinePhaseOneFirstOutput n d L₀ e₀ x y j)
        (affinePhaseOneFirstOutput n d L₀ e₀ mask y j) :=
  Internal.affinePhaseOneFirstOutput_xor n d L₀ e₀ x mask y

/-- Fixing the first right message makes every actual first output left-only. -/
theorem affinePhaseOneFirstLeft_eq (n d t L₀ e₀ : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affinePhaseOneFirstLeft n t L₀ e₀ x
        (affinePhaseOneRightTranscript n d t L₀ e₀ mask ys p.1) p.2 =
      fun i => affinePhaseOneFirstOutput n d L₀ e₀
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j)) (ys p.1.1 p.1.2 i) :=
  Internal.affinePhaseOneFirstLeft_eq n d t L₀ e₀ x mask ys p

/-- Fixing all first outputs makes every actual advice output right-only. -/
theorem affinePhaseOneSecondRight_eq (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) :
    affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice
        (affinePhaseOneLeftTranscript n d t L₀ e₀ x mask ys p) p.1.2 =
      fun i => affinePhaseOneSecondSeed n d L₀ e₀ L₁ e₁
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j))
        (ys p.1.1 p.1.2 i) (advice i) :=
  Internal.affinePhaseOneSecondRight_eq n d t L₀ e₀ L₁ e₁ x mask ys advice p

/-- The actual final output is the XOR of its original-left and mask contributions. -/
theorem affinePhaseOneOutput_eq_xor (n d t h L₀ e₀ L₁ e₁ er : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) (i : Option (Fin t)) :
    affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j))
        (ys p.1.1 p.1.2 i) (advice i) =
      fun j => Bool.xor
        (affinePhaseOneOutputLeft n t h L₀ L₁ er x
          (affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p) p.2 i j)
        (affinePhaseOneOutputRight n t h L₀ L₁ er mask
          (affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p) p.1.2 i j) :=
  Internal.affinePhaseOneOutput_eq_xor n d t h L₀ e₀ L₁ e₁ er x mask ys advice p i

/-- The first right observation has a normalized transcript and normalized right rows. -/
theorem affinePhaseOneRight_probability (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys) ∧
      ∀ z, IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) :=
  Internal.affinePhaseOneRight_probability n d t L₀ e₀ w r mask ys hw hr

/-- The first two observations have normalized transcript and original-state kernels. -/
theorem affinePhaseOneLeft_probability (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys) ∧
      (∀ z, IsProbabilityWeight (affinePhaseOneLeftKernel n t L₀ e₀ l x z)) ∧
      ∀ z : AffinePhaseOneLeftTranscript Z t L₀,
        IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) :=
  Internal.affinePhaseOneLeft_probability n d t L₀ e₀ w l r x mask ys hw hl hr

/-- All three actual observations have normalized transcript and original-state kernels. -/
theorem affinePhaseOneTranscript_probability (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁
      w l r x mask ys advice) ∧
      (∀ z, IsProbabilityWeight (affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x z)) ∧
      ∀ z, IsProbabilityWeight
        (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice z) :=
  Internal.affinePhaseOneTranscript_probability n d t L₀ e₀ L₁ e₁ w l r x mask ys advice hw hl hr

/-- The first observed law is exactly the original law with its right message retained. -/
theorem affinePhaseOneRight_factored (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((affinePhaseOneRightTranscript n d t L₀ e₀ mask ys p.1, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys)
        (fun z => l z.1) (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys) :=
  Internal.affinePhaseOneRight_factored n d t L₀ e₀ w l r mask ys hr

/-- Both first observations preserve the actual joint law of the original latent states. -/
theorem affinePhaseOneLeft_factored (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((affinePhaseOneLeftTranscript n d t L₀ e₀ x mask ys p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
        (affinePhaseOneLeftKernel n t L₀ e₀ l x)
        (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) :=
  Internal.affinePhaseOneLeft_factored n d t L₀ e₀ w l r x mask ys hl hr

/-- The complete actual first-phase transcript has the displayed exact factorization. -/
theorem affinePhaseOneTranscript_factored (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice)
        (affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x)
        (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice) :=
  Internal.affinePhaseOneTranscript_factored n d t L₀ e₀ L₁ e₁ w l r x mask ys advice hl hr

/-- The first right message scales the original-left envelope by its message probability. -/
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
  Internal.affinePhaseOneRight_left_envelope n d t L₀ e₀ w l r x mask ys μ hr cap z x₀

/-- The original-right source pays for the first right message by copying its envelope. -/
theorem affinePhaseOneRight_right_envelope (n d t L₀ e₀ : Nat) {Z B Y : Type*}
    [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (y : Z → B → Y) (ξ : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffinePhaseOneRightTranscript Z t L₀) (y₀ : Y) :
    affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys z *
        mapWeight (y z.1) (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) y₀ ≤ ξ z.1 :=
  Internal.affinePhaseOneRight_right_envelope n d t L₀ e₀ w r mask ys y ξ hw hr cap z y₀

/-- The original-left source pays for the family of first extraction outputs. -/
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
      affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z :=
  Internal.affinePhaseOneLeft_left_envelope n d t L₀ e₀ w l r x mask ys μ hw hl hr cap z x₀

/-- Observing the first extraction outputs preserves the right-source envelope total. -/
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
  Internal.affinePhaseOneLeft_right_envelope n d t L₀ e₀ w l r x mask ys y ξ hw hl hr cap z y₀

/-- The complete transcript preserves the displayed original-left source bound. -/
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
      affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice z :=
  Internal.affinePhaseOneTranscript_left_envelope n d t L₀ e₀ L₁ e₁ w l r x mask ys advice μ hw hl
  hr cap z x₀

/-- The complete transcript preserves the displayed original-right source bound. -/
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
      affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ξ l x z :=
  Internal.affinePhaseOneTranscript_right_envelope n d t L₀ e₀ L₁ e₁ w l r x mask ys advice y ξ hw
  hl hr cap z y₀

/-- A normalized right kernel preserves the first original-left envelope total. -/
theorem affinePhaseOneRightLeftEnvelope_sum (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affinePhaseOneRightLeftEnvelope n d t L₀ e₀ μ r mask ys z) = ∑ z, μ z :=
  Internal.affinePhaseOneRightLeftEnvelope_sum n d t L₀ e₀ μ r mask ys hr

/-- The left-envelope total pays exactly the number of first output families. -/
theorem affinePhaseOneLeftEnvelope_sum (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z) =
      (Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) : ℝ) *
        ∑ z, μ z :=
  Internal.affinePhaseOneLeftEnvelope_sum n d t L₀ e₀ μ r mask ys hr

/-- The right-envelope total after two stages pays exactly the first right-message size. -/
theorem affinePhaseOneRightEnvelope_sum (n t L₀ e₀ : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (x : Z → A → Fin n → Bool) (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x z) =
      (Fintype.card (AffinePhaseOneRightMessage t L₀) : ℝ) * ∑ z, ξ z :=
  Internal.affinePhaseOneRightEnvelope_sum n t L₀ e₀ ξ l x hl

/-- The final left-envelope total pays only the first output-family alphabet. -/
theorem affinePhaseOneTranscriptLeftEnvelope_sum (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z B : Type*} [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (advice : Option (Fin t) → List Bool) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice z) =
      (Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) : ℝ) *
        ∑ z, μ z :=
  Internal.affinePhaseOneTranscriptLeftEnvelope_sum n d t L₀ e₀ L₁ e₁ μ r mask ys advice hr

/-- The final right-envelope total pays both right-message alphabets. -/
theorem affinePhaseOneTranscriptRightEnvelope_sum (n t L₀ e₀ L₁ : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (x : Z → A → Fin n → Bool) (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ξ l x z) =
      (Fintype.card (AffinePhaseOneCopies t (matchedBlockSeedBits L₁)) : ℝ) *
        Fintype.card (AffinePhaseOneRightMessage t L₀) * ∑ z, ξ z :=
  Internal.affinePhaseOneTranscriptRightEnvelope_sum n t L₀ e₀ L₁ ξ l x hl

/-- Nonnegative original-left envelopes remain nonnegative after the first two stages. -/
theorem affinePhaseOneLeftEnvelope_nonnegative (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z b, 0 ≤ r z b)
    (z : AffinePhaseOneLeftTranscript Z t L₀) :
    0 ≤ affinePhaseOneLeftEnvelope n d t L₀ e₀ μ r mask ys z :=
  Internal.affinePhaseOneLeftEnvelope_nonnegative n d t L₀ e₀ μ r mask ys nonnegative hr z

/-- Nonnegative original-right envelopes remain nonnegative after the first two stages. -/
theorem affinePhaseOneRightEnvelope_nonnegative (n t L₀ e₀ : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → Fin n → Bool)
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffinePhaseOneLeftTranscript Z t L₀) :
    0 ≤ affinePhaseOneRightEnvelope n t L₀ e₀ ξ l x z :=
  Internal.affinePhaseOneRightEnvelope_nonnegative n t L₀ e₀ ξ l x nonnegative hl z

/-- The final original-left envelope is nonnegative, including null transcript rows. -/
theorem affinePhaseOneTranscriptLeftEnvelope_nonnegative (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z B : Type*} [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (advice : Option (Fin t) → List Bool) (nonnegative : ∀ z, 0 ≤ μ z)
    (hr : ∀ z, IsProbabilityWeight (r z)) (z : AffinePhaseOneTranscript Z t L₀ L₁) :
    0 ≤ affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice z :=
  Internal.affinePhaseOneTranscriptLeftEnvelope_nonnegative n d t L₀ e₀ L₁ e₁ μ r mask ys advice
  nonnegative hr z

/-- The final original-right envelope is nonnegative, including null transcript rows. -/
theorem affinePhaseOneTranscriptRightEnvelope_nonnegative (n t L₀ e₀ L₁ : Nat)
    {Z A : Type*} [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (x : Z → A → Fin n → Bool) (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffinePhaseOneTranscript Z t L₀ L₁) :
    0 ≤ affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ξ l x z :=
  Internal.affinePhaseOneTranscriptRightEnvelope_nonnegative n t L₀ e₀ L₁ ξ l x nonnegative hl z

/-- There are exactly this many families of honest and tampered Boolean words. -/
theorem card_affinePhaseOneCopies (t width : Nat) :
    Fintype.card (AffinePhaseOneCopies t width) = (2 ^ width) ^ (t + 1) :=
  Internal.card_affinePhaseOneCopies t width

/-- The first right message contains all seed prefixes and all mask outputs. -/
theorem card_affinePhaseOneRightMessage (t L₀ : Nat) :
    Fintype.card (AffinePhaseOneRightMessage t L₀) =
      (2 ^ (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀)) ^ (t + 1) :=
  Internal.card_affinePhaseOneRightMessage t L₀

end Algebraic.Cutwidth.Extractor
