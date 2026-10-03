/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope.Internal

/-!
# Joint source envelopes under deterministic transcript messages

A left message restricts each original source event, so copying the old
envelope to every message bounds the updated joint masses. Its total grows
by the message alphabet's size. A right message scales each envelope by
the message probability, preserving the total for a normalized right kernel.
The same laws compose when the right message depends on the left message.

These are finite mass bounds underlying the conditional-entropy accounting
in Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), proof of
Theorem 6.1, printed pp.22--25, using the deterministic observation rule of
Lemma 3.25: <https://arxiv.org/abs/2110.12652>. The bounds apply to the actual
updated kernels, including null observation rows; they impose no individual
conditional entropy requirement.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Updating a nonnegative transcript envelope by nonnegative message weights preserves its sign. -/
theorem observedTranscriptWeight_nonnegative {Z A U : Type*} [Fintype A]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U)
    (hw : ∀ z, 0 ≤ w z) (hp : ∀ z a, 0 ≤ p z a) (zu : Z × U) :
    0 ≤ observedTranscriptWeight w p f zu :=
  Internal.observedTranscriptWeight_nonnegative w p f hw hp zu

/-- Observed source masses are exactly the original joint message-and-source masses. -/
theorem observedTranscript_left_source_eq {Z A X U : Type*} [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → X) (f : Z → A → U)
    (hl : ∀ z a, 0 ≤ l z a) (zu : Z × U) (x₀ : X) :
    observedTranscriptWeight w l f zu *
        mapWeight (x zu.1) (observedTranscriptKernel l f zu) x₀ =
      w zu.1 * mapWeight (fun a => (f zu.1 a, x zu.1 a)) (l zu.1) (zu.2, x₀) :=
  Internal.observedTranscript_left_source_eq w l x f hl zu x₀

/-- Copying the old envelope to each left message bounds the updated joint source law. -/
theorem observedTranscript_left_envelope {Z A X U : Type*} [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ) (x : Z → A → X) (f : Z → A → U)
    (μ : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (zu : Z × U) (x₀ : X) :
    observedTranscriptWeight w l f zu *
      mapWeight (x zu.1) (observedTranscriptKernel l f zu) x₀ ≤ μ zu.1 :=
  Internal.observedTranscript_left_envelope w l x f μ hw hl cap zu x₀

/-- Copying an envelope over a finite message alphabet multiplies its total by that size. -/
theorem observedTranscript_left_envelope_sum {Z U : Type*} [Fintype Z] [Fintype U]
    (μ : Z → ℝ) :
    (∑ zu : Z × U, μ zu.1) = (Fintype.card U : ℝ) * ∑ z, μ z :=
  Internal.observedTranscript_left_envelope_sum μ

/-- A right message scales the source envelope by its own probability, leaving the source intact. -/
theorem observedTranscript_right_envelope {Z A B X V : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (g : Z → B → V) (μ : Z → ℝ)
    (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (zv : Z × V) (x₀ : X) :
    observedTranscriptWeight w r g zv * mapWeight (x zv.1) (l zv.1) x₀ ≤
      observedTranscriptWeight μ r g zv :=
  Internal.observedTranscript_right_envelope w l r x g μ hr cap zv x₀

/-- A right kernel of total mass one preserves the total source envelope exactly. -/
theorem observedTranscript_right_envelope_sum {Z B V : Type*}
    [Fintype Z] [Fintype B] [Fintype V]
    (μ : Z → ℝ) (r : Z → B → ℝ) (g : Z → B → V)
    (mass : ∀ z, ∑ b, r z b = 1) :
    (∑ zv, observedTranscriptWeight μ r g zv) = ∑ z, μ z :=
  Internal.observedTranscript_right_envelope_sum μ r g mass

/-- A left message followed by an adaptive right message has the composed joint envelope. -/
theorem observedTranscript_left_right_envelope {Z A B X U V : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (f : Z → A → U) (g : Z × U → B → V) (μ : Z → ℝ)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (zuv : (Z × U) × V) (x₀ : X) :
    observedTranscriptWeight (observedTranscriptWeight w l f) (fun zu => r zu.1) g zuv *
        mapWeight (x zuv.1.1) (observedTranscriptKernel l f zuv.1) x₀ ≤
      observedTranscriptWeight (fun zu : Z × U => μ zu.1) (fun zu => r zu.1) g zuv :=
  Internal.observedTranscript_left_right_envelope w l r x f g μ hw hl hr cap zuv x₀

/-- The adaptive two-message envelope pays only for the left message alphabet. -/
theorem observedTranscript_left_right_envelope_sum {Z B U V : Type*}
    [Fintype Z] [Fintype B] [Fintype U] [Fintype V]
    (μ : Z → ℝ) (r : Z → B → ℝ) (g : Z × U → B → V)
    (mass : ∀ z, ∑ b, r z b = 1) :
    (∑ zuv, observedTranscriptWeight (fun zu : Z × U => μ zu.1)
      (fun zu => r zu.1) g zuv) = (Fintype.card U : ℝ) * ∑ z, μ z :=
  Internal.observedTranscript_left_right_envelope_sum μ r g mass

end Algebraic.Cutwidth.Extractor
