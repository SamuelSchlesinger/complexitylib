/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Internal

/-!
# Conditional independence after deterministic observations

A deterministic observation of one side extends the transcript and
conditions that side's kernel. The opposite kernel stays unchanged, and
the resulting factored law is exactly the pushforward of the original
joint law. Every conditional kernel is normalized, including null
observation rows. A second observation may depend on the first message.

This is the finite weighted deterministic-observation rule in
Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Lemma 3.25,
printed p.15, repeatedly used in the proof of Theorem 6.1, pp.22--25:
<https://arxiv.org/abs/2110.12652>. No positive-probability conditioning or
additional independence hypothesis is hidden in a transcript update.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Normalized transcript and side kernels define a normalized factored joint law. -/
theorem factoredWeight_probability {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) : IsProbabilityWeight (factoredWeight w l r) :=
  Internal.factoredWeight_probability w l r hw hl hr

/-- A deterministic message extends the transcript to another probability law. -/
theorem observedTranscriptWeight_probability {Z A U : Type*}
    [Fintype Z] [Fintype A] [Fintype U]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U)
    (hw : IsProbabilityWeight w) (hp : ∀ z, IsProbabilityWeight (p z)) :
    IsProbabilityWeight (observedTranscriptWeight w p f) :=
  Internal.observedTranscriptWeight_probability w p f hw hp

/-- Every updated conditional row is normalized, even for an impossible message. -/
theorem observedTranscriptKernel_probability {Z A U : Type*} [Fintype A] [Fintype U]
    (p : Z → A → ℝ) (f : Z → A → U) (probability : ∀ z, IsProbabilityWeight (p z))
    (zu : Z × U) : IsProbabilityWeight (observedTranscriptKernel p f zu) :=
  Internal.observedTranscriptKernel_probability p f probability zu

/-- A null observation row uses exactly the existing uniform completion. -/
theorem observedTranscriptKernel_eq_uniform {Z A U : Type*} [Fintype A]
    (p : Z → A → ℝ) (f : Z → A → U) (zu : Z × U)
    (zero : mapWeight (f zu.1) (p zu.1) zu.2 = 0) :
    observedTranscriptKernel p f zu = uniformWeight A :=
  Internal.observedTranscriptKernel_eq_uniform p f zu zero

/-- The new joint source masses are the original masses restricted to the message event. -/
theorem observedTranscriptWeight_mul_kernel {Z A U : Type*} [Fintype A]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U)
    (nonnegative : ∀ z a, 0 ≤ p z a) (zu : Z × U) (a : A) :
    observedTranscriptWeight w p f zu * observedTranscriptKernel p f zu a =
      if f zu.1 a = zu.2 then w zu.1 * p zu.1 a else 0 :=
  Internal.observedTranscriptWeight_mul_kernel w p f nonnegative zu a

/-- Observing the left side preserves the right kernel and the complete actual joint law. -/
theorem factoredWeight_observe_left {Z A B U : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (f : Z → A → U)
    (nonnegative : ∀ z a, 0 ≤ l z a) :
    mapWeight (fun p : (Z × B) × A => (((p.1.1, f p.1.1 p.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (observedTranscriptWeight w l f) (observedTranscriptKernel l f)
        (fun zu => r zu.1) :=
  Internal.factoredWeight_observe_left w l r f nonnegative

/-- Observing the right side preserves the left kernel and the complete actual joint law. -/
theorem factoredWeight_observe_right {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (g : Z → B → V)
    (nonnegative : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A => (((p.1.1, g p.1.1 p.1.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (observedTranscriptWeight w r g) (fun zv => l zv.1)
        (observedTranscriptKernel r g) :=
  Internal.factoredWeight_observe_right w l r g nonnegative

/-- A left message followed by an adaptive right message has an exact factored representation. -/
theorem factoredWeight_observe_left_right {Z A B U V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (f : Z → A → U) (g : Z × U → B → V)
    (left_nonnegative : ∀ z a, 0 ≤ l z a) (right_nonnegative : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((((p.1.1, f p.1.1 p.2), g (p.1.1, f p.1.1 p.2) p.1.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (observedTranscriptWeight (observedTranscriptWeight w l f) (fun zu => r zu.1) g)
        (fun zuv => observedTranscriptKernel l f zuv.1)
        (observedTranscriptKernel (fun zu => r zu.1) g) :=
  Internal.factoredWeight_observe_left_right w l r f g left_nonnegative right_nonnegative

/-- Both conditional sides and the transcript remain normalized after two alternating messages. -/
theorem observedTranscript_left_right_probability {Z A B U V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (f : Z → A → U) (g : Z × U → B → V)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
        (observedTranscriptWeight (observedTranscriptWeight w l f) (fun zu => r zu.1) g) ∧
      (∀ zuv : (Z × U) × V, IsProbabilityWeight (observedTranscriptKernel l f zuv.1)) ∧
      (∀ zuv : (Z × U) × V,
        IsProbabilityWeight (observedTranscriptKernel (fun zu => r zu.1) g zuv)) :=
  Internal.observedTranscript_left_right_probability w l r f g hw hl hr

end Algebraic.Cutwidth.Extractor
