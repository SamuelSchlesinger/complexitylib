/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!+# Updating finite transcripts by deterministic observations

An observation extends a transcript by a deterministic function of one
side's variable. Its new transcript mass counts all preimages, and its
conditional kernel keeps the original variable. Null observation rows use
the existing uniform completion of `conditionalWeight`. The other side's
kernel will remain unchanged in the factorization theorems.

These definitions give the finite weighted form of the deterministic
observation rule in Chattopadhyay--Liao, *Extractors for Sum of Two Sources*
(2021), Lemma 3.25, printed p.15, used in the proof of Theorem 6.1:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Extend a transcript by an observation of its conditional source. -/
noncomputable def observedTranscriptWeight {Z A U : Type*} [Fintype A]
    (w : Z → ℝ) (p : Z → A → ℝ) (f : Z → A → U) (zu : Z × U) : ℝ :=
  w zu.1 * mapWeight (f zu.1) (p zu.1) zu.2

/-- Condition the observed side on its message, with normalized null-row completion. -/
noncomputable def observedTranscriptKernel {Z A U : Type*} [Fintype A]
    (p : Z → A → ℝ) (f : Z → A → U) (zu : Z × U) : A → ℝ :=
  conditionalWeight (mapWeight (fun a => (f zu.1 a, a)) (p zu.1)) zu.2

end Algebraic.Cutwidth.Extractor
