/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs

/-!
# Actual extraction laws for a smooth left source

The transcript retains an original left observation and then an actual
finite prefix message. The right seed and its observation may depend on
both messages. Every law is a deterministic image of the original
factored sample. In particular, the prefix and the extra leak are read
from the original left variable, even when a proof repairs its honest
source coordinate.

These laws support the smooth-source step of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources* (2021), Theorem 6.1:
<https://arxiv.org/abs/2110.12652>. Definitions alone impose no source
uniformity or extraction guarantee.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The original tag, selected left observation, and actual prefix message. -/
abbrev SmoothMergingTranscript (Z U Q : Type*) := (Z × U) × Q

/-- Both original left observations extend the original tag in their execution order. -/
def smoothMergingTranscript {Z A U Q : Type*}
    (u : Z → A → U) (q : Z → A → Q) (z : Z) (a : A) :
    SmoothMergingTranscript Z U Q :=
  ((z, u z a), q z a)

/-- The actual right-derived seed retains both original left messages and its right observation. -/
noncomputable def smoothMergingSeedWeight {Z A B U Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed) :
    (SmoothMergingTranscript Z U Q × V) × Seed → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let h := smoothMergingTranscript u q p.1.1 p.2
    ((h, v h p.1.2), y h p.1.2)) (factoredWeight w l r)

/-- Actual extraction retaining both left messages, the entire right variable, and its left leak. -/
noncomputable def smoothTwoSidedExtractionWeight {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W) (E : X → Seed → Out) :
    ((SmoothMergingTranscript Z U Q × B) × W) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let h := smoothMergingTranscript u q p.1.1 p.2
    (((h, p.1.2), leak h (v h p.1.2) p.2), E (x p.1.1 p.2) (y h p.1.2)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
