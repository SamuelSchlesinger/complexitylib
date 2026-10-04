/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Reindex.Internal

/-!
# Explicit sampler-index equivalences preserve sampling

Changing the enumeration of outer seeds and candidate positions preserves
the source threshold, test density, and failure probability. The actual
reduction uses this transport with fixed-width binary encodings.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Bijections of both index types preserve the full somewhere-sampler guarantee. -/
theorem SomewhereSampler.reindex {α Outer Outer' Candidate Candidate' Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Outer'] [Fintype Ω]
    {S : α → Outer → Candidate → Ω} {L ε δ : ℝ}
    (sample : SomewhereSampler S L ε δ) (outer : Outer' ≃ Outer)
    (candidate : Candidate' ≃ Candidate) :
    SomewhereSampler (fun x y z => S x (outer y) (candidate z)) L ε δ :=
  Internal.somewhereSampler_reindex sample outer candidate

end Algebraic.Cutwidth.Extractor
