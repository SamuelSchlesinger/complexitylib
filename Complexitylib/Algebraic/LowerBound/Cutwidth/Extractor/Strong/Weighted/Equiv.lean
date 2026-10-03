/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Equiv.Internal

/-!
# Strong extraction under seed and output equivalences

A bijective seed representation preserves uniform sampling, and a bijective
output representation preserves the uniform output law. Reindexing retained
seed-output tests therefore transfers the weighted strong-extractor guarantee
with exactly the same source cap and error. Empty finite types are included.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Equivalent seed and output alphabets preserve weighted strong extraction without error loss. -/
theorem WeightedStrongSeededExtractor.equiv {α Seed Seed' Ω Ω' : Type*}
    [Fintype α] [Fintype Seed] [Fintype Seed'] [Fintype Ω] [Fintype Ω']
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    (seed : Seed' ≃ Seed) (output : Ω ≃ Ω') :
    WeightedStrongSeededExtractor (fun a y => output (E a (seed y))) K ε :=
  Internal.weightedStrongSeededExtractor_equiv extract seed output

end Algebraic.Cutwidth.Extractor
