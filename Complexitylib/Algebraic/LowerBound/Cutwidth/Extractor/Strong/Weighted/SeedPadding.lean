/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedPadding.Internal

/-!
# Padding strong-extractor seeds to a fixed upper budget

Independent unused random bits do not change the strong-extraction error.
The statistical test retains every seed bit, including the unused suffix.
Thus an extractor with an exact seed length bounded by a simpler computed
budget can use that larger seed width without changing its guarantee.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Retaining an additional independent unused seed preserves strong extraction. -/
theorem WeightedStrongSeededExtractor.ignoreSeed {α Seed Ω Tail : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Fintype Tail]
    [Nonempty Seed] [Nonempty Ω] [Nonempty Tail]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededExtractor (fun a (seeds : Seed × Tail) => E a seeds.1) K ε :=
  Internal.weightedStrongSeededExtractor_ignoreSeed extract

/-- A Boolean seed can be padded to any larger width while retaining the entire padded seed. -/
theorem WeightedStrongSeededExtractor.padSeed {α Ω : Type*}
    [Fintype α] [Fintype Ω] [Nonempty Ω]
    {d r K : Nat} {ε : ℝ} {E : α → (Fin d → Bool) → Ω}
    (extract : WeightedStrongSeededExtractor E K ε) (size : d ≤ r) :
    WeightedStrongSeededExtractor
      (fun a (seed : Fin r → Bool) => E a (fun j => seed (Fin.castLE size j))) K ε :=
  Internal.weightedStrongSeededExtractor_padSeed extract size

end Algebraic.Cutwidth.Extractor
