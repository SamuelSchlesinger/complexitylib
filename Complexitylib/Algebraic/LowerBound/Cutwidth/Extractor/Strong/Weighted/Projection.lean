/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Projection.Internal

/-!
# Source thresholds and output projections for strong extractors

Increasing the source cap threshold and discarding output coordinates
preserve the same retained-seed error. Boolean truncation keeps precisely
the first requested coordinates, including an empty prefix or the whole
output. No positive source threshold or nonempty seed alphabet is required.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A stronger source cap preserves the weighted strong-extractor guarantee. -/
theorem WeightedStrongSeededExtractor.mono_threshold {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    {E : α → Seed → Ω} {K L : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (threshold : K ≤ L) :
    WeightedStrongSeededExtractor E L ε :=
  Internal.weightedStrongSeededExtractor_mono_threshold extract threshold

/-- Dropping a nonempty finite output factor preserves strong extraction with the same error. -/
theorem WeightedStrongSeededExtractor.fst {α Seed Ω Tail : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Fintype Tail] [Nonempty Tail]
    {E : α → Seed → Ω × Tail} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededExtractor (fun a y => (E a y).1) K ε :=
  Internal.weightedStrongSeededExtractor_fst extract

/-- Keeping the first `b` of `M` output bits preserves the source threshold and strong error. -/
theorem WeightedStrongSeededExtractor.truncate {α Seed : Type*}
    [Fintype α] [Fintype Seed]
    {b M K : Nat} {ε : ℝ} {E : α → Seed → Fin M → Bool}
    (extract : WeightedStrongSeededExtractor E K ε) (size : b ≤ M) :
    WeightedStrongSeededExtractor
      (fun a y (j : Fin b) => E a y (Fin.castLE size j)) K ε :=
  Internal.weightedStrongSeededExtractor_truncate extract size

end Algebraic.Cutwidth.Extractor
