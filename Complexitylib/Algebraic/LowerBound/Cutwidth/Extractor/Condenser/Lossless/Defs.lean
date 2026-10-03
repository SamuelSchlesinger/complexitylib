/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic

/-!
# Finite seeded neighbors and test probabilities

The neighbor set retains the seed coordinate. Test probabilities count all
source and seed pairs, including pairs with the same output, before dividing
by the number of pairs. These definitions describe uniform finite sources;
they do not assert anything about arbitrary probability weights.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- All seed and output pairs reached from the finite source support. -/
noncomputable def seededNeighborSet {α Seed Ω : Type*} [Fintype Seed]
    (C : α → Seed → Ω) (P : Finset α) : Finset (Seed × Ω) :=
  P.biUnion fun x => Finset.univ.image fun y => (y, C x y)

/-- The probability that a uniform independent source and seed pass a test.
The value is zero when either sampling type is empty. -/
noncomputable def seededTestProb {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    (C : α → Seed → Ω) (T : Finset (Seed × Ω)) : ℝ :=
  (((Finset.univ : Finset (α × Seed)).filter
    fun xy => (xy.2, C xy.1 xy.2) ∈ T).card : ℝ) /
      ((Fintype.card α : ℝ) * Fintype.card Seed)

end Algebraic.Cutwidth.Extractor
