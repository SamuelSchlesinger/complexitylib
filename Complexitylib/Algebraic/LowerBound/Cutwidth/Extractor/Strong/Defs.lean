/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Defs

/-!
# Strong extraction from finite flat sources

A strong seeded extractor preserves the seed in every test and compares its
joint output with an independent uniform seed and uniform output. The source
is uniform on any nonempty finite support above the cardinality threshold.
The explicit nonemptiness requirement allows threshold zero without treating
the empty support as a probability distribution.

The probability definitions use real division, which is zero at a zero
denominator. Results using probability normalization state nonempty seed
and output assumptions explicitly. Every source and seed pair is counted,
including repeated output values.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Probability of a joint test under independent uniform seed and output.
The value is zero if either finite sampling type is empty. -/
noncomputable def uniformSeededTestProb {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (T : Finset (Seed × Ω)) : ℝ :=
  (T.card : ℝ) / ((Fintype.card Seed : ℝ) * Fintype.card Ω)

/-- Every nonempty flat support above `K` gives a joint seed-output distribution
within `ε` of the independent uniform distribution on every retained-seed test. -/
def FlatStrongSeededExtractor {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) (K : Nat) (ε : ℝ) : Prop :=
  ∀ P : Finset α, P.Nonempty → K ≤ P.card → ∀ T : Finset (Seed × Ω),
    |seededTestProb (fun x : P => E x.val) T - uniformSeededTestProb T| ≤ ε

end Algebraic.Cutwidth.Extractor
