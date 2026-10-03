/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs

/-!
# Strong condensation of finite weighted sources

The actual joint output retains an independent uniform seed. An ideal
witness supplies a normalized output distribution for each seed, with a
point-mass cap at every seed. Strong condensation bounds the total variation
between these joint distributions while preserving the uniform seed.

The operations are defined for arbitrary real weights. Empty seed types
use the zero-division convention; probability-preservation theorems require
a nonempty seed type explicitly.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Joint output weights of a weighted source and an independent uniform seed. -/
noncomputable def weightedSeededOutput {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    (p : α → ℝ) (C : α → Seed → Ω) (yz : Seed × Ω) : ℝ :=
  mapWeight (fun x => C x yz.1) p yz.2 / (Fintype.card Seed : ℝ)

/-- Joint weights of a uniform seed and its supplied conditional output weights. -/
noncomputable def seedFamilyWeight {Seed Ω : Type*} [Fintype Seed]
    (q : Seed → Ω → ℝ) (yz : Seed × Ω) : ℝ :=
  q yz.1 yz.2 / (Fintype.card Seed : ℝ)

/-- Every capped probability source has a close retained-seed output witness,
normalized and capped at the requested output threshold for every seed. -/
def WeightedStrongSeededCondenser {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    (C : α → Seed → Ω) (Kin Kout : Nat) (ε : ℝ) : Prop :=
  ∀ p : α → ℝ, IsProbabilityWeight p → CappedWeight p Kin →
    ∃ q : Seed → Ω → ℝ,
      (∀ y, IsProbabilityWeight (q y)) ∧ (∀ y, CappedWeight (q y) Kout) ∧
      weightDist (weightedSeededOutput p C) (seedFamilyWeight q) ≤ ε

end Algebraic.Cutwidth.Extractor
