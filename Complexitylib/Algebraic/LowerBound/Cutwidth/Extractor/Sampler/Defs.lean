/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

/-!
# Finite seeded extraction and sampling from weak sources

The sampler tests only small output sets, as in Chattopadhyay and Liao,
*Extractors for Sum of Two Sources* (2021), Definition 3.14. Its source may
have any probability weights with the stated point-mass bound. The seeded
extractor premise only needs uniform sources on finite supports, since the
proof applies it to the full set of bad inputs.

Seed and output types are assumed nonempty by the public conversion theorems.
All counts retain seed multiplicity, including repeated output values.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Number of seeds whose output belongs to the test set, at a fixed input. -/
noncomputable def seedHits {α Seed Ω : Type*} [Fintype Seed]
    (E : α → Seed → Ω) (T : Finset Ω) (x : α) : Nat :=
  (Finset.univ.filter fun y => E x y ∈ T).card

/-- Inputs for which more than a `2ε` fraction of seeds hit the test set. -/
noncomputable def badInputs {α Seed Ω : Type*} [Fintype α] [Fintype Seed]
    (E : α → Seed → Ω) (T : Finset Ω) (ε : ℝ) : Finset α :=
  Finset.univ.filter fun x => 2 * ε * Fintype.card Seed < (seedHits E T x : ℝ)

/-- Seeded extraction from every uniform support of size at least `K`.
The discrepancy for every output test is multiplied by the number of source
pairs and output values, so this definition uses no division. -/
def FlatSeededExtractor {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) (K : Nat) (ε : ℝ) : Prop :=
  ∀ P : Finset α, K ≤ P.card → ∀ T : Finset Ω,
    |(∑ x ∈ P, (seedHits E T x : ℝ)) * Fintype.card Ω -
      (P.card : ℝ) * Fintype.card Seed * T.card| ≤
        ε * P.card * Fintype.card Seed * Fintype.card Ω

/-- Small-set sampling for every probability source with point masses at
most `1 / L`, expressed as `L * p x ≤ 1`. For positive `L`, this is source
min-entropy at least `log₂ L`. The seed is uniform and independent of the source. -/
def Sampler {α Seed Ω : Type*} [Fintype α] [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) (L ε δ : ℝ) : Prop :=
  ∀ T : Finset Ω, (T.card : ℝ) ≤ ε * Fintype.card Ω →
    ∀ p : α → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x) = 1 →
      (∀ x, L * p x ≤ 1) → ∑ x ∈ badInputs E T ε, p x ≤ δ

end Algebraic.Cutwidth.Extractor
