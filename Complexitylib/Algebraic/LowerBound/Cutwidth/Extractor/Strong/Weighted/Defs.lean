/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite weighted sources and strong extraction

Real weights describe finite distributions without requiring their atoms
to have equal probability. Normalization and the point-mass cap are separate
predicates. The cap `K * p x ≤ 1` expresses min-entropy at least `log₂ K`
without logarithms or division in conditional-source arguments.

Distance is half the sum of absolute coordinate differences. The weighted
seeded test samples the source according to its weights and an independent
uniform seed, retaining both the seed and output in the test. All finite-sum
operations remain defined on arbitrary real weights; probability theorems
state normalization and nonnegativity explicitly.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- Nonnegative finite weights whose total mass is one. -/
def IsProbabilityWeight {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Every point has probability at most the reciprocal of the support threshold. -/
def CappedWeight {α : Type*} (p : α → ℝ) (K : Nat) : Prop :=
  ∀ x, (K : ℝ) * p x ≤ 1

/-- Total variation distance for finite probability weights. -/
noncomputable def weightDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- The probability mass assigned to a finite test. -/
noncomputable def weightTestProb {α : Type*} (p : α → ℝ) (T : Finset α) : ℝ :=
  ∑ x ∈ T, p x

/-- Push weights through a deterministic map, counting every source occurrence. -/
noncomputable def mapWeight {α β : Type*} [Fintype α]
    (f : α → β) (p : α → ℝ) (y : β) : ℝ :=
  ∑ x, if f x = y then p x else 0

/-- Marginal weights on the first component of a finite product. -/
noncomputable def firstWeight {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (a : α) : ℝ :=
  ∑ b, p (a, b)

/-- Uniform weights, with the zero convention on an empty sampling type. -/
noncomputable def uniformWeight (α : Type*) [Fintype α] (_ : α) : ℝ :=
  (Fintype.card α : ℝ)⁻¹

/-- Uniform weights on a finite support, and zero weights for the empty support. -/
noncomputable def flatWeight {α : Type*} (P : Finset α) (x : α) : ℝ :=
  if x ∈ P then (P.card : ℝ)⁻¹ else 0

/-- Test probability for a weighted source and an independent uniform seed. -/
noncomputable def weightedSeededTestProb {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (p : α → ℝ) (E : α → Seed → Ω)
    (T : Finset (Seed × Ω)) : ℝ :=
  (∑ x, p x * ((Finset.univ.filter fun y => (y, E x y) ∈ T).card : ℝ)) /
    (Fintype.card Seed : ℝ)

/-- Strong extraction from every normalized source satisfying the point-mass cap. -/
def WeightedStrongSeededExtractor {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    (E : α → Seed → Ω) (K : Nat) (ε : ℝ) : Prop :=
  ∀ p : α → ℝ, IsProbabilityWeight p → CappedWeight p K → ∀ T : Finset (Seed × Ω),
    |weightedSeededTestProb p E T - uniformSeededTestProb T| ≤ ε

end Algebraic.Cutwidth.Extractor
