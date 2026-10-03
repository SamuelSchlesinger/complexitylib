/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
public import Mathlib.Data.Finset.Union

/-!
# Finite neighbor coverage and somewhere sampling

A neighbor map replaces each outer seed by a list of base seeds. Coverage
bounds the union reached by every sufficiently large outer support. A somewhere
sampler fails at an outer seed only when every candidate belongs to the test set.

These are the finite contracts used by Chattopadhyay and Liao,
*Extractors for Sum of Two Sources* (2021), Definition 3.16 and Appendix A.
They do not assert an explicit construction or a polynomial-time evaluator.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- All base seeds reached from a finite set of outer seeds. -/
noncomputable def neighborSet {Outer Candidate Base : Type*} [Fintype Candidate]
    (Γ : Outer → Candidate → Base) (P : Finset Outer) : Finset Base :=
  P.biUnion fun y => Finset.univ.image (Γ y)

/-- Every outer support of size at least `K` reaches a `ρ` fraction of base seeds. -/
def NeighborCoverage {Outer Candidate Base : Type*} [Fintype Candidate] [Fintype Base]
    (Γ : Outer → Candidate → Base) (K : Nat) (ρ : ℝ) : Prop :=
  ∀ P : Finset Outer, K ≤ P.card →
    ρ * Fintype.card Base ≤ ((neighborSet Γ P).card : ℝ)

/-- Outer seeds whose every candidate output belongs to the test set. -/
noncomputable def allHitSeeds {α Outer Candidate Ω : Type*} [Fintype Outer]
    (S : α → Outer → Candidate → Ω) (T : Finset Ω) (x : α) : Finset Outer :=
  Finset.univ.filter fun y => ∀ z, S x y z ∈ T

/-- Inputs for which more than a `2ε` fraction of outer seeds have all candidates
in the test set. -/
noncomputable def somewhereBadInputs {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] (S : α → Outer → Candidate → Ω)
    (T : Finset Ω) (ε : ℝ) : Finset α :=
  Finset.univ.filter fun x => 2 * ε * Fintype.card Outer < ((allHitSeeds S T x).card : ℝ)

/-- Small-set sampling with a list of candidates at each outer seed, for every
probability source whose point masses are at most `1 / L`. The failure event
counts outer seeds whose entire candidate list hits the test set. -/
def SomewhereSampler {α Outer Candidate Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω]
    (S : α → Outer → Candidate → Ω) (L ε δ : ℝ) : Prop :=
  ∀ T : Finset Ω, (T.card : ℝ) ≤ ε * Fintype.card Ω →
    ∀ p : α → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x) = 1 →
      (∀ x, L * p x ≤ 1) → ∑ x ∈ somewhereBadInputs S T ε, p x ≤ δ

end Algebraic.Cutwidth.Extractor
