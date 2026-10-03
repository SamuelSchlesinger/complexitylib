/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators

/-!
# Tests of supplied finite mixtures of seeded sources

Each component samples its own finite source type uniformly and uses an
independent uniform seed. The mixture weights choose the component before
sampling either value. Normalization and nonnegativity are hypotheses of
the probability theorems, rather than requirements of the finite sum.
Empty sampling types use the zero convention of `seededTestProb`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Test probability for a supplied mixture when its weights are nonnegative
and sum to one. Component source types may differ; the seed type is shared. -/
noncomputable def seededMixtureTestProb {ι Seed Ω : Type*}
    [Fintype ι] [Fintype Seed] {Source : ι → Type*} [∀ i, Fintype (Source i)]
    (w : ι → ℝ) (C : ∀ i, Source i → Seed → Ω) (T : Finset (Seed × Ω)) : ℝ :=
  ∑ i, w i * seededTestProb (C i) T

end Algebraic.Cutwidth.Extractor
