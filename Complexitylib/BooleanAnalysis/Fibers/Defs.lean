/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Uniform entropy deficits and coordinate fibers

Definitions for Lemma 4 and the mirror-set argument in Oliver Korten,
*Top-Down Lower Bounds for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.

A fiber is a set of patterns on the free coordinates, so its deficit is
measured in that smaller cube. Logarithms in deficits are base two.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

/-- Uniform probability mass on a nonempty finite set; zero off the set.
The empty set gives the zero mass function. -/
noncomputable def uniformMass {α : Type*} [DecidableEq α] (X : Finset α) (x : α) : ℝ :=
  if x ∈ X then 1 / X.card else 0

/-- Min-entropy deficit of the uniform distribution on a nonempty Boolean
cube subset. The real formula takes value `card ι` at the empty set because
`Real.logb 2 0 = 0`; entropy interpretations require nonemptiness. -/
noncomputable def uniformDeficit {ι : Type*} [Fintype ι]
    (X : Finset (ι → Bool)) : ℝ :=
  Fintype.card ι - Real.logb 2 X.card

/-- Insert a pattern on selected coordinates, retaining `x` elsewhere. -/
def completePattern {ι : Type*} (s x : ι → Bool)
    (z : {i // s i = true} → Bool) : ι → Bool :=
  fun i => if h : s i = true then z ⟨i, h⟩ else x i

/-- The fiber of `X` over the bits of `x` outside `s`, represented on the
selected-coordinate cube. This is Korten's `X_{x,S}` inside its own subcube. -/
noncomputable def coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) : Finset ({i // s i = true} → Bool) :=
  univ.filter (fun z => completePattern s x z ∈ X)

end Complexity.BooleanAnalysis
