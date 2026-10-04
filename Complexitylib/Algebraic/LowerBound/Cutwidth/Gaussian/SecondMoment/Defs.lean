/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs

/-!
# Local events

An event in a real coordinate space depends on a finite set `S` of coordinates when
any two points that agree on `S` are either both in it or both outside it.
`Gaussian.SecondMoment` bounds the deviation of a count of such events.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- A set of points depends only on the coordinates in `S`. -/
def DependsOn {ι : Type} (S : Finset ι) (A : Set (ι → ℝ)) : Prop :=
  ∀ ω ω' : ι → ℝ, (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)

end Algebraic.Cutwidth.Gaussian
