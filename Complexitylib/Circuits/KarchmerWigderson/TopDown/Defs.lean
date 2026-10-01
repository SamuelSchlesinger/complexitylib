/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Rounds.Defs
public import Complexitylib.BooleanAnalysis.MirrorSets.Defs

/-!
# Density rectangles for the top-down adversary

The invariant from Sections 3--4 of Oliver Korten, *Top-Down Lower Bounds
for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.

The actual sampling rate may be smaller than the parameter bound. This is
needed because density-limit conditions need not be monotone in the rate.
-/

@[expose] public section

namespace Complexity.KarchmerWigderson

open BooleanAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonempty rectangle with both deficits at most `k`, and a positive
sampling rate at most `p` for which one side consists of density limits of
the other side. -/
def DensityRectangle (X Y : Finset (ι → Bool)) (p k : ℝ) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧ uniformDeficit X ≤ k ∧ uniformDeficit Y ≤ k ∧
    ∃ r : ℝ, 0 < r ∧ r ≤ p ∧
      ((∀ x ∈ X, IsDensityLimit Y r k x) ∨ (∀ y ∈ Y, IsDensityLimit X r k y))


end Complexity.KarchmerWigderson
