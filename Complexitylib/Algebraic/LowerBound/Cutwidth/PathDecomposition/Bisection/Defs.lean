/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# The cubic bisection bound

This records the conclusion of Monien and Preis's bisection theorem.
`Bisection.Helpful` proves the sharp theorem for every positive slack.
-/

@[expose] public section

namespace Algebraic.Cutwidth

/-- The cubic bisection bound with slack `ξ` and threshold `N₀`:
each simple 3-regular graph on `n > N₀` vertices has a cut into sides
differing in size by at most one, with at most `(1/6 + ξ) n` crossing edges. -/
def BisectionBound (ξ : ℝ) (N₀ : Nat) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
    ∃ S : Finset W, S.card ≤ Sᶜ.card + 1 ∧ Sᶜ.card ≤ S.card + 1 ∧
      ((H.cutFinset S).card : ℝ) ≤ (1 / 6 + ξ) * Fintype.card W

end Algebraic.Cutwidth
