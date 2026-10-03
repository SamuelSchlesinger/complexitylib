/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Mathlib.Data.Nat.Log
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Reduction.Internal

/-!
# Reducing the sharp cubic bisection theorem to bounded helpful sets

The accumulation and rebalancing steps reduce sharp bisection to a local
helpful-set lemma: for every positive slack, a side with cut density above
`1/3` plus that slack contains a helpful set of uniformly bounded size.
`Bisection.Helpful` proves that local lemma and instantiates this reduction.

The finite theorem displays the size threshold needed by this reduction.
Its logarithmic remainder is absorbed in any positive asymptotic slack.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

/-- The finite local-improvement argument. Accumulate a gain of
`ceil(log₂ n) + 3`, then restore balance using the prescribed-size subset
bound. The maximum in that bound also handles overshoot of the helpful move. -/
theorem exists_bisection_of_helpful {W : Type} [Fintype W] (H : SimpleGraph W)
    (regular : H.IsRegularOfDegree 3) {ξ : ℝ} (hξ : 0 < ξ) (M : Nat)
    (budget : ((M : ℝ) + 3) * ((Nat.clog 2 (Fintype.card W) : ℝ) + 4) <
      ξ * Fintype.card W)
    (find : ∀ S : Finset W, (1 / 3 + ξ) * S.card < (H.cutFinset S).card →
      ∃ X ⊆ S, X.card ≤ M ∧ 1 ≤ helpfulness H S X) :
    ∃ S : Finset W, S.card ≤ Sᶜ.card + 1 ∧ Sᶜ.card ≤ S.card + 1 ∧
      ((H.cutFinset S).card : ℝ) ≤ (1 / 6 + ξ) * Fintype.card W :=
  Internal.exists_bisection_of_helpful H regular hξ M budget find

/-- A uniform bounded helpful-set lemma at positive slack implies the sharp
asymptotic bisection bound at that same slack. `Bisection.Helpful` supplies
the local lemma with an explicit size bound. -/
theorem exists_bisectionBound_of_helpful {ξ : ℝ} (hξ : 0 < ξ) (M : Nat)
    (find : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 →
      ∀ S : Finset W, (1 / 3 + ξ) * S.card < (H.cutFinset S).card →
        ∃ X ⊆ S, X.card ≤ M ∧ 1 ≤ helpfulness H S X) :
    ∃ N₀ : Nat, BisectionBound ξ N₀ :=
  Internal.exists_bisectionBound_of_helpful hξ M find

end Algebraic.Cutwidth.Bisection
