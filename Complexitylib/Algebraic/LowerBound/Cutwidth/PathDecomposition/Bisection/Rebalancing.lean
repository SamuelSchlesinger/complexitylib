/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Mathlib.Data.Nat.Log
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Rebalancing.Internal

/-!
# Rebalancing a cubic graph cut at logarithmic cost

Combining Fomin and Høie's prescribed-endpoint decomposition with the median
ordering gives the prescribed-size subsets below. This supplies a substitute
for the rebalancing step in Monien and Preis's cubic bisection argument. Its
cost is logarithmic in the side's size; accumulating logarithmically many
bounded helpful moves suffices to pay that cost.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

/-- A subset of any prescribed size can be selected while bounding its cut
by the larger of the original cut and one third of the side, plus a
logarithmic remainder. No density or connectivity assumption is needed. -/
theorem exists_subset_cut_le {W : Type} [Fintype W] (H : SimpleGraph W)
    (S : Finset W) (regular : H.IsRegularOfDegree 3) {k : Nat} (hk : k ≤ S.card) :
    ∃ T ⊆ S, T.card = k ∧
      (H.cutFinset T).card ≤ max (H.cutFinset S).card (S.card / 3 + 1) +
        Nat.clog 2 S.card + 2 :=
  Internal.exists_subset_cut_le H S regular hk

/-- A side with more than one crossing edge per three vertices admits
a move of every prescribed size whose cost is at most `ceil(log₂ |S|) + 2`.
The bound includes moves of size zero and the whole side. -/
theorem exists_rebalancing_set {W : Type} [Fintype W] (H : SimpleGraph W)
    (S : Finset W) (regular : H.IsRegularOfDegree 3)
    (dense : S.card < 3 * (H.cutFinset S).card) {k : Nat} (hk : k ≤ S.card) :
    ∃ X ⊆ S, X.card = k ∧
      -((Nat.clog 2 S.card : ℤ) + 2) ≤ helpfulness H S X :=
  Internal.exists_rebalancing_set H S regular dense hk

end Algebraic.Cutwidth.Bisection
