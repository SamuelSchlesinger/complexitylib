/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal

/-!
# Local improvements of a graph bisection

These are the cut identities, minimization argument, and first local cases
in Monien and Preis's *Upper Bounds on the Bisection Width of 3- and
4-regular Graphs*. A helpful move decreases the cut by exactly its signed
helpfulness. An equally sized reverse move restores balance; if the total
helpfulness is positive, the original cut was not minimal.

A subcubic vertex with two crossing edges is helpful. More generally, a
connected set of boundary vertices has helpfulness at least its size minus
two. `Bisection.LocalConfigurations` proves the remaining small configurations
used before normalization. `Bisection.Rebalancing` supplies the rebalancing step. The bounded
local helpful-set lemma needed for the sharp bisection theorem remains unproved.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical symmDiff

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- Flipping membership in `X` toggles exactly the edges in the cut of `X`. -/
theorem cutFinset_symmDiff (S X : Finset W) :
    H.cutFinset (S ∆ X) = H.cutFinset S ∆ H.cutFinset X :=
  Bisection.Internal.cutFinset_symmDiff H S X

/-- Helpfulness is exactly the signed decrease in the cut size. -/
theorem helpfulness_eq_sub (S X : Finset W) :
    helpfulness H S X = (H.cutFinset S).card - (H.cutFinset (S ∆ X)).card :=
  Bisection.Internal.helpfulness_eq_sub H S X

/-- Moving a subset out of one side decreases the cut by its helpfulness. -/
theorem helpfulness_eq_sub_sdiff {S X : Finset W} (hX : X ⊆ S) :
    helpfulness H S X = (H.cutFinset S).card - (H.cutFinset (S \ X)).card :=
  Bisection.Internal.helpfulness_eq_sub_sdiff H hX

/-- Moving a disjoint set into a side decreases the cut by its helpfulness. -/
theorem helpfulness_eq_sub_union {S X : Finset W} (hX : Disjoint S X) :
    helpfulness H S X = (H.cutFinset S).card - (H.cutFinset (S ∪ X)).card :=
  Bisection.Internal.helpfulness_eq_sub_union H hX

/-- Successive moves have additive helpfulness, measured at the current cut. -/
theorem helpfulness_add (S X Y : Finset W) :
    helpfulness H S (X ∆ Y) = helpfulness H S X + helpfulness H (S ∆ X) Y :=
  Bisection.Internal.helpfulness_add H S X Y

/-- Renaming the two sides does not affect the helpfulness of a flip. -/
theorem helpfulness_compl (S X : Finset W) :
    helpfulness H Sᶜ X = helpfulness H S X :=
  Bisection.Internal.helpfulness_compl H S X

/-- Among all cuts with a prescribed side cardinality, a minimum exists. -/
theorem Bisection.exists_min_cut_of_card {m : Nat} (hm : m ≤ Fintype.card W) :
    ∃ S : Finset W, S.card = m ∧
      ∀ T : Finset W, T.card = m → (H.cutFinset S).card ≤ (H.cutFinset T).card :=
  Internal.exists_min_cut_of_card H hm

/-- A minimum balanced cut exists, including when the graph has odd order. -/
theorem Bisection.exists_min_bisection :
    ∃ S : Finset W, S.card ≤ Sᶜ.card + 1 ∧ Sᶜ.card ≤ S.card + 1 ∧
      ∀ T : Finset W, T.card ≤ Tᶜ.card + 1 → Tᶜ.card ≤ T.card + 1 →
        (H.cutFinset S).card ≤ (H.cutFinset T).card :=
  Internal.exists_min_bisection H

/-- A minimum cut cannot admit an improving pair of moves that restores its
side cardinality. The reverse move may include vertices of the first move. -/
theorem Bisection.two_moves_le_zero {S : Finset W}
    (minimal : ∀ T : Finset W, T.card = S.card → (H.cutFinset S).card ≤ (H.cutFinset T).card)
    {X Y : Finset W} (hX : X ⊆ S) (hY : Y ⊆ (S \ X)ᶜ) (sameSize : Y.card = X.card) :
    helpfulness H S X + helpfulness H (S \ X)ᶜ Y ≤ 0 :=
  Internal.two_moves_le_zero H minimal hX hY sameSize

/-- Crossing edges incident to a moved subset are counted once by their
endpoint in that subset. -/
theorem card_cut_inter_eq_sum_neighbors {S X : Finset W} (hX : X ⊆ S) :
    (H.cutFinset X ∩ H.cutFinset S).card = ∑ v ∈ X, (H.neighborFinset v \ S).card :=
  Bisection.Internal.card_cut_inter_eq_sum_neighbors H hX

/-- The degree sum of a vertex set counts internal edges twice and crossing
edges once. -/
theorem degree_sum_cut (X : Finset W) :
    (H.cutFinset X).card + 2 * (H.induce {w | w ∈ X}).edgeFinset.card =
      ∑ v ∈ X, H.degree v :=
  Bisection.Internal.degree_sum_cut H X

/-- Flipping a set changes the cut by at most the number of edges leaving
that set, whether the move is helpful or costly. -/
theorem abs_helpfulness_le_card_cut (S X : Finset W) :
    |helpfulness H S X| ≤ (H.cutFinset X).card :=
  Bisection.Internal.abs_helpfulness_le_card_cut H S X

/-- A maximum degree bound controls the change in cut size by the number
of moved vertices. In particular, this bounds overshoot when accumulating moves. -/
theorem abs_helpfulness_le_mul_card (S X : Finset W) {d : Nat}
    (degree : ∀ v ∈ X, H.degree v ≤ d) :
    |helpfulness H S X| ≤ d * X.card :=
  Bisection.Internal.abs_helpfulness_le_mul_card H S X degree

/-- Helpfulness expressed by outside neighbors, internal edges, and degrees. -/
theorem helpfulness_eq_degree_sum {S X : Finset W} (hX : X ⊆ S) :
    helpfulness H S X = 2 * (∑ v ∈ X, ((H.neighborFinset v \ S).card : ℤ)) +
      2 * ((H.induce {w | w ∈ X}).edgeFinset.card : ℤ) - ∑ v ∈ X, (H.degree v : ℤ) :=
  Bisection.Internal.helpfulness_eq_degree_sum H hX

/-- A single vertex removes its outside edges and adds its inside edges. -/
theorem helpfulness_singleton {S : Finset W} {v : W} (hv : v ∈ S) :
    helpfulness H S {v} = 2 * ((H.neighborFinset v \ S).card : ℤ) - H.degree v :=
  Bisection.Internal.helpfulness_singleton H hv

/-- A subcubic vertex incident to at least two crossing edges is helpful. -/
theorem one_le_helpfulness_singleton {S : Finset W} {v : W} (hv : v ∈ S)
    (degree : H.degree v ≤ 3) (outside : 2 ≤ (H.neighborFinset v \ S).card) :
    1 ≤ helpfulness H S {v} :=
  Bisection.Internal.one_le_helpfulness_singleton H hv degree outside

/-- Connected boundary vertices have helpfulness at least their number
minus two in a graph of maximum degree three. -/
theorem card_sub_two_le_helpfulness {S X : Finset W} (hX : X ⊆ S)
    (connected : (H.induce {w | w ∈ X}).Connected)
    (degree : ∀ v ∈ X, H.degree v ≤ 3)
    (boundary : ∀ v ∈ X, ∃ w ∉ S, H.Adj v w) :
    (X.card : ℤ) - 2 ≤ helpfulness H S X :=
  Bisection.Internal.card_sub_two_le_helpfulness H hX connected degree boundary

/-- In particular, three or more connected boundary vertices form a
helpful set. This is a local case in Monien–Preis's bounded helpful-set lemma. -/
theorem one_le_helpfulness_of_connected_boundary {S X : Finset W}
    (hX : X ⊆ cutBoundary H S) (connected : (H.induce {w | w ∈ X}).Connected)
    (degree : ∀ v ∈ X, H.degree v ≤ 3) (size : 3 ≤ X.card) :
    1 ≤ helpfulness H S X := by
  have h := card_sub_two_le_helpfulness H (hX.trans (cutBoundary_subset H S))
    connected degree (fun v hv => ((mem_cutBoundary H).mp (hX hv)).2)
  lia

end Algebraic.Cutwidth
