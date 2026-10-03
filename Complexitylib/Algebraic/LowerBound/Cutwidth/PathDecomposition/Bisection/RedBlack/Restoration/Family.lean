/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Internal

/-!
# Restoring a whole family with a uniform size bound

A positive witness avoiding the isolated regions transfers back to the
original graph by adding just those regions whose cuts touch the witness,
together with their closed attachments. Each selected region contributes
at most one new external black edge and a distinct new internal red edge.
The size bound depends on the original witness, not the number of regions.
Attached sets may overlap and may already be partly selected.
The mark-based bound charges only the endpoint marks on the witness,
at most one region-plus-attachment size per such mark.
If the original set is closed in the deleted graph and contains every
outside endpoint of some nonempty region boundary, restoration creates
positivity: that region supplies a red edge with no remaining black cost.

For black degree at most three and region-plus-attachment size at most `4 M`,
the bound is `(1 + 12 M) |X|`. Thus an `O(M)` witness remains `O(M²)` after
all paths are restored, as required in Monien and Preis's cycle-removal
argument. `PathSystem` constructs the thin family with `L = 3 M`, giving
the factor `1 + 9 M`. Tree reorganization remains a separate obligation.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype E] [Fintype ι]
  {B : SimpleGraph V} {R : Multigraph V E} (F : RestorationFamily B R ι)

omit [Fintype E] [Fintype ι] in
/-- For pairwise disjoint region cuts, isolating a subfamily empties exactly
its cuts and preserves the cuts of all other regions. -/
theorem cut_deletedGraph_restrict
    (cuts : Pairwise (fun i j => Disjoint (B.cutFinset (F.region i)) (B.cutFinset (F.region j))))
    (indices : Finset ι) (i : ι) :
    (F.restrict indices).deletedGraph.cutFinset (F.region i) =
      if i ∈ indices then ∅ else B.cutFinset (F.region i) :=
  Internal.cut_deletedGraph_restrict F cuts indices i

/-- A closed set of core vertices becomes positive after restoring the incident
regions if it absorbs the entire nonempty boundary of one region. -/
theorem exists_positive_of_closed_core (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (closed : F.deletedGraph.cutFinset X = ∅)
    {i : ι} (nonempty : (B.cutFinset (F.region i)).Nonempty)
    (absorbed : B.cutFinset (F.region i) ⊆ B.cutFinset X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (B.cutFinset X).card ∧ Positive B R Y :=
  Internal.exists_positive_of_closed_core F L small fresh closed nonempty absorbed

/-- In bounded degree, a closed core set absorbing one complete region boundary
gives a positive witness whose size is linear in the core size. -/
theorem exists_positive_of_closed_core_of_degree (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (closed : F.deletedGraph.cutFinset X = ∅) (degree : ∀ v ∈ X, B.degree v ≤ d)
    {i : ι} (nonempty : (B.cutFinset (F.region i)).Nonempty)
    (absorbed : B.cutFinset (F.region i) ⊆ B.cutFinset X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ (1 + d * L) * X.card ∧ Positive B R Y :=
  Internal.exists_positive_of_closed_core_of_degree F L d small fresh closed degree
    nonempty absorbed

/-- Restore all deleted cuts. At most one region and its attachment need be
added per black edge crossing the original witness. -/
theorem exists_positive_restore (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (B.cutFinset X).card ∧ Positive B R Y :=
  Internal.exists_positive_restore F L small fresh positive

/-- Restore the witness by paying at most `L` added vertices per endpoint mark
on the witness. Only marks on the original witness enter the size bound. -/
theorem exists_positive_restore_by_marks (L : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ X.card + L * (∑ v ∈ X, F.endpointMarks v) ∧ Positive B R Y :=
  Internal.exists_positive_restore_by_marks F L small fresh positive

/-- Bounded degree turns simultaneous restoration into a size bound that
is independent of the total number of deleted regions. -/
theorem exists_positive_restore_of_degree (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i))
    (degree : ∀ v ∈ X, B.degree v ≤ d) (positive : Positive F.deletedGraph R X) :
    ∃ Y, X ⊆ Y ∧ Y.card ≤ (1 + d * L) * X.card ∧ Positive B R Y :=
  Internal.exists_positive_restore_of_degree F L d small fresh degree positive

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily
