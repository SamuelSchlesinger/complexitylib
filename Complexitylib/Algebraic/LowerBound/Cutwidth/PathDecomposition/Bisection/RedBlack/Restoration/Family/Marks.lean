/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Marks.Internal

/-!
# Endpoint marks record boundary edges and degree loss

Each cut edge supplies one outside mark. For a restoration family, marks
at vertices outside all regions count exactly their incident deleted edges.
The original degree is the sum of the remaining degree and these marks.
On a set avoiding every region, marks count the region cuts crossing it;
these are the incidences that require compensation during restoration.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V) (P : Finset V)

/-- Every boundary edge gives exactly one outside mark. -/
theorem degree_boundaryMarks : (boundaryMarks B P).degree = (B.cutFinset P).card :=
  RestorationFamily.Internal.degree_boundaryMarks B P

/-- Marks at an outside vertex count its incident boundary edges; inside vertices get none. -/
theorem boundaryMarks_apply (v : V) :
    boundaryMarks B P v =
      if v ∈ P then 0 else (B.incidenceFinset v ∩ B.cutFinset P).card :=
  RestorationFamily.Internal.boundaryMarks_apply B P v

/-- On a set disjoint from a region, its marks count exactly the shared cut edges. -/
theorem sum_boundaryMarks {X : Finset V} (fresh : Disjoint X P) :
    (∑ v ∈ X, boundaryMarks B P v) = (B.cutFinset P ∩ B.cutFinset X).card :=
  RestorationFamily.Internal.sum_boundaryMarks B P fresh

namespace RestorationFamily

variable {E ι : Type} [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι)

/-- Total endpoint marks equal the sum of the region boundary sizes. -/
theorem degree_endpointMarks : F.endpointMarks.degree = ∑ i, (B.cutFinset (F.region i)).card :=
  Internal.degree_endpointMarks F

/-- Marks on an outside set count all region boundaries meeting its cut. -/
theorem sum_endpointMarks {X : Finset V} (fresh : ∀ i, Disjoint X (F.region i)) :
    (∑ v ∈ X, F.endpointMarks v) = ∑ i, (B.cutFinset (F.region i) ∩ B.cutFinset X).card :=
  Internal.sum_endpointMarks F fresh

/-- At an outside vertex, endpoint marks count precisely the incident deleted edges. -/
theorem endpointMarks_apply {v : V} (outside : ∀ i, v ∉ F.region i) :
    F.endpointMarks v = (B.incidenceFinset v ∩ F.deletedEdges).card :=
  Internal.endpointMarks_apply F outside

/-- Isolating the regions reduces each outside vertex's degree by exactly its mark count. -/
theorem degree_deletedGraph_add_endpointMarks {v : V} (outside : ∀ i, v ∉ F.region i) :
    F.deletedGraph.degree v + F.endpointMarks v = B.degree v :=
  Internal.degree_deletedGraph_add_endpointMarks F outside

end RestorationFamily

end Algebraic.Cutwidth.Bisection.RedBlack
