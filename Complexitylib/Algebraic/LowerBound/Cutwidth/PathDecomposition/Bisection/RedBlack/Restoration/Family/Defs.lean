/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# A family of regions with compensating red attachments

The cycle-removal step of Monien and Preis's argument isolates thin paths.
For restoration, the relevant data are disjoint regions with at most two
black boundary edges, each joined by a red edge to an attached set with
empty black cut. Attached sets can overlap one another, but are disjoint
from all regions. No path ordering or cycle choice is needed for the
simultaneous restoration theorem.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

/-- Disjoint regions that can pay for restoration of their black cuts by
adding their closed red attachments. This records the data of removed
paths; it does not assert that a cycle-removal procedure has produced them. -/
structure RestorationFamily {V E : Type} [Fintype V] (B : SimpleGraph V)
    (R : Multigraph V E) (ι : Type) where
  /-- The regions whose black cuts are temporarily deleted. -/
  region : ι → Finset V
  /-- Closed sets added together with their regions during restoration. -/
  attachment : ι → Finset V
  disjoint : Pairwise (fun i j => Disjoint (region i) (region j))
  separate : ∀ i j, Disjoint (region i) (attachment j)
  closed : ∀ i, B.cutFinset (attachment i) = ∅
  boundary : ∀ i, (B.cutFinset (region i)).card ≤ 2
  /-- A red edge paying for the restored region's remaining black boundary. -/
  redEdge : ι → E
  incident : ∀ i,
    (R.fst (redEdge i) ∈ region i ∧ R.snd (redEdge i) ∈ attachment i) ∨
      (R.snd (redEdge i) ∈ region i ∧ R.fst (redEdge i) ∈ attachment i)

namespace RestorationFamily

variable {V E ι : Type} [Fintype V] [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}

/-- Retain any chosen subfamily of the regions and their attachments. -/
def restrict (F : RestorationFamily B R ι) (indices : Finset ι) :
    RestorationFamily B R indices where
  region i := F.region i.val
  attachment i := F.attachment i.val
  disjoint := fun _ _ distinct => F.disjoint (fun eq => distinct (Subtype.ext eq))
  separate i j := F.separate i.val j.val
  closed i := F.closed i.val
  boundary i := F.boundary i.val
  redEdge i := F.redEdge i.val
  incident i := F.incident i.val

/-- All black edges removed to isolate the family's regions. -/
noncomputable def deletedEdges (F : RestorationFamily B R ι) : Finset (Sym2 V) :=
  Finset.univ.biUnion (fun i => B.cutFinset (F.region i))

/-- The black graph after every region has been isolated. -/
noncomputable def deletedGraph (F : RestorationFamily B R ι) : SimpleGraph V :=
  B.deleteEdges (F.deletedEdges : Set (Sym2 V))

omit [Fintype ι] in
/-- Restricting the family deletes exactly the cuts of the selected regions. -/
theorem deletedEdges_restrict (F : RestorationFamily B R ι) (indices : Finset ι) :
    (F.restrict indices).deletedEdges = indices.biUnion (fun i => B.cutFinset (F.region i)) := by
  ext e
  simp only [deletedEdges, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, he⟩
    exact ⟨i, hi, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨⟨i, hi⟩, he⟩

end RestorationFamily

end Algebraic.Cutwidth.Bisection.RedBlack
