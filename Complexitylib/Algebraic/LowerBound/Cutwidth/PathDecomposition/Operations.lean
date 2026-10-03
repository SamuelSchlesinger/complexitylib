/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Internal

/-!
# Preserving endpoint bags in graph induction

These operations implement the deletion cases of Fomin and Høie's Lemma 4
in *Pathwidth of cubic graphs and exact algorithms* (2006). A subset can be
appended as a new last bag. A deleted vertex can be restored when all its
neighbors occur in the last bag. All bounds count bag vertices, so a bound
`b` on nonempty bags corresponds to width at most `b - 1`. Without a terminal
neighbor condition, inserting the vertex into every bag costs at most one.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

/-- The one-bag decomposition ends in the full vertex set. -/
theorem trivial_endsAt [Fintype W] : (trivial H).EndsAt Finset.univ := by
  refine ⟨⟨0, by simp [trivial]⟩, ?_, rfl⟩
  intro i
  have hi := i.isLt
  change i.val < 1 at hi
  change i.val ≤ 0
  lia

/-- Reversal turns a prescribed last bag into a prescribed first bag. -/
theorem EndsAt.reverse {D : PathDecomposition H} {X : Finset W}
    (hend : D.EndsAt X) : D.reverse.StartsAt X := by
  obtain ⟨last, hlast, hX⟩ := hend
  change ∃ first : Fin D.length, (∀ i, first ≤ i) ∧ D.bag first.rev = X
  refine ⟨last.rev, fun i => ?_, ?_⟩
  · simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr (hlast i.rev)
  · simpa only [Fin.rev_rev] using hX

/-- Reversal turns a prescribed first bag into a prescribed last bag. -/
theorem StartsAt.reverse {D : PathDecomposition H} {X : Finset W}
    (hstart : D.StartsAt X) : D.reverse.EndsAt X := by
  obtain ⟨first, hfirst, hX⟩ := hstart
  change ∃ last : Fin D.length, (∀ i, i ≤ last) ∧ D.bag last.rev = X
  refine ⟨first.rev, fun i => ?_, ?_⟩
  · simpa only [Fin.rev_rev] using Fin.rev_le_rev.mpr (hfirst i.rev)
  · simpa only [Fin.rev_rev] using hX

/-- A decomposition with a first bag also has a last bag. -/
theorem StartsAt.exists_endsAt {D : PathDecomposition H} {X : Finset W}
    (hstart : D.StartsAt X) : ∃ Y, D.EndsAt Y := by
  obtain ⟨first, _, _⟩ := hstart
  have hpos : 0 < D.length := lt_of_le_of_lt (Nat.zero_le _) first.isLt
  let last : Fin D.length := ⟨D.length - 1, by lia⟩
  refine ⟨D.bag last, last, ?_, rfl⟩
  intro i
  have hi := i.isLt
  change i.val ≤ D.length - 1
  lia

/-- Relabelling preserves the prescribed last bag. -/
theorem EndsAt.relabel {V : Type} {G : SimpleGraph V} {D : PathDecomposition G}
    {X : Finset V} (hend : D.EndsAt X) (e : G ≃g H) :
    (D.relabel e).EndsAt (X.map e.toEquiv.toEmbedding) := by
  obtain ⟨last, hlast, hX⟩ := hend
  exact ⟨last, hlast, congrArg (Finset.map e.toEquiv.toEmbedding) hX⟩

/-- Relabelling preserves the prescribed first bag. -/
theorem StartsAt.relabel {V : Type} {G : SimpleGraph V} {D : PathDecomposition G}
    {X : Finset V} (hstart : D.StartsAt X) (e : G ≃g H) :
    (D.relabel e).StartsAt (X.map e.toEquiv.toEmbedding) := by
  obtain ⟨first, hfirst, hX⟩ := hstart
  exact ⟨first, hfirst, congrArg (Finset.map e.toEquiv.toEmbedding) hX⟩

/-- A graph isomorphism preserves every bag's cardinality. -/
theorem card_relabel_bag {V : Type} {G : SimpleGraph V} (D : PathDecomposition G)
    (e : G ≃g H) (i : Fin D.length) : ((D.relabel e).bag i).card = (D.bag i).card :=
  Finset.card_map _

/-- Appending a subset of the terminal bag preserves the bag-size bound. -/
theorem EndsAt.exists_subset {D : PathDecomposition H} {X Y : Finset W}
    (hend : D.EndsAt Y) (hXY : X ⊆ Y) {b : Nat}
    (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt X ∧ ∀ i, (D'.bag i).card ≤ b :=
  Internal.exists_endsAt_subset D hend hXY bound

/-- Restore a deleted vertex in a new last bag. The last bag before
restoration must contain every neighbor; no other bag grows. -/
theorem exists_restoreVertex (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v}))
    {Y : Finset {w : W // w ≠ v}} (hend : D.EndsAt Y)
    (neighbors : ∀ w, H.Adj v w → w ∈ Y.map (.subtype (· ≠ v)))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) (hY : Y.card + 1 ≤ b) :
    ∃ D' : PathDecomposition H,
      D'.EndsAt (insert v (Y.map (.subtype (· ≠ v)))) ∧
        ∀ i, (D'.bag i).card ≤ b :=
  Internal.exists_restoreVertex v D hend neighbors bound hY

/-- Delete a boundary vertex, then restore it and shrink the endpoint bag.
For the zero-neighbor case use `Y = X`; for a unique outside neighbor `u`,
use `Y = insert u X`. Only the new bag `Y` must fit the size bound. -/
theorem exists_endsAt_of_delete (v : W) {X Y : Finset W} (hv : v ∈ Y)
    (D : PathDecomposition (H.induce {w | w ≠ v}))
    (hend : D.EndsAt (Y.subtype (· ≠ v)))
    (neighbors : ∀ w, H.Adj v w → w ∈ Y) (hXY : X ⊆ Y)
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) (hY : Y.card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt X ∧ ∀ i, (D'.bag i).card ≤ b :=
  Internal.exists_endsAt_of_delete v hv D hend neighbors hXY bound hY

/-- Insert a deleted vertex into every bag, then append its singleton.
This costs at most one vertex per bag and needs no condition on its neighbors. -/
theorem exists_addVertex (v : W) (D : PathDecomposition (H.induce {w | w ≠ v}))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt {v} ∧ ∀ i, (D'.bag i).card ≤ b + 1 :=
  Internal.exists_addVertex v D bound

end Algebraic.Cutwidth.PathDecomposition
