/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Glue.Internal

/-!
# Concatenation along prescribed endpoints

Induced graphs covering every vertex and edge can share vertices. If every
shared vertex lies in both bags at the join, concatenate their decompositions
without increasing the common bag-size bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

/-- Concatenate induced decompositions whose adjoining bags contain every
shared vertex. The last bag is inherited from the right decomposition. -/
theorem exists_glue {W : Type} {H : SimpleGraph W} {A B : Set W}
    (D : PathDecomposition (H.induce A)) (E : PathDecomposition (H.induce B))
    (cover : ∀ w, w ∈ A ∨ w ∈ B)
    (edges : ∀ u v, H.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    {X : Finset A} (hend : D.EndsAt X) {Y Z : Finset B}
    (hstart : E.StartsAt Y) (hend' : E.EndsAt Z)
    (overlap : ∀ w (ha : w ∈ A) (hb : w ∈ B),
      (⟨w, ha⟩ : A) ∈ X ∧ (⟨w, hb⟩ : B) ∈ Y)
    {b : Nat} (leftBound : ∀ i, (D.bag i).card ≤ b)
    (rightBound : ∀ i, (E.bag i).card ≤ b) :
    ∃ F : PathDecomposition H,
      F.EndsAt (Z.map (.subtype (· ∈ B))) ∧ ∀ i, (F.bag i).card ≤ b :=
  Internal.exists_glue D E cover edges hend hstart hend' overlap leftBound rightBound

/-- Concatenate two induced copies covering all vertices and edges. Shared
vertices must belong to the adjoining bags, expressed through their embeddings. -/
theorem exists_glue_embeddings {U V W : Type} {G : SimpleGraph U} {J : SimpleGraph V}
    {H : SimpleGraph W} (D : PathDecomposition G) (E : PathDecomposition J)
    (f : G ↪g H) (g : J ↪g H)
    (cover : ∀ w, w ∈ Set.range f ∨ w ∈ Set.range g)
    (edges : ∀ u v, H.Adj u v →
      (u ∈ Set.range f ∧ v ∈ Set.range f) ∨ (u ∈ Set.range g ∧ v ∈ Set.range g))
    {X : Finset U} (hend : D.EndsAt X) {Y Z : Finset V}
    (hstart : E.StartsAt Y) (hend' : E.EndsAt Z)
    (overlap : ∀ u v, f u = g v → u ∈ X ∧ v ∈ Y)
    {b : Nat} (leftBound : ∀ i, (D.bag i).card ≤ b)
    (rightBound : ∀ i, (E.bag i).card ≤ b) :
    ∃ F : PathDecomposition H,
      F.EndsAt (Z.map g.toEmbedding) ∧ ∀ i, (F.bag i).card ≤ b :=
  Internal.exists_glue_embeddings D E f g cover edges hend hstart hend' overlap
    leftBound rightBound

/-- Attach an induced subgraph along a boundary `X`. The remaining graph
ends at the part of `X` outside the copy, and all edges leaving the copy meet
`X`. Padding the copy's bags by `X` gives the final endpoint `X`. -/
theorem exists_attach {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (X : Finset W)
    (D : PathDecomposition (H.induce {w | w ∉ Set.range f}))
    (E : PathDecomposition G) (hend : D.EndsAt (X.subtype (· ∉ Set.range f)))
    (neighbors : ∀ u v, H.Adj (f u) v → v ∈ Set.range f ∨ v ∈ X)
    {b c : Nat} (leftBound : ∀ i, (D.bag i).card ≤ b)
    (rightBound : ∀ i, (E.bag i).card ≤ c) :
    ∃ F : PathDecomposition H, F.EndsAt X ∧
      ∀ i, (F.bag i).card ≤ max b (X.card + c) :=
  Internal.exists_attach f X D E hend neighbors leftBound rightBound

end Algebraic.Cutwidth.PathDecomposition
