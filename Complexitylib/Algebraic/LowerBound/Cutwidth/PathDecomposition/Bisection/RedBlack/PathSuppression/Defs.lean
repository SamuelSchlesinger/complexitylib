/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Suppressing an independent family of path vertices

Remove designated vertices and join each pair of their surviving
neighbors, retaining original edges between surviving vertices. When
the removed vertices are independent and have degree at most two, this
contracts the intervening paths and deletes isolated vertices or leaves.
It is the final contraction from the region-boundary forest to the core
pieces in Monien and Preis's weighted-tree argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression

/-- Remove `S` and replace two-edge paths through `S` by edges between their endpoints. -/
def graph {V : Type} (B : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} where
  Adj u v := u ≠ v ∧ (B.Adj u.val v.val ∨ ∃ x ∈ S, B.Adj u.val x ∧ B.Adj x v.val)
  symm := ⟨by
    rintro u v ⟨different, adjacent | ⟨x, hx, ux, xv⟩⟩
    · exact ⟨different.symm, Or.inl adjacent.symm⟩
    · exact ⟨different.symm, Or.inr ⟨x, hx, xv.symm, ux.symm⟩⟩⟩
  loopless := ⟨fun _ ⟨different, _⟩ => different rfl⟩

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression
