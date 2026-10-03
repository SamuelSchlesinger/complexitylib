/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Partial connected partitions with a rooted remainder

Removing a root splits a connected graph into at most its degree many
components. Joining their small rooted remainders back to the root produces
one bounded connected piece. This intermediate record supports that
induction without carrying a rooted-tree representation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition

open scoped Classical

/-- Connected pieces of size between `M` and `3 M`, and at most one smaller
remainder containing the prescribed root. -/
structure Partial {V : Type} (B : SimpleGraph V) (S : Finset V) (root : V) (M : Nat) where
  /-- Completed connected pieces, each with at least `M` vertices. -/
  parts : Finset (Finset V)
  /-- The still-unassigned connected set containing the root, or the empty set. -/
  remainder : Finset V
  cover : parts.biUnion id ∪ remainder = S
  disjoint : (parts : Set (Finset V)).Pairwise Disjoint
  separate : ∀ P ∈ parts, Disjoint P remainder
  pieces : ∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected ∧ M ≤ P.card ∧ P.card ≤ 3 * M
  small : remainder.card < M
  rooted : remainder = ∅ ∨ root ∈ remainder ∧ (B.induce {v | v ∈ remainder}).Connected

end Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition
