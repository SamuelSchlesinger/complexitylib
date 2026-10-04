/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# Small components and thin paths in the red/black argument

These are the first two witness constructions in Monien and Preis's core
red/black lemma. A red edge inside one small black component, or between
two such components, gives a positive set. A black path with many red
attachments relative to its length also gives a uniformly bounded positive
set: choose three nearby attachments, retain the subpath between them, and
add their black components.

`WeightedTree` supplies the light adjacent-pair lemma, `RedBlack.Restoration`
the local compensation for deleted black edges, and `Restoration.Family`
a uniform bound for restoring a whole family. `CycleRemoval` selects
regions to isolate in a supplied degree-two family and excludes all cycles
through that family. `PathSystem` constructs the family from eligible
vertices and their actual red attachments. Its initial attachment marks
and their shared budget with small cyclic components are counted exactly.
Preserving marks through the tree reorganization is not formalized:
`RedBlack.Clusters` proves the red/black density lemma by bounded connected
partitions instead, and `Bisection.exists_bisectionBound` uses it.
These constructions also apply after black-edge deletions; they do not
require cubic regularity.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

omit [Fintype V] in
/-- Both endpoints characterize membership among the internal red edges. -/
theorem mem_internalEdges {X : Finset V} {e : E} :
    e ∈ internalEdges R X ↔ R.fst e ∈ X ∧ R.snd e ∈ X :=
  Internal.mem_internalEdges R

omit [Fintype V] in
/-- Adding vertices preserves every existing internal red edge. -/
theorem internalEdges_mono {X Y : Finset V} (h : X ⊆ Y) :
    internalEdges R X ⊆ internalEdges R Y :=
  Internal.internalEdges_mono R h

/-- A red edge joining small black components gives a positive set of size
at most `2 M`. The two components may coincide. -/
theorem exists_positive_of_component_edge (C D : B.ConnectedComponent) (M : Nat)
    (smallC : Fintype.card C ≤ M) (smallD : Fintype.card D ≤ M)
    {e : E} (hfst : R.fst e ∈ C.supp) (hsnd : R.snd e ∈ D.supp) :
    ∃ X : Finset V, X.card ≤ 2 * M ∧ Positive B R X :=
  Internal.exists_positive_of_component_edge B R C D M smallC smallD hfst hsnd

/-- Attach sets with empty black cuts to a connecting set. More distinct
red attachments than black crossing edges suffice for positivity. -/
theorem exists_positive_of_attachments (P : Finset V) (edges : Finset E)
    (A : E → Finset V) (M : Nat)
    (cut : (B.cutFinset P).card < edges.card)
    (closed : ∀ e ∈ edges, B.cutFinset (A e) = ∅)
    (small : ∀ e ∈ edges, (A e).card ≤ M)
    (attached : ∀ e ∈ edges,
      (R.fst e ∈ P ∧ R.snd e ∈ A e) ∨ (R.snd e ∈ P ∧ R.fst e ∈ A e)) :
    ∃ X : Finset V, X.card ≤ P.card + edges.card * M ∧ Positive B R X :=
  Internal.exists_positive_of_attachments B R P edges A M cut closed small attached

/-- A nonempty connected set whose vertices have black degree at most two
has at most two external black edges. -/
theorem card_cut_le_two_of_connected {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) : (B.cutFinset P).card ≤ 2 :=
  Internal.card_cut_le_two_of_connected B connected degree

/-- Among at least two nonnegative integer weights, two adjacent weights
have sum at most three times the average. This is the gap estimate in
Monien and Preis's thin-path construction, stated without division. -/
theorem exists_adjacent_pair_le_three_average {n : Nat} (w : Fin (n + 2) → Nat) :
    ∃ i : Fin (n + 1), (n + 2) * (w i.castSucc + w i.succ) ≤ 3 * ∑ j, w j :=
  Internal.exists_adjacent_pair_le_three_average w

/-- Three consecutive marked positions have span at most three times the
average gap between all marked positions. -/
theorem exists_three_close_positions {n : Nat} (pos : Fin (n + 3) → Nat)
    (ordered : Monotone pos) :
    ∃ i : Fin (n + 1), (n + 2) * (pos i.succ.succ - pos i.castSucc.castSucc) ≤
      3 * (pos (Fin.last (n + 2)) - pos 0) :=
  Internal.exists_three_close_positions pos ordered

/-- A walk of black degree at most two with `n + 3` distinct red attachments
and length at most `M * (n + 3)` gives a positive set of at most `8 M + 1`
vertices, provided each attached set has at most `M` vertices and an empty
black cut. The proof uses three nearby attachments and their connecting subwalk. -/
theorem exists_positive_of_thin_walk {u v : V} (p : B.Walk u v) {n : Nat}
    (edge : Fin (n + 3) ↪ E) (pos : Fin (n + 3) → Nat) (A : E → Finset V) (M : Nat)
    (ordered : Monotone pos) (within : ∀ i, pos i ≤ p.length)
    (degree : ∀ w ∈ p.support, B.degree w ≤ 2)
    (thin : p.length ≤ M * (n + 3))
    (closed : ∀ i, B.cutFinset (A (edge i)) = ∅)
    (small : ∀ i, (A (edge i)).card ≤ M)
    (attached : ∀ i,
      (R.fst (edge i) = p.getVert (pos i) ∧ R.snd (edge i) ∈ A (edge i)) ∨
        (R.snd (edge i) = p.getVert (pos i) ∧ R.fst (edge i) ∈ A (edge i))) :
    ∃ X : Finset V, X.card ≤ 8 * M + 1 ∧ Positive B R X :=
  Internal.exists_positive_of_thin_walk B R p edge pos A M ordered within degree thin
    closed small attached

end Algebraic.Cutwidth.Bisection.RedBlack
