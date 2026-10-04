/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Ordering.Internal

/-!
# Transferring graph orderings to straight-line programs

The graph-ordering hypothesis `Multigraph.OrderingBound A η C` lays out every connected loopless
multigraph of maximum degree three so that every lower-set cut has at most
`(A + η) (M - N)⁺ + 3 log₂ N + C` edges. This file transfers it to the wires of a straight-line
program over **any signature**, with **any value type** and **any outputs**, whose gates have at
most two arguments: it ranks the wires so that every prefix is crossed by few signals in the
sense of `SingleCut.forward` and `SingleCut.backward`.

**The ordering transfer** (`exists_rank`). For a program with fan-in at most two there is an
injective ranking of its wires, with ranks below `n + s`, such that for every wire `w` the
prefix `P` of the wires ranked at most as high as `w` satisfies
`|forward P| + |backward P| ≤ (A + η) (g - i)⁺ + 3 log₂ (n + 3 s) + C`,
where `g` and `i` are the numbers of gates and inputs in the component of `w` in the wire graph
(`component`). When the wire graph is connected (`exists_rank_of_connected`), every prefix
satisfies `|forward P| + |backward P| ≤ (A + η) (s - n)⁺ + 3 log₂ (n + 3 s) + C`.

The proof builds, for each component, the subcubic wire graph of `Cutwidth.Wiring` (a vertex per
wire, plus copy vertices routing a signal read by several argument slots), applies the ordering
hypothesis to it, and pulls the vertex order back to the wires. A signal crossing a split of the
wires crosses the corresponding cut of the wire graph with an edge of its own copy tree, so the
signals crossing a prefix number at most the edges of a lower-set cut. Components are laid out
one after another; a component is closed (`component_closed`), and closed sets contribute no
crossing signals (`forward_union_of_closed`, `backward_union_of_closed`), so a prefix is charged
to the component of its last wire. The outputs play no role: the bound holds for every set of
designated output wires.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut

variable {σ : Signature} {n s : Nat}

/-! ## Components and closed sets -/

section Components

variable {p : Program σ n s}

theorem mem_component {v w : Wire n s} :
    v ∈ component p w ↔ Relation.ReflTransGen (Linked p) w v :=
  Internal.mem_component

variable (p) in
theorem mem_component_self (w : Wire n s) : w ∈ component p w :=
  Internal.mem_component_self p w

variable (p) in
/-- **Components are closed.** A gate lies in a component exactly when the wires it reads do. -/
theorem component_closed (w : Wire n s) (g : Fin s) (v : Wire n s) (h : p.Reads g v) :
    Wire.gate g ∈ component p w ↔ v ∈ component p w :=
  Internal.component_closed p w g v h

/-- Components partition the wires. -/
theorem component_eq_of_mem {v w : Wire n s} (h : v ∈ component p w) :
    component p v = component p w :=
  Internal.component_eq_of_mem h

variable (p) in
/-- Any two wires of a component are joined by a path of linked wires. -/
theorem component_connected (w : Wire n s) :
    ∀ u ∈ component p w, ∀ v ∈ component p w, Relation.ReflTransGen (Linked p) u v :=
  Internal.component_connected p w

/-- **Closed sets are invisible to a split.** Adding a closed set disjoint from `P` changes
neither the forward nor the backward signals of `P`. -/
theorem forward_union_of_closed {Q P : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) (hdisj : Disjoint Q P) :
    forward p (Q ∪ P) = forward p P :=
  Internal.forward_union_of_closed hQ hdisj

/-- The backward half of `forward_union_of_closed`. -/
theorem backward_union_of_closed {Q P : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) (hdisj : Disjoint Q P) :
    backward p (Q ∪ P) = backward p P :=
  Internal.backward_union_of_closed hQ hdisj

/-- A closed set has no forward signals. -/
theorem forward_eq_empty_of_closed {Q : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) : forward p Q = ∅ :=
  Internal.forward_eq_empty_of_closed hQ

/-- A closed set has no backward signals. -/
theorem backward_eq_empty_of_closed {Q : Finset (Wire n s)}
    (hQ : ∀ g w, p.Reads g w → (Wire.gate g ∈ Q ↔ w ∈ Q)) : backward p Q = ∅ :=
  Internal.backward_eq_empty_of_closed hQ

end Components

/-! ## The ordering transfer -/

/-- The graph-ordering hypothesis forces a nonnegative additive constant. -/
theorem orderingBound_nonneg {A η C : ℝ} (order : Multigraph.OrderingBound A η C) : 0 ≤ C :=
  Internal.orderingBound_nonneg order

/-- **The ordering transfer.** Let a program over any signature have fan-in at most two, and
assume the graph-ordering hypothesis with coefficient `A`, slack `η` and constant `C`. Then
some injective ranking of the wires, with ranks below `n + s`, has the following property: for
every wire `w`, the wires ranked at most as high as `w` are crossed by at most
`(A + η) (g - i)⁺ + 3 log₂ (n + 3 s) + C` forward and backward signals, where `g` and `i` are the
numbers of gates and inputs in the component of `w`. -/
theorem exists_rank {A η C : ℝ} (hAη : 0 ≤ A + η) (order : Multigraph.OrderingBound A η C)
    (p : Program σ n s) (hp : p.FanInAtMost 2) :
    ∃ rank : Wire n s → Nat, Function.Injective rank ∧ (∀ w, rank w < n + s) ∧ ∀ w,
      (((forward p (prefixUpTo rank w)).card + (backward p (prefixUpTo rank w)).card : Nat) :
          ℝ) ≤
        (A + η) * max (((gatesIn (component p w)).card : ℝ) - (inputsIn (component p w)).card) 0 +
          3 * Real.logb 2 (n + 3 * s) + C :=
  Internal.exists_rank hAη order p hp

/-- **The ordering transfer for a connected wire graph.** If any two wires are joined by a path
of linked wires, some injective ranking of the wires has every prefix crossed by at most
`(A + η) (s - n)⁺ + 3 log₂ (n + 3 s) + C` forward and backward signals. -/
theorem exists_rank_of_connected {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) (p : Program σ n s) (hp : p.FanInAtMost 2)
    (hconn : ∀ u v : Wire n s, Relation.ReflTransGen (Linked p) u v) :
    ∃ rank : Wire n s → Nat, Function.Injective rank ∧ (∀ w, rank w < n + s) ∧ ∀ t,
      (((forward p (prefixBelow rank t)).card + (backward p (prefixBelow rank t)).card : Nat) :
          ℝ) ≤
        (A + η) * max ((s : ℝ) - n) 0 + 3 * Real.logb 2 (n + 3 * s) + C :=
  Internal.exists_rank_of_connected hAη order p hp hconn

end Algebraic.Cutwidth.MultiOutput
