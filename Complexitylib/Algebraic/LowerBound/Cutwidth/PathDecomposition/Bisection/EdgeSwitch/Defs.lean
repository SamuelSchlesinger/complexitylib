/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# A switch of two disjoint edges

Monien and Preis normalize a side by replacing edges `a-b` and `c-d`
with edges `a-c` and `b-d`. The four endpoints are distinct and the new
edges must be absent, so this operation preserves each vertex degree.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

/-- The two old edges are disjoint and the two new edges are absent.
The old adjacencies also imply `a ≠ b` and `c ≠ d`. -/
structure Switchable {W : Type} (H : SimpleGraph W) (a b c d : W) : Prop where
  ab : H.Adj a b
  cd : H.Adj c d
  ac : ¬ H.Adj a c
  bd : ¬ H.Adj b d
  distinct : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

/-- Delete `a-b` and `c-d`, then add `a-c` and `b-d`. -/
def switchEdges {W : Type} (H : SimpleGraph W) (a b c d : W) : SimpleGraph W :=
  H.deleteEdges {s(a, b), s(c, d)} ⊔ SimpleGraph.edge a c ⊔ SimpleGraph.edge b d

end Algebraic.Cutwidth.Bisection
