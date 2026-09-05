/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph

/-!
# Padding a constraint graph with isolated vertices

The expander family built by the zig-zag tower supplies graphs only at certain
sizes, far apart from one another. Rather than fold a large expander onto an
arbitrary vertex count — which costs a delicate spectral argument — one can
enlarge the constraint graph instead, up to the next size the family offers.

Nothing is lost by doing so. The added vertices carry no edges, and every
quantity the amplification tracks is counted over *edges*: the number of edges
is unchanged, an assignment matters only through its values on the original
vertices, and so both the unsatisfiability value and satisfiability are
untouched.

## Main definitions

- `Complexity.ConstraintGraph.pad` — the same graph on more vertices

## Main results

- `Complexity.ConstraintGraph.numEdges_pad`, `unsatVal_pad`,
  `satisfiable_pad_iff` — padding changes nothing that matters
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type}

/-- The same constraint graph, on `N ≥ numVerts` vertices; the extra ones carry
no edges. -/
def pad (G : ConstraintGraph α) (N : ℕ) (h : G.numVerts ≤ N) : ConstraintGraph α where
  numVerts := N
  numEdges := G.numEdges
  tail := fun e => Fin.castLE h (G.tail e)
  head := fun e => Fin.castLE h (G.head e)
  rel := G.rel

@[simp] theorem numEdges_pad (G : ConstraintGraph α) (N : ℕ) (h : G.numVerts ≤ N) :
    (G.pad N h).numEdges = G.numEdges := rfl

@[simp] theorem numVerts_pad (G : ConstraintGraph α) (N : ℕ) (h : G.numVerts ≤ N) :
    (G.pad N h).numVerts = N := rfl

/-- Restricting an assignment of the padded graph to the original vertices. -/
def restrict (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) : G.Assignment :=
  fun v => a (Fin.castLE h v)

/-- Extending an assignment to the padded graph, arbitrarily on the new
vertices. -/
noncomputable def extend [Nonempty α] (G : ConstraintGraph α) {N : ℕ}
    (h : G.numVerts ≤ N) (a : G.Assignment) : (G.pad N h).Assignment :=
  fun v => if hv : v.val < G.numVerts then a ⟨v.val, hv⟩ else Classical.arbitrary α

theorem restrict_extend [Nonempty α] (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : G.Assignment) : G.restrict h (G.extend h a) = a := by
  funext v
  rw [restrict, extend]
  exact dite_eq_left v.isLt

theorem satisfies_pad_iff (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) (e : Fin (G.pad N h).numEdges) :
    (G.pad N h).Satisfies a e ↔ G.Satisfies (G.restrict h a) e := Iff.rfl

theorem unsatEdges_pad (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) :
    (G.pad N h).unsatEdges a = G.unsatEdges (G.restrict h a) := rfl

theorem unsatFrac_pad (G : ConstraintGraph α) {N : ℕ} (h : G.numVerts ≤ N)
    (a : (G.pad N h).Assignment) :
    (G.pad N h).unsatFrac a = G.unsatFrac (G.restrict h a) := rfl

/-- **Padding does not change the value.** -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem unsatVal_pad [Fintype α] [Nonempty α] [DecidableEq α] (G : ConstraintGraph α)
    (N : ℕ) (h : G.numVerts ≤ N) :
    (G.pad N h).unsatVal = G.unsatVal := by
  classical
  refine le_antisymm (Finset.le_inf' _ _ fun b _ => ?_) (Finset.le_inf' _ _ fun a _ => ?_)
  · have hle := Finset.inf'_le (G.pad N h).unsatFrac (Finset.mem_univ (G.extend h b))
    rw [unsatFrac_pad, restrict_extend] at hle
    exact hle
  · rw [unsatFrac_pad]
    exact Finset.inf'_le G.unsatFrac (Finset.mem_univ _)

/-- **Padding does not change satisfiability.** -/
theorem satisfiable_pad_iff [Nonempty α] (G : ConstraintGraph α) (N : ℕ)
    (h : G.numVerts ≤ N) :
    (G.pad N h).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨G.restrict h a, fun e => (G.satisfies_pad_iff h a e).1 (ha e)⟩
  · rintro ⟨b, hb⟩
    refine ⟨G.extend h b, fun e => ?_⟩
    rw [satisfies_pad_iff, restrict_extend]
    exact hb e

end ConstraintGraph

end Complexity
