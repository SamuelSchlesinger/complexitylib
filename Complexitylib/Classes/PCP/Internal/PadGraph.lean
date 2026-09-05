/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.ConstraintGraph

/-!
# Padding a constraint graph

A `PCP` verifier tosses a number of coins that depends on the input's *length*
alone, and it uses them to pick an edge. So the graph it reads must have a
number of edges that depends on the length alone — which the graph of a formula
does not.

Padding fixes that: extra self-loops at vertex `0`, each carrying the constraint
that is always true. They change nothing about satisfiability, and they let the
edge count be pushed up to any size a length determines.

## Main definitions

- `Complexity.ConstraintGraph.padGraph` — the graph with extra trivial edges

## Main results

- `Complexity.ConstraintGraph.satisfiable_padGraph_iff` — padding preserves
  satisfiability
-/

@[expose] public section

namespace Complexity

namespace ConstraintGraph

variable {α : Type}

/-- `G` with trivial self-loops added until it has at least `n` edges. -/
def padGraph (G : ConstraintGraph α) (hv : 0 < G.numVerts) (n : ℕ) : ConstraintGraph α where
  numVerts := G.numVerts
  numEdges := max n G.numEdges
  tail e := if h : e.val < G.numEdges then G.tail ⟨e.val, h⟩ else ⟨0, hv⟩
  head e := if h : e.val < G.numEdges then G.head ⟨e.val, h⟩ else ⟨0, hv⟩
  rel e := if h : e.val < G.numEdges then G.rel ⟨e.val, h⟩ else fun _ _ => true

variable {G : ConstraintGraph α} {hv : 0 < G.numVerts} {n : ℕ}

@[simp] theorem numVerts_padGraph : (G.padGraph hv n).numVerts = G.numVerts := rfl

@[simp] theorem numEdges_padGraph : (G.padGraph hv n).numEdges = max n G.numEdges := rfl

theorem tail_padGraph_of_lt {e : ℕ} (he : e < (G.padGraph hv n).numEdges)
    (h : e < G.numEdges) :
    ((G.padGraph hv n).tail ⟨e, he⟩).val = (G.tail ⟨e, h⟩).val := by
  show (dite _ _ _ : Fin G.numVerts).val = _
  rw [dite_eq_left h]

theorem head_padGraph_of_lt {e : ℕ} (he : e < (G.padGraph hv n).numEdges)
    (h : e < G.numEdges) :
    ((G.padGraph hv n).head ⟨e, he⟩).val = (G.head ⟨e, h⟩).val := by
  show (dite _ _ _ : Fin G.numVerts).val = _
  rw [dite_eq_left h]

theorem rel_padGraph_of_lt {e : ℕ} (he : e < (G.padGraph hv n).numEdges)
    (h : e < G.numEdges) :
    (G.padGraph hv n).rel ⟨e, he⟩ = G.rel ⟨e, h⟩ := by
  show (dite _ _ _ : α → α → Bool) = _
  rw [dite_eq_left h]

theorem tail_padGraph_of_ge {e : ℕ} (he : e < (G.padGraph hv n).numEdges)
    (h : ¬ e < G.numEdges) : ((G.padGraph hv n).tail ⟨e, he⟩).val = 0 := by
  show (dite _ _ _ : Fin G.numVerts).val = _
  rw [dite_eq_right h]

theorem head_padGraph_of_ge {e : ℕ} (he : e < (G.padGraph hv n).numEdges)
    (h : ¬ e < G.numEdges) : ((G.padGraph hv n).head ⟨e, he⟩).val = 0 := by
  show (dite _ _ _ : Fin G.numVerts).val = _
  rw [dite_eq_right h]

theorem rel_padGraph_of_ge {e : ℕ} (he : e < (G.padGraph hv n).numEdges)
    (h : ¬ e < G.numEdges) :
    (G.padGraph hv n).rel ⟨e, he⟩ = fun _ _ => true := by
  show (dite _ _ _ : α → α → Bool) = _
  rw [dite_eq_right h]

/-- The padded graph has the same assignments. -/
theorem assignment_padGraph : (G.padGraph hv n).Assignment = G.Assignment := rfl

/-- **Padding preserves satisfiability.** -/
theorem satisfiable_padGraph_iff : (G.padGraph hv n).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun e => ?_⟩
    have hlt : e.val < (G.padGraph hv n).numEdges :=
      lt_of_lt_of_le e.isLt (le_max_right _ _)
    have h := ha ⟨e.val, hlt⟩
    unfold Satisfies satisfies at h ⊢
    rw [rel_padGraph_of_lt hlt e.isLt] at h
    rw [show (⟨e.val, e.isLt⟩ : Fin G.numEdges) = e from rfl] at h
    rw [← h]
    congr 1
    · exact congrArg a (Fin.ext (tail_padGraph_of_lt hlt e.isLt)).symm
    · exact congrArg a (Fin.ext (head_padGraph_of_lt hlt e.isLt)).symm
  · rintro ⟨a, ha⟩
    refine ⟨a, fun e => ?_⟩
    unfold Satisfies satisfies
    by_cases h : e.val < G.numEdges
    · have hb := ha ⟨e.val, h⟩
      unfold Satisfies satisfies at hb
      rw [rel_padGraph_of_lt e.isLt h]
      rw [show a ((G.padGraph hv n).tail e) = a (G.tail ⟨e.val, h⟩) from
        congrArg a (Fin.ext (tail_padGraph_of_lt e.isLt h)),
        show a ((G.padGraph hv n).head e) = a (G.head ⟨e.val, h⟩) from
        congrArg a (Fin.ext (head_padGraph_of_lt e.isLt h))]
      exact hb
    · rw [rel_padGraph_of_ge e.isLt h]

end ConstraintGraph

end Complexity
