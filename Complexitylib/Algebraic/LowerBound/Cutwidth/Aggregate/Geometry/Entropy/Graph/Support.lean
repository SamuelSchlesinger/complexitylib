/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union

/-!
# Supports of finite families of edges

Adding an edge introduces zero, one, or two new endpoints. These exact cardinality
increments are the combinatorial accounting used by the joint-message entropy bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

open scoped Classical

variable {V E : Type*} [DecidableEq V]

/-- The vertices occurring among a finite family of edges. -/
def support (left right : E → V) (edges : Finset E) : Finset V :=
  edges.biUnion fun e => {left e, right e}

/-- Membership in the support gives an incident edge in the selected family. -/
@[simp] theorem mem_support (left right : E → V) (edges : Finset E) (v : V) :
    v ∈ support left right edges ↔ ∃ e ∈ edges, v = left e ∨ v = right e := by
  simp [support]

/-- The empty edge family has empty support. -/
@[simp] theorem support_empty (left right : E → V) : support left right ∅ = ∅ := by
  simp [support]

/-- Inserting an edge adds precisely its two endpoints to the support. -/
theorem support_insert [DecidableEq E] (left right : E → V) (edges : Finset E) (e : E) :
    support left right (insert e edges) = insert (left e) (insert (right e)
      (support left right edges)) := by
  ext v
  simp [or_assoc]

/-- No support vertex is added when both endpoints already occur. -/
theorem card_support_insert_of_mem_mem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E)
    (hl : left e ∈ support left right edges) (hr : right e ∈ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card := by
  rw [support_insert, Finset.insert_eq_of_mem hr, Finset.insert_eq_of_mem hl]

/-- Exactly one support vertex is added when only the right endpoint is new. -/
theorem card_support_insert_of_mem_notMem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E)
    (hl : left e ∈ support left right edges) (hr : right e ∉ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card + 1 := by
  rw [support_insert, Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hl),
    Finset.card_insert_of_notMem hr]

/-- Exactly one support vertex is added when only the left endpoint is new. -/
theorem card_support_insert_of_notMem_mem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E)
    (hl : left e ∉ support left right edges) (hr : right e ∈ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card + 1 := by
  rw [support_insert, Finset.insert_eq_of_mem hr, Finset.card_insert_of_notMem hl]

/-- Two support vertices are added when the distinct endpoints are both new. -/
theorem card_support_insert_of_notMem_notMem [DecidableEq E]
    (left right : E → V) (edges : Finset E) (e : E) (hne : left e ≠ right e)
    (hl : left e ∉ support left right edges) (hr : right e ∉ support left right edges) :
    (support left right (insert e edges)).card = (support left right edges).card + 2 := by
  rw [support_insert, Finset.card_insert_of_notMem (by simp [hne, hl]),
    Finset.card_insert_of_notMem hr]

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
