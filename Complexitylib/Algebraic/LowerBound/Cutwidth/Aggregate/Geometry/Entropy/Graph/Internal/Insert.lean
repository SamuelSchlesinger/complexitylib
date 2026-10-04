/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Weights

/-!
# Extending an edge message by one coordinate

The inserted coordinate is equivalent to a pair of its Boolean value and the old
message. This equivalence lets a normalized conditional kernel extend the old weight.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- A new Boolean coordinate together with an old tuple is the tuple on an insertion. -/
noncomputable def tupleInsertEquiv (selected : Finset E) (e : E) (fresh : e ∉ selected) :
    (Bool × (selected → Bool)) ≃ (↥(insert e selected) → Bool) where
  toFun p i := if h : i.val = e then p.1 else
    p.2 ⟨i.val, Finset.mem_of_mem_insert_of_ne i.property h⟩
  invFun m := (m ⟨e, Finset.mem_insert_self _ _⟩,
    fun i => m ⟨i.val, Finset.mem_insert_of_mem i.property⟩)
  left_inv p := by
    apply Prod.ext
    · simp
    · funext i
      have h : i.val ≠ e := by intro he; exact fresh (he ▸ i.property)
      simp [h]
  right_inv m := by
    funext i
    by_cases h : i.val = e
    · simp only [h, ↓reduceDIte]
      exact congrArg m (Subtype.ext h.symm)
    · simp only [h, ↓reduceDIte]

omit [DecidableEq V] in
/-- The insertion equivalence combines the actual edge value and actual previous tuple. -/
@[simp] theorem tupleInsertEquiv_apply (edge : E → SignedEdge V) (selected : Finset E)
    (e : E) (fresh : e ∉ selected) (x : V → Bool) :
    tupleInsertEquiv selected e fresh ((edge e).eval x, tuple edge selected x) =
      tuple edge (insert e selected) x := by
  funext i
  dsimp [tupleInsertEquiv, tuple]
  split_ifs with h
  · rw [h]
  · rfl

/-- An old tuple weight and one conditional edge weight extend to the inserted tuple. -/
noncomputable def insertWeight [Fintype V]
    (edge : E → SignedEdge V) (selected : Finset E) (e : E) (fresh : e ∉ selected)
    {a b : ℝ} (previous : WeightBound (tuple edge selected) a)
    (next : ConditionalWeightBound (edge e).eval (tuple edge selected) b) :
    WeightBound (tuple edge (insert e selected)) (a + b) := by
  have result := (previous.pairConditional next).equiv (tupleInsertEquiv selected e fresh)
  simpa only [tupleInsertEquiv_apply] using result

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
