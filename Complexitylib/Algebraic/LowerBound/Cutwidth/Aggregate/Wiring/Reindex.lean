/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.NetworkDefs

/-!
# Reindexing the inputs read by an aggregate network

An equivalence enumerating the read variables turns a network on a subset of the original
coordinates into a network reading all coordinates of a smaller cube. Graphs, local checks,
contributions, and the final predicate are unchanged.
-/

@[expose] public section

namespace Algebraic.Cutwidth.AggregateNetwork

open scoped Classical

variable {n k : Nat} {V E M : Type} [CommMonoid M] (N : AggregateNetwork n V E M)
  (e : Fin k ≃ ↥N.read)

/-- Extend the enumerated read variables, fixing all other coordinates. -/
noncomputable def extendInput (outside : Fin n → Bool) (x : Fin k → Bool) (j : Fin n) : Bool :=
  if h : j ∈ N.read then x (e.symm ⟨j, h⟩) else outside j

@[simp] theorem extendInput_apply (outside : Fin n → Bool) (x : Fin k → Bool) (j : Fin k) :
    N.extendInput e outside x (e j) = x j := by
  simp [extendInput, (e j).2]

/-- Enumerate the read variables without changing the graph or local data. -/
noncomputable def reindex : AggregateNetwork k V E M where
  toMultigraph := N.toMultigraph
  Check := N.Check
  check_local := N.check_local
  read := Finset.univ
  portVertex := fun j => N.portVertex (e j)
  portEdge := fun j => N.portEdge (e j)
  port_incident := fun j _ => N.port_incident (e j) (e j).2
  contribution := N.contribution
  contribution_local := N.contribution_local
  Accept := N.Accept

/-- Input reindexing preserves the underlying multigraph. -/
theorem reindex_toMultigraph : (N.reindex e).toMultigraph = N.toMultigraph := rfl

@[simp] theorem reindex_read : (N.reindex e).read = Finset.univ := rfl

variable [Fintype V]

/-- Satisfaction is preserved by the coordinate enumeration. -/
theorem reindex_satisfies_iff (x : Fin k → Bool) (y : Fin n → Bool)
    (hxy : ∀ j, y (e j) = x j) (α : E → Bool) :
    (N.reindex e).Satisfies x α ↔ N.Satisfies y α := by
  constructor
  · rintro ⟨⟨checks, ports⟩, acc⟩
    refine ⟨⟨checks, fun j hj => ?_⟩, acc⟩
    let i := e.symm ⟨j, hj⟩
    have hi : (e i).val = j := congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)
    have hp := ports i (Finset.mem_univ i)
    change α (N.portEdge (e i)) = x i at hp
    rw [← hxy i, hi] at hp
    exact hp
  · rintro ⟨⟨checks, ports⟩, acc⟩
    refine ⟨⟨checks, fun j _ => ?_⟩, acc⟩
    exact (ports (e j) (e j).2).trans (hxy j)

/-- The reindexed network computes the restriction obtained by fixing outside coordinates. -/
theorem reindex_computes {f : Cslib.BooleanFunction n} (hf : N.Computes f)
    (outside : Fin n → Bool) :
    (N.reindex e).Computes (fun x => f (N.extendInput e outside x)) := by
  intro x
  rw [hf]
  apply exists_congr
  intro α
  exact (N.reindex_satisfies_iff e x (N.extendInput e outside x)
    (fun j => N.extendInput_apply e outside x j) α).symm

end Algebraic.Cutwidth.AggregateNetwork
