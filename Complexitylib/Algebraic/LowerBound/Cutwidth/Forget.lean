/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Network
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Forgetting the ports of witness variables

A network over `n + m` variables reads its variables through ports. Forgetting
the ports of the last `m` variables leaves a network over `n` variables with
the same multigraph and the same local checks; an edge that carried a
forgotten variable is now unconstrained. If the original network computes
`F`, the forgotten network computes the existential projection
`x ↦ ∃ y, F (x, y)`: a satisfying assignment of the forgotten network reads
off a witness from the forgotten port edges.

This is the only ingredient needed to transfer the cut-counting lower bound
from deterministic to nondeterministic circuits, since the multigraph, and
hence its cutwidth, is unchanged.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth
namespace Network

open scoped Classical

variable {n m : Nat} {V E : Type} (N : Network (n + m) V E)

/-- Forget the ports of the last `m` variables. The multigraph and the local
checks are unchanged; only the first `n` variables are read. -/
noncomputable def forget : Network n V E where
  toMultigraph := N.toMultigraph
  Check := N.Check
  check_local := N.check_local
  read := Finset.univ.filter fun j : Fin n => Fin.castAdd m j ∈ N.read
  portVertex := fun j => N.portVertex (Fin.castAdd m j)
  portEdge := fun j => N.portEdge (Fin.castAdd m j)
  port_incident := fun j hj => N.port_incident (Fin.castAdd m j) (Finset.mem_filter.mp hj).2

theorem mem_forget_read {j : Fin n} : j ∈ N.forget.read ↔ Fin.castAdd m j ∈ N.read := by
  simp [forget]

@[simp] theorem forget_toMultigraph : N.forget.toMultigraph = N.toMultigraph := rfl

@[simp] theorem forget_portEdge (j : Fin n) : N.forget.portEdge j = N.portEdge (Fin.castAdd m j) :=
  rfl

/-- The forgotten network reads at most as many variables as the original. -/
theorem card_forget_read_le : N.forget.read.card ≤ N.read.card := by
  apply Finset.card_le_card_of_injOn (Fin.castAdd m)
  · intro j hj
    exact Finset.mem_coe.mpr ((N.mem_forget_read).mp (Finset.mem_coe.mp hj))
  · intro j _ j' _ h
    exact Fin.castAdd_injective n m h

/-- Forgetting witness ports computes the existential projection. -/
theorem Computes.forget {F : Cslib.BooleanFunction (n + m)} (h : N.Computes F) :
    N.forget.Computes fun x => decide (∃ y : Fin m → Bool, F (Fin.append x y) = true) := by
  intro x
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨α, checks, ports⟩ := (h _).mp hy
    refine ⟨α, checks, fun j hj => ?_⟩
    rw [forget_portEdge, ports (Fin.castAdd m j) ((N.mem_forget_read).mp hj), Fin.append_left]
  · rintro ⟨α, checks, ports⟩
    refine ⟨fun k => α (N.portEdge (Fin.natAdd n k)), (h _).mpr ⟨α, checks, fun j hj => ?_⟩⟩
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      exact ports j ((N.mem_forget_read).mpr hj)
    | right k =>
      rw [Fin.append_right]

end Network
end Cutwidth
end Algebraic
