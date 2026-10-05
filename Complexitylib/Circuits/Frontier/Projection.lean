/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Network
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Existentially hiding inputs

`Network.hide` existentially quantifies the last `k` inputs without changing the graph.
Local witnesses can be assembled into one global witness because each input is read at a
single site. No uniqueness of witnesses is assumed or needed.
-/

@[expose] public section

namespace Complexity.Frontier.Network

open Set

variable {U V E : Type*} {n k : ℕ} (N : Network U (Fin (n + k)) V E)

/-- Hide the last `k` inputs by existentially quantifying them in each local constraint. -/
def hide : Network U (Fin n) V E where
  toMultigraph := N.toMultigraph
  site i := N.site (Fin.castAdd k i)
  Check v x α := ∃ y : Fin k → U, N.Check v (Fin.append x y) α
  check_local v x x' α α' hx hα := by
    rintro ⟨y, hy⟩
    refine ⟨y, N.check_local v _ _ _ _ ?_ hα hy⟩
    intro i
    refine Fin.addCases (fun j hj => ?_) (fun j _ => ?_) i
    · simpa using hx j hj
    · simp

/-- Local existential witnesses assemble into one assignment of the hidden inputs. -/
theorem satisfies_hide_iff [Nonempty U] (x : Fin n → U) (α : E → U) :
    N.hide.Satisfies x α ↔ ∃ y : Fin k → U, N.Satisfies (Fin.append x y) α := by
  classical
  constructor
  · intro h
    choose ys hys using h
    let y : Fin k → U := fun j => (N.site (Fin.natAdd n j)).elim
      (Classical.arbitrary U) (fun v => ys v j)
    refine ⟨y, fun v => N.check_local v _ _ _ _ ?_ (fun _ _ => rfl) (hys v)⟩
    intro i
    refine Fin.addCases (fun j _ => ?_) (fun j hj => ?_) i
    · simp
    · simp [y, hj]
  · rintro ⟨y, hy⟩ v
    exact ⟨y, hy v⟩

/-- Hiding inputs is exactly projection of the accepted set. -/
theorem accepted_hide [Nonempty U] :
    N.hide.accepted = {x | ∃ y : Fin k → U, Fin.append x y ∈ N.accepted} := by
  ext x
  simp only [accepted, mem_ofPred_eq, satisfies_hide_iff]
  exact exists_comm

/-- The visible inputs read at a vertex inject into its original inputs. -/
theorem ncard_readAt_hide_le (v : V) :
    (N.hide.readAt v).ncard ≤ (N.readAt v).ncard := by
  refine ncard_le_ncard_of_injOn (Fin.castAdd k) (fun _ hi => hi)
    (Fin.castAdd_injective n k).injOn (toFinite _)

/-- Hiding inputs can only reduce the number of inputs read. -/
theorem ncard_read_hide_le : N.hide.read.ncard ≤ N.read.ncard := by
  refine ncard_le_ncard_of_injOn (Fin.castAdd k) (fun i hi => ?_)
    (Fin.castAdd_injective n k).injOn (toFinite _)
  exact hi

end Complexity.Frontier.Network
