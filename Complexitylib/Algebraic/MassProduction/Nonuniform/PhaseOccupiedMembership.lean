/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PhaseMenu

/-!
# Membership in optional-line occupancy

This instance-independent characterization avoids unfolding the finite
union's equality implementation when specializing to encoded vector spaces.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open scoped LinearAlgebra.Projectivization

/-- An occupied point belongs to one of the present line descriptions. -/
theorem mem_phaseOccupied_iff
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    (state : PhaseState V (ℙ K V) capacity active) (point : V) :
    point ∈ phaseOccupied state ↔
      ∃ slot line, state.1 slot = some line ∧ point ∈ puncturedLine line.1 line.2 := by
  classical
  rw [phaseOccupied, Finset.mem_biUnion]
  constructor
  · rintro ⟨slot, _, membership⟩
    cases present : state.1 slot with
    | none => simp [present] at membership
    | some line => exact ⟨slot, line, present, by simpa only [present, Option.elim_some] using membership⟩
  · rintro ⟨slot, line, present, membership⟩
    exact ⟨slot, Finset.mem_univ _, by simpa only [present, Option.elim_some] using membership⟩

end Algebraic.MassProduction.Nonuniform
