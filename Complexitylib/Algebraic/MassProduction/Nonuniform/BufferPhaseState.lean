/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferOccupancy
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PhaseOccupiedMembership

/-!
# Embedding a buffer model into a universal phase state

Completed request directions occupy a prefix of the fixed-capacity optional
line array. The pending tuple supplies the active targets. The occupied set
is exactly the buffer's completed-line union.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- Completed and pending positions partition the original request count. -/
theorem State.completed_add_pending (state : State total completed pending dimension width) :
    completed + pending = total := by
  simpa using Fintype.card_congr state.order

/-- Completed positions fit in the original fixed capacity. -/
theorem State.completed_le (state : State total completed pending dimension width) : completed ≤ total := by
  have count := state.completed_add_pending
  omega

/-- Pending positions fit in the original fixed capacity. -/
theorem State.pending_le (state : State total completed pending dimension width) : pending ≤ total := by
  have count := state.completed_add_pending
  omega

/-- Embed completed lines into optional fixed-capacity slots. -/
noncomputable def State.toPhaseState (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) :
    PhaseState (Fin dimension → BinaryExtension width)
      (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) total pending :=
  (fun slot => if before : slot.val < completed then
      some (targets (state.order (.inl ⟨slot.val, before⟩)), state.directions ⟨slot.val, before⟩)
    else none,
    pendingTargets state targets)

/-- The universal phase state has precisely the buffer's occupied points. -/
theorem State.toPhaseState_occupied (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) :
    phaseOccupied (state.toPhaseState targets) = occupied state targets := by
  classical
  ext point
  rw [mem_phaseOccupied_iff]
  constructor
  · rintro ⟨slot, description, present, membership⟩
    change (if before : slot.val < completed then
      some (targets (state.order (.inl ⟨slot.val, before⟩)), state.directions ⟨slot.val, before⟩)
      else none) = some description at present
    split_ifs at present with before
    · have sameDescription := Option.some.inj present
      subst description
      exact Finset.mem_biUnion.mpr ⟨⟨slot.val, before⟩, Finset.mem_univ _, membership⟩
  · intro membership
    obtain ⟨request, _, membership⟩ := Finset.mem_biUnion.mp membership
    refine ⟨Fin.castLE state.completed_le request,
      (targets (state.order (.inl request)), state.directions request), ?_, membership⟩
    simp only [State.toPhaseState, Fin.val_castLE, request.isLt, dite_true]

end Algebraic.MassProduction.Nonuniform.BufferModel
