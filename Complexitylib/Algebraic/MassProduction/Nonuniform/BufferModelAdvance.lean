/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferModel

/-!
# Preserving the scheduler invariant through one halving step

Request identities are updated by an equivalence. Newly accepted recovery
lines avoid all previously occupied points and every other accepted line,
so the enlarged completed buffer remains a disjoint schedule.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open BufferAdvance
open scoped LinearAlgebra.Projectivization

/-- Move a permuted pending prefix into the completed request partition. -/
def State.advance (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    State total (completed + accepted) remaining dimension width where
  order := BufferOrder.advance state.order permutation split
  directions := Fin.append state.directions (fun index => directions (permutation (acceptedIndex split index)))

/-- Each completed line is included in the occupied set. -/
theorem line_subset_occupied (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) (index : Fin completed) :
    line state targets index ⊆ occupied state targets := by
  classical
  exact Finset.subset_biUnion_of_mem (line state targets) (Finset.mem_univ index)

/-- Previously completed lines retain their targets and directions. -/
theorem advance_line_completed (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets : Fin total → Fin dimension → BinaryExtension width) (index : Fin completed) :
    line (state.advance permutation split directions) targets (Fin.castAdd accepted index) = line state targets index := by
  simp only [line, State.advance, BufferOrder.advance_completed, Fin.append_left]

/-- Newly completed lines use the selected pending target and candidate direction. -/
theorem advance_line_accepted (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets : Fin total → Fin dimension → BinaryExtension width) (index : Fin accepted) :
    line (state.advance permutation split directions) targets (Fin.natAdd completed index) =
      puncturedLine (pendingTargets state targets (permutation (acceptedIndex split index)))
        (directions (permutation (acceptedIndex split index))) := by
  simp only [line, State.advance, BufferOrder.advance_accepted, Fin.append_right, pendingTargets]

/-- The pending target tuple is the permuted suffix of the previous tuple. -/
theorem advance_pendingTargets (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets : Fin total → Fin dimension → BinaryExtension width) (index : Fin remaining) :
    pendingTargets (state.advance permutation split directions) targets index =
      pendingTargets state targets (permutation (pendingIndex split index)) := by
  simp only [pendingTargets, State.advance, BufferOrder.advance_pending]

/-- Old completed records survive advancement bit for bit. -/
theorem advance_completedRecord_old (positive : 0 < width)
    (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (data : Fin total → Fin requestWidth → Bool) (targets : Fin total → Fin dimension → BinaryExtension width)
    (index : Fin completed) :
    completedRecord positive (state.advance permutation split directions) data targets (Fin.castAdd accepted index) =
      completedRecord positive state data targets index := by
  simp only [completedRecord, State.advance, BufferOrder.advance_completed, Fin.append_left]

/-- New completed records use the accepted original data and generated line. -/
theorem advance_completedRecord_new (positive : 0 < width)
    (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (data : Fin total → Fin requestWidth → Bool) (targets : Fin total → Fin dimension → BinaryExtension width)
    (index : Fin accepted) :
    completedRecord positive (state.advance permutation split directions) data targets (Fin.natAdd completed index) =
      Fin.append (pendingRecord state data (permutation (acceptedIndex split index)))
        (fun pointBit =>
          let pair := (finProdFinEquiv (m := 2 ^ width) (n := dimension * width)).symm pointBit
          binaryExtensionVectorBits positive
            (PaddedLinePoints.point positive
              (pendingTargets state targets (permutation (acceptedIndex split index)))
              (directions (permutation (acceptedIndex split index))) pair.1) pair.2) := by
  simp only [completedRecord, State.advance, BufferOrder.advance_accepted, Fin.append_right,
    pendingRecord, pendingTargets]

/-- New pending records are precisely the permuted original-data suffix. -/
theorem advance_pendingRecord (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (data : Fin total → Fin requestWidth → Bool) (index : Fin remaining) :
    pendingRecord (state.advance permutation split directions) data index =
      pendingRecord state data (permutation (pendingIndex split index)) := by
  simp only [pendingRecord, State.advance, BufferOrder.advance_pending]

/-- Accepting a clean prefix preserves pairwise disjointness of all completed lines. -/
theorem advance_wellScheduled (state : State total completed pending dimension width)
    (permutation : Equiv.Perm (Fin pending)) (split : accepted + remaining = pending)
    (directions : Fin pending → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets : Fin total → Fin dimension → BinaryExtension width)
    (previous : WellScheduled state targets)
    (clean : ∀ index : Fin accepted,
      Clean (fun request direction => puncturedLine (pendingTargets state targets request) direction)
        (occupied state targets) directions (permutation (acceptedIndex split index))) :
    WellScheduled (state.advance permutation split directions) targets := by
  intro left
  refine Fin.addCases (fun oldLeft => ?_) (fun newLeft => ?_) left
  · intro right
    refine Fin.addCases (fun oldRight => ?_) (fun newRight => ?_) right
    · intro different
      rw [advance_line_completed, advance_line_completed]
      exact previous (fun equal => different (congrArg (Fin.castAdd accepted) equal))
    · intro _
      rw [advance_line_completed, advance_line_accepted]
      exact ((clean newRight).1.mono_right (line_subset_occupied state targets oldLeft)).symm
  · intro right
    refine Fin.addCases (fun oldRight => ?_) (fun newRight => ?_) right
    · intro _
      rw [advance_line_accepted, advance_line_completed]
      exact (clean newLeft).1.mono_right (line_subset_occupied state targets oldRight)
    · intro different
      rw [advance_line_accepted, advance_line_accepted]
      apply (clean newLeft).2 (permutation (acceptedIndex split newRight))
      intro equal
      have same := acceptedIndex_injective split (permutation.injective equal)
      exact different (congrArg (Fin.natAdd completed) same.symm)

end Algebraic.MassProduction.Nonuniform.BufferModel
