/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferModelAdvance

/-!
# Correctness of a compacted geometric scheduler step

A phase satisfying the geometric output contract, followed by the fixed
buffer wiring, produces another encoded scheduler state. All request
identities and stored point lists are preserved, and the completed schedule
remains pairwise disjoint.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open Sorting BufferAdvance
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- A correct geometric phase plus free compaction preserves the full
encoded-state invariant needed by the next halving phase. -/
theorem advance_input_of_correct (positive : 0 < width)
    (state : State total completed (networkRecords requestDepth) dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width)
    (previous : WellScheduled state targets)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (phase : Circuit DeMorgan.signature
      (BufferInput.inputWidth completed (networkRecords requestDepth) requestWidth (2 ^ width) (dimension * width))
      (networkRecords requestDepth * (1 + BufferInput.storedWidth requestWidth (2 ^ width) (dimension * width))))
    (split : accepted + remaining = networkRecords requestDepth)
    (correct : GeometricPhase.CorrectOutput positive menu (pendingRecord state data)
      (pendingTargets state targets) (occupied state targets) accepted
      (phase.eval DeMorgan.interpretation (input positive state data targets))) :
    ∃ next : State total (completed + accepted) remaining dimension width,
      (BufferAdvance.circuit phase split).eval DeMorgan.interpretation (input positive state data targets) =
        input positive next data targets ∧ WellScheduled next targets := by
  obtain ⟨candidate, permutation, originalPreserved, pointsPreserved, clean⟩ := correct
  let next := state.advance permutation split (menu candidate)
  refine ⟨next, ?_, ?_⟩
  · rw [input, BufferAdvance.circuit_eval]
    change BufferInput.encode _ _ =
      BufferInput.encode (completedRecord positive next data targets) (pendingRecord next data)
    congr 1
    · funext record bit
      refine Fin.addCases (fun old => ?_) (fun fresh => ?_) record
      · rw [Fin.append_left]
        exact (congrFun (advance_completedRecord_old positive state permutation split (menu candidate)
          data targets old) bit).symm
      · rw [Fin.append_right]
        change _ = completedRecord positive (state.advance permutation split (menu candidate))
          data targets (Fin.natAdd completed fresh) bit
        rw [advance_completedRecord_new]
        refine Fin.addCases (fun dataBit => ?_) (fun pointBit => ?_) bit
        · rw [Fin.append_left]
          exact originalPreserved (acceptedIndex split fresh) dataBit
        · rw [Fin.append_right]
          obtain ⟨⟨slot, digit⟩, rfl⟩ := finProdFinEquiv.surjective pointBit
          simp only [Equiv.symm_apply_apply]
          exact pointsPreserved (acceptedIndex split fresh) slot digit
    · funext request bit
      change _ = pendingRecord (state.advance permutation split (menu candidate)) data request bit
      rw [advance_pendingRecord]
      exact originalPreserved (pendingIndex split request) bit
  · apply advance_wellScheduled state permutation split (menu candidate) targets previous
    intro index
    exact clean (acceptedIndex split index) index.isLt

end Algebraic.MassProduction.Nonuniform.BufferModel
