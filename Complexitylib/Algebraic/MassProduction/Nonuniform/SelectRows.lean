/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.FlaggedRows
public import Complexitylib.Algebraic.MassProduction.Nonuniform.OrderedPermutation

/-!
# Selecting a candidate from computed clean flags

The clean-flag circuit is evaluated once, request payloads are attached by
free wiring, and the complete candidate-selection circuit chooses one row.
All original records survive as a permutation; the required prefix is clean.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.SelectRows

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Compute the clean flags, attach payloads, and select one complete row. -/
def circuit
    (flags : Circuit DeMorgan.signature inputs (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :=
  (CandidateSelection.circuit menuDepth requestDepth payloadWidth needed positive fits).comp
    (FlaggedRows.circuit flags payloads)

/-- Row selection has exactly the gates of the flagged rows followed by candidate selection. -/
@[simp] theorem circuit_size
    (flags : Circuit DeMorgan.signature inputs
      (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :
    (circuit flags payloads positive fits).size =
      (FlaggedRows.circuit flags payloads).size +
        (CandidateSelection.circuit menuDepth requestDepth payloadWidth needed positive
          fits).size := by
  rfl

/-- One original flagged record, with its complete payload. -/
def record
    (flags : Circuit DeMorgan.signature inputs (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (candidate : Fin (networkRecords menuDepth))
    (request : Fin (networkRecords requestDepth)) : Fin (1 + payloadWidth) → Bool :=
  Fin.append (fun _ : Fin 1 => flags.eval DeMorgan.interpretation input
    (finProdFinEquiv (candidate, request)))
    (fun bit => (payloads (finProdFinEquiv (candidate, request)) bit).eval input)

/-- The output permutes one candidate's original records and has a clean prefix. -/
theorem circuit_selects
    (flags : Circuit DeMorgan.signature inputs (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth)
    (input : Fin inputs → Bool)
    (available : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      flags.eval DeMorgan.interpretation input (finProdFinEquiv (candidate, request)) = true}) :
    ∃ candidate,
      Semantics.SequencePermutes
        (flatRecords ((circuit flags payloads positive fits).eval DeMorgan.interpretation input))
        (record flags payloads input candidate) ∧
      ∀ request : Fin (networkRecords requestDepth), request.val < needed →
        FlagSelection.flag ((circuit flags payloads positive fits).eval
          DeMorgan.interpretation input) request = true := by
  let prepared := (FlaggedRows.circuit flags payloads).eval DeMorgan.interpretation input
  have enough : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      FlagSelection.flag (CandidateSelection.row prepared candidate) request = true} := by
    simpa only [prepared, FlaggedRows.circuit_eval_flag] using available
  obtain ⟨candidate, selectedRow, selectedFlags⟩ :=
    CandidateSelection.circuit_selects positive fits prepared enough
  refine ⟨candidate, ?_, ?_⟩
  · rw [circuit, Circuit.eval_comp]
    change Semantics.SequencePermutes
      (flatRecords ((CandidateSelection.circuit menuDepth requestDepth payloadWidth needed positive fits).eval
        DeMorgan.interpretation prepared)) (record flags payloads input candidate)
    rw [selectedRow]
    have permuted := FlagSelection.circuit_recordsPermute (CandidateSelection.row prepared candidate)
    have original : flatRecords (CandidateSelection.row prepared candidate) =
        record flags payloads input candidate := by
      funext request
      exact FlaggedRows.circuit_eval_record flags payloads input candidate request
    rw [← original]
    exact permuted
  · rw [circuit, Circuit.eval_comp]
    exact selectedFlags

/-- Distinct request payloads give an actual permutation of request indices.
Every accepted index is one of the original clean requests. -/
theorem circuit_selects_indices
    (flags : Circuit DeMorgan.signature inputs (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth)
    (input : Fin inputs → Bool)
    (available : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      flags.eval DeMorgan.interpretation input (finProdFinEquiv (candidate, request)) = true})
    (distinct : ∀ candidate, Function.Injective (record flags payloads input candidate)) :
    ∃ candidate, ∃ order : Equiv.Perm (Fin (networkRecords requestDepth)),
      (∀ request, flatRecords ((circuit flags payloads positive fits).eval
        DeMorgan.interpretation input) request = record flags payloads input candidate (order request)) ∧
      ∀ request : Fin (networkRecords requestDepth), request.val < needed →
        flags.eval DeMorgan.interpretation input (finProdFinEquiv (candidate, order request)) = true := by
  obtain ⟨candidate, permuted, selected⟩ := circuit_selects flags payloads positive fits input available
  obtain ⟨order, sameRecords⟩ := existsIndexPermutation permuted (distinct candidate)
  refine ⟨candidate, order, sameRecords, ?_⟩
  intro request before
  have flagged := selected request before
  change flatRecords ((circuit flags payloads positive fits).eval DeMorgan.interpretation input) request
    (Fin.castAdd payloadWidth (0 : Fin 1)) = true at flagged
  rw [sameRecords, record, Fin.append_left] at flagged
  exact flagged

/-- The flag computation is charged once; both selection sorts have their
explicit linear record-count bounds. -/
theorem circuit_cost_le
    (flags : Circuit DeMorgan.signature inputs (networkRecords menuDepth * networkRecords requestDepth))
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :
    (circuit flags payloads positive fits).cost DeMorgan.standardCost ≤
      flags.cost DeMorgan.standardCost +
        (networkRecords menuDepth *
          (48 * requestDepth * requestDepth * networkRecords requestDepth * (1 + payloadWidth)) +
          48 * menuDepth * menuDepth * networkRecords menuDepth *
            (1 + CandidateSelection.rowBits requestDepth payloadWidth)) := by
  rw [circuit, Circuit.cost_comp, FlaggedRows.circuit_cost]
  exact Nat.add_le_add_left (CandidateSelection.circuit_cost_le positive fits) _

end Algebraic.MassProduction.Nonuniform.SelectRows
