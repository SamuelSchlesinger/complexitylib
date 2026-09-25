/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MenuClean
public import Complexitylib.Algebraic.MassProduction.Nonuniform.SelectRows

/-!
# Selecting disjoint requests from an enumerated candidate menu

This circuit computes the clean flags of all enumerated recovery sets and
selects a clean prefix from one successful candidate. Original request
payloads are preserved as a permutation. The remaining obligations for a
complete geometric scheduler are point generation, a menu guarantee for the
encoded state, and iteration of the resulting phase.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MenuSelection

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Recovery set represented by one candidate/request's valid point slots. -/
def requestSet
    (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (candidate : Fin candidates) (request : Fin requests) :=
  EnumeratedClean.pointSet (fun slot => (valid (layout (candidate, request, slot))).eval input)
    (fun slot bit => (keys (layout (candidate, request, slot)) bit).eval input)

/-- Cleanliness of the represented recovery set in its candidate. -/
def RequestClean
    (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (candidate : Fin candidates) (request : Fin requests) : Prop :=
  Clean (fun request (_ : Unit) => requestSet layout valid keys input candidate request)
    (MenuPointLayout.occupied sourceKeys sourceFlags input) (fun _ => ()) request

/-- The complete clean-test and selection circuit for an enumerated menu. -/
noncomputable def circuit
    (layout : (Fin (networkRecords menuDepth) × Fin (networkRecords requestDepth) × Fin slots) ≃
      Fin (networkRecords depth))
    (codes : Fin (networkRecords menuDepth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :=
  SelectRows.circuit (MenuClean.circuit layout codes valid keys sourceKeys sourceFlags recordCount)
    payloads positive fits

/-- The chosen candidate preserves all request payloads and has a clean
prefix of the requested size. Distinct payloads can be ensured by hardwired
request identifiers. -/
theorem circuit_selects
    (layout : (Fin (networkRecords menuDepth) × Fin (networkRecords requestDepth) × Fin slots) ≃
      Fin (networkRecords depth))
    (codes : Fin (networkRecords menuDepth) → Fin groupWidth → Bool)
    (codesInjective : Function.Injective codes)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth)
    (input : Fin inputs → Bool)
    (withinRequest : ∀ candidate request left right,
      (valid (layout (candidate, request, left))).eval input = true →
      (valid (layout (candidate, request, right))).eval input = true →
      (fun bit => (keys (layout (candidate, request, left)) bit).eval input) =
        (fun bit => (keys (layout (candidate, request, right)) bit).eval input) → left = right)
    (available : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      RequestClean layout valid keys sourceKeys sourceFlags input candidate request})
    (distinct : ∀ candidate, Function.Injective (fun request : Fin (networkRecords requestDepth) =>
      fun bit => (payloads (finProdFinEquiv (candidate, request)) bit).eval input)) :
    ∃ candidate, ∃ order : Equiv.Perm (Fin (networkRecords requestDepth)),
      (∀ request bit, flatRecords
        ((circuit layout codes valid keys sourceKeys sourceFlags recordCount payloads positive fits).eval
          DeMorgan.interpretation input) request (Fin.natAdd 1 bit) =
            (payloads (finProdFinEquiv (candidate, order request)) bit).eval input) ∧
      ∀ request : Fin (networkRecords requestDepth), request.val < needed →
        RequestClean layout valid keys sourceKeys sourceFlags input candidate (order request) := by
  let flags := MenuClean.circuit layout codes valid keys sourceKeys sourceFlags recordCount
  have flagsCorrect (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth)) :
      flags.eval DeMorgan.interpretation input (finProdFinEquiv (candidate, request)) = true ↔
        RequestClean layout valid keys sourceKeys sourceFlags input candidate request :=
    MenuClean.circuit_eval_iff layout codes codesInjective valid keys sourceKeys sourceFlags
      recordCount input candidate request (withinRequest candidate)
  have enough : ∃ candidate, needed ≤ Nat.card {request : Fin (networkRecords requestDepth) //
      flags.eval DeMorgan.interpretation input (finProdFinEquiv (candidate, request)) = true} := by
    obtain ⟨candidate, enough⟩ := available
    refine ⟨candidate, ?_⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight (flagsCorrect candidate))]
    exact enough
  have recordsDistinct : ∀ candidate, Function.Injective (SelectRows.record flags payloads input candidate) := by
    intro candidate left right equal
    apply distinct candidate
    funext bit
    have sameBit := congrFun equal (Fin.natAdd 1 bit)
    simpa only [SelectRows.record, Fin.append_right] using sameBit
  obtain ⟨candidate, order, sameRecords, selected⟩ :=
    SelectRows.circuit_selects_indices flags payloads positive fits input enough recordsDistinct
  refine ⟨candidate, order, ?_, ?_⟩
  · intro request bit
    change flatRecords ((SelectRows.circuit flags payloads positive fits).eval
      DeMorgan.interpretation input) request (Fin.natAdd 1 bit) = _
    rw [sameRecords, SelectRows.record, Fin.append_right]
  · intro request before
    exact (flagsCorrect candidate (order request)).mp (selected request before)

/-- Explicit bound for the full enumerated-menu evaluator and selector. -/
theorem circuit_cost_le
    (layout : (Fin (networkRecords menuDepth) × Fin (networkRecords requestDepth) × Fin slots) ≃
      Fin (networkRecords depth))
    (codes : Fin (networkRecords menuDepth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (payloads : Fin (networkRecords menuDepth * networkRecords requestDepth) →
      Fin payloadWidth → DeMorgan.Wiring inputs)
    (positive : 0 < needed) (fits : needed ≤ networkRecords requestDepth) :
    (circuit layout codes valid keys sourceKeys sourceFlags recordCount payloads positive fits).cost
      DeMorgan.standardCost ≤
      (((256 * networkRecords depth * (depth + (groupWidth + (1 + keyWidth)) + 1) ^ 5 +
        128 * networkRecords routingDepth * (routingDepth + keyWidth + 1 + 2) ^ 5) +
        2 * networkRecords depth) +
        (networkRecords menuDepth * networkRecords requestDepth) * (slots + 1)) +
      (networkRecords menuDepth *
        (48 * requestDepth * requestDepth * networkRecords requestDepth * (1 + payloadWidth)) +
        48 * menuDepth * menuDepth * networkRecords menuDepth *
          (1 + CandidateSelection.rowBits requestDepth payloadWidth)) := by
  apply (SelectRows.circuit_cost_le _ payloads positive fits).trans
  exact Nat.add_le_add_right (MenuClean.circuit_cost_le layout codes valid keys sourceKeys sourceFlags recordCount) _

end Algebraic.MassProduction.Nonuniform.MenuSelection
