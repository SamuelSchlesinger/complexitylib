/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PointConflicts
public import Complexitylib.Algebraic.MassProduction.Nonuniform.EnumeratedClean

/-!
# Interpreting a flat menu point array

An equivalence identifies the sorting-network records with candidate,
request, and point-slot triples. Candidate identifiers are fixed and
injective. Under this layout the point-conflict circuit computes precisely
the enumerated recovery-set conflict predicate for each candidate.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MenuPointLayout

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- The candidate identifier of each flat point record. -/
def groups (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (codes : Fin candidates → Fin groupWidth → Bool) (index : Fin (networkRecords depth)) :=
  codes (layout.symm index).1

/-- The occupied points represented by active source flags. -/
def occupied (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs) (input : Fin inputs → Bool) :
    Finset (Fin keyWidth → Bool) :=
  EnumeratedClean.pointSet (fun source => (sourceFlags source).eval input)
    (fun source bit => (sourceKeys source bit).eval input)

/-- Source matching is exactly membership in the occupied point set. -/
theorem mem_occupied_iff
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs) (input : Fin inputs → Bool)
    (point : Fin keyWidth → Bool) :
    point ∈ occupied sourceKeys sourceFlags input ↔
      ∃ source, (fun bit => (sourceKeys source bit).eval input) = point ∧
        (sourceFlags source).eval input = true := by
  rw [occupied, EnumeratedClean.mem_pointSet_iff]
  simp only [and_comm]

/-- The flat circuit computes the exact conflict predicate of one candidate. -/
theorem pointCircuit_eval_iff
    (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (codes : Fin candidates → Fin groupWidth → Bool) (codesInjective : Function.Injective codes)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (input : Fin inputs → Bool) (candidate : Fin candidates) (request : Fin requests) (slot : Fin slots) :
    (PointConflicts.circuit (groups layout codes) valid keys sourceKeys sourceFlags recordCount).eval
      DeMorgan.interpretation input (layout (candidate, request, slot)) = true ↔
      EnumeratedClean.Conflict
        (fun request slot => (valid (layout (candidate, request, slot))).eval input)
        (fun request slot bit => (keys (layout (candidate, request, slot)) bit).eval input)
        (occupied sourceKeys sourceFlags input) request slot := by
  rw [PointConflicts.circuit_eval_iff]
  change _ ↔ (valid (layout (candidate, request, slot))).eval input = true ∧ _
  apply and_congr_right
  intro _
  constructor
  · intro conflict
    rcases conflict with collision | inOccupied
    · obtain ⟨other, different, sameGroup, validOther, sameKey⟩ := collision
      obtain ⟨⟨otherCandidate, otherRequest, otherSlot⟩, rfl⟩ := layout.surjective other
      simp only [groups, Equiv.symm_apply_apply] at sameGroup
      have sameCandidate := codesInjective sameGroup
      subst otherCandidate
      exact Or.inl ⟨otherRequest, otherSlot,
        fun equal => different (congrArg (fun pair => layout (candidate, pair)) equal),
        validOther, sameKey⟩
    · exact Or.inr ((mem_occupied_iff sourceKeys sourceFlags input _).mpr inOccupied)
  · intro conflict
    rcases conflict with collision | inOccupied
    · obtain ⟨otherRequest, otherSlot, different, validOther, sameKey⟩ := collision
      refine Or.inl ⟨layout (candidate, otherRequest, otherSlot), ?_, ?_, validOther, sameKey⟩
      · intro equal
        exact different (congrArg Prod.snd (layout.injective equal))
      · simp only [groups, Equiv.symm_apply_apply]
    · exact Or.inr ((mem_occupied_iff sourceKeys sourceFlags input _).mp inOccupied)

end Algebraic.MassProduction.Nonuniform.MenuPointLayout
