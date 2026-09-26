/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.DuplicateFlags
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOrCircuit
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MaskedOr

/-!
# Shared conflict detection for all candidate points

Each point carries a fixed candidate identifier and a validity flag. Equal
points from different candidates do not collide. Invalid slots do not cause
conflicts. One source array represents occupied points for the whole menu.
The circuit combines duplicate detection and shared occupancy lookup and
returns conflict flags in original point order.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.PointConflicts

open Sorting

set_option backward.isDefEq.respectTransparency false

private theorem append_eq_iff {a c : Fin left → Bool} {b d : Fin right → Bool} :
    Fin.append a b = Fin.append c d ↔ a = c ∧ b = d := by
  constructor
  · intro equal
    constructor
    · funext bit
      simpa only [Fin.append_left] using congrFun equal (Fin.castAdd right bit)
    · funext bit
      simpa only [Fin.append_right] using congrFun equal (Fin.natAdd left bit)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Group and validity tags precede the point address in the collision key. -/
def taggedKeys
    (groups : Fin (networkRecords depth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (index : Fin (networkRecords depth)) : Fin (groupWidth + (1 + keyWidth)) → DeMorgan.Wiring inputs :=
  Fin.append (fun bit => .constant (groups index bit))
    (Fin.append (fun _ : Fin 1 => valid index) (keys index))

/-- Equality of collision keys means equality of each of their three fields. -/
theorem taggedKeys_eq_iff
    (groups : Fin (networkRecords depth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (left right : Fin (networkRecords depth)) :
    (fun bit => (taggedKeys groups valid keys left bit).eval input) =
      (fun bit => (taggedKeys groups valid keys right bit).eval input) ↔
        groups left = groups right ∧ (valid left).eval input = (valid right).eval input ∧
          (fun bit => (keys left bit).eval input) = (fun bit => (keys right bit).eval input) := by
  simp only [taggedKeys, DeMorgan.Wiring.eval_finAppend, DeMorgan.Wiring.eval_constant,
    append_eq_iff]
  constructor
  · rintro ⟨sameGroup, sameValidity, sameKey⟩
    exact ⟨sameGroup, congrFun sameValidity 0, sameKey⟩
  · rintro ⟨sameGroup, sameValidity, sameKey⟩
    exact ⟨sameGroup, funext (fun _ => sameValidity), sameKey⟩

/-- One shared occupied-point lookup, with one Boolean flag per query. -/
noncomputable def occupancyCircuit
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :=
  (BatchOr.circuit sourceKeys (fun source (_ : Fin 1) => sourceFlags source) keys recordCount).mapOutputs
    (fun index => finProdFinEquiv (index, (0 : Fin 1)))

/-- `occupancyCircuit` has exactly the gates of `BatchOr.circuit`; the surrounding wiring adds
none. -/
@[simp] theorem occupancyCircuit_size
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :
    (occupancyCircuit sourceKeys sourceFlags keys recordCount).size =
      (BatchOr.circuit sourceKeys (fun source (_ : Fin 1) => sourceFlags source) keys
        recordCount).size := by
  simp [occupancyCircuit]

/-- Occupancy is exactly the existence of an active matching source. -/
theorem occupancyCircuit_eval_iff
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (input : Fin inputs → Bool) (index : Fin (networkRecords depth)) :
    (occupancyCircuit sourceKeys sourceFlags keys recordCount).eval DeMorgan.interpretation input index = true ↔
      ∃ source, (fun bit => (sourceKeys source bit).eval input) =
          (fun bit => (keys index bit).eval input) ∧ (sourceFlags source).eval input = true := by
  rw [occupancyCircuit, Circuit.eval_mapOutputs]
  exact BatchOr.circuit_eval_iff sourceKeys (fun source (_ : Fin 1) => sourceFlags source)
    keys recordCount input index 0

/-- Detect every valid point conflict for all candidates at once. -/
noncomputable def circuit
    (groups : Fin (networkRecords depth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :=
  MaskedOr.circuit (DuplicateFlags.circuit (taggedKeys groups valid keys))
    (occupancyCircuit sourceKeys sourceFlags keys recordCount) (DeMorgan.Wiring.circuit valid)

/-- `circuit` has exactly the gates of `MaskedOr.circuit`; the surrounding wiring adds none. -/
@[simp] theorem circuit_size
    (groups : Fin (networkRecords depth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :
    (circuit groups valid keys sourceKeys sourceFlags recordCount).size =
      (MaskedOr.circuit (DuplicateFlags.circuit (taggedKeys groups valid keys))
          (occupancyCircuit sourceKeys sourceFlags keys recordCount)
          (DeMorgan.Wiring.circuit valid)).size := by
  simp [circuit]

/-- Exact conflict semantics, with invalid slots and different candidates excluded. -/
theorem circuit_eval_iff
    (groups : Fin (networkRecords depth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (input : Fin inputs → Bool) (index : Fin (networkRecords depth)) :
    (circuit groups valid keys sourceKeys sourceFlags recordCount).eval
      DeMorgan.interpretation input index = true ↔
      (valid index).eval input = true ∧
        ((∃ other, other ≠ index ∧ groups other = groups index ∧
          (valid other).eval input = true ∧
          (fun bit => (keys other bit).eval input) = (fun bit => (keys index bit).eval input)) ∨
        ∃ source, (fun bit => (sourceKeys source bit).eval input) =
          (fun bit => (keys index bit).eval input) ∧ (sourceFlags source).eval input = true) := by
  rw [circuit, MaskedOr.circuit_eval, DeMorgan.Wiring.circuit_eval,
    Bool.and_eq_true, Bool.or_eq_true, DuplicateFlags.circuit_eval_iff,
    occupancyCircuit_eval_iff]
  simp_rw [taggedKeys_eq_iff]
  constructor
  · rintro ⟨validIndex, collision | occupied⟩
    · obtain ⟨other, different, sameGroup, sameValidity, sameKey⟩ := collision
      exact ⟨validIndex, Or.inl ⟨other, different, sameGroup, sameValidity.trans validIndex, sameKey⟩⟩
    · exact ⟨validIndex, Or.inr occupied⟩
  · rintro ⟨validIndex, collision | occupied⟩
    · obtain ⟨other, different, sameGroup, validOther, sameKey⟩ := collision
      exact ⟨validIndex, Or.inl ⟨other, different, sameGroup, validOther.trans validIndex.symm, sameKey⟩⟩
    · exact ⟨validIndex, Or.inr occupied⟩

/-- The entire menu shares one occupancy scan and one duplicate-detection circuit. -/
theorem circuit_cost_le
    (groups : Fin (networkRecords depth) → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :
    (circuit groups valid keys sourceKeys sourceFlags recordCount).cost DeMorgan.standardCost ≤
      (256 * networkRecords depth * (depth + (groupWidth + (1 + keyWidth)) + 1) ^ 5 +
        128 * networkRecords routingDepth * (routingDepth + keyWidth + 1 + 2) ^ 5) +
        2 * networkRecords depth := by
  rw [circuit, MaskedOr.circuit_cost, DeMorgan.Wiring.circuit_cost, Nat.add_zero]
  apply Nat.add_le_add_right
  apply Nat.add_le_add (DuplicateFlags.circuit_cost_le _)
  rw [occupancyCircuit, Circuit.cost_mapOutputs]
  exact BatchOr.circuit_cost_le _ _ _ recordCount

end Algebraic.MassProduction.Nonuniform.PointConflicts
