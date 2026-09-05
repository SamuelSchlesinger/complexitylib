/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Padded.Defs
import Complexitylib.Circuits.Encoding.FixedWidth

/-!
# Padded fixed-width raw-circuit semantics -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

private theorem fromBits_replicate_false : ∀ width : Nat,
    Nat.fromBits (List.replicate width false) = 0
  | 0 => rfl
  | width + 1 => by
      simp [List.replicate_succ, Nat.fromBits,
        fromBits_replicate_false width]

private theorem zero_wellFormedAt {width available : Nat}
    (hpositive : 0 < available) :
    (GateSlot.zero width).WellFormedAt available := by
  unfold GateSlot.WellFormedAt GateSlot.input0Value
    GateSlot.input1Value GateSlot.zero
  simpa [BitString.toList, Nat.fromBitsLE,
    fromBits_replicate_false] using
    And.intro hpositive hpositive

theorem slot_wellFormedAt_of_wellFormed_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) (slot : Fin gateBound) :
    (description.slots slot).WellFormedAt (inputWidth + slot.val) := by
  by_cases hactive : slot.val < description.gateCountNat
  · have hslot := hdescription.2.1
      ⟨slot.val, hactive⟩
    simpa [activeSlot] using hslot
  · have hinactive : description.gateCountNat ≤ slot.val :=
      Nat.le_of_not_gt hactive
    rw [hdescription.2.2 slot hinactive]
    apply zero_wellFormedAt
    have hpositive : 0 < slot.val :=
      lt_of_lt_of_le hdescription.1 hinactive
    omega

theorem length_toPaddedRawCircuit_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toPaddedRawCircuit.length = gateBound := by
  simp [toPaddedRawCircuit]

theorem take_toPaddedRawCircuit_gateCount_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    description.toPaddedRawCircuit.take description.gateCountNat =
      description.toRawCircuit := by
  apply List.ext_get
  · simp [toPaddedRawCircuit]
    have hcount := description.gateCount.isLt
    change description.gateCountNat < gateBound + 1 at hcount
    omega
  · intro index hleft hright
    simp [toPaddedRawCircuit, toRawCircuit, activeSlot]

theorem get_toPaddedRawCircuit_internal
    {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (slot : Fin description.toPaddedRawCircuit.length) :
    description.toPaddedRawCircuit.get slot =
      (description.slots
        ⟨slot.val, by simpa [length_toPaddedRawCircuit_internal]
          using slot.isLt⟩).toRawGate := by
  simp only [List.get_eq_getElem]
  simp [toPaddedRawCircuit]

theorem topologicallyWellFormed_toPaddedRawCircuit_internal
    {inputWidth gateBound : Nat}
    {description : Description inputWidth gateBound}
    (hdescription : description.WellFormed) :
    description.toPaddedRawCircuit.TopologicallyWellFormed inputWidth := by
  intro slot
  rw [get_toPaddedRawCircuit_internal]
  exact slot_wellFormedAt_of_wellFormed_internal hdescription
    ⟨slot.val, by simpa [length_toPaddedRawCircuit_internal]
      using slot.isLt⟩

end Description

end FixedWidth

end CircuitCode

end Complexity
