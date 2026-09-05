/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Gate

/-!
# Sequential fixed-width evaluator wire layout -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationLayout

theorem sizeAt_eq_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    sizeAt inputWidth gateBound slot.val =
      GateFormula.gateSize inputWidth gateBound slot := by
  unfold sizeAt
  rw [dite_eq_left slot.isLt]

theorem prefixSize_succ_internal (inputWidth gateBound count : Nat) :
    prefixSize inputWidth gateBound (count + 1) =
      prefixSize inputWidth gateBound count +
        sizeAt inputWidth gateBound count := by
  rfl

theorem prefixSize_mono_internal (inputWidth gateBound : Nat)
    {first second : Nat} (hbound : first ≤ second) :
    prefixSize inputWidth gateBound first ≤
      prefixSize inputWidth gateBound second := by
  induction second with
  | zero =>
      have hfirst : first = 0 := by omega
      subst first
      exact le_rfl
  | succ second ih =>
      by_cases hequal : first = second + 1
      · subst first
        exact le_rfl
      · have hle : first ≤ second := by omega
        exact (ih hle).trans (by rw [prefixSize_succ_internal]; omega)

theorem stepEnd_eq_prefix_succ_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    stepAvailable inputWidth gateBound slot +
        GateFormula.gateSize inputWidth gateBound slot =
      baseWireCount inputWidth gateBound +
        prefixSize inputWidth gateBound (slot.val + 1) := by
  rw [prefixSize_succ_internal, sizeAt_eq_internal slot]
  unfold stepAvailable
  omega

theorem stepOutputWire_lt_stepEnd_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    stepOutputWire inputWidth gateBound slot <
      stepAvailable inputWidth gateBound slot +
        GateFormula.gateSize inputWidth gateBound slot := by
  unfold stepOutputWire
  have hpositive :
      0 < GateFormula.gateSize inputWidth gateBound slot := by
    simp only [GateFormula.gateSize]
    omega
  omega

theorem earlier_output_lt_stepAvailable_internal
    {inputWidth gateBound : Nat} (slot : Fin gateBound)
    (earlier : Fin slot.val) :
    stepOutputWire inputWidth gateBound (earlierSlot slot earlier) <
      stepAvailable inputWidth gateBound slot := by
  have houtput :=
    stepOutputWire_lt_stepEnd_internal
      (inputWidth := inputWidth) (gateBound := gateBound)
      (earlierSlot slot earlier)
  rw [stepEnd_eq_prefix_succ_internal] at houtput
  simp only [earlierSlot] at houtput
  have hprefix := prefixSize_mono_internal inputWidth gateBound
    (Nat.succ_le_of_lt earlier.isLt)
  unfold stepAvailable
  exact lt_of_lt_of_le houtput
    (Nat.add_le_add_left hprefix (baseWireCount inputWidth gateBound))

theorem size_sourceFormula_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) (source : Fin (inputWidth + slot.val)) :
    (sourceFormula inputWidth gateBound slot source).size = 1 := by
  refine Fin.addCases ?_ ?_ source
  · intro input
    simp [sourceFormula, BoolFormula.size]
  · intro earlier
    simp [sourceFormula, BoolFormula.size]

theorem size_stepFormula_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    (stepFormula inputWidth gateBound slot).size =
      GateFormula.gateSize inputWidth gateBound slot := by
  unfold stepFormula
  apply GateFormula.size_gate
  exact size_sourceFormula_internal slot

theorem rawOutputWire_stepFormula_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    BoolFormula.rawOutputWire
        (stepAvailable inputWidth gateBound slot)
        (stepFormula inputWidth gateBound slot) =
      stepOutputWire inputWidth gateBound slot := by
  unfold BoolFormula.rawOutputWire stepOutputWire
  rw [size_stepFormula_internal]

theorem vars_sourceFormula_lt_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    ∀ source wire,
      wire ∈ (sourceFormula inputWidth gateBound slot source).vars →
      wire < stepAvailable inputWidth gateBound slot := by
  intro source
  refine Fin.addCases ?_ ?_ source
  · intro input wire hwire
    simp only [sourceFormula, Fin.addCases_left, BoolFormula.vars,
      Finset.mem_singleton] at hwire
    subst wire
    unfold stepAvailable baseWireCount
    omega
  · intro earlier wire hwire
    simp only [sourceFormula, Fin.addCases_right, BoolFormula.vars,
      Finset.mem_singleton] at hwire
    subst wire
    exact earlier_output_lt_stepAvailable_internal slot earlier

theorem vars_stepFormula_lt_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    ∀ wire ∈ (stepFormula inputWidth gateBound slot).vars,
      wire < stepAvailable inputWidth gateBound slot := by
  unfold stepFormula
  apply GateFormula.vars_gate_lt
  · unfold stepAvailable baseWireCount
    omega
  · exact vars_sourceFormula_lt_internal slot

end EvaluationLayout

end Description

end FixedWidth

end CircuitCode

end Complexity
