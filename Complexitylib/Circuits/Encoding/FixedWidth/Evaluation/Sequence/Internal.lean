/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Sequence.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Evaluation.Layout
import Complexitylib.Circuits.Encoding.Fragment
import Complexitylib.Circuits.Encoding.Formula

/-!
# Sequential fixed-width gate evaluation -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

namespace EvaluationSequence

open EvaluationLayout

theorem length_stepCircuit_internal {inputWidth gateBound : Nat}
    (slot : Fin gateBound) :
    (stepCircuit inputWidth gateBound slot).length =
      GateFormula.gateSize inputWidth gateBound slot := by
  rw [stepCircuit, BoolFormula.length_compileRaw,
    EvaluationLayout.size_stepFormula]

theorem length_stepCircuitAt_internal (inputWidth gateBound index : Nat) :
    (stepCircuitAt inputWidth gateBound index).length =
      sizeAt inputWidth gateBound index := by
  unfold stepCircuitAt sizeAt
  split
  · exact length_stepCircuit_internal _
  · rfl

theorem length_prefixCircuit_internal (inputWidth gateBound count : Nat) :
    (prefixCircuit inputWidth gateBound count).length =
      prefixSize inputWidth gateBound count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prefixCircuit, List.length_append, ih,
        length_stepCircuitAt_internal, prefixSize_succ]

theorem length_circuit_internal (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).length =
      prefixSize inputWidth gateBound gateBound := by
  exact length_prefixCircuit_internal inputWidth gateBound gateBound

theorem topologicallyWellFormed_stepCircuit_internal
    {inputWidth gateBound : Nat} (slot : Fin gateBound) :
    (stepCircuit inputWidth gateBound slot).TopologicallyWellFormed
      (stepAvailable inputWidth gateBound slot) := by
  have hcode : codeWidth inputWidth gateBound ≠ 0 :=
    NeZero.ne (codeWidth inputWidth gateBound)
  let : NeZero (stepAvailable inputWidth gateBound slot) := ⟨by
    unfold stepAvailable baseWireCount
    omega⟩
  unfold stepCircuit
  exact BoolFormula.topologicallyWellFormed_compileRaw _ _
    (vars_stepFormula_lt slot)

theorem topologicallyWellFormed_prefixCircuit_internal
    (inputWidth gateBound count : Nat) (hcount : count ≤ gateBound) :
    (prefixCircuit inputWidth gateBound count).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) := by
  induction count with
  | zero =>
      simp [prefixCircuit, RawCircuit.TopologicallyWellFormed]
  | succ count ih =>
      have hindex : count < gateBound := by omega
      rw [prefixCircuit, RawCircuit.topologicallyWellFormed_append]
      constructor
      · exact ih (by omega)
      · rw [stepCircuitAt, dite_eq_left hindex]
        have havailable :
            baseWireCount inputWidth gateBound +
                (prefixCircuit inputWidth gateBound count).length =
              stepAvailable inputWidth gateBound ⟨count, hindex⟩ := by
          rw [length_prefixCircuit_internal]
          rfl
        rw [havailable]
        exact topologicallyWellFormed_stepCircuit_internal ⟨count, hindex⟩

theorem topologicallyWellFormed_circuit_internal
    (inputWidth gateBound : Nat) :
    (circuit inputWidth gateBound).TopologicallyWellFormed
      (baseWireCount inputWidth gateBound) := by
  exact topologicallyWellFormed_prefixCircuit_internal
    inputWidth gateBound gateBound (Nat.le_refl gateBound)

end EvaluationSequence

end Description

end FixedWidth

end CircuitCode

end Complexity
