/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Majority.Defs
public import Complexitylib.Circuits.BitString
import Complexitylib.Circuits.Encoding.Threshold.Internal

/-!
# Strict-majority circuits -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

theorem strictMajorityThreshold_le_internal (inputCount : ℕ)
    [NeZero inputCount] :
    strictMajorityThreshold inputCount ≤ inputCount := by
  unfold strictMajorityThreshold
  have hpositive := NeZero.ne inputCount
  omega

theorem length_strictMajorityRawCircuit_internal (inputCount : ℕ) :
    (strictMajorityRawCircuit inputCount).length =
      3 + 2 * inputCount * strictMajorityThreshold inputCount := by
  simp [strictMajorityRawCircuit, Threshold.length_compileRaw_internal]

theorem strictMajorityRawCircuit_wellFormed_internal (inputCount : ℕ)
    [NeZero inputCount] :
    (strictMajorityRawCircuit inputCount).WellFormed inputCount := by
  constructor
  · intro hempty
    have hlength := length_strictMajorityRawCircuit_internal inputCount
    rw [hempty] at hlength
    simp at hlength
    omega
  · apply Threshold.topologicallyWellFormed_compileRaw_internal
    intro i
    exact i.isLt

theorem eval?_strictMajorityRawCircuit_internal (inputCount : ℕ)
    [NeZero inputCount] (input : BitString inputCount) :
    (strictMajorityRawCircuit inputCount).eval? (BitString.toList input) =
      some (decide
        (strictMajorityThreshold inputCount ≤ Fin.countP input)) := by
  let wires := (BitString.toList input).toArray
  have hwiresSize : wires.size = inputCount := by
    simp [wires]
  have hwiresInput : ∀ i : Fin inputCount,
      wires[i.val]? = some (input i) := by
    intro i
    simp [wires, BitString.toList, i.isLt]
  obtain ⟨result, heval, _hresultSize, _hprefix, houtput⟩ :=
    Threshold.evalAux?_compileRaw_internal inputCount
      (strictMajorityThreshold inputCount)
      (fun i : Fin inputCount => i.val) input wires hwiresSize
      (fun i => i.isLt) hwiresInput
  have heval' :
      RawCircuit.evalAux? (strictMajorityRawCircuit inputCount)
          (BitString.toList input).toArray = some result := by
    simpa [strictMajorityRawCircuit, wires] using heval
  have hnonempty :
      (strictMajorityRawCircuit inputCount).isEmpty = false := by
    simp [strictMajorityRawCircuit, Threshold.compileRaw]
  have houtputIndex :
      (BitString.toList input).length +
          (strictMajorityRawCircuit inputCount).length - 1 =
        Threshold.outputWire inputCount inputCount
          (strictMajorityThreshold inputCount) := by
    rw [BitString.length_toList]
    symm
    exact Threshold.outputWire_eq_internal inputCount
      (strictMajorityThreshold inputCount)
      (fun i : Fin inputCount => i.val)
  rw [RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false, heval']
  rw [houtputIndex]
  exact houtput

end CircuitCode

end Complexity
