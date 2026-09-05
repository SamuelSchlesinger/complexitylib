/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Formula.Defs
public import Complexitylib.Circuits.Encoding.Internal.Fragment

/-!
# Boolean-formula raw compiler internals

This module proves the structural and semantic invariants of the proof-free
formula compiler. Public statements are re-exported by
`Complexitylib.Circuits.Encoding.Formula`.
-/


public section

namespace Complexity

namespace BoolFormula

open CircuitCode

/-- Internal exact gate-count theorem for formula compilation. -/
theorem length_compileRaw_internal (available : ℕ) (formula : BoolFormula) :
    (compileRaw available formula).length = formula.size := by
  induction formula generalizing available with
  | var i => simp [compileRaw, size]
  | tru => simp [compileRaw, size]
  | fls => simp [compileRaw, size]
  | neg formula ih => simp [compileRaw, size, ih]
  | conj left right ihLeft ihRight =>
      simp [compileRaw, size, ihLeft, ihRight]
      omega
  | disj left right ihLeft ihRight =>
      simp [compileRaw, size, ihLeft, ihRight]
      omega

/-- Internal bound placing the output inside its compiled fragment. -/
theorem rawOutputWire_lt_internal (available : ℕ) (formula : BoolFormula) :
    rawOutputWire available formula < available + formula.size := by
  have hsize := formula.one_le_size
  simp only [rawOutputWire]
  omega

/-- Internal equation identifying the fragment's final wire. -/
theorem rawOutputWire_eq_internal (available : ℕ) (formula : BoolFormula) :
    rawOutputWire available formula =
      available + (compileRaw available formula).length - 1 := by
  simp [rawOutputWire, length_compileRaw_internal]

theorem evalAux?_compileRaw_of_agree_internal (available : ℕ) [NeZero available]
    (formula : BoolFormula) (assignment : ℕ → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hvars : ∀ i ∈ formula.vars, i < available)
    (hagree : ∀ i ∈ formula.vars, wires[i]? = some (assignment i)) :
    ∃ result,
      RawCircuit.evalAux? (compileRaw available formula) wires = some result ∧
        result.size = wires.size + formula.size ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        result[rawOutputWire available formula]? = some (formula.eval assignment) := by
  induction formula generalizing available wires with
  | var i =>
      have hvalue := hagree i (by simp [vars])
      refine ⟨wires.push (assignment i), ?_, by simp [size], ?_, ?_⟩
      · simp [compileRaw, RawCircuit.evalAux?, CircuitCode.RawGate.copy,
          hvalue, CircuitCode.RawGate.eval]
      · intro j hj
        rw [Array.getElem?_push, ite_eq_right (by omega)]
      · have hwire : rawOutputWire available (.var i) = wires.size := by
          simp [rawOutputWire, size, hsize]
        rw [hwire]
        exact Array.getElem?_push_size
  | tru =>
      have havailable : 0 < available := by
        have := NeZero.ne available
        omega
      have hzero : 0 < wires.size := by omega
      have hvalue : wires[0]? = some wires[0] := Array.getElem?_eq_getElem hzero
      refine ⟨wires.push true, ?_, by simp [size], ?_, ?_⟩
      · simp [compileRaw, RawCircuit.evalAux?, CircuitCode.RawGate.constant,
          hvalue, CircuitCode.RawGate.eval]
      · intro j hj
        rw [Array.getElem?_push, ite_eq_right (by omega)]
      · have hwire : rawOutputWire available .tru = wires.size := by
          simp [rawOutputWire, size, hsize]
        rw [hwire]
        exact Array.getElem?_push_size
  | fls =>
      have havailable : 0 < available := by
        have := NeZero.ne available
        omega
      have hzero : 0 < wires.size := by omega
      have hvalue : wires[0]? = some wires[0] := Array.getElem?_eq_getElem hzero
      refine ⟨wires.push false, ?_, by simp [size], ?_, ?_⟩
      · simp [compileRaw, RawCircuit.evalAux?, CircuitCode.RawGate.constant,
          hvalue, CircuitCode.RawGate.eval]
      · intro j hj
        rw [Array.getElem?_push, ite_eq_right (by omega)]
      · have hwire : rawOutputWire available .fls = wires.size := by
          simp [rawOutputWire, size, hsize]
        rw [hwire]
        exact Array.getElem?_push_size
  | neg formula ih =>
      obtain ⟨formulaResult, heval, hresultSize, hpreserved, houtput⟩ :=
        ih available wires hsize (by simpa [vars] using hvars)
          (by simpa [vars] using hagree)
      let value := !(formula.eval assignment)
      refine ⟨formulaResult.push value, ?_, ?_, ?_, ?_⟩
      · rw [compileRaw, RawCircuit.evalAux?_append_internal, heval]
        simp [RawCircuit.evalAux?, CircuitCode.RawGate.copy, houtput, value,
          CircuitCode.RawGate.eval]
      · simp only [Array.size_push, hresultSize, size]
        omega
      · intro i hi
        rw [Array.getElem?_push, ite_eq_right (by omega)]
        exact hpreserved i hi
      · have hwire : rawOutputWire available (.neg formula) = formulaResult.size := by
          simp only [rawOutputWire, size, hresultSize, hsize]
          omega
        rw [hwire]
        simp [value, eval]
  | conj left right ihLeft ihRight =>
      have hvarsLeft : ∀ i ∈ left.vars, i < available := by
        intro i hi
        exact hvars i (Finset.mem_union_left _ hi)
      have hagreeLeft : ∀ i ∈ left.vars, wires[i]? = some (assignment i) := by
        intro i hi
        exact hagree i (Finset.mem_union_left _ hi)
      obtain ⟨leftResult, hevalLeft, hleftSize, hleftPreserved, hleftOutput⟩ :=
        ihLeft available wires hsize hvarsLeft hagreeLeft
      have hleftSize' : leftResult.size = available + left.size := by
        omega
      let : NeZero (available + left.size) := ⟨by
        have := NeZero.ne available
        omega⟩
      have hvarsRight : ∀ i ∈ right.vars, i < available + left.size := by
        intro i hi
        have := hvars i (Finset.mem_union_right _ hi)
        omega
      have hagreeRight :
          ∀ i ∈ right.vars, leftResult[i]? = some (assignment i) := by
        intro i hi
        have hiAvailable := hvars i (Finset.mem_union_right _ hi)
        rw [hleftPreserved i (by omega)]
        exact hagree i (Finset.mem_union_right _ hi)
      obtain ⟨rightResult, hevalRight, hrightSize, hrightPreserved, hrightOutput⟩ :=
        ihRight (available + left.size) leftResult hleftSize'
          hvarsRight hagreeRight
      have hleftWireLt : rawOutputWire available left < leftResult.size := by
        rw [hleftSize']
        exact rawOutputWire_lt_internal available left
      have hleftOutput' :
          rightResult[rawOutputWire available left]? = some (left.eval assignment) := by
        rw [hrightPreserved _ hleftWireLt]
        exact hleftOutput
      let value := left.eval assignment && right.eval assignment
      refine ⟨rightResult.push value, ?_, ?_, ?_, ?_⟩
      · rw [compileRaw, RawCircuit.evalAux?_append_internal, hevalLeft]
        simp only [Option.bind_some]
        rw [RawCircuit.evalAux?_append_internal, hevalRight]
        simp [RawCircuit.evalAux?, hleftOutput', hrightOutput, value,
          CircuitCode.RawGate.eval]
      · simp only [Array.size_push, hrightSize, hleftSize, size]
        omega
      · intro i hi
        rw [Array.getElem?_push, ite_eq_right (by omega)]
        rw [hrightPreserved i (by omega)]
        exact hleftPreserved i hi
      · have hwire : rawOutputWire available (.conj left right) = rightResult.size := by
          simp only [rawOutputWire, size, hrightSize, hleftSize, hsize]
          omega
        rw [hwire]
        simp [value, eval]
  | disj left right ihLeft ihRight =>
      have hvarsLeft : ∀ i ∈ left.vars, i < available := by
        intro i hi
        exact hvars i (Finset.mem_union_left _ hi)
      have hagreeLeft : ∀ i ∈ left.vars, wires[i]? = some (assignment i) := by
        intro i hi
        exact hagree i (Finset.mem_union_left _ hi)
      obtain ⟨leftResult, hevalLeft, hleftSize, hleftPreserved, hleftOutput⟩ :=
        ihLeft available wires hsize hvarsLeft hagreeLeft
      have hleftSize' : leftResult.size = available + left.size := by
        omega
      let : NeZero (available + left.size) := ⟨by
        have := NeZero.ne available
        omega⟩
      have hvarsRight : ∀ i ∈ right.vars, i < available + left.size := by
        intro i hi
        have := hvars i (Finset.mem_union_right _ hi)
        omega
      have hagreeRight :
          ∀ i ∈ right.vars, leftResult[i]? = some (assignment i) := by
        intro i hi
        have hiAvailable := hvars i (Finset.mem_union_right _ hi)
        rw [hleftPreserved i (by omega)]
        exact hagree i (Finset.mem_union_right _ hi)
      obtain ⟨rightResult, hevalRight, hrightSize, hrightPreserved, hrightOutput⟩ :=
        ihRight (available + left.size) leftResult hleftSize'
          hvarsRight hagreeRight
      have hleftWireLt : rawOutputWire available left < leftResult.size := by
        rw [hleftSize']
        exact rawOutputWire_lt_internal available left
      have hleftOutput' :
          rightResult[rawOutputWire available left]? = some (left.eval assignment) := by
        rw [hrightPreserved _ hleftWireLt]
        exact hleftOutput
      let value := left.eval assignment || right.eval assignment
      refine ⟨rightResult.push value, ?_, ?_, ?_, ?_⟩
      · rw [compileRaw, RawCircuit.evalAux?_append_internal, hevalLeft]
        simp only [Option.bind_some]
        rw [RawCircuit.evalAux?_append_internal, hevalRight]
        simp [RawCircuit.evalAux?, hleftOutput', hrightOutput, value,
          CircuitCode.RawGate.eval]
      · simp only [Array.size_push, hrightSize, hleftSize, size]
        omega
      · intro i hi
        rw [Array.getElem?_push, ite_eq_right (by omega)]
        rw [hrightPreserved i (by omega)]
        exact hleftPreserved i hi
      · have hwire : rawOutputWire available (.disj left right) = rightResult.size := by
          simp only [rawOutputWire, size, hrightSize, hleftSize, hsize]
          omega
        rw [hwire]
        simp [value, eval]

/-- Internal semantic correctness theorem for formula fragments. -/
theorem evalAux?_compileRaw_internal (available : ℕ) [NeZero available]
    (formula : BoolFormula) (assignment : ℕ → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hinput : ∀ i < available, wires[i]? = some (assignment i))
    (hvars : ∀ i ∈ formula.vars, i < available) :
    ∃ result,
      RawCircuit.evalAux? (compileRaw available formula) wires = some result ∧
        result.size = wires.size + formula.size ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        result[rawOutputWire available formula]? = some (formula.eval assignment) := by
  apply evalAux?_compileRaw_of_agree_internal available formula assignment wires hsize hvars
  intro i hi
  exact hinput i (hvars i hi)

/-- Internal topological correctness theorem for formula fragments. -/
theorem topologicallyWellFormed_compileRaw_internal (available : ℕ)
    [NeZero available] (formula : BoolFormula)
    (hvars : ∀ i ∈ formula.vars, i < available) :
    (compileRaw available formula).TopologicallyWellFormed available := by
  let wires := Array.replicate available false
  have hsize : wires.size = available := by simp [wires]
  have hinput : ∀ i < available, wires[i]? = some false := by
    intro i hi
    simp [wires, hi]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileRaw_internal available formula (fun _ => false) wires
      hsize hinput hvars
  have htop :=
    (RawCircuit.evalAux?_isSome_iff (compileRaw available formula) wires).mp
      (by simp [heval])
  simpa [hsize] using htop

end BoolFormula

end Complexity
