/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Threshold.Defs
public import Complexitylib.Circuits.Encoding.Fragment
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Raw threshold-fragment internals

This module proves the structural and semantic invariants of the unary dynamic
program defined in `Complexitylib.Circuits.Encoding.Threshold.Defs`. Public
statements are re-exported by `Complexitylib.Circuits.Encoding.Threshold`.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Threshold

/-! ## Exact structural accounting -/

/-- Internal exact size of a two-gate table cell. -/
theorem length_cellGates_internal (available threshold inputRow
    thresholdColumn input : ℕ) :
    (cellGates available threshold inputRow thresholdColumn input).length = 2 := by
  rfl

/-- Internal exact size of a row prefix. -/
theorem length_rowPrefix_internal (available threshold inputRow input columnCount : ℕ) :
    (rowPrefix available threshold inputRow input columnCount).length =
      2 * columnCount := by
  induction columnCount with
  | zero => simp [rowPrefix]
  | succ columnCount ih =>
      simp [rowPrefix, ih, length_cellGates_internal]
      omega

/-- Internal exact size of a sequence of table rows. -/
theorem length_rows_internal (available threshold inputRow inputCount : ℕ)
    (refs : Fin inputCount → ℕ) :
    (rows available threshold inputRow inputCount refs).length =
      2 * inputCount * threshold := by
  induction inputCount generalizing inputRow with
  | zero => simp [rows]
  | succ inputCount ih =>
      simp [rows, length_rowPrefix_internal, ih]
      rw [← Nat.add_mul]
      congr 1
      omega

/-- Internal exact gate count for threshold compilation. -/
theorem length_compileRaw_internal (available threshold : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    (compileRaw available threshold refs).length =
      3 + 2 * inputCount * threshold := by
  simp [compileRaw, length_rows_internal]
  omega

/-- Internal equation identifying the final emitted wire. -/
theorem outputWire_eq_internal (available threshold : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    outputWire available inputCount threshold =
      available + (compileRaw available threshold refs).length - 1 := by
  rw [length_compileRaw_internal]
  simp only [outputWire]
  omega

/-! ## Boolean recurrence -/

/-- Boolean recurrence implemented by one unary-table cell. -/
private theorem thresholdStep (required count : ℕ) (bit : Bool) :
    decide (required + 1 ≤ count + bit.toNat) =
      (decide (required + 1 ≤ count) ||
        (bit && decide (required ≤ count))) := by
  cases bit with
  | false => simp [Bool.toNat]
  | true =>
      simp [Bool.toNat]
      omega

/-! ## Iterative evaluation -/

/-- Internal evaluator equation for one table cell. -/
private theorem evalAux?_cellGates (available threshold inputRow thresholdColumn
    input : ℕ) (bit lower current : Bool) (wires : Array Bool)
    (hsize : wires.size = andWire available threshold inputRow thresholdColumn)
    (hinput : wires[input]? = some bit)
    (hlower : wires[stateWire available threshold inputRow thresholdColumn]? =
      some lower)
    (hcurrent : wires[stateWire available threshold inputRow (thresholdColumn + 1)]? =
      some current) :
    RawCircuit.evalAux?
        (cellGates available threshold inputRow thresholdColumn input) wires =
      some ((wires.push (bit && lower)).push (current || (bit && lower))) := by
  have hstateNe :
      stateWire available threshold inputRow (thresholdColumn + 1) ≠ wires.size := by
    rw [hsize]
    cases inputRow with
    | zero =>
        simp only [andWire, stateWire, falseWire]
        omega
    | succ inputRow =>
        simp only [andWire, stateWire, cellWire]
        omega
  have hcurrentPush :
      (wires.push (bit && lower))[stateWire available threshold inputRow
        (thresholdColumn + 1)]? = some current := by
    rw [Array.getElem?_push, ite_eq_right hstateNe]
    exact hcurrent
  have hand : (wires.push (bit && lower))[andWire available threshold inputRow
      thresholdColumn]? = some (bit && lower) := by
    rw [← hsize]
    exact Array.getElem?_push_size
  simp [cellGates, RawCircuit.evalAux?, RawGate.eval, hinput, hlower,
    hcurrentPush, hand]

/-- Internal row-prefix invariant for the unary dynamic program. -/
private theorem evalAux?_rowPrefix (available threshold inputRow input columnCount
    count : ℕ) (bit : Bool) (wires : Array Bool)
    (hcolumns : columnCount ≤ threshold)
    (hsize : wires.size = andWire available threshold inputRow 0)
    (hinput : wires[input]? = some bit)
    (hstates : ∀ required ≤ threshold,
      wires[stateWire available threshold inputRow required]? =
        some (decide (required ≤ count))) :
    ∃ result,
      RawCircuit.evalAux?
          (rowPrefix available threshold inputRow input columnCount) wires =
        some result ∧
      result.size = andWire available threshold inputRow columnCount ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      ∀ required ≤ columnCount,
        result[stateWire available threshold (inputRow + 1) required]? =
          some (decide (required ≤ count + bit.toNat)) := by
  induction columnCount with
  | zero =>
      refine ⟨wires, by simp [rowPrefix, RawCircuit.evalAux?], ?_,
        fun _ _ => rfl, ?_⟩
      · simpa using hsize
      · intro required hrequired
        have : required = 0 := by omega
        subst required
        have hzero := hstates 0 (by omega)
        simpa [stateWire] using hzero
  | succ columnCount ih =>
      obtain ⟨middle, hevalMiddle, hmiddleSize, hmiddlePreserved, hmiddleStates⟩ :=
        ih (by omega)
      have hinputLt : input < wires.size :=
        (Array.getElem?_eq_some_iff.mp hinput).choose
      have hinputMiddle : middle[input]? = some bit := by
        rw [hmiddlePreserved input hinputLt]
        exact hinput
      have hlowerOriginal := hstates columnCount (by omega)
      have hlowerLt :
          stateWire available threshold inputRow columnCount < wires.size :=
        (Array.getElem?_eq_some_iff.mp hlowerOriginal).choose
      have hlowerMiddle :
          middle[stateWire available threshold inputRow columnCount]? =
            some (decide (columnCount ≤ count)) := by
        rw [hmiddlePreserved _ hlowerLt]
        exact hlowerOriginal
      have hcurrentOriginal := hstates (columnCount + 1) (by omega)
      have hcurrentLt :
          stateWire available threshold inputRow (columnCount + 1) < wires.size :=
        (Array.getElem?_eq_some_iff.mp hcurrentOriginal).choose
      have hcurrentMiddle :
          middle[stateWire available threshold inputRow (columnCount + 1)]? =
            some (decide (columnCount + 1 ≤ count)) := by
        rw [hmiddlePreserved _ hcurrentLt]
        exact hcurrentOriginal
      have hevalCell := evalAux?_cellGates available threshold inputRow columnCount
        input bit (decide (columnCount ≤ count))
          (decide (columnCount + 1 ≤ count)) middle hmiddleSize
            hinputMiddle hlowerMiddle hcurrentMiddle
      let conjunction := bit && decide (columnCount ≤ count)
      let next := decide (columnCount + 1 ≤ count) || conjunction
      let result := (middle.push conjunction).push next
      have hevalCell' :
          RawCircuit.evalAux?
              (cellGates available threshold inputRow columnCount input) middle =
            some result := by
        simpa [conjunction, next, result] using hevalCell
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · rw [rowPrefix, RawCircuit.evalAux?_append, hevalMiddle]
        exact hevalCell'
      · simp only [result, Array.size_push, hmiddleSize, andWire]
        omega
      · intro i hi
        have hwiresLeMiddle : wires.size ≤ middle.size := by
          rw [hsize, hmiddleSize]
          simp only [andWire]
          omega
        simp only [result]
        rw [Array.getElem?_push,
          ite_eq_right (by simp only [Array.size_push]; omega)]
        rw [Array.getElem?_push, ite_eq_right (by omega)]
        exact hmiddlePreserved i hi
      · intro required hrequired
        by_cases hlast : required = columnCount + 1
        · subst required
          have hwire :
              stateWire available threshold (inputRow + 1) (columnCount + 1) =
                (middle.push conjunction).size := by
            simp only [stateWire, cellWire, Array.size_push, hmiddleSize]
          rw [hwire]
          simp only [result, Array.getElem?_push_size, next, conjunction,
            thresholdStep]
        · have hrequired' : required ≤ columnCount := by omega
          have hprevious := hmiddleStates required hrequired'
          have hpreviousLt :
              stateWire available threshold (inputRow + 1) required < middle.size :=
            (Array.getElem?_eq_some_iff.mp hprevious).choose
          simp only [result]
          rw [Array.getElem?_push, ite_eq_right (by simp only [Array.size_push]; omega)]
          rw [Array.getElem?_push, ite_eq_right (by omega)]
          exact hprevious

/-- Internal multi-row invariant, with an accumulated count supplied by the
already processed prefix. -/
private theorem evalAux?_rows (available threshold inputRow inputCount count : ℕ)
    (refs : Fin inputCount → ℕ) (bits : Fin inputCount → Bool)
    (wires : Array Bool)
    (hsize : wires.size = andWire available threshold inputRow 0)
    (hinputs : ∀ i, wires[refs i]? = some (bits i))
    (hstates : ∀ required ≤ threshold,
      wires[stateWire available threshold inputRow required]? =
        some (decide (required ≤ count))) :
    ∃ result,
      RawCircuit.evalAux?
          (rows available threshold inputRow inputCount refs) wires =
        some result ∧
      result.size = andWire available threshold (inputRow + inputCount) 0 ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      ∀ required ≤ threshold,
        result[stateWire available threshold (inputRow + inputCount) required]? =
          some (decide (required ≤ count + Fin.countP bits)) := by
  induction inputCount generalizing inputRow count wires with
  | zero =>
      refine ⟨wires, by simp [rows, RawCircuit.evalAux?], ?_,
        fun _ _ => rfl, ?_⟩
      · simpa using hsize
      · intro required hrequired
        simpa using hstates required hrequired
  | succ inputCount ih =>
      obtain ⟨middle, hevalRow, hmiddleSize, hmiddlePreserved, hmiddleStates⟩ :=
        evalAux?_rowPrefix available threshold inputRow (refs 0) threshold count
          (bits 0) wires (Nat.le_refl threshold) hsize (hinputs 0) hstates
      have hmiddleSize' :
          middle.size = andWire available threshold (inputRow + 1) 0 := by
        rw [hmiddleSize]
        simp only [andWire, Nat.add_mul, Nat.add_zero]
        omega
      have htailInputs : ∀ i : Fin inputCount,
          middle[refs i.succ]? = some (bits i.succ) := by
        intro i
        have horiginal := hinputs i.succ
        have hrefLt : refs i.succ < wires.size :=
          (Array.getElem?_eq_some_iff.mp horiginal).choose
        rw [hmiddlePreserved _ hrefLt]
        exact horiginal
      obtain ⟨result, hevalTail, hresultSize, hresultPreserved, hresultStates⟩ :=
        ih (inputRow + 1) (count + (bits 0).toNat)
          (fun i => refs i.succ) (fun i => bits i.succ) middle hmiddleSize'
            htailInputs hmiddleStates
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · rw [rows, RawCircuit.evalAux?_append, hevalRow]
        exact hevalTail
      · have hrowIndex : inputRow + 1 + inputCount = inputRow + (inputCount + 1) := by
          omega
        rw [hrowIndex] at hresultSize
        exact hresultSize
      · intro i hi
        have hwiresLeMiddle : wires.size ≤ middle.size := by
          rw [hsize, hmiddleSize]
          simp only [andWire]
          omega
        rw [hresultPreserved i (lt_of_lt_of_le hi hwiresLeMiddle)]
        exact hmiddlePreserved i hi
      · intro required hrequired
        have hrowIndex : inputRow + 1 + inputCount = inputRow + (inputCount + 1) := by
          omega
        rw [hrowIndex] at hresultStates
        have hstate := hresultStates required hrequired
        rw [Fin.countP_succ bits]
        simpa only [Nat.add_assoc] using hstate

/-- Internal semantic correctness theorem for raw threshold fragments. -/
theorem evalAux?_compileRaw_internal (available threshold : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (bits : Fin inputCount → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hrefs : ∀ i, refs i < available)
    (hinputs : ∀ i, wires[refs i]? = some (bits i)) :
    ∃ result,
      RawCircuit.evalAux? (compileRaw available threshold refs) wires = some result ∧
      result.size = wires.size + (3 + 2 * inputCount * threshold) ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[outputWire available inputCount threshold]? =
        some (decide (threshold ≤ Fin.countP bits)) := by
  have havailable : 0 < available := by
    have := NeZero.ne available
    omega
  have hzero : wires[0]? = some wires[0] :=
    Array.getElem?_eq_getElem (by omega)
  let base := (wires.push false).push true
  have hevalConstants :
      RawCircuit.evalAux?
          [RawGate.constant 0 false, RawGate.constant 0 true] wires =
        some base := by
    simp [RawCircuit.evalAux?, RawGate.constant, RawGate.eval, hzero, base]
  have hbaseSize : base.size = andWire available threshold 0 0 := by
    simp [base, andWire, hsize]
  have hbaseInputs : ∀ i, base[refs i]? = some (bits i) := by
    intro i
    have hrefLt : refs i < wires.size := by
      rw [hsize]
      exact hrefs i
    simp only [base]
    rw [Array.getElem?_push,
      ite_eq_right (by simp only [Array.size_push]; omega)]
    rw [Array.getElem?_push, ite_eq_right (by omega)]
    exact hinputs i
  have hbaseStates : ∀ required ≤ threshold,
      base[stateWire available threshold 0 required]? =
        some (decide (required ≤ 0)) := by
    intro required _
    cases required with
    | zero =>
        have hwire : trueWire available = (wires.push false).size := by
          simp [trueWire, hsize]
        rw [stateWire, hwire]
        simp only [base]
        exact Array.getElem?_push_size
    | succ required =>
        have hwire : falseWire available = wires.size := by
          simp [falseWire, hsize]
        rw [stateWire, hwire]
        have hfalse : (wires.push false)[wires.size]? = some false :=
          Array.getElem?_push_size
        simp only [base]
        rw [Array.getElem?_push, ite_eq_right (by simp)]
        exact hfalse
  obtain ⟨table, hevalRows, htableSize, htablePreserved, htableStates⟩ :=
    evalAux?_rows available threshold 0 inputCount 0 refs bits base
      hbaseSize hbaseInputs hbaseStates
  have htableOutput :
      table[stateWire available threshold inputCount threshold]? =
        some (decide (threshold ≤ Fin.countP bits)) := by
    simpa using htableStates threshold (Nat.le_refl threshold)
  let value := decide (threshold ≤ Fin.countP bits)
  let result := table.push value
  have hevalCopy :
      RawCircuit.evalAux?
          [RawGate.copy (stateWire available threshold inputCount threshold)] table =
        some result := by
    simp [RawCircuit.evalAux?, RawGate.copy, RawGate.eval, htableOutput,
      value, result]
  have hevalRemainder :
      RawCircuit.evalAux?
          (rows available threshold 0 inputCount refs ++
            [RawGate.copy (stateWire available threshold inputCount threshold)])
          base = some result := by
    rw [RawCircuit.evalAux?_append, hevalRows]
    exact hevalCopy
  have heval :
      RawCircuit.evalAux? (compileRaw available threshold refs) wires =
        some result := by
    rw [compileRaw, List.append_assoc, RawCircuit.evalAux?_append,
      hevalConstants]
    exact hevalRemainder
  refine ⟨result, heval, ?_, ?_, ?_⟩
  · simp only [Nat.zero_add] at htableSize
    simp only [result, Array.size_push, htableSize, hsize, andWire,
      Nat.add_zero, Nat.mul_assoc]
    omega
  · intro i hi
    exact RawCircuit.evalAux?_preserves_prefix heval hi
  · have hwire : outputWire available inputCount threshold = table.size := by
      rw [htableSize]
      simp only [outputWire, andWire, Nat.zero_add, Nat.add_zero, Nat.mul_assoc]
    rw [hwire]
    simp [result, value]

/-- Internal topological correctness theorem for raw threshold fragments. -/
theorem topologicallyWellFormed_compileRaw_internal (available threshold : ℕ)
    [NeZero available] {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) :
    (compileRaw available threshold refs).TopologicallyWellFormed available := by
  let wires := Array.replicate available false
  let bits : Fin inputCount → Bool := fun _ => false
  have hsize : wires.size = available := by
    simp [wires]
  have hinputs : ∀ i, wires[refs i]? = some (bits i) := by
    intro i
    simp [wires, bits, hrefs i]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileRaw_internal available threshold refs bits wires
      hsize hrefs hinputs
  have htop :=
    (RawCircuit.evalAux?_isSome_iff (compileRaw available threshold refs) wires).mp
      (by simp [heval])
  simpa [hsize] using htop

end Threshold

end CircuitCode

end Complexity
