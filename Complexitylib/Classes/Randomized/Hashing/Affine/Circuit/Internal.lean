/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Circuit.Defs
public import Complexitylib.Circuits.Encoding.Fragment
public import Complexitylib.Circuits.Encoding.Parity
public import Complexitylib.Circuits.Encoding.Threshold

/-!
# Circuit fragments for affine Boolean forms -- proof internals
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

namespace AffineCircuit

theorem linearValue_eq_sum_add_internal {width : ℕ}
    (coefficients input : BitString width) (constant : Bool) :
    linearValue coefficients input constant =
      (∑ coordinate, coefficients coordinate * input coordinate) + constant := by
  rw [linearValue, CircuitCode.Parity.foldXor_eq_sum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_last]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Fin.lastCases_castSucc]
  cases coefficients coordinate <;> cases input coordinate <;> rfl

private theorem countP_eq_zero_iff (width : ℕ) (bits : BitString width) :
    Fin.countP bits = 0 ↔ ∀ i, bits i = false := by
  induction width with
  | zero => simp
  | succ width ih =>
      rw [Fin.countP, Fin.sum, Fin.foldr_succ, Nat.add_eq_zero_iff]
      change (bits 0).toNat = 0 ∧
        Fin.countP (fun i => bits i.succ) = 0 ↔ _
      rw [ih]
      constructor
      · rintro ⟨hzero, htail⟩ i
        have hzero' : bits 0 = false := by
          cases hbit : bits 0 with
          | false => rfl
          | true => simp [hbit] at hzero
        exact Fin.cases hzero' (fun j => htail j) i
      · intro h
        constructor
        · have := h 0
          simp_all
        · intro i
          exact h i.succ

theorem zeroValue_eq_decide_internal {width : ℕ} (output : BitString width) :
    zeroValue output = decide (output = fun _ => false) := by
  by_cases hpositive : 1 ≤ Fin.countP output
  · have hnotZero : output ≠ fun _ => false := by
      intro hzero
      have hcount : Fin.countP output = 0 :=
        (countP_eq_zero_iff width output).mpr (congrFun hzero)
      omega
    rw [zeroValue, decide_eq_true hpositive]
    exact (decide_eq_false hnotZero).symm
  · have hcount : Fin.countP output = 0 := by omega
    have hzero : output = fun _ => false := by
      funext i
      exact (countP_eq_zero_iff width output).mp hcount i
    rw [zeroValue, decide_eq_false hpositive, decide_eq_true hzero]
    rfl

theorem length_productGates_internal (width : ℕ)
    (coefficientRefs inputRefs : Fin width → ℕ) :
    (productGates width coefficientRefs inputRefs).length = width := by
  induction width with
  | zero => simp [productGates]
  | succ width ih => simp [productGates, ih]

private theorem evalAux?_productGates (available width : ℕ)
    (coefficientRefs inputRefs : Fin width → ℕ)
    (coefficients input : BitString width) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hcoefficients : ∀ i, wires[coefficientRefs i]? = some (coefficients i))
    (hinputs : ∀ i, wires[inputRefs i]? = some (input i)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (productGates width coefficientRefs inputRefs) wires = some result ∧
      result.size = available + width ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      ∀ i, result[productWire available i]? =
        some (coefficients i && input i) := by
  induction width generalizing available wires with
  | zero =>
      refine ⟨wires, by simp [productGates, CircuitCode.RawCircuit.evalAux?],
        by simpa using hsize, fun _ _ => rfl, ?_⟩
      exact fun i => Fin.elim0 i
  | succ width ih =>
      let value := coefficients 0 && input 0
      let middle := wires.push value
      have hmiddleSize : middle.size = available + 1 := by
        simp [middle, hsize]
      have hcoefficientTail : ∀ i : Fin width,
          middle[coefficientRefs i.succ]? = some (coefficients i.succ) := by
        intro i
        have hne : coefficientRefs i.succ ≠ wires.size := by
          rw [hsize]
          exact ne_of_lt (hcoefficientRefs i.succ)
        dsimp only [middle]
        rw [Array.getElem?_push, ite_eq_right hne]
        exact hcoefficients i.succ
      have hinputTail : ∀ i : Fin width,
          middle[inputRefs i.succ]? = some (input i.succ) := by
        intro i
        have hne : inputRefs i.succ ≠ wires.size := by
          rw [hsize]
          exact ne_of_lt (hinputRefs i.succ)
        dsimp only [middle]
        rw [Array.getElem?_push, ite_eq_right hne]
        exact hinputs i.succ
      obtain ⟨result, hevalTail, hresultSize, hresultPreserved,
          hresultProducts⟩ :=
        ih (available + 1) (fun i => coefficientRefs i.succ)
          (fun i => inputRefs i.succ) (fun i => coefficients i.succ)
          (fun i => input i.succ) middle hmiddleSize
          (fun i => by exact lt_trans (hcoefficientRefs i.succ) (by omega))
          (fun i => by exact lt_trans (hinputRefs i.succ) (by omega))
          hcoefficientTail hinputTail
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · simp only [productGates, CircuitCode.RawCircuit.evalAux?,
          CircuitCode.RawGate.eval, hcoefficients 0, hinputs 0,
          Bool.false_xor]
        exact hevalTail
      · omega
      · intro i hi
        have hiMiddle : i < middle.size := by
          rw [hmiddleSize, ← hsize]
          omega
        rw [hresultPreserved i hiMiddle]
        dsimp only [middle]
        rw [Array.getElem?_push, ite_eq_right (ne_of_lt hi)]
      · intro coordinate
        refine Fin.cases ?_ (fun i => ?_) coordinate
        · have hwire : productWire available (0 : Fin (width + 1)) =
              wires.size := by
            simp [productWire, hsize]
          have hwireLt :
              productWire available (0 : Fin (width + 1)) < middle.size := by
            rw [hwire]
            simp [middle]
          rw [hresultPreserved _ hwireLt]
          rw [hwire]
          exact Array.getElem?_push_size
        · have hwire : productWire (available + 1) i =
              productWire available i.succ := by
            simp only [productWire, Fin.val_succ]
            omega
          rw [← hwire]
          exact hresultProducts i

theorem length_compileLinearRaw_internal (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    (compileLinearRaw available coefficientRefs inputRefs constantRef).length =
      linearGateCount width := by
  simp [compileLinearRaw, length_productGates_internal,
    CircuitCode.Parity.length_compileRaw, linearGateCount]

theorem outputWire_eq_internal (available : ℕ) {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ) :
    outputWire available width =
      available +
        (compileLinearRaw available coefficientRefs inputRefs constantRef).length - 1 := by
  rw [length_compileLinearRaw_internal]
  simp only [outputWire, CircuitCode.Parity.outputWire,
    CircuitCode.Parity.accumulatorWire, linearGateCount]
  omega

theorem evalAux?_compileLinearRaw_internal (available : ℕ) [NeZero available]
    {width : ℕ} (coefficientRefs inputRefs : Fin width → ℕ)
    (constantRef : ℕ) (coefficients input : BitString width)
    (constant : Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available)
    (hcoefficients : ∀ i, wires[coefficientRefs i]? = some (coefficients i))
    (hinputs : ∀ i, wires[inputRefs i]? = some (input i))
    (hconstant : wires[constantRef]? = some constant) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (compileLinearRaw available coefficientRefs inputRefs constantRef)
          wires = some result ∧
      result.size = wires.size + linearGateCount width ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[outputWire available width]? =
        some (linearValue coefficients input constant) := by
  obtain ⟨middle, hevalProducts, hmiddleSize, hmiddlePreserved,
      hmiddleProducts⟩ :=
    evalAux?_productGates available width coefficientRefs inputRefs
      coefficients input wires hsize hcoefficientRefs hinputRefs
      hcoefficients hinputs
  let bits : Fin (width + 1) → Bool :=
    Fin.lastCases constant fun coordinate =>
      coefficients coordinate && input coordinate
  have hparityRefs : ∀ i,
      parityRefs (width := width) available constantRef i < available + width := by
    intro i
    refine Fin.lastCases ?_ (fun coordinate => ?_) i
    · simp only [parityRefs, Fin.lastCases_last]
      omega
    · simp only [parityRefs, Fin.lastCases_castSucc, productWire]
      omega
  have hparityInputs : ∀ i,
      middle[parityRefs (width := width) available constantRef i]? =
        some (bits i) := by
    intro i
    refine Fin.lastCases ?_ (fun coordinate => ?_) i
    · simp only [parityRefs, Fin.lastCases_last, bits, Fin.lastCases_last]
      rw [hmiddlePreserved constantRef (by rw [hsize]; exact hconstantRef)]
      exact hconstant
    · simp only [parityRefs, Fin.lastCases_castSucc, bits,
        Fin.lastCases_castSucc]
      exact hmiddleProducts coordinate
  let : NeZero (available + width) := ⟨by
    have := NeZero.ne available
    omega⟩
  obtain ⟨result, hevalParity, hresultSize, hresultPreserved,
      hresultOutput⟩ :=
    CircuitCode.Parity.evalAux?_compileRaw (available + width)
      (parityRefs (width := width) available constantRef) bits middle
      hmiddleSize hparityRefs hparityInputs
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · rw [compileLinearRaw, CircuitCode.RawCircuit.evalAux?_append,
      hevalProducts]
    exact hevalParity
  · rw [hresultSize, hmiddleSize, hsize]
    simp only [linearGateCount]
    omega
  · intro i hi
    have hiMiddle : i < middle.size := by
      rw [hmiddleSize]
      rw [hsize] at hi
      omega
    rw [hresultPreserved i hiMiddle]
    exact hmiddlePreserved i hi
  · simpa only [outputWire, linearValue, bits] using hresultOutput

theorem length_compileRowsRaw_internal (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) :
    (compileRowsRaw available width rowCount coefficientRefs inputRefs).length =
      rowCount * linearGateCount width := by
  induction rowCount generalizing available with
  | zero => simp [compileRowsRaw]
  | succ rowCount ih =>
      simp [compileRowsRaw, length_compileLinearRaw_internal, ih]
      rw [Nat.add_mul]
      simp
      ac_rfl

theorem evalAux?_compileRowsRaw_internal
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (coefficients : Fin rowCount → BitString (width + 1))
    (input : BitString width) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available)
    (hcoefficients : ∀ row coordinate,
      wires[coefficientRefs row coordinate]? =
        some (coefficients row coordinate))
    (hinputs : ∀ coordinate,
      wires[inputRefs coordinate]? = some (input coordinate)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (compileRowsRaw available width rowCount coefficientRefs inputRefs)
          wires = some result ∧
      result.size = available + rowCount * linearGateCount width ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      ∀ row,
        result[rowOutputWire available width row]? =
          some (linearValue
            (fun coordinate => coefficients row coordinate.castSucc)
            input (coefficients row (Fin.last width))) := by
  induction rowCount generalizing available wires with
  | zero =>
      refine ⟨wires, by simp [compileRowsRaw,
        CircuitCode.RawCircuit.evalAux?], by simpa using hsize,
        fun _ _ => rfl, ?_⟩
      exact fun row => Fin.elim0 row
  | succ rowCount ih =>
      obtain ⟨middle, hevalFirst, hmiddleSizeRaw, hmiddlePreserved,
          hmiddleOutput⟩ :=
        evalAux?_compileLinearRaw_internal available
          (fun coordinate => coefficientRefs 0 coordinate.castSucc)
          inputRefs (coefficientRefs 0 (Fin.last width))
          (fun coordinate => coefficients 0 coordinate.castSucc) input
          (coefficients 0 (Fin.last width)) wires hsize
          (fun coordinate => hcoefficientRefs 0 coordinate.castSucc)
          hinputRefs (hcoefficientRefs 0 (Fin.last width))
          (fun coordinate => hcoefficients 0 coordinate.castSucc)
          hinputs (hcoefficients 0 (Fin.last width))
      have hmiddleSize : middle.size = available + linearGateCount width := by
        rw [hmiddleSizeRaw, hsize]
      have hcoefficientTail : ∀ (row : Fin rowCount)
          (coordinate : Fin (width + 1)),
          middle[coefficientRefs row.succ coordinate]? =
            some (coefficients row.succ coordinate) := by
        intro row coordinate
        rw [hmiddlePreserved _ (by
          rw [hsize]
          exact hcoefficientRefs row.succ coordinate)]
        exact hcoefficients row.succ coordinate
      have hinputTail : ∀ coordinate,
          middle[inputRefs coordinate]? = some (input coordinate) := by
        intro coordinate
        rw [hmiddlePreserved _ (by
          rw [hsize]
          exact hinputRefs coordinate)]
        exact hinputs coordinate
      let : NeZero (available + linearGateCount width) := ⟨by
        have := NeZero.ne available
        omega⟩
      have havailableLt :
          available < available + linearGateCount width := by
        simp only [linearGateCount]
        omega
      obtain ⟨result, hevalTail, hresultSize, hresultPreserved,
          hresultOutputs⟩ :=
        ih (available + linearGateCount width)
          (fun (row : Fin rowCount) coordinate =>
            coefficientRefs row.succ coordinate)
          (fun row => coefficients row.succ) middle
          hmiddleSize
          (fun row coordinate => by
            exact lt_trans (hcoefficientRefs row.succ coordinate) havailableLt)
          (fun coordinate => by
            exact lt_trans (hinputRefs coordinate) havailableLt)
          hcoefficientTail hinputTail
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · rw [compileRowsRaw, CircuitCode.RawCircuit.evalAux?_append,
          hevalFirst]
        exact hevalTail
      · rw [Nat.add_mul]
        omega
      · intro i hi
        have hiMiddle : i < middle.size := by
          rw [hmiddleSize, ← hsize]
          omega
        rw [hresultPreserved i hiMiddle]
        exact hmiddlePreserved i hi
      · intro row
        refine Fin.cases ?_ (fun prior => ?_) row
        · have hwireLt :
              rowOutputWire available width (0 : Fin (rowCount + 1)) <
                middle.size := by
            simp only [rowOutputWire, rowAvailable, Fin.val_zero,
              Nat.zero_mul, Nat.add_zero, outputWire,
              CircuitCode.Parity.outputWire,
              CircuitCode.Parity.accumulatorWire, hmiddleSize,
              linearGateCount]
            omega
          rw [hresultPreserved _ hwireLt]
          simpa [rowOutputWire, rowAvailable] using hmiddleOutput
        · have hwire :
              rowOutputWire (available + linearGateCount width) width prior =
                rowOutputWire available width prior.succ := by
            simp only [rowOutputWire, rowAvailable, Fin.val_succ]
            congr 1
            rw [Nat.add_mul]
            omega
          rw [← hwire]
          exact hresultOutputs prior

theorem length_compileZeroRaw_internal
    (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) :
    (compileZeroRaw available width rowCount coefficientRefs inputRefs).length =
      zeroGateCount width rowCount := by
  simp [compileZeroRaw, length_compileRowsRaw_internal,
    CircuitCode.Threshold.length_compileRaw, zeroGateCount]
  omega

theorem zeroOutputWire_eq_internal
    (available width rowCount : ℕ)
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ) :
    zeroOutputWire available width rowCount =
      available +
        (compileZeroRaw available width rowCount coefficientRefs inputRefs).length - 1 := by
  rw [length_compileZeroRaw_internal]
  simp only [zeroOutputWire, rowsAvailable,
    CircuitCode.Threshold.outputWire, zeroGateCount]
  omega

theorem evalAux?_compileZeroRaw_internal
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (coefficients : Fin rowCount → BitString (width + 1))
    (input : BitString width) (wires : Array Bool)
    (hsize : wires.size = available)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available)
    (hcoefficients : ∀ row coordinate,
      wires[coefficientRefs row coordinate]? =
        some (coefficients row coordinate))
    (hinputs : ∀ coordinate,
      wires[inputRefs coordinate]? = some (input coordinate)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (compileZeroRaw available width rowCount coefficientRefs inputRefs)
          wires = some result ∧
      result.size = wires.size + zeroGateCount width rowCount ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[zeroOutputWire available width rowCount]? =
        some (zeroValue fun row =>
          linearValue
            (fun coordinate => coefficients row coordinate.castSucc)
            input (coefficients row (Fin.last width))) := by
  let values : BitString rowCount := fun row =>
    linearValue (fun coordinate => coefficients row coordinate.castSucc)
      input (coefficients row (Fin.last width))
  obtain ⟨middle, hevalRows, hmiddleSize, hmiddlePreserved,
      hmiddleOutputs⟩ :=
    evalAux?_compileRowsRaw_internal available width rowCount
      coefficientRefs inputRefs coefficients input wires hsize
      hcoefficientRefs hinputRefs hcoefficients hinputs
  let afterRows := rowsAvailable available width rowCount
  let outputs : Fin rowCount → ℕ := rowOutputWire available width
  have hafterRows : middle.size = afterRows := by
    simpa only [afterRows, rowsAvailable] using hmiddleSize
  have houtputRefs : ∀ row, outputs row < afterRows := by
    intro row
    simp only [outputs, rowOutputWire, rowAvailable, outputWire,
      CircuitCode.Parity.outputWire,
      CircuitCode.Parity.accumulatorWire, afterRows, rowsAvailable,
      linearGateCount]
    have hrow := row.isLt
    nlinarith
  have houtputValues : ∀ row,
      middle[outputs row]? = some (values row) := by
    intro row
    exact hmiddleOutputs row
  let : NeZero afterRows := ⟨by
    have := NeZero.ne available
    simp only [afterRows, rowsAvailable]
    omega⟩
  obtain ⟨almost, hevalThreshold, halmostSize, halmostPreserved,
      halmostOutput⟩ :=
    CircuitCode.Threshold.evalAux?_compileRaw afterRows 1 outputs values
      middle hafterRows houtputRefs houtputValues
  let answer := zeroValue values
  let result := almost.push answer
  have hevalCopy :
      CircuitCode.RawCircuit.evalAux?
          [CircuitCode.RawGate.copy
            (CircuitCode.Threshold.outputWire afterRows rowCount 1) true]
          almost = some result := by
    simp [CircuitCode.RawCircuit.evalAux?, CircuitCode.RawGate.copy,
      CircuitCode.RawGate.eval, halmostOutput, result, answer, zeroValue]
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · rw [compileZeroRaw]
    rw [CircuitCode.RawCircuit.evalAux?_append]
    rw [CircuitCode.RawCircuit.evalAux?_append, hevalRows]
    simp only [Option.bind_some]
    rw [show CircuitCode.RawCircuit.evalAux?
        (CircuitCode.Threshold.compileRaw
          (rowsAvailable available width rowCount) 1
          (rowOutputWire available width)) middle = some almost by
      simpa only [afterRows, outputs] using hevalThreshold]
    simpa only [Option.bind_some, afterRows, outputs] using hevalCopy
  · simp only [result, Array.size_push, halmostSize, hafterRows,
      afterRows, rowsAvailable, hsize, zeroGateCount]
    omega
  · intro i hi
    have hiMiddle : i < middle.size := by
      rw [hmiddleSize, ← hsize]
      omega
    have hiAlmost : i < almost.size := by
      rw [halmostSize]
      omega
    rw [CircuitCode.RawCircuit.evalAux?_preserves_prefix hevalCopy hiAlmost]
    rw [halmostPreserved i hiMiddle]
    exact hmiddlePreserved i hi
  · have hwire : zeroOutputWire available width rowCount = almost.size := by
      rw [halmostSize, hafterRows]
      simp only [zeroOutputWire, CircuitCode.Threshold.outputWire]
      omega
    rw [hwire]
    simp only [result, Array.getElem?_push_size, answer, values]

theorem topologicallyWellFormed_compileLinearRaw_internal
    (available : ℕ) [NeZero available] {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available) :
    CircuitCode.RawCircuit.TopologicallyWellFormed available
      (compileLinearRaw available coefficientRefs inputRefs constantRef) := by
  let wires := Array.replicate available false
  have hsize : wires.size = available := by simp [wires]
  have hcoefficients : ∀ i, wires[coefficientRefs i]? = some false := by
    intro i
    simp [wires, hcoefficientRefs i]
  have hinputs : ∀ i, wires[inputRefs i]? = some false := by
    intro i
    simp [wires, hinputRefs i]
  have hconstant : wires[constantRef]? = some false := by
    simp [wires, hconstantRef]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileLinearRaw_internal available coefficientRefs inputRefs
      constantRef (fun _ => false) (fun _ => false) false wires hsize
      hcoefficientRefs hinputRefs hconstantRef hcoefficients hinputs hconstant
  have htop :=
    (CircuitCode.RawCircuit.evalAux?_isSome_iff
      (compileLinearRaw available coefficientRefs inputRefs constantRef)
      wires).mp (by simp [heval])
  simpa [hsize] using htop

theorem compileLinearRaw_wellFormed_internal
    (available : ℕ) [NeZero available] {width : ℕ}
    (coefficientRefs inputRefs : Fin width → ℕ) (constantRef : ℕ)
    (hcoefficientRefs : ∀ i, coefficientRefs i < available)
    (hinputRefs : ∀ i, inputRefs i < available)
    (hconstantRef : constantRef < available) :
    CircuitCode.RawCircuit.WellFormed available
      (compileLinearRaw available coefficientRefs inputRefs constantRef) := by
  constructor
  · intro hempty
    have hlength := congrArg List.length hempty
    rw [length_compileLinearRaw_internal] at hlength
    simp [linearGateCount] at hlength
  · exact topologicallyWellFormed_compileLinearRaw_internal available
      coefficientRefs inputRefs constantRef hcoefficientRefs hinputRefs
      hconstantRef

theorem topologicallyWellFormed_compileZeroRaw_internal
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available) :
    CircuitCode.RawCircuit.TopologicallyWellFormed available
      (compileZeroRaw available width rowCount coefficientRefs inputRefs) := by
  let wires := Array.replicate available false
  have hsize : wires.size = available := by simp [wires]
  have hcoefficients : ∀ row coordinate,
      wires[coefficientRefs row coordinate]? = some false := by
    intro row coordinate
    simp [wires, hcoefficientRefs row coordinate]
  have hinputs : ∀ coordinate,
      wires[inputRefs coordinate]? = some false := by
    intro coordinate
    simp [wires, hinputRefs coordinate]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileZeroRaw_internal available width rowCount
      coefficientRefs inputRefs (fun _ _ => false) (fun _ => false)
      wires hsize hcoefficientRefs hinputRefs hcoefficients hinputs
  have htop :=
    (CircuitCode.RawCircuit.evalAux?_isSome_iff
      (compileZeroRaw available width rowCount coefficientRefs inputRefs)
      wires).mp (by simp [heval])
  simpa [hsize] using htop

theorem compileZeroRaw_wellFormed_internal
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available) :
    CircuitCode.RawCircuit.WellFormed available
      (compileZeroRaw available width rowCount coefficientRefs inputRefs) := by
  constructor
  · intro hempty
    have hlength := congrArg List.length hempty
    rw [length_compileZeroRaw_internal] at hlength
    simp [zeroGateCount] at hlength
  · exact topologicallyWellFormed_compileZeroRaw_internal
      available width rowCount coefficientRefs inputRefs
      hcoefficientRefs hinputRefs

theorem eval?_compileZeroRaw_internal
    (available width rowCount : ℕ) [NeZero available]
    (coefficientRefs : Fin rowCount → Fin (width + 1) → ℕ)
    (inputRefs : Fin width → ℕ)
    (hcoefficientRefs : ∀ row coordinate,
      coefficientRefs row coordinate < available)
    (hinputRefs : ∀ coordinate, inputRefs coordinate < available)
    (input : BitString available) :
    CircuitCode.RawCircuit.eval?
        (compileZeroRaw available width rowCount coefficientRefs inputRefs)
        input.toList =
      some (zeroValue fun row =>
        linearValue
          (fun coordinate => input ⟨coefficientRefs row coordinate.castSucc,
            hcoefficientRefs row coordinate.castSucc⟩)
          (fun coordinate => input ⟨inputRefs coordinate,
            hinputRefs coordinate⟩)
          (input ⟨coefficientRefs row (Fin.last width),
            hcoefficientRefs row (Fin.last width)⟩)) := by
  let wires := input.toList.toArray
  let coefficients : Fin rowCount → BitString (width + 1) :=
    fun row coordinate =>
      input ⟨coefficientRefs row coordinate,
        hcoefficientRefs row coordinate⟩
  let selectedInput : BitString width := fun coordinate =>
    input ⟨inputRefs coordinate, hinputRefs coordinate⟩
  have hsize : wires.size = available := by
    simp [wires]
  have hcoefficients : ∀ row coordinate,
      wires[coefficientRefs row coordinate]? =
        some (coefficients row coordinate) := by
    intro row coordinate
    simp [wires, coefficients, BitString.toList,
      hcoefficientRefs row coordinate]
  have hinputs : ∀ coordinate,
      wires[inputRefs coordinate]? = some (selectedInput coordinate) := by
    intro coordinate
    simp [wires, selectedInput, BitString.toList, hinputRefs coordinate]
  obtain ⟨result, heval, _hresultSize, _hpreserved, houtput⟩ :=
    evalAux?_compileZeroRaw_internal available width rowCount
      coefficientRefs inputRefs coefficients selectedInput wires hsize
      hcoefficientRefs hinputRefs hcoefficients hinputs
  have hnonempty :
      (compileZeroRaw available width rowCount coefficientRefs inputRefs).isEmpty =
        false := by
    simp [compileZeroRaw]
  have houtputIndex :
      input.toList.length +
          (compileZeroRaw available width rowCount coefficientRefs inputRefs).length - 1 =
        zeroOutputWire available width rowCount := by
    rw [BitString.length_toList,
      zeroOutputWire_eq_internal available width rowCount coefficientRefs inputRefs]
  rw [CircuitCode.RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false]
  rw [show input.toList.toArray = wires by rfl, heval, houtputIndex]
  exact houtput

theorem linearValue_affineRow_internal {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth))
    (input : BitString domainWidth) (row : Fin rangeWidth) :
    linearValue
        (fun coordinate => affineRows seed row coordinate.castSucc)
        input (affineRows seed row (Fin.last domainWidth)) =
      affineEval seed input row := by
  rw [linearValue_eq_sum_add_internal]
  simp only [affineEval]
  rw [Fin.sum_univ_castSucc]
  simp [affineAugment]
  cases affineRows seed row (Fin.last domainWidth) <;> rfl

theorem zeroValue_affineEval_internal {domainWidth rangeWidth : ℕ}
    (seed : BitString (affineSeedWidth domainWidth rangeWidth))
    (input : BitString domainWidth) :
    zeroValue (fun row =>
      linearValue
        (fun coordinate => affineRows seed row coordinate.castSucc)
        input (affineRows seed row (Fin.last domainWidth))) =
      decide (affineEval seed input = fun _ => false) := by
  rw [zeroValue_eq_decide_internal]
  have hvalues :
      (fun row =>
        linearValue
          (fun coordinate => affineRows seed row coordinate.castSucc)
          input (affineRows seed row (Fin.last domainWidth))) =
        affineEval seed input := by
    funext row
    exact linearValue_affineRow_internal seed input row
  rw [hvalues]

end AffineCircuit

end PairwiseIndependentHash

end Complexity
