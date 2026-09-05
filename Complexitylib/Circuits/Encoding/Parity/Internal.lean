/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Parity.Defs
public import Complexitylib.Circuits.Encoding.Fragment

/-!
# Raw parity-circuit fragments -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace Parity

theorem foldXor_eq_sum_internal (count : ℕ) (bits : Fin count → Bool) :
    foldXor count bits = ∑ i, bits i := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Fin.sum_univ_succ]
      simp only [foldXor]
      rw [ih]
      rfl

theorem length_xorGates_internal (available step input : ℕ) :
    (xorGates available step input).length = 3 := by
  rfl

theorem length_steps_internal (available step inputCount : ℕ)
    (refs : Fin inputCount → ℕ) :
    (steps available step inputCount refs).length = 3 * inputCount := by
  induction inputCount generalizing step with
  | zero => simp [steps]
  | succ inputCount ih =>
      simp [steps, length_xorGates_internal, ih]
      omega

theorem length_compileRaw_internal (available : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    (compileRaw available refs).length = 1 + 3 * inputCount := by
  simp [compileRaw, length_steps_internal]
  omega

theorem outputWire_eq_internal (available : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) :
    outputWire available inputCount =
      available + (compileRaw available refs).length - 1 := by
  rw [length_compileRaw_internal]
  simp only [outputWire, accumulatorWire]
  omega

private theorem evalAux?_xorGates (available step input : ℕ)
    (accumulator bit : Bool) (wires : Array Bool)
    (hsize : wires.size = orWire available step)
    (haccumulator : wires[accumulatorWire available step]? = some accumulator)
    (hinput : wires[input]? = some bit) :
    RawCircuit.evalAux? (xorGates available step input) wires =
      some (((wires.push (accumulator || bit)).push (accumulator && bit)).push
        (accumulator.xor bit)) := by
  let first := wires.push (accumulator || bit)
  let second := first.push (accumulator && bit)
  have haccumulatorNe : accumulatorWire available step ≠ wires.size := by
    rw [hsize]
    simp only [accumulatorWire, orWire]
    omega
  have hinputNe : input ≠ wires.size := by
    intro heq
    rw [heq, Array.getElem?_eq_none (Nat.le_refl wires.size)] at hinput
    simp at hinput
  have haccumulatorFirst :
      first[accumulatorWire available step]? =
        some accumulator := by
    dsimp only [first]
    rw [Array.getElem?_push, ite_eq_right haccumulatorNe]
    exact haccumulator
  have hinputFirst :
      first[input]? = some bit := by
    dsimp only [first]
    rw [Array.getElem?_push, ite_eq_right hinputNe]
    exact hinput
  have hor :
      first[orWire available step]? = some (accumulator || bit) := by
    dsimp only [first]
    rw [← hsize]
    exact Array.getElem?_push_size
  have haccumulatorFirst' :
      (wires.push (accumulator || bit))[accumulatorWire available step]? =
        some accumulator := by
    simpa only [first] using haccumulatorFirst
  have hinputFirst' :
      (wires.push (accumulator || bit))[input]? = some bit := by
    simpa only [first] using hinputFirst
  have hand :
      second[andWire available step]? = some (accumulator && bit) := by
    have hwire : andWire available step = first.size := by
      simp only [andWire, first, Array.size_push, hsize]
    rw [hwire]
    dsimp only [second]
    exact Array.getElem?_push_size
  have horSecond :
      second[orWire available step]? = some (accumulator || bit) := by
    have hne : orWire available step ≠ first.size := by
      simp only [first, Array.size_push, hsize]
      omega
    dsimp only [second]
    rw [Array.getElem?_push, ite_eq_right hne]
    exact hor
  have horSecond' :
      ((wires.push (accumulator || bit)).push
        (accumulator && bit))[orWire available step]? =
          some (accumulator || bit) := by
    simpa only [second, first] using horSecond
  have hand' :
      ((wires.push (accumulator || bit)).push
        (accumulator && bit))[andWire available step]? =
          some (accumulator && bit) := by
    simpa only [second, first] using hand
  simp only [xorGates, RawCircuit.evalAux?, RawGate.eval, Bool.false_xor,
    Bool.true_xor]
  rw [haccumulator, hinput]
  simp [haccumulatorFirst', hinputFirst', horSecond', hand']
  cases accumulator <;> cases bit <;> rfl

private theorem evalAux?_steps (available step inputCount : ℕ)
    (refs : Fin inputCount → ℕ) (bits : Fin inputCount → Bool)
    (accumulator : Bool) (wires : Array Bool)
    (hsize : wires.size = orWire available step)
    (hrefs : ∀ i, refs i < available)
    (hinputs : ∀ i, wires[refs i]? = some (bits i))
    (haccumulator : wires[accumulatorWire available step]? = some accumulator) :
    ∃ result,
      RawCircuit.evalAux? (steps available step inputCount refs) wires =
        some result ∧
      result.size = orWire available (step + inputCount) ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[accumulatorWire available (step + inputCount)]? =
        some (accumulator.xor (foldXor inputCount bits)) := by
  induction inputCount generalizing step accumulator wires with
  | zero =>
      refine ⟨wires, by simp [steps, RawCircuit.evalAux?], ?_,
        fun _ _ => rfl, ?_⟩
      · simpa using hsize
      · simpa [foldXor] using haccumulator
  | succ inputCount ih =>
      have hfirst := evalAux?_xorGates available step (refs 0)
        accumulator (bits 0) wires hsize haccumulator (hinputs 0)
      let middle :=
        ((wires.push (accumulator || bits 0)).push
          (accumulator && bits 0)).push (accumulator.xor (bits 0))
      have hfirst' :
          RawCircuit.evalAux? (xorGates available step (refs 0)) wires =
            some middle := by
        simpa [middle] using hfirst
      have hmiddleSize : middle.size = orWire available (step + 1) := by
        simp only [middle, Array.size_push]
        rw [hsize]
        simp only [orWire]
        omega
      have hmiddleInputs : ∀ i : Fin inputCount,
          middle[refs i.succ]? = some (bits i.succ) := by
        intro i
        have horiginal := hinputs i.succ
        have hrefLt : refs i.succ < wires.size := by
          apply lt_of_lt_of_le (hrefs i.succ)
          rw [hsize]
          simp only [orWire]
          omega
        exact RawCircuit.evalAux?_preserves_prefix hfirst' hrefLt |>.trans horiginal
      have hmiddleAccumulator :
          middle[accumulatorWire available (step + 1)]? =
            some (accumulator.xor (bits 0)) := by
        have hwire : accumulatorWire available (step + 1) =
            ((wires.push (accumulator || bits 0)).push
              (accumulator && bits 0)).size := by
          simp [accumulatorWire, hsize, orWire]
          omega
        simp only [middle, hwire, Array.getElem?_push_size]
      obtain ⟨result, hevalTail, hresultSize, hresultPreserved,
          hresultAccumulator⟩ :=
        ih (step + 1) (fun i => refs i.succ) (fun i => bits i.succ)
          (accumulator.xor (bits 0)) middle hmiddleSize
            (fun i => hrefs i.succ)
            hmiddleInputs hmiddleAccumulator
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · rw [steps, RawCircuit.evalAux?_append, hfirst']
        exact hevalTail
      · have hstep : step + 1 + inputCount = step + (inputCount + 1) := by
          omega
        rw [hstep] at hresultSize
        exact hresultSize
      · intro i hi
        have hwiresLeMiddle : wires.size ≤ middle.size := by
          simp only [middle, Array.size_push]
          omega
        rw [hresultPreserved i (lt_of_lt_of_le hi hwiresLeMiddle)]
        exact RawCircuit.evalAux?_preserves_prefix hfirst' hi
      · have hstep : step + 1 + inputCount = step + (inputCount + 1) := by
          omega
        rw [hstep] at hresultAccumulator
        rw [hresultAccumulator]
        simp only [foldXor]
        rw [Bool.xor_assoc]

theorem evalAux?_compileRaw_internal (available : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (bits : Fin inputCount → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hrefs : ∀ i, refs i < available)
    (hinputs : ∀ i, wires[refs i]? = some (bits i)) :
    ∃ result,
      RawCircuit.evalAux? (compileRaw available refs) wires = some result ∧
      result.size = wires.size + (1 + 3 * inputCount) ∧
      (∀ i < wires.size, result[i]? = wires[i]?) ∧
      result[outputWire available inputCount]? = some (foldXor inputCount bits) := by
  have havailable : 0 < available := by
    have := NeZero.ne available
    omega
  have hzero : wires[0]? = some wires[0] :=
    Array.getElem?_eq_getElem (by omega)
  let base := wires.push false
  have hevalFalse :
      RawCircuit.evalAux? [RawGate.constant 0 false] wires = some base := by
    simp [RawCircuit.evalAux?, RawGate.constant, RawGate.eval, hzero, base]
  have hbaseSize : base.size = orWire available 0 := by
    simp [base, orWire, hsize]
  have hbaseInputs : ∀ i, base[refs i]? = some (bits i) := by
    intro i
    rw [Array.getElem?_push, ite_eq_right (by rw [hsize]; exact ne_of_lt (hrefs i))]
    exact hinputs i
  have hbaseAccumulator :
      base[accumulatorWire available 0]? = some false := by
    have hwire : accumulatorWire available 0 = wires.size := by
      simp [accumulatorWire, hsize]
    rw [hwire]
    exact Array.getElem?_push_size
  obtain ⟨result, hevalSteps, hresultSize, hresultPreserved, hresultOutput⟩ :=
    evalAux?_steps available 0 inputCount refs bits false base hbaseSize
      hrefs hbaseInputs hbaseAccumulator
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · rw [compileRaw, RawCircuit.evalAux?_append, hevalFalse]
    exact hevalSteps
  · simp only [Nat.zero_add] at hresultSize hresultOutput
    rw [hresultSize, hsize]
    simp [orWire]
    omega
  · intro i hi
    rw [hresultPreserved i (by simp [base]; omega)]
    rw [Array.getElem?_push, ite_eq_right (by omega)]
  · simpa [outputWire, Bool.false_xor] using hresultOutput

theorem topologicallyWellFormed_compileRaw_internal (available : ℕ)
    [NeZero available] {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) :
    (compileRaw available refs).TopologicallyWellFormed available := by
  let wires := Array.replicate available false
  let bits : Fin inputCount → Bool := fun _ => false
  have hsize : wires.size = available := by
    simp [wires]
  have hinputs : ∀ i, wires[refs i]? = some (bits i) := by
    intro i
    simp [wires, bits, hrefs i]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileRaw_internal available refs bits wires hsize hrefs hinputs
  have htop :=
    (RawCircuit.evalAux?_isSome_iff (compileRaw available refs) wires).mp
      (by simp [heval])
  simpa [hsize] using htop

theorem compileRaw_wellFormed_internal (available : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) :
    (compileRaw available refs).WellFormed available := by
  constructor
  · simp [compileRaw]
  · exact topologicallyWellFormed_compileRaw_internal available refs hrefs

theorem eval?_compileRaw_internal (available : ℕ) [NeZero available]
    {inputCount : ℕ} (refs : Fin inputCount → ℕ)
    (hrefs : ∀ i, refs i < available) (input : BitString available) :
    RawCircuit.eval? (compileRaw available refs) input.toList =
      some (foldXor inputCount (fun i => input ⟨refs i, hrefs i⟩)) := by
  let wires := input.toList.toArray
  have hsize : wires.size = available := by
    simp [wires]
  have hinputs : ∀ i,
      wires[refs i]? = some (input ⟨refs i, hrefs i⟩) := by
    intro i
    simp [wires, BitString.toList, hrefs i]
  obtain ⟨result, heval, hresultSize, _hpreserved, houtput⟩ :=
    evalAux?_compileRaw_internal available refs
      (fun i => input ⟨refs i, hrefs i⟩) wires hsize hrefs hinputs
  have hnonempty : (compileRaw available refs).isEmpty = false := by
    simp [compileRaw]
  have houtputIndex :
      input.toList.length + (compileRaw available refs).length - 1 =
        outputWire available inputCount := by
    rw [BitString.length_toList, outputWire_eq_internal]
  rw [RawCircuit.eval?]
  simp only [hnonempty, Bool.false_eq_true, ite_false]
  rw [show input.toList.toArray = wires by rfl, heval]
  rw [houtputIndex]
  exact houtput

end Parity

end CircuitCode

end Complexity
