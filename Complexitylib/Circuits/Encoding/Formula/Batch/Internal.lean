/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Formula.Batch.Defs
public import Complexitylib.Circuits.Encoding.Formula.Internal
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Internals for batch formula compilation

This module proves the structural, topological, and iterative-evaluator laws
for `BoolFormula.compileRawBatch`. Public statements are re-exported by
`Complexitylib.Circuits.Encoding.Formula.Batch`.
-/


public section

namespace Complexity

namespace BoolFormula

open CircuitCode

/-! ## Formula-list combinators -/

theorem eval_literal_internal (wire : ℕ) (value : Bool)
    (assignment : ℕ → Bool) :
    (literal wire value).eval assignment = decide (assignment wire = value) := by
  generalize hactual : assignment wire = actual
  cases value <;> cases actual <;> simp_all [literal, eval]

theorem size_literal_le_two_internal (wire : ℕ) (value : Bool) :
    (literal wire value).size ≤ 2 := by
  cases value <;> simp [literal, size]

theorem eval_conjs_internal (formulas : List BoolFormula)
    (assignment : ℕ → Bool) :
    (conjs formulas).eval assignment =
      formulas.all (fun formula => formula.eval assignment) := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih => simp [conjs, eval, ih]

theorem eval_disjs_internal (formulas : List BoolFormula)
    (assignment : ℕ → Bool) :
    (disjs formulas).eval assignment =
      formulas.any (fun formula => formula.eval assignment) := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih => simp [disjs, eval, ih]

theorem size_conjs_internal (formulas : List BoolFormula) :
    (conjs formulas).size =
      1 + (formulas.map fun formula => formula.size + 1).sum := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [conjs, size, List.map_cons, List.sum_cons, ih]
      omega

theorem size_disjs_internal (formulas : List BoolFormula) :
    (disjs formulas).size =
      1 + (formulas.map fun formula => formula.size + 1).sum := by
  induction formulas with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [disjs, size, List.map_cons, List.sum_cons, ih]
      omega

/-! ## Structural accounting -/

theorem length_compileRawOutputs_circuit_internal (available : ℕ)
    (formulas : List BoolFormula) :
    (compileRawOutputs available formulas).circuit.length =
      (formulas.map size).sum := by
  induction formulas generalizing available with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [compileRawOutputs, List.length_append,
        length_compileRaw_internal, List.map_cons, List.sum_cons, ih]

theorem length_compileRawOutputs_outputs_internal (available : ℕ)
    (formulas : List BoolFormula) :
    (compileRawOutputs available formulas).outputs.length = formulas.length := by
  induction formulas generalizing available with
  | nil => rfl
  | cons formula formulas ih =>
      simp only [compileRawOutputs, List.length_cons, ih]

theorem length_compileRawBatch_internal (available : ℕ)
    (formulas : List BoolFormula) :
    (compileRawBatch available formulas).length =
      (formulas.map size).sum + formulas.length := by
  simp [compileRawBatch, length_compileRawOutputs_circuit_internal,
    length_compileRawOutputs_outputs_internal]

/-! ## Sequential formula evaluation -/

private theorem evalAux?_compileRawOutputs
    (origin available : ℕ) [NeZero available]
    (formulas : List BoolFormula) (assignment : ℕ → Bool)
    (wires : Array Bool) (hsize : wires.size = available)
    (horigin : origin ≤ available)
    (hvars : ∀ formula ∈ formulas, ∀ i ∈ formula.vars, i < origin)
    (hinput : ∀ i < origin, wires[i]? = some (assignment i)) :
    ∃ result,
      RawCircuit.evalAux? (compileRawOutputs available formulas).circuit wires =
          some result ∧
        result.size = wires.size + (formulas.map size).sum ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        List.Forall₂
          (fun formula output =>
            result[output]? = some (formula.eval assignment))
          formulas (compileRawOutputs available formulas).outputs := by
  induction formulas generalizing available wires with
  | nil =>
      refine ⟨wires, rfl, by simp, ?_, .nil⟩
      intro i hi
      rfl
  | cons formula formulas ih =>
      have hformulaVars : ∀ i ∈ formula.vars, i < available := by
        intro i hi
        exact (hvars formula (by simp) i hi).trans_le horigin
      have hformulaInput :
          ∀ i ∈ formula.vars, wires[i]? = some (assignment i) := by
        intro i hi
        exact hinput i (hvars formula (by simp) i hi)
      obtain ⟨formulaResult, hevalFormula, hformulaSize,
          hformulaPrefix, hformulaOutput⟩ :=
        evalAux?_compileRaw_of_agree_internal available formula assignment wires
          hsize hformulaVars hformulaInput
      have hnextSize : formulaResult.size = available + formula.size := by
        omega
      let : NeZero (available + formula.size) := ⟨by
        have havailable := NeZero.ne available
        have hpositive := formula.one_le_size
        omega⟩
      have htailVars :
          ∀ tailFormula ∈ formulas, ∀ i ∈ tailFormula.vars, i < origin := by
        intro tailFormula htail i hi
        exact hvars tailFormula (by simp [htail]) i hi
      have htailInput :
          ∀ i < origin, formulaResult[i]? = some (assignment i) := by
        intro i hi
        rw [hformulaPrefix i (by omega)]
        exact hinput i hi
      obtain ⟨result, hevalTail, hresultSize, hresultPrefix, htailOutputs⟩ :=
        ih (available + formula.size) formulaResult hnextSize (by omega)
          htailVars htailInput
      have hformulaWireLt :
          rawOutputWire available formula < formulaResult.size := by
        rw [hnextSize]
        exact rawOutputWire_lt_internal available formula
      have hformulaOutput' :
          result[rawOutputWire available formula]? =
            some (formula.eval assignment) := by
        rw [hresultPrefix _ hformulaWireLt]
        exact hformulaOutput
      refine ⟨result, ?_, ?_, ?_, ?_⟩
      · change RawCircuit.evalAux?
          (compileRaw available formula ++
            (compileRawOutputs (available + formula.size) formulas).circuit)
          wires = some result
        rw [RawCircuit.evalAux?_append_internal, hevalFormula]
        simpa only [Option.bind_some] using hevalTail
      · simp only [List.map_cons, List.sum_cons]
        omega
      · intro i hi
        rw [hresultPrefix i (by omega)]
        exact hformulaPrefix i hi
      · change List.Forall₂
          (fun tailFormula output =>
            result[output]? = some (tailFormula.eval assignment))
          (formula :: formulas)
          (rawOutputWire available formula ::
            (compileRawOutputs (available + formula.size) formulas).outputs)
        exact .cons hformulaOutput' htailOutputs

/-! ## Contiguous output packing -/

private theorem evalAux?_copyOutputs
    (outputs : List ℕ) (values : List Bool) (wires : Array Bool)
    (houtputs :
      List.Forall₂ (fun output value => wires[output]? = some value)
        outputs values) :
    ∃ result,
      RawCircuit.evalAux? (outputs.map RawGate.copy) wires = some result ∧
        result.size = wires.size + outputs.length ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        (∀ (j : ℕ) (hj : j < values.length),
          result[wires.size + j]? = some (values[j]'hj)) := by
  induction outputs generalizing values wires with
  | nil =>
      cases houtputs
      refine ⟨wires, by simp [RawCircuit.evalAux?], by simp, ?_, ?_⟩
      · intro i hi
        rfl
      · intro j hj
        simp at hj
  | cons output outputs ih =>
      cases values with
      | nil => cases houtputs
      | cons value values =>
       cases houtputs with
       | cons houtput htail =>
        have houtputLt : output < wires.size := by
          by_contra hnot
          have hnone : wires[output]? = none :=
            Array.getElem?_eq_none (by omega)
          rw [houtput] at hnone
          simp at hnone
        have hevalHead :
            RawCircuit.evalAux? [RawGate.copy output] wires =
              some (wires.push value) := by
          simp [RawCircuit.evalAux?, RawGate.copy, RawGate.eval, houtput]
        have htailPush :
            List.Forall₂
              (fun tailOutput tailValue =>
                (wires.push value)[tailOutput]? = some tailValue)
              outputs values := by
          apply htail.imp
          intro tailOutput tailValue htailOutput
          have htailOutputLt : tailOutput < wires.size := by
            by_contra hnot
            have hnone : wires[tailOutput]? = none :=
              Array.getElem?_eq_none (by omega)
            rw [htailOutput] at hnone
            simp at hnone
          rw [Array.getElem?_push, ite_eq_right (by omega)]
          exact htailOutput
        obtain ⟨result, hevalTail, hresultSize, hresultPrefix, hresultOutputs⟩ :=
          ih values (wires.push value) htailPush
        refine ⟨result, ?_, ?_, ?_, ?_⟩
        · change RawCircuit.evalAux?
            ([RawGate.copy output] ++ outputs.map RawGate.copy) wires = some result
          rw [RawCircuit.evalAux?_append_internal, hevalHead]
          simpa only [Option.bind_some] using hevalTail
        · simp only [List.length_cons, Array.size_push] at hresultSize ⊢
          omega
        · intro i hi
          rw [hresultPrefix i (by simp; omega)]
          rw [Array.getElem?_push, ite_eq_right (by omega)]
        · intro j hj
          cases j with
          | zero =>
              have hfirst :
                  (wires.push value)[wires.size]? = some value :=
                Array.getElem?_push_size
              have hwireLt : wires.size < (wires.push value).size := by simp
              have hfirstResult : result[wires.size]? = some value := by
                rw [hresultPrefix _ hwireLt]
                exact hfirst
              simpa using hfirstResult
          | succ j =>
              have hjtail : j < values.length := by simpa using hj
              have htailResult := hresultOutputs j hjtail
              have hindex :
                  wires.size + (j + 1) = (wires.push value).size + j := by
                simp
                omega
              rw [hindex]
              simpa using htailResult

/-! ## Batch correctness -/

theorem evalAux?_compileRawBatch_internal (available : ℕ) [NeZero available]
    (formulas : List BoolFormula) (assignment : ℕ → Bool)
    (wires : Array Bool) (hsize : wires.size = available)
    (hinput : ∀ i < available, wires[i]? = some (assignment i))
    (hvars : ∀ formula ∈ formulas, ∀ i ∈ formula.vars, i < available) :
    ∃ result,
      RawCircuit.evalAux? (compileRawBatch available formulas) wires = some result ∧
        result.size =
          wires.size + (formulas.map size).sum + formulas.length ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        (∀ j : Fin formulas.length,
          result[rawBatchOutputBase available formulas + j.val]? =
            some ((formulas.get j).eval assignment)) := by
  obtain ⟨compiled, hevalCompiled, hcompiledSize, hcompiledPrefix,
      hcompiledOutputs⟩ :=
    evalAux?_compileRawOutputs available available formulas assignment wires
      hsize le_rfl hvars hinput
  let values := formulas.map fun formula => formula.eval assignment
  have hpackedInputs :
      List.Forall₂ (fun output value => compiled[output]? = some value)
        (compileRawOutputs available formulas).outputs values := by
    dsimp only [values]
    have flip : ∀ {source : List BoolFormula} {outputs : List ℕ},
        List.Forall₂
            (fun formula output =>
              compiled[output]? = some (formula.eval assignment))
            source outputs →
          List.Forall₂
            (fun output value => compiled[output]? = some value)
            outputs (source.map fun formula => formula.eval assignment) := by
      intro source outputs h
      induction h with
      | nil => exact .nil
      | cons hhead _ ih => exact .cons hhead ih
    exact flip hcompiledOutputs
  obtain ⟨result, hevalPacked, hresultSize, hresultPrefix, hpackedOutputs⟩ :=
    evalAux?_copyOutputs (compileRawOutputs available formulas).outputs
      values compiled hpackedInputs
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · rw [compileRawBatch, RawCircuit.evalAux?_append_internal, hevalCompiled]
    simpa only [Option.bind_some] using hevalPacked
  · rw [hresultSize, hcompiledSize]
    simp only [length_compileRawOutputs_outputs_internal]
  · intro i hi
    rw [hresultPrefix i (by omega)]
    exact hcompiledPrefix i hi
  · intro j
    have hjvalues : j.val < values.length := by simp [values]
    have houtput := hpackedOutputs j.val hjvalues
    have hcompiledSize' :
        compiled.size = available + (formulas.map size).sum := by
      omega
    rw [hcompiledSize'] at houtput
    simpa [rawBatchOutputBase, values] using houtput

theorem topologicallyWellFormed_compileRawBatch_internal (available : ℕ)
    [NeZero available] (formulas : List BoolFormula)
    (hvars : ∀ formula ∈ formulas, ∀ i ∈ formula.vars, i < available) :
    (compileRawBatch available formulas).TopologicallyWellFormed available := by
  let wires := Array.replicate available false
  have hsize : wires.size = available := by simp [wires]
  have hinput : ∀ i < available, wires[i]? = some false := by
    intro i hi
    simp [wires, hi]
  obtain ⟨result, heval, _⟩ :=
    evalAux?_compileRawBatch_internal available formulas (fun _ => false)
      wires hsize hinput hvars
  have htop :=
    (RawCircuit.evalAux?_isSome_iff (compileRawBatch available formulas) wires).mp
      (by simp [heval])
  simpa [hsize] using htop

end BoolFormula

end Complexity
