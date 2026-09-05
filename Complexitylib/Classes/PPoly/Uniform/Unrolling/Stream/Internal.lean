/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Stream.Defs

/-!
# Streamable deterministic unrolling arithmetic — proof internals

This module proves that absolute wire bases do not affect transition-formula
tree sizes, then solves the deterministic trace-prefix recurrences using the
resulting constant packed-layer size.
-/


public section

namespace Complexity

namespace CircuitUnrolling

private def eraseFormulaVars : BoolFormula → BoolFormula
  | .var _ => .var 0
  | .tru => .tru
  | .fls => .fls
  | .neg formula => .neg (eraseFormulaVars formula)
  | .conj left right => .conj (eraseFormulaVars left) (eraseFormulaVars right)
  | .disj left right => .disj (eraseFormulaVars left) (eraseFormulaVars right)

@[simp] private theorem size_eraseFormulaVars (formula : BoolFormula) :
    (eraseFormulaVars formula).size = formula.size := by
  induction formula <;> simp [eraseFormulaVars, BoolFormula.size, *]

@[simp] private theorem eraseFormulaVars_conjs (formulas : List BoolFormula) :
    eraseFormulaVars (BoolFormula.conjs formulas) =
      BoolFormula.conjs (formulas.map eraseFormulaVars) := by
  induction formulas <;> simp [BoolFormula.conjs, eraseFormulaVars, *]

@[simp] private theorem eraseFormulaVars_disjs (formulas : List BoolFormula) :
    eraseFormulaVars (BoolFormula.disjs formulas) =
      BoolFormula.disjs (formulas.map eraseFormulaVars) := by
  induction formulas <;> simp [BoolFormula.disjs, eraseFormulaVars, *]

@[simp] private theorem eraseFormulaVars_literal (wire : ℕ) (value : Bool) :
    eraseFormulaVars (BoolFormula.literal wire value) =
      eraseFormulaVars (BoolFormula.literal 0 value) := by
  cases value <;> rfl

private theorem eraseFormulaVars_readFormula (tm : NTM k) (T base base' : ℕ)
    (tape : TapeSlot k) (symbol : Γ) :
    eraseFormulaVars (readFormula tm T base tape symbol) =
      eraseFormulaVars (readFormula tm T base' tape symbol) := by
  unfold readFormula
  rw [eraseFormulaVars_disjs, eraseFormulaVars_disjs,
    List.map_ofFn, List.map_ofFn]
  apply congrArg BoolFormula.disjs
  apply congrArg List.ofFn
  funext position
  simp [configVar, eraseFormulaVars]

private theorem eraseFormulaVars_caseFormula (tm : NTM k)
    (T base base' choiceWire choiceWire' : ℕ) (view : TransitionCase tm) :
    eraseFormulaVars (caseFormula tm T base choiceWire view) =
      eraseFormulaVars (caseFormula tm T base' choiceWire' view) := by
  have hwork :
      (List.ofFn fun i : Fin k =>
        readFormula tm T base (.work i) (view.workRead i)).map eraseFormulaVars =
      (List.ofFn fun i : Fin k =>
        readFormula tm T base' (.work i) (view.workRead i)).map eraseFormulaVars := by
    rw [List.map_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact eraseFormulaVars_readFormula tm T base base' (.work i) (view.workRead i)
  unfold caseFormula
  rw [eraseFormulaVars_conjs, eraseFormulaVars_conjs]
  apply congrArg BoolFormula.conjs
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [eraseFormulaVars_literal choiceWire view.choice,
    eraseFormulaVars_literal choiceWire' view.choice,
    eraseFormulaVars_readFormula tm T base base' .input view.inputRead,
    eraseFormulaVars_readFormula tm T base base' .output view.outputRead, hwork]
  simp [configVar, eraseFormulaVars]

private theorem eraseFormulaVars_effectFormula (tm : NTM k)
    (T base base' choiceWire choiceWire' : ℕ)
    (selects : TransitionEffect tm → Bool) :
    eraseFormulaVars (effectFormula tm T base choiceWire selects) =
      eraseFormulaVars (effectFormula tm T base' choiceWire' selects) := by
  unfold effectFormula
  rw [eraseFormulaVars_disjs, eraseFormulaVars_disjs]
  apply congrArg BoolFormula.disjs
  simp only [List.map_map]
  apply List.map_congr_left
  intro view _
  by_cases hselects : selects view.effect = true
  · simp only [Function.comp_apply, ite_eq_left hselects]
    exact eraseFormulaVars_caseFormula tm T base base' choiceWire choiceWire' view
  · simp [Function.comp_apply, hselects, eraseFormulaVars]

private theorem eraseFormulaVars_predecessorHeadFormula (tm : NTM k)
    (T base base' : ℕ) (tape : TapeSlot k) (target : Fin (T + 1))
    (direction : Dir3) :
    eraseFormulaVars (predecessorHeadFormula tm T base tape target direction) =
      eraseFormulaVars (predecessorHeadFormula tm T base' tape target direction) := by
  unfold predecessorHeadFormula
  rw [eraseFormulaVars_disjs, eraseFormulaVars_disjs,
    List.map_ofFn, List.map_ofFn]
  apply congrArg BoolFormula.disjs
  apply congrArg List.ofFn
  funext source
  by_cases hsource : movedHeadPosition source.val direction = target.val
  · simp [hsource, configVar, eraseFormulaVars]
  · simp [hsource, eraseFormulaVars]

private theorem eraseFormulaVars_movedHeadFormula (tm : NTM k)
    (T base base' choiceWire choiceWire' : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) :
    eraseFormulaVars (movedHeadFormula tm T base choiceWire tape target) =
      eraseFormulaVars (movedHeadFormula tm T base' choiceWire' tape target) := by
  unfold movedHeadFormula selectedMoveFormula
  rw [eraseFormulaVars_disjs, eraseFormulaVars_disjs]
  simp only [List.map_cons, List.map_nil, eraseFormulaVars]
  rw [eraseFormulaVars_effectFormula tm T base base' choiceWire choiceWire',
    eraseFormulaVars_predecessorHeadFormula tm T base base' tape target .left,
    eraseFormulaVars_effectFormula tm T base base' choiceWire choiceWire',
    eraseFormulaVars_predecessorHeadFormula tm T base base' tape target .right,
    eraseFormulaVars_effectFormula tm T base base' choiceWire choiceWire',
    eraseFormulaVars_predecessorHeadFormula tm T base base' tape target .stay]

private theorem eraseFormulaVars_headAtCellFormula (tm : NTM k)
    (T base base' : ℕ) (tape : TapeSlot k) (position : Fin (T + 2)) :
    eraseFormulaVars (headAtCellFormula tm T base tape position) =
      eraseFormulaVars (headAtCellFormula tm T base' tape position) := by
  unfold headAtCellFormula configVar
  split <;> rfl

private theorem eraseFormulaVars_writtenCellFormula (tm : NTM k)
    (T base base' choiceWire choiceWire' : ℕ) (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ) :
    eraseFormulaVars (writtenCellFormula tm T base choiceWire tape position symbol) =
      eraseFormulaVars
        (writtenCellFormula tm T base' choiceWire' tape position symbol) := by
  unfold writtenCellFormula selectedWriteFormula
  simp only [eraseFormulaVars, configVar]
  rw [eraseFormulaVars_headAtCellFormula tm T base base' tape.toTapeSlot position,
    eraseFormulaVars_effectFormula tm T base base' choiceWire choiceWire']

private theorem eraseFormulaVars_nextFormula (tm : NTM k)
    (T base base' choiceWire choiceWire' : ℕ) (atom : ConfigAtom tm T) :
    eraseFormulaVars (nextFormula tm T base choiceWire atom) =
      eraseFormulaVars (nextFormula tm T base' choiceWire' atom) := by
  cases atom with
  | state state =>
      unfold nextFormula haltedOrFormula haltVar selectedStateFormula configVar
      simp only [eraseFormulaVars]
      rw [eraseFormulaVars_effectFormula tm T base base' choiceWire choiceWire']
  | head tape position =>
      unfold nextFormula haltedOrFormula haltVar configVar
      simp only [eraseFormulaVars]
      rw [eraseFormulaVars_movedHeadFormula tm T base base' choiceWire choiceWire']
  | cell tape position symbol =>
      cases tape with
      | input => rfl
      | work i =>
          simp only [nextFormula]
          split
          · rfl
          · simp only [haltedOrFormula, haltVar, configVar]
            simp only [eraseFormulaVars]
            rw [eraseFormulaVars_writtenCellFormula tm T base base' choiceWire
              choiceWire']
      | output =>
          simp only [nextFormula]
          split
          · rfl
          · simp only [haltedOrFormula, haltVar, configVar]
            simp only [eraseFormulaVars]
            rw [eraseFormulaVars_writtenCellFormula tm T base base' choiceWire
              choiceWire']

theorem size_nextFormula_eq_directStepFormulaSize_internal (tm : NTM k)
    (T configBase choiceWire : ℕ) (atom : ConfigAtom tm T) :
    (nextFormula tm T configBase choiceWire atom).size =
      directStepFormulaSize tm T atom := by
  unfold directStepFormulaSize
  rw [← size_eraseFormulaVars (nextFormula tm T configBase choiceWire atom),
    eraseFormulaVars_nextFormula tm T configBase 0 choiceWire 0,
    size_eraseFormulaVars]

theorem stepFragmentSize_eq_directStepSize_internal (tm : NTM k)
    (T configBase choiceWire : ℕ) :
    stepFragmentSize tm T configBase choiceWire = directStepSize tm T := by
  unfold stepFragmentSize directStepSize stepFormulas
  rw [List.map_map, List.length_map, length_configAtoms_internal]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom _
  exact size_nextFormula_eq_directStepFormulaSize_internal tm T configBase
    choiceWire atom

private theorem prefixTraceBuild_closedForms (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) (hi : i ≤ T) :
    (prefixTraceBuild tm T n available i layout).configBase =
        available + i * directStepSize tm T ∧
      (prefixTraceBuild tm T n available i layout).available =
        available + configWidth tm T + i * directStepSize tm T ∧
      (prefixTraceBuild tm T n available i layout).size =
        configWidth tm T + i * directStepSize tm T := by
  induction i with
  | zero =>
      simp [prefixTraceBuild, traceBuildFrom, initialTraceBuild]
  | succ i ih =>
      have hindex : i < T := by omega
      obtain ⟨_hconfigBase, havailable, hsize⟩ := ih (by omega)
      have houtputEnd := stepOutputEnd_eq_internal tm T
        (prefixTraceBuild tm T n available i layout).configBase
        (layout.choice ⟨i, hindex⟩).val
        (prefixTraceBuild tm T n available i layout).available
      rw [stepFragmentSize_eq_directStepSize_internal, havailable] at houtputEnd
      constructor
      · rw [prefixTraceBuild_succ_configBase_internal tm T n available i layout hindex,
          havailable, Nat.succ_mul]
        omega
      · constructor
        · rw [prefixTraceBuild_succ_available_internal tm T n available i layout hindex,
            stepFragmentSize_eq_directStepSize_internal, havailable, Nat.succ_mul]
          omega
        · rw [prefixTraceBuild_succ_size_internal tm T n available i layout hindex,
            stepFragmentSize_eq_directStepSize_internal, hsize, Nat.succ_mul]
          omega

end CircuitUnrolling

namespace TM

theorem directPrefixTraceBuild_configBase_internal (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).configBase =
      n + i * CircuitUnrolling.directStepSize tm.toNTM T := by
  exact (CircuitUnrolling.prefixTraceBuild_closedForms tm.toNTM T n n i
    (CircuitUnrolling.deterministicInputWires T n) hi).1

theorem directPrefixTraceBuild_available_internal (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).available =
      n + CircuitUnrolling.configWidth tm.toNTM T +
        i * CircuitUnrolling.directStepSize tm.toNTM T := by
  exact (CircuitUnrolling.prefixTraceBuild_closedForms tm.toNTM T n n i
    (CircuitUnrolling.deterministicInputWires T n) hi).2.1

theorem directPrefixTraceBuild_size_internal (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).size =
      CircuitUnrolling.configWidth tm.toNTM T +
        i * CircuitUnrolling.directStepSize tm.toNTM T := by
  exact (CircuitUnrolling.prefixTraceBuild_closedForms tm.toNTM T n n i
    (CircuitUnrolling.deterministicInputWires T n) hi).2.2

theorem directPrefixTraceBuild_circuit_internal (tm : TM k)
    (T n i : ℕ) [NeZero n] (hi : i ≤ T) :
    (tm.directPrefixTraceBuild T n i).circuit =
      CircuitUnrolling.initFragment tm.toNTM T n n
          (CircuitUnrolling.deterministicInputWires T n) ++
        ((List.finRange T).take i).flatMap (tm.directStepFragment T n) := by
  induction i with
  | zero =>
      simp [directPrefixTraceBuild, CircuitUnrolling.prefixTraceBuild_zero_internal,
        CircuitUnrolling.initialTraceBuild]
  | succ i ih =>
      have hindex : i < T := by omega
      let layout := CircuitUnrolling.deterministicInputWires T n
      have hprefix := ih (by omega)
      change
        (CircuitUnrolling.prefixTraceBuild tm.toNTM T n n i layout).circuit =
          CircuitUnrolling.initFragment tm.toNTM T n n layout ++
            ((List.finRange T).take i).flatMap (tm.directStepFragment T n)
        at hprefix
      have hlistIndex : i < (List.finRange T).length := by simpa using hindex
      have hget : (List.finRange T)[i]'hlistIndex = (⟨i, hindex⟩ : Fin T) := by
        apply Fin.ext
        simp
      have htake :
          (List.finRange T).take (i + 1) =
            (List.finRange T).take i ++ [(⟨i, hindex⟩ : Fin T)] := by
        rw [List.take_succ_eq_append_getElem hlistIndex, hget]
      have hforms := CircuitUnrolling.prefixTraceBuild_closedForms tm.toNTM
        T n n i layout (by omega)
      change
        (CircuitUnrolling.prefixTraceBuild tm.toNTM T n n (i + 1) layout).circuit = _
      rw [CircuitUnrolling.prefixTraceBuild_succ_circuit_internal tm.toNTM
        T n n i layout hindex, htake, List.flatMap_append, hprefix]
      rw [hforms.1, hforms.2.1]
      simp [directStepFragment, layout, CircuitUnrolling.deterministicInputWires,
        List.append_assoc]

theorem directTraceFragment_eq_init_append_steps_internal (tm : TM k)
    (T n : ℕ) [NeZero n] :
    CircuitUnrolling.traceFragment tm.toNTM T n n
        (CircuitUnrolling.deterministicInputWires T n) =
      CircuitUnrolling.initFragment tm.toNTM T n n
          (CircuitUnrolling.deterministicInputWires T n) ++
        (List.finRange T).flatMap (tm.directStepFragment T n) := by
  have hprefix := tm.directPrefixTraceBuild_circuit_internal T n T le_rfl
  unfold directPrefixTraceBuild at hprefix
  rw [CircuitUnrolling.prefixTraceBuild_eq_traceBuild_internal] at hprefix
  have htake : (List.finRange T).take T = List.finRange T := by simp
  rw [htake] at hprefix
  exact hprefix

theorem directTraceOutputBase_internal (tm : TM k) (T n : ℕ) [NeZero n] :
    CircuitUnrolling.traceOutputBase tm.toNTM T n n
        (CircuitUnrolling.deterministicInputWires T n) =
      n + T * CircuitUnrolling.directStepSize tm.toNTM T := by
  have hbase := tm.directPrefixTraceBuild_configBase_internal T n T le_rfl
  unfold directPrefixTraceBuild at hbase
  rw [CircuitUnrolling.prefixTraceBuild_eq_traceBuild_internal] at hbase
  exact hbase

theorem directUnrollingRawCircuit_eq_init_append_steps_internal (tm : TM k)
    (f : ℕ → ℕ) (n : ℕ) [NeZero n] :
    tm.directUnrollingRawCircuit f n =
      CircuitUnrolling.initFragment tm.toNTM (f n) n n
          (CircuitUnrolling.deterministicInputWires (f n) n) ++
        (List.finRange (f n)).flatMap (tm.directStepFragment (f n) n) ++
        [CircuitUnrolling.acceptanceGate tm.toNTM (f n)
          (n + f n * CircuitUnrolling.directStepSize tm.toNTM (f n))] := by
  unfold directUnrollingRawCircuit CircuitUnrolling.acceptanceRawCircuit
  rw [tm.directTraceFragment_eq_init_append_steps_internal,
    tm.directTraceOutputBase_internal]

end TM

end Complexity
