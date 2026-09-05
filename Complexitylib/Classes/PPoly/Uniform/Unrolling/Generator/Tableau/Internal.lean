/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Finalization
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength

/-!
# Complete direct-unrolling generator -- proof internals

This file first verifies the outer transition-layer loop. Its pure trajectory
keeps the step scratch convention reusable, preserves the horizon, and advances
the dedicated layer counter exactly once per emitted packed step.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

open scoped BigOperators

private theorem stepLoopValues_invariant (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (count : ℕ) :
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      values count
    StepClean current ∧ current Work.horizon = values Work.horizon ∧
      current Work.loop₂ = values Work.loop₂ + count := by
  induction count with
  | zero => simp [BinaryRoutine.binaryForValues, hclean]
  | succ count ih =>
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hcurrentClean : StepClean current := ih.1
      have hcurrentHorizon : current Work.horizon = values Work.horizon := ih.2.1
      have hcurrentLoop : current Work.loop₂ = values Work.loop₂ + count :=
        ih.2.2
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      have hstepClean : StepClean ((emitStep tm).effect current) :=
        emitStep_preserves_clean tm current hcurrentClean hhorizonCurrent
      have hnextClean : StepClean
          (Function.update ((emitStep tm).effect current) Work.loop₂
            (current Work.loop₂ + 1)) :=
        hstepClean.updateOuter_forEffect_internal _ Work.loop₂ _
          (Or.inr (Or.inr (Or.inr rfl)))
      have hstepHorizon :
          (emitStep tm).effect current Work.horizon = current Work.horizon := by
        rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
        simp [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
          Work.horizon]
      change StepClean
          (BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current) ∧
        BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
            Work.horizon = values Work.horizon ∧
        BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
            Work.loop₂ = values Work.loop₂ + (count + 1)
      refine ⟨hnextClean, ?_, ?_⟩
      · exact hstepHorizon.trans hcurrentHorizon
      · calc
          current Work.loop₂ + 1 =
              (values Work.loop₂ + count) + 1 := by rw [hcurrentLoop]
          _ = values Work.loop₂ + (count + 1) := by omega

private theorem stepLoopValues_frontier (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (count : ℕ) :
    BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ values count
        Work.frontier = values Work.frontier := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hinvariant := stepLoopValues_invariant tm values hclean hhorizon count
      have hcurrentClean : StepClean current := hinvariant.1
      have hcurrentHorizon : current Work.horizon = values Work.horizon :=
        hinvariant.2.1
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      rw [BinaryRoutine.binaryForValues]
      change Function.update ((emitStep tm).effect current) Work.loop₂
          (current Work.loop₂ + 1) Work.frontier = values Work.frontier
      rw [Function.update_of_ne (by decide),
        emitStep_effect tm current hcurrentClean hhorizonCurrent]
      simpa [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
        Work.frontier] using ih

private theorem stepScheduleSize_eq_directStepSizeInternal (tm : NTM k)
    (T configBase : ℕ) :
    stepScheduleSize (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) = directStepSize tm T := by
  rw [← stepFragmentSize_eq_stepScheduleSize tm T configBase 0,
    stepFragmentSize_eq_directStepSize]

private theorem initializationEndpoint (tm : TM k) (q : Polynomial ℕ)
    (n : ℕ) :
    let values := preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n)
    let T := (TM.directSerializerHorizonPolynomial q).eval n
    let final := (initialization tm).effect values
    StepClean final ∧ final Work.horizon = T ∧ final Work.loop₂ = 0 ∧
      final Work.frontier = n + tm.directUnrollingGateBound
        (TM.directSerializerHorizonPolynomial q).eval n ∧
      final Work.configBase = n ∧
      final Work.available = n + configWidth tm.toNTM T := by
  dsimp only
  rw [initialization_effect_preambleValues]
  have hclean : StepClean
      (Function.update
        (Function.update
          (preambleValues tm q
            (BinaryRoutine.inputLengthValues Work.inputLength n))
          Work.available
          (n + Fintype.card tm.Q +
            ((TM.directSerializerHorizonPolynomial q).eval n + 1) *
              (k + 2) + 4 +
            4 * ((TM.directSerializerHorizonPolynomial q).eval n + 1) +
            (4 + 4 *
              ((TM.directSerializerHorizonPolynomial q).eval n + 1)) *
                (k + 1)))
        Work.limit₀ 0) := by
    constructor
    · constructor
      · constructor
        · constructor <;>
            simp [preambleValues, BinaryRoutine.inputLengthValues,
              Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
              Work.available, Work.configBase, Work.limit₀, Work.position,
              Work.loop₀, Work.reference₀, Work.reference₁,
              Work.emitCounter, Work.copyCounter, Work.multiplyCounter,
              Work.addCounter, Work.temporary₀, Work.temporary₁,
              Work.temporary₂]
        all_goals
          simp [preambleValues, BinaryRoutine.inputLengthValues,
            Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
            Work.available, Work.configBase, Work.limit₀, Work.position,
            Work.loop₃, Work.temporary₃, Work.polynomialScratch,
            Work.tapeIndex, Work.symbolIndex]
      all_goals
        simp [preambleValues, BinaryRoutine.inputLengthValues,
          Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
          Work.available, Work.configBase, Work.limit₀,
          Work.limit₂, Work.loop₁, Work.savedOutput, Work.direction,
          Work.atomKind]
    · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
        Work.horizon, Work.frontier, Work.gateCount, Work.available,
        Work.configBase, Work.limit₀, Work.position]
    · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
        Work.horizon, Work.frontier, Work.gateCount, Work.available,
        Work.configBase, Work.limit₀, Work.limit₁]
  refine ⟨hclean, ?_, ?_, ?_, ?_, ?_⟩
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀, Work.loop₂]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀, configWidth]
    have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
    rw [hcard]
    ring

private theorem stepScheduleOutputBase_eq_nextInternal (tm : TM k)
    (T n count available configBase : ℕ)
    (havailable : available = n + configWidth tm.toNTM T +
      count * directStepSize tm.toNTM T) :
    stepScheduleOutputBase (transitionCases tm.toNTM).length
        (Fintype.card tm.Q) k T available (stepAtomKindAt tm.toNTM T)
        (stepAtomEffectSelectedAt tm.toNTM T) (effectCaseChoiceAt tm.toNTM) =
      n + (count + 1) * directStepSize tm.toNTM T := by
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  rw [← hcard]
  rw [← stepOutputBase_eq_stepScheduleOutputBase tm.toNTM T configBase 0
    available]
  have hend := stepOutputEnd_eq tm.toNTM T configBase 0 available
  rw [stepFragmentSize_eq_directStepSize] at hend
  have hrhs : available + directStepSize tm.toNTM T =
      (n + (count + 1) * directStepSize tm.toNTM T) +
        configWidth tm.toNTM T := by
    rw [havailable]
    ring
  rw [hrhs] at hend
  exact Nat.add_right_cancel hend

private theorem stepLoopValues_numeric_invariant (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n count : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      values count
    StepClean current ∧ current Work.horizon = values Work.horizon ∧
      current Work.loop₂ = count ∧
      current Work.configBase =
        n + count * directStepSize tm.toNTM (values Work.horizon) ∧
      current Work.available =
        n + configWidth tm.toNTM (values Work.horizon) +
          count * directStepSize tm.toNTM (values Work.horizon) := by
  have hbasic := stepLoopValues_invariant tm values hclean hhorizon count
  have hnumeric :
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      current Work.configBase =
          n + count * directStepSize tm.toNTM (values Work.horizon) ∧
        current Work.available =
          n + configWidth tm.toNTM (values Work.horizon) +
            count * directStepSize tm.toNTM (values Work.horizon) := by
    induction count with
    | zero =>
        simp [BinaryRoutine.binaryForValues, hconfigBase, havailable]
    | succ count ih =>
        let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
          values count
        have hcountInvariant :=
          stepLoopValues_invariant tm values hclean hhorizon count
        have hcurrentClean : StepClean current := hcountInvariant.1
        have hcurrentHorizon : current Work.horizon = values Work.horizon :=
          hcountInvariant.2.1
        have hhorizonCurrent : 0 < current Work.horizon := by
          simpa [hcurrentHorizon] using hhorizon
        have ihNumeric := ih hcountInvariant
        have hcurrentBase : current Work.configBase =
            n + count * directStepSize tm.toNTM (values Work.horizon) :=
          ihNumeric.1
        have hcurrentAvailable : current Work.available =
            n + configWidth tm.toNTM (values Work.horizon) +
              count * directStepSize tm.toNTM (values Work.horizon) :=
          ihNumeric.2
        have hsize :
            stepScheduleSize (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (current Work.horizon)
                (stepAtomKindAt tm.toNTM (current Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
                (effectCaseChoiceAt tm.toNTM) =
              directStepSize tm.toNTM (values Work.horizon) := by
          rw [hcurrentHorizon]
          exact stepScheduleSize_eq_directStepSizeInternal tm.toNTM
            (values Work.horizon) (current Work.configBase)
        have hbase :
            stepScheduleOutputBase (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (current Work.horizon)
                (current Work.available)
                (stepAtomKindAt tm.toNTM (current Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
                (effectCaseChoiceAt tm.toNTM) =
              n + (count + 1) *
                directStepSize tm.toNTM (values Work.horizon) := by
          rw [hcurrentHorizon]
          exact stepScheduleOutputBase_eq_nextInternal tm
            (values Work.horizon) n count (current Work.available)
            (current Work.configBase) hcurrentAvailable
        change
          BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
                Work.configBase =
              n + (count + 1) *
                directStepSize tm.toNTM (values Work.horizon) ∧
            BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
                Work.available =
              n + configWidth tm.toNTM (values Work.horizon) +
                (count + 1) * directStepSize tm.toNTM (values Work.horizon)
        constructor
        · change (emitStep tm).effect current Work.configBase = _
          rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
          simpa [Work.available, Work.configBase, Work.gateBound,
            Work.gateCount] using hbase
        · change (emitStep tm).effect current Work.available = _
          rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
          rw [hsize, hcurrentAvailable]
          simp [Work.available, Work.configBase,
            Work.gateBound, Work.gateCount]
          ring
  refine ⟨hbasic.1, hbasic.2.1, ?_, hnumeric⟩
  simpa [hloop] using hbasic.2.2

/-- Polynomial space envelope for indexing one tableau-step iteration. -/
noncomputable def stepLoopIndexPolynomial
    (tm : NTM k) : Polynomial ℕ :=
  Polynomial.C (Fintype.card tm.Q) +
    Polynomial.C (k + 2) * (Polynomial.X + Polynomial.C 2) +
    Polynomial.C 5 *
      (Polynomial.C (k + 2) * (Polynomial.X + Polynomial.C 2) +
        (Polynomial.X + Polynomial.C 2)) +
    (Polynomial.X + Polynomial.C 2) +
    Polynomial.C (2 * (k + 2) + 8)

/-- Polynomial space envelope for evaluating one tableau-step iteration. -/
noncomputable def stepLoopEvaluatorPolynomial
    (tm : NTM k) : Polynomial ℕ :=
  TM.binaryPolynomialSpaceWidthPolynomial
      predecessorHeadSchedulePolynomial +
    (∑ state : tm.Q,
      TM.binaryPolynomialSpaceWidthPolynomial
        (stateNextChildPolynomial tm state)) +
    (∑ tape : TapeSlot k,
      TM.binaryPolynomialSpaceWidthPolynomial
        (headNextChildPolynomial tm tape)) +
    (∑ tape : WritableSlot k, ∑ symbol : Γ,
      TM.binaryPolynomialSpaceWidthPolynomial
        (writtenNextChildPolynomial tm tape symbol)) +
    (∑ state : tm.Q,
      TM.binaryPolynomialSpaceWidthPolynomial
        (stateNextFormulaPolynomial tm state)) +
    (∑ tape : TapeSlot k,
      TM.binaryPolynomialSpaceWidthPolynomial
        (headNextFormulaPolynomial tm tape)) +
    (∑ tape : WritableSlot k, ∑ symbol : Γ,
      TM.binaryPolynomialSpaceWidthPolynomial
        (writtenNextFormulaPolynomial tm tape symbol)) +
    TM.binaryPolynomialSpaceWidthPolynomial (Polynomial.C 1)

/-- Polynomial endpoint bound after the tableau-step loop. -/
noncomputable def stepLoopEndPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  let horizon := TM.directSerializerHorizonPolynomial q
  Polynomial.X +
    Polynomial.C (Fintype.card tm.Q + 5 * (k + 2)) *
      (horizon + Polynomial.C 2) +
    horizon *
      (Polynomial.C (stepSizeCoeff tm.toNTM) *
        (horizon + Polynomial.C 2) ^ 2)

/-- Polynomial work-width envelope for the complete tableau-step loop. -/
noncomputable def stepLoopWidthPolynomial
    (tm : TM k) (q : Polynomial ℕ) : Polynomial ℕ :=
  let horizon := TM.directSerializerHorizonPolynomial q
  let endpoint := stepLoopEndPolynomial tm q
  Polynomial.X + horizon +
      TM.directSerializerFrontierPolynomial tm q +
      TM.directSerializerGateCountPolynomial tm q + endpoint +
      Polynomial.C 1 +
    Polynomial.C 4 * endpoint +
    Polynomial.C 5 * (stepLoopIndexPolynomial tm.toNTM).comp horizon +
    (stepLoopEvaluatorPolynomial tm.toNTM).comp horizon

private theorem directStepSize_le_stepBound (tm : NTM k) (T : ℕ) :
    directStepSize tm T ≤ stepSizeCoeff tm * (T + 2) ^ 2 := by
  rw [← stepFragmentSize_eq_directStepSize tm T 0 0]
  exact stepFragmentSize_le tm T 0 0

private theorem stepLoopEndPolynomial_eval (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    (stepLoopEndPolynomial tm q).eval n =
      n + (Fintype.card tm.Q + 5 * (k + 2)) *
          ((TM.directSerializerHorizonPolynomial q).eval n + 2) +
        (TM.directSerializerHorizonPolynomial q).eval n *
          (stepSizeCoeff tm.toNTM *
            ((TM.directSerializerHorizonPolynomial q).eval n + 2) ^ 2) := by
  simp [stepLoopEndPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow]

private theorem stepLoopWidthPolynomial_eval (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    (stepLoopWidthPolynomial tm q).eval n =
      n + (TM.directSerializerHorizonPolynomial q).eval n +
        (TM.directSerializerFrontierPolynomial tm q).eval n +
        (TM.directSerializerGateCountPolynomial tm q).eval n +
        (stepLoopEndPolynomial tm q).eval n + 1 +
        4 * (stepLoopEndPolynomial tm q).eval n +
        5 * (stepLoopIndexPolynomial tm.toNTM).eval
          ((TM.directSerializerHorizonPolynomial q).eval n) +
        (stepLoopEvaluatorPolynomial tm.toNTM).eval
          ((TM.directSerializerHorizonPolynomial q).eval n) := by
  simp [stepLoopWidthPolynomial, Polynomial.eval_comp]

private theorem stepLoopEnd_final_le (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    let T := (TM.directSerializerHorizonPolynomial q).eval n
    n + configWidth tm.toNTM T + T * directStepSize tm.toNTM T ≤
      (stepLoopEndPolynomial tm q).eval n := by
  dsimp only
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  have hconfig := configWidth_le tm.toNTM T
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  rw [hcard] at hconfig
  have hstep := directStepSize_le_stepBound tm.toNTM T
  have hmul := Nat.mul_le_mul_left T hstep
  rw [stepLoopEndPolynomial_eval]
  dsimp only [T] at hconfig hstep hmul ⊢
  omega

private theorem stepLoopIndex_bounds
    (tm : NTM k) (T base stateIndex tapeIndex symbolIndex position : ℕ)
    (hstate : stateIndex < Fintype.card tm.Q)
    (htape : tapeIndex ≤ k + 1) (hsymbol : symbolIndex < 4)
    (hposition : position ≤ T + 1) :
    transitionStateRef base stateIndex ≤
        base + (stepLoopIndexPolynomial tm).eval T ∧
    transitionHeadRef (Fintype.card tm.Q) T base tapeIndex position +
        tapeIndex + T + 1 ≤
      base + (stepLoopIndexPolynomial tm).eval T ∧
    transitionCellRef (Fintype.card tm.Q) (k + 2) T base tapeIndex
          position symbolIndex +
        (tapeIndex * (T + 2) + position) +
        (T + 2) + (k + 2) + tapeIndex + 4 ≤
      base + (stepLoopIndexPolynomial tm).eval T ∧
    caseReadSize T ≤ (stepLoopIndexPolynomial tm).eval T ∧
    2 * (T + 2) + T ≤ (stepLoopIndexPolynomial tm).eval T := by
  have htape' : tapeIndex ≤ k + 2 := by omega
  have htapeHead := Nat.mul_le_mul_right (T + 1) htape'
  have htapeCell := Nat.mul_le_mul_right (T + 2) htape'
  have hKHead := Nat.mul_le_mul_left (k + 2)
    (show T + 1 ≤ T + 2 by omega)
  have hposition' : position ≤ T + 2 := by omega
  have hpair := Nat.add_le_add htapeCell hposition'
  have hscaled := Nat.mul_le_mul_left 5 hpair
  simp only [stepLoopIndexPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  unfold transitionStateRef transitionHeadRef transitionCellRef caseReadSize
  omega

private theorem stepLoopEvaluator_caps
    (tm : NTM k) (T : ℕ) (state : tm.Q)
    (headTape : TapeSlot k) (writtenTape : WritableSlot k) (symbol : Γ) :
    2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial T +
      2 * TM.binaryPolynomialValueCap
        (stateNextChildPolynomial tm state) T +
      2 * TM.binaryPolynomialValueCap
        (headNextChildPolynomial tm headTape) T +
      2 * TM.binaryPolynomialValueCap
        (writtenNextChildPolynomial tm writtenTape symbol) T +
      2 * TM.binaryPolynomialValueCap
        (stateNextFormulaPolynomial tm state) T +
      2 * TM.binaryPolynomialValueCap
        (headNextFormulaPolynomial tm headTape) T +
      2 * TM.binaryPolynomialValueCap
        (writtenNextFormulaPolynomial tm writtenTape symbol) T +
      2 * TM.binaryPolynomialValueCap (Polynomial.C 1) T ≤
        (stepLoopEvaluatorPolynomial tm).eval T := by
  have hstateChild :
      2 * TM.binaryPolynomialValueCap
          (stateNextChildPolynomial tm state) T ≤
        ∑ current : tm.Q,
          2 * TM.binaryPolynomialValueCap
            (stateNextChildPolynomial tm current) T := by
    apply Finset.single_le_sum
      (f := fun current : tm.Q =>
        2 * TM.binaryPolynomialValueCap
          (stateNextChildPolynomial tm current) T)
    · intro
      omega
    · exact Finset.mem_univ state
  have hheadChild :
      2 * TM.binaryPolynomialValueCap
          (headNextChildPolynomial tm headTape) T ≤
        ∑ current : TapeSlot k,
          2 * TM.binaryPolynomialValueCap
            (headNextChildPolynomial tm current) T := by
    apply Finset.single_le_sum
      (f := fun current : TapeSlot k =>
        2 * TM.binaryPolynomialValueCap
          (headNextChildPolynomial tm current) T)
    · intro
      omega
    · exact Finset.mem_univ headTape
  have hwrittenChild :
      2 * TM.binaryPolynomialValueCap
          (writtenNextChildPolynomial tm writtenTape symbol) T ≤
        ∑ tape : WritableSlot k, ∑ current : Γ,
          2 * TM.binaryPolynomialValueCap
            (writtenNextChildPolynomial tm tape current) T := by
    have hsymbol :
        2 * TM.binaryPolynomialValueCap
            (writtenNextChildPolynomial tm writtenTape symbol) T ≤
          ∑ current : Γ,
            2 * TM.binaryPolynomialValueCap
              (writtenNextChildPolynomial tm writtenTape current) T := by
      apply Finset.single_le_sum
        (f := fun current : Γ =>
          2 * TM.binaryPolynomialValueCap
            (writtenNextChildPolynomial tm writtenTape current) T)
      · intro
        omega
      · exact Finset.mem_univ symbol
    exact hsymbol.trans (by
      apply Finset.single_le_sum
        (f := fun tape : WritableSlot k =>
          ∑ current : Γ,
            2 * TM.binaryPolynomialValueCap
              (writtenNextChildPolynomial tm tape current) T)
      · intro
        omega
      · exact Finset.mem_univ writtenTape)
  have hstateFormula :
      2 * TM.binaryPolynomialValueCap
          (stateNextFormulaPolynomial tm state) T ≤
        ∑ current : tm.Q,
          2 * TM.binaryPolynomialValueCap
            (stateNextFormulaPolynomial tm current) T := by
    apply Finset.single_le_sum
      (f := fun current : tm.Q =>
        2 * TM.binaryPolynomialValueCap
          (stateNextFormulaPolynomial tm current) T)
    · intro
      omega
    · exact Finset.mem_univ state
  have hheadFormula :
      2 * TM.binaryPolynomialValueCap
          (headNextFormulaPolynomial tm headTape) T ≤
        ∑ current : TapeSlot k,
          2 * TM.binaryPolynomialValueCap
            (headNextFormulaPolynomial tm current) T := by
    apply Finset.single_le_sum
      (f := fun current : TapeSlot k =>
        2 * TM.binaryPolynomialValueCap
          (headNextFormulaPolynomial tm current) T)
    · intro
      omega
    · exact Finset.mem_univ headTape
  have hwrittenFormula :
      2 * TM.binaryPolynomialValueCap
          (writtenNextFormulaPolynomial tm writtenTape symbol) T ≤
        ∑ tape : WritableSlot k, ∑ current : Γ,
          2 * TM.binaryPolynomialValueCap
            (writtenNextFormulaPolynomial tm tape current) T := by
    have hsymbol :
        2 * TM.binaryPolynomialValueCap
            (writtenNextFormulaPolynomial tm writtenTape symbol) T ≤
          ∑ current : Γ,
            2 * TM.binaryPolynomialValueCap
              (writtenNextFormulaPolynomial tm writtenTape current) T := by
      apply Finset.single_le_sum
        (f := fun current : Γ =>
          2 * TM.binaryPolynomialValueCap
            (writtenNextFormulaPolynomial tm writtenTape current) T)
      · intro
        omega
      · exact Finset.mem_univ symbol
    exact hsymbol.trans (by
      apply Finset.single_le_sum
        (f := fun tape : WritableSlot k =>
          ∑ current : Γ,
            2 * TM.binaryPolynomialValueCap
              (writtenNextFormulaPolynomial tm tape current) T)
      · intro
        omega
      · exact Finset.mem_univ writtenTape)
  simp only [stepLoopEvaluatorPolynomial, Polynomial.eval_add,
    Polynomial.eval_finsetSum,
    TM.binaryPolynomialSpaceWidthPolynomial_eval]
  omega

private theorem stepLoopCap_sum_le
    {endpoint index evaluator frontier stateRef headRef cellRef readSize
      horizonArithmetic evaluatorCaps : ℕ}
    (hfrontier : frontier ≤ endpoint)
    (hstate : stateRef ≤ endpoint + index)
    (hhead : headRef ≤ endpoint + index)
    (hcell : cellRef ≤ endpoint + index)
    (hread : readSize ≤ index)
    (hhorizon : horizonArithmetic ≤ index)
    (hevaluator : evaluatorCaps ≤ evaluator) :
    frontier + stateRef + headRef + cellRef + readSize +
        horizonArithmetic + evaluatorCaps ≤
      4 * endpoint + 5 * index + evaluator := by
  omega

private theorem stepLoopValues_all_le
    (tm : TM k) (values : BinaryValues WorkCount)
    (hclean : StepClean values) (hhorizon : 0 < values Work.horizon)
    (n width : ℕ) (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon))
    (hvalues : ∀ index, values index ≤ width)
    (hend : n + configWidth tm.toNTM (values Work.horizon) +
        values Work.horizon *
          directStepSize tm.toNTM (values Work.horizon) ≤ width)
    (count : ℕ) (hcount : count ≤ values Work.horizon) :
    ∀ index,
      BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count index ≤ width := by
  induction count with
  | zero =>
      simpa [BinaryRoutine.binaryForValues] using hvalues
  | succ count ih =>
      have hcountPrev : count ≤ values Work.horizon := by omega
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hcurrentValues : ∀ index, current index ≤ width :=
        ih hcountPrev
      have hinvariant := stepLoopValues_numeric_invariant tm values hclean
        hhorizon n count hloop hconfigBase havailable
      have hcurrentClean : StepClean current := hinvariant.1
      have hcurrentHorizon :
          current Work.horizon = values Work.horizon := hinvariant.2.1
      have hcurrentAvailable :
          current Work.available =
            n + configWidth tm.toNTM (values Work.horizon) +
              count * directStepSize tm.toNTM
                (values Work.horizon) :=
        hinvariant.2.2.2.2
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      have hsize :
          stepScheduleSize (transitionCases tm.toNTM).length
              (Fintype.card tm.Q) k (current Work.horizon)
              (stepAtomKindAt tm.toNTM (current Work.horizon))
              (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
              (effectCaseChoiceAt tm.toNTM) =
            directStepSize tm.toNTM (values Work.horizon) := by
        rw [hcurrentHorizon]
        exact stepScheduleSize_eq_directStepSizeInternal tm.toNTM
          (values Work.horizon) (current Work.configBase)
      have hbase :
          stepScheduleOutputBase (transitionCases tm.toNTM).length
              (Fintype.card tm.Q) k (current Work.horizon)
              (current Work.available)
              (stepAtomKindAt tm.toNTM (current Work.horizon))
              (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
              (effectCaseChoiceAt tm.toNTM) =
            n + (count + 1) *
              directStepSize tm.toNTM (values Work.horizon) := by
        rw [hcurrentHorizon]
        exact stepScheduleOutputBase_eq_nextInternal tm
          (values Work.horizon) n count (current Work.available)
          (current Work.configBase) hcurrentAvailable
      have hmul := Nat.mul_le_mul_right
        (directStepSize tm.toNTM (values Work.horizon)) hcount
      have havailableNext :
          current Work.available +
              stepScheduleSize (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (current Work.horizon)
                (stepAtomKindAt tm.toNTM (current Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM
                  (current Work.horizon))
                (effectCaseChoiceAt tm.toNTM) ≤ width := by
        calc
          current Work.available +
                stepScheduleSize (transitionCases tm.toNTM).length
                  (Fintype.card tm.Q) k (current Work.horizon)
                  (stepAtomKindAt tm.toNTM (current Work.horizon))
                  (stepAtomEffectSelectedAt tm.toNTM
                    (current Work.horizon))
                  (effectCaseChoiceAt tm.toNTM) =
              n + configWidth tm.toNTM (values Work.horizon) +
                (count + 1) *
                  directStepSize tm.toNTM (values Work.horizon) := by
            rw [hsize, hcurrentAvailable]
            ring
          _ ≤ n + configWidth tm.toNTM (values Work.horizon) +
              values Work.horizon *
                directStepSize tm.toNTM (values Work.horizon) := by
            exact Nat.add_le_add_left hmul _
          _ ≤ width := hend
      have hbaseNext :
          stepScheduleOutputBase (transitionCases tm.toNTM).length
              (Fintype.card tm.Q) k (current Work.horizon)
              (current Work.available)
              (stepAtomKindAt tm.toNTM (current Work.horizon))
              (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
              (effectCaseChoiceAt tm.toNTM) ≤ width := by
        rw [hbase]
        calc
          n + (count + 1) *
                directStepSize tm.toNTM (values Work.horizon) ≤
              n + configWidth tm.toNTM (values Work.horizon) +
                (count + 1) *
                  directStepSize tm.toNTM (values Work.horizon) := by
            omega
          _ ≤ n + configWidth tm.toNTM (values Work.horizon) +
              values Work.horizon *
                directStepSize tm.toNTM (values Work.horizon) := by
            exact Nat.add_le_add_left hmul _
          _ ≤ width := hend
      rw [BinaryRoutine.binaryForValues]
      change ∀ index,
        Function.update ((emitStep tm).effect current) Work.loop₂
          (current Work.loop₂ + 1) index ≤ width
      apply BinaryRoutine.values_update_le Work.loop₂
      · rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
        exact BinaryRoutine.values_update_le Work.gateCount
          (BinaryRoutine.values_update_le Work.gateBound
            (BinaryRoutine.values_update_le Work.configBase
              (BinaryRoutine.values_update_le Work.available
                hcurrentValues havailableNext)
              hbaseNext)
            (Nat.zero_le _))
          (Nat.zero_le _)
      · have hhorizonWidth := hvalues Work.horizon
        have hcurrentLoop : current Work.loop₂ = count :=
          hinvariant.2.2.1
        rw [hcurrentLoop]
        omega

private theorem stepLoopInitialValues_le (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    let initial := (initialization tm).effect
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n))
    ∀ index, initial index ≤ (stepLoopWidthPolynomial tm q).eval n := by
  dsimp only
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let width := (stepLoopWidthPolynomial tm q).eval n
  have hwidthEval := stepLoopWidthPolynomial_eval tm q n
  have hn : n ≤ width := by
    dsimp only [width]
    rw [hwidthEval]
    omega
  have hT : T ≤ width := by
    dsimp only [T, width]
    rw [hwidthEval]
    omega
  have hfrontier :
      (TM.directSerializerFrontierPolynomial tm q).eval n ≤ width := by
    dsimp only [width]
    rw [hwidthEval]
    omega
  have hgateCount :
      (TM.directSerializerGateCountPolynomial tm q).eval n ≤ width := by
    dsimp only [width]
    rw [hwidthEval]
    omega
  have hendpoint : (stepLoopEndPolynomial tm q).eval n ≤ width := by
    dsimp only [width]
    rw [hwidthEval]
    omega
  have hfinal := stepLoopEnd_final_le tm q n
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  have havailableExact :
      n + Fintype.card tm.Q + (T + 1) * (k + 2) + 4 +
          4 * (T + 1) + (4 + 4 * (T + 1)) * (k + 1) =
        n + configWidth tm.toNTM T := by
    simp only [configWidth]
    rw [hcard]
    ring
  have havailable :
      n + Fintype.card tm.Q + (T + 1) * (k + 2) + 4 +
          4 * (T + 1) + (4 + 4 * (T + 1)) * (k + 1) ≤ width := by
    rw [havailableExact]
    calc
      n + configWidth tm.toNTM T ≤
          n + configWidth tm.toNTM T +
            T * directStepSize tm.toNTM T := by omega
      _ ≤ (stepLoopEndPolynomial tm q).eval n := by
        simpa only [T] using hfinal
      _ ≤ width := hendpoint
  have hzero : ∀ index : Fin WorkCount, (fun _ => 0) index ≤ width := by
    intro
    simp
  have hinput := BinaryRoutine.values_update_le Work.inputLength hzero hn
  have hhorizon := BinaryRoutine.values_update_le Work.horizon hinput hT
  have hfrontierValues := BinaryRoutine.values_update_le Work.frontier
    hhorizon hfrontier
  have hgateCountValues := BinaryRoutine.values_update_le Work.gateCount
    hfrontierValues hgateCount
  have havailableValues := BinaryRoutine.values_update_le Work.available
    hgateCountValues hn
  have hconfigBaseValues := BinaryRoutine.values_update_le Work.configBase
    havailableValues hn
  dsimp only [T] at hconfigBaseValues
  have hpreamble : ∀ index,
      preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n) index ≤
        width := by
    simpa [preambleValues, BinaryRoutine.inputLengthValues,
      Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
      Work.available, Work.configBase] using hconfigBaseValues
  rw [initialization_effect_preambleValues]
  exact BinaryRoutine.values_update_le Work.limit₀
    (BinaryRoutine.values_update_le Work.available hpreamble havailable)
    (Nat.zero_le _)

private theorem stepLoopWidthEnvelope (tm : TM k) (q : Polynomial ℕ)
    (n count : ℕ)
    (hcount : count < (TM.directSerializerHorizonPolynomial q).eval n) :
    let initial := (initialization tm).effect
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n))
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      initial count
    StepWidthEnvelope tm.toNTM current
      ((stepLoopWidthPolynomial tm q).eval n) := by
  dsimp only
  let entry := preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength n)
  let initial := (initialization tm).effect entry
  let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
    initial count
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let width := (stepLoopWidthPolynomial tm q).eval n
  change StepWidthEnvelope tm.toNTM current width
  have hinit : StepClean initial ∧ initial Work.horizon = T ∧
      initial Work.loop₂ = 0 ∧
      initial Work.frontier = n + tm.directUnrollingGateBound
        (TM.directSerializerHorizonPolynomial q).eval n ∧
      initial Work.configBase = n ∧
      initial Work.available = n + configWidth tm.toNTM T := by
    simpa only [initial, entry, T] using initializationEndpoint tm q n
  have hhorizon : 0 < initial Work.horizon := by
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [hinit.2.1]
    dsimp only [T]
    omega
  have hinitAvailable : initial Work.available =
      n + configWidth tm.toNTM (initial Work.horizon) := by
    rw [hinit.2.1]
    exact hinit.2.2.2.2.2
  have hinvariant := stepLoopValues_numeric_invariant tm initial hinit.1
    hhorizon n count hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable
  have hcurrentClean : StepClean current := hinvariant.1
  have hcurrentHorizon : current Work.horizon = T :=
    hinvariant.2.1.trans hinit.2.1
  have hcurrentBase : current Work.configBase =
      n + count * directStepSize tm.toNTM T := by
    have hbase := hinvariant.2.2.2.1
    change current Work.configBase =
      n + count * directStepSize tm.toNTM (initial Work.horizon) at hbase
    rw [hinit.2.1] at hbase
    exact hbase
  have hcurrentAvailable : current Work.available =
      n + configWidth tm.toNTM T +
        count * directStepSize tm.toNTM T := by
    have havailable := hinvariant.2.2.2.2
    change current Work.available =
      n + configWidth tm.toNTM (initial Work.horizon) +
        count * directStepSize tm.toNTM (initial Work.horizon) at havailable
    rw [hinit.2.1] at havailable
    exact havailable
  have hendpointWidth :
      (stepLoopEndPolynomial tm q).eval n ≤ width := by
    dsimp only [width]
    rw [stepLoopWidthPolynomial_eval]
    omega
  have hend := stepLoopEnd_final_le tm q n
  have hendWidth :
      n + configWidth tm.toNTM T + T * directStepSize tm.toNTM T ≤
        width := by
    have hend' :
        n + configWidth tm.toNTM T + T * directStepSize tm.toNTM T ≤
          (stepLoopEndPolynomial tm q).eval n := by
      simpa only [T] using hend
    exact hend'.trans hendpointWidth
  have hinitialValues : ∀ index, initial index ≤ width := by
    simpa only [initial, entry, width] using
      stepLoopInitialValues_le tm q n
  have hendInitial :
      n + configWidth tm.toNTM (initial Work.horizon) +
          initial Work.horizon *
            directStepSize tm.toNTM (initial Work.horizon) ≤ width := by
    rw [hinit.2.1]
    exact hendWidth
  have hcurrentValues : ∀ index, current index ≤ width := by
    have hcountInitial : count ≤ initial Work.horizon := by
      rw [hinit.2.1]
      exact Nat.le_of_lt hcount
    exact stepLoopValues_all_le tm initial hinit.1 hhorizon n width
      hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable hinitialValues
      hendInitial count hcountInitial
  refine ⟨hcurrentValues, ?_⟩
  intro state headTape writtenTape symbol stateIndex tapeIndex symbolIndex
    position hstate htape hsymbol hposition
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  have hconfig := configWidth_le tm.toNTM T
  rw [hcard] at hconfig
  have hstep := directStepSize_le_stepBound tm.toNTM T
  let stepBound := stepSizeCoeff tm.toNTM * (T + 2) ^ 2
  have hcountSucc : count + 1 ≤ T := by
    change count < T at hcount
    omega
  have hcountStep := Nat.mul_le_mul_left (count + 1) hstep
  have hcountHorizon := Nat.mul_le_mul_right stepBound hcountSucc
  have hcountBound :
      (count + 1) * directStepSize tm.toNTM T ≤ T * stepBound := by
    exact hcountStep.trans hcountHorizon
  have hcountDirect :
      count * directStepSize tm.toNTM T ≤
        (count + 1) * directStepSize tm.toNTM T := by
    exact Nat.mul_le_mul_right _ (Nat.le_succ count)
  have hsize :
      stepScheduleSize (transitionCases tm.toNTM).length
          (Fintype.card tm.Q) k (current Work.horizon)
          (stepAtomKindAt tm.toNTM (current Work.horizon))
          (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
          (effectCaseChoiceAt tm.toNTM) = directStepSize tm.toNTM T := by
    rw [hcurrentHorizon]
    exact stepScheduleSize_eq_directStepSizeInternal tm.toNTM T
      (current Work.configBase)
  have hfrontier :
      current Work.available +
          stepScheduleSize (transitionCases tm.toNTM).length
            (Fintype.card tm.Q) k (current Work.horizon)
            (stepAtomKindAt tm.toNTM (current Work.horizon))
            (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
            (effectCaseChoiceAt tm.toNTM) ≤
        (stepLoopEndPolynomial tm q).eval n := by
    rw [hsize, hcurrentAvailable]
    calc
      n + configWidth tm.toNTM T +
            count * directStepSize tm.toNTM T +
          directStepSize tm.toNTM T =
          n + configWidth tm.toNTM T +
            (count + 1) * directStepSize tm.toNTM T := by ring
      _ ≤ n + configWidth tm.toNTM T + T * stepBound := by
        exact Nat.add_le_add_left hcountBound _
      _ ≤ n + (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) +
          T * stepBound := by
        exact Nat.add_le_add_right (Nat.add_le_add_left hconfig n) _
      _ = (stepLoopEndPolynomial tm q).eval n := by
        rw [stepLoopEndPolynomial_eval]
  have hbaseEnd : current Work.configBase ≤
      (stepLoopEndPolynomial tm q).eval n := by
    rw [hcurrentBase]
    calc
      n + count * directStepSize tm.toNTM T ≤ n + T * stepBound :=
        Nat.add_le_add_left (hcountDirect.trans hcountBound) n
      _ ≤ n + (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) +
          T * stepBound := by omega
      _ = (stepLoopEndPolynomial tm q).eval n := by
        rw [stepLoopEndPolynomial_eval]
  have hpositionT : position ≤ T + 1 := by
    rw [hcurrentHorizon] at hposition
    exact hposition
  have hindices := stepLoopIndex_bounds tm.toNTM T
    (current Work.configBase) stateIndex tapeIndex symbolIndex position
    hstate htape hsymbol hpositionT
  let indexBound := (stepLoopIndexPolynomial tm.toNTM).eval T
  have hstateRef :
      transitionStateRef (current Work.configBase) stateIndex ≤
        (stepLoopEndPolynomial tm q).eval n + indexBound :=
    hindices.1.trans (Nat.add_le_add_right hbaseEnd indexBound)
  have hheadRef :
      transitionHeadRef (Fintype.card tm.toNTM.Q) T
            (current Work.configBase)
            tapeIndex position + tapeIndex + T + 1 ≤
        (stepLoopEndPolynomial tm q).eval n + indexBound := by
    exact hindices.2.1.trans (Nat.add_le_add_right hbaseEnd indexBound)
  have hcellRef :
      transitionCellRef (Fintype.card tm.toNTM.Q) (k + 2) T
            (current Work.configBase) tapeIndex position symbolIndex +
          (tapeIndex * (T + 2) + position) +
          (T + 2) + (k + 2) + tapeIndex + 4 ≤
        (stepLoopEndPolynomial tm q).eval n + indexBound := by
    exact hindices.2.2.1.trans
      (Nat.add_le_add_right hbaseEnd indexBound)
  have hread : caseReadSize T ≤ indexBound := hindices.2.2.2.1
  have hhorizonArithmetic : 2 * (T + 2) + T ≤ indexBound :=
    hindices.2.2.2.2
  have hevaluator := stepLoopEvaluator_caps tm.toNTM T state headTape
    writtenTape symbol
  have hfrontier' :
      current Work.available +
          stepScheduleSize (transitionCases tm.toNTM).length
            (Fintype.card tm.toNTM.Q) k T
            (stepAtomKindAt tm.toNTM T)
            (stepAtomEffectSelectedAt tm.toNTM T)
            (effectCaseChoiceAt tm.toNTM) ≤
        (stepLoopEndPolynomial tm q).eval n := by
    simpa only [hcard, hcurrentHorizon] using hfrontier
  rw [hcurrentHorizon]
  dsimp only [indexBound] at hstateRef hheadRef hcellRef hread
  dsimp only [indexBound] at hhorizonArithmetic hevaluator
  have hcap := stepLoopCap_sum_le hfrontier' hstateRef hheadRef hcellRef
    hread hhorizonArithmetic hevaluator
  have hcapWidth :
      4 * (stepLoopEndPolynomial tm q).eval n +
          5 * (stepLoopIndexPolynomial tm.toNTM).eval T +
          (stepLoopEvaluatorPolynomial tm.toNTM).eval T ≤ width := by
    dsimp only [width, T]
    rw [stepLoopWidthPolynomial_eval]
    omega
  calc
    _ =
        (current Work.available +
          stepScheduleSize (transitionCases tm.toNTM).length
            (Fintype.card tm.toNTM.Q) k T
            (stepAtomKindAt tm.toNTM T)
            (stepAtomEffectSelectedAt tm.toNTM T)
            (effectCaseChoiceAt tm.toNTM)) +
        transitionStateRef (current Work.configBase) stateIndex +
        (transitionHeadRef (Fintype.card tm.toNTM.Q) T
            (current Work.configBase) tapeIndex position + tapeIndex + T + 1) +
        (transitionCellRef (Fintype.card tm.toNTM.Q) (k + 2) T
              (current Work.configBase) tapeIndex position symbolIndex +
            (tapeIndex * (T + 2) + position) +
            (T + 2) + (k + 2) + tapeIndex + 4) +
        caseReadSize T + (2 * (T + 2) + T) +
        (2 * TM.binaryPolynomialValueCap
              predecessorHeadSchedulePolynomial T +
          2 * TM.binaryPolynomialValueCap
              (stateNextChildPolynomial tm.toNTM state) T +
          2 * TM.binaryPolynomialValueCap
              (headNextChildPolynomial tm.toNTM headTape) T +
          2 * TM.binaryPolynomialValueCap
              (writtenNextChildPolynomial tm.toNTM writtenTape symbol) T +
          2 * TM.binaryPolynomialValueCap
              (stateNextFormulaPolynomial tm.toNTM state) T +
          2 * TM.binaryPolynomialValueCap
              (headNextFormulaPolynomial tm.toNTM headTape) T +
          2 * TM.binaryPolynomialValueCap
              (writtenNextFormulaPolynomial tm.toNTM writtenTape symbol) T +
          2 * TM.binaryPolynomialValueCap (Polynomial.C 1) T) := by ring
    _ ≤ 4 * (stepLoopEndPolynomial tm q).eval n +
          5 * (stepLoopIndexPolynomial tm.toNTM).eval T +
          (stepLoopEvaluatorPolynomial tm.toNTM).eval T := hcap
    _ ≤ width := hcapWidth

private theorem stepLoopEmitted_eq_prefix (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n count : ℕ)
    (hcount : count ≤ values Work.horizon)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    BinaryRoutine.binaryForEmitted (emitStep tm) Work.loop₂ values count =
      (((List.finRange (values Work.horizon)).take count).flatMap
        (tm.directStepFragment (values Work.horizon) n)).flatMap
          CircuitCode.RawGate.encode := by
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted]
  | succ count ih =>
      have hindex : count < values Work.horizon := by omega
      have hprefix := ih (by omega)
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hinvariant := stepLoopValues_numeric_invariant tm values hclean
        hhorizon n count hloop hconfigBase havailable
      have hcurrentClean : StepClean current := hinvariant.1
      have hcurrentHorizon : current Work.horizon = values Work.horizon :=
        hinvariant.2.1
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      have hcurrentBase : current Work.configBase =
          n + count * directStepSize tm.toNTM (values Work.horizon) :=
        hinvariant.2.2.2.1
      have hcurrentAvailable : current Work.available =
          n + configWidth tm.toNTM (values Work.horizon) +
            count * directStepSize tm.toNTM (values Work.horizon) :=
        hinvariant.2.2.2.2
      have hlistIndex : count < (List.finRange (values Work.horizon)).length := by
        simpa using hindex
      have hget : (List.finRange (values Work.horizon))[count]'hlistIndex =
          (⟨count, hindex⟩ : Fin (values Work.horizon)) := by
        apply Fin.ext
        simp
      have htake :
          (List.finRange (values Work.horizon)).take (count + 1) =
            (List.finRange (values Work.horizon)).take count ++
              [(⟨count, hindex⟩ : Fin (values Work.horizon))] := by
        rw [List.take_succ_eq_append_getElem hlistIndex, hget]
      rw [BinaryRoutine.binaryForEmitted, hprefix,
        emitStep_emitted tm current hcurrentClean hhorizonCurrent, htake,
        List.flatMap_append]
      simp [TM.directStepFragment, hcurrentHorizon, hcurrentBase,
        hcurrentAvailable]

theorem emitTransitionSteps_sound_internal (tm : TM k) :
    (emitTransitionSteps tm).Sound :=
  ((emitStep_sound tm).binaryFor Work.loop₂ Work.horizon).seq
    (BinaryRoutine.clear_sound Work.loop₂)

theorem emitTransitionSteps_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hloop : values Work.loop₂ = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitTransitionSteps tm).requires values := by
  unfold emitTransitionSteps
  constructor
  · refine ⟨by decide, by omega, ?_⟩
    intro count hcount
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      values count
    have hinvariant := stepLoopValues_invariant tm values hclean hhorizon count
    have hcurrentClean : StepClean current := hinvariant.1
    have hcurrentHorizon : current Work.horizon = values Work.horizon :=
      hinvariant.2.1
    have hhorizonCurrent : 0 < current Work.horizon := by
      simpa [hcurrentHorizon] using hhorizon
    refine ⟨emitStep_requires tm current hcurrentClean hhorizonCurrent, ?_, ?_⟩
    · change (emitStep tm).effect current Work.loop₂ = current Work.loop₂
      rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
      simp [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
        Work.loop₂]
    · change (emitStep tm).effect current Work.horizon = current Work.horizon
      rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
      simp [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
        Work.horizon]
  · trivial

theorem tableauTransitionSteps_spaceBoundByPolynomial_internal
    (tm : TM k) (q : Polynomial ℕ) {initialSpace : ℕ → ℕ} :
    BinaryRoutine.SpaceBoundByWidthAt (tableauTransitionSteps tm)
      initialSpace
      (fun n => (initialization tm).effect
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)))
      (stepLoopWidthPolynomial tm q).eval := by
  let values := fun n => (initialization tm).effect
    (preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n))
  let width := (stepLoopWidthPolynomial tm q).eval
  have hendpoint : ∀ n,
      StepClean (values n) ∧
        values n Work.horizon =
          (TM.directSerializerHorizonPolynomial q).eval n ∧
        values n Work.loop₂ = 0 ∧
        values n Work.frontier = n + tm.directUnrollingGateBound
          (TM.directSerializerHorizonPolynomial q).eval n ∧
        values n Work.configBase = n ∧
        values n Work.available = n + configWidth tm.toNTM
          ((TM.directSerializerHorizonPolynomial q).eval n) := by
    intro n
    simpa only [values] using initializationEndpoint tm q n
  have hclean : ∀ n, StepClean (values n) := fun n => (hendpoint n).1
  have hhorizon : ∀ n, 0 < values n Work.horizon := by
    intro n
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [(hendpoint n).2.1]
    omega
  have hloop : ∀ n, values n Work.loop₂ = 0 :=
    fun n => (hendpoint n).2.2.1
  have hconfigBase : ∀ n, values n Work.configBase = n :=
    fun n => (hendpoint n).2.2.2.2.1
  have havailable : ∀ n, values n Work.available =
      n + configWidth tm.toNTM (values n Work.horizon) := by
    intro n
    rw [(hendpoint n).2.1]
    exact (hendpoint n).2.2.2.2.2
  have hwidth : ∀ n, values n Work.horizon ≤ width n := by
    intro n
    exact (by
      simpa only [values, width] using
        stepLoopInitialValues_le tm q n Work.horizon)
  have hclampedCount : ∀ code,
      min (Nat.unpair code).2
          (BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
            (values (Nat.unpair code).1) - 1) <
        (TM.directSerializerHorizonPolynomial q).eval
          (Nat.unpair code).1 := by
    intro code
    let n := (Nat.unpair code).1
    change min (Nat.unpair code).2
        (BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
          (values n) - 1) <
      (TM.directSerializerHorizonPolynomial q).eval n
    have hcount : BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
        (values n) = values n Work.horizon := by
      simp [BinaryRoutine.binaryForCount, hloop n]
    rw [hcount, (hendpoint n).2.1]
    have hpositive := hhorizon n
    rw [(hendpoint n).2.1] at hpositive
    omega
  have hclampedInvariant : ∀ code,
      let n := (Nat.unpair code).1
      let count := min (Nat.unpair code).2
        (BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
          (values n) - 1)
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        (values n) count
      StepClean current ∧ current Work.horizon = values n Work.horizon := by
    intro code
    dsimp only
    let n := (Nat.unpair code).1
    let count := min (Nat.unpair code).2
      (BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
        (values n) - 1)
    have hinvariant := stepLoopValues_invariant tm (values n) (hclean n)
      (hhorizon n) count
    exact ⟨hinvariant.1, hinvariant.2.1⟩
  have hclampedClean : ∀ code,
      StepClean (BinaryRoutine.binaryForClampedValues (emitStep tm)
        Work.loop₂ Work.horizon values code) := by
    intro code
    simpa only [BinaryRoutine.binaryForClampedValues] using
      (hclampedInvariant code).1
  have hclampedHorizon : ∀ code,
      0 < (BinaryRoutine.binaryForClampedValues (emitStep tm)
        Work.loop₂ Work.horizon values code) Work.horizon := by
    intro code
    have hinvariant := (hclampedInvariant code).2
    rw [BinaryRoutine.binaryForClampedValues, hinvariant]
    exact hhorizon (Nat.unpair code).1
  have hclampedEnvelope : ∀ code,
      StepWidthEnvelope tm.toNTM
        (BinaryRoutine.binaryForClampedValues (emitStep tm)
          Work.loop₂ Work.horizon values code)
        (width (Nat.unpair code).1) := by
    intro code
    let n := (Nat.unpair code).1
    let count := min (Nat.unpair code).2
      (BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
        (values n) - 1)
    have hcount := hclampedCount code
    have henvelope := stepLoopWidthEnvelope tm q n count hcount
    simpa only [BinaryRoutine.binaryForClampedValues, values, width, n, count]
      using henvelope
  have hbody : BinaryRoutine.SpaceBoundByWidthAt (emitStep tm)
      (fun code => initialSpace (Nat.unpair code).1)
      (BinaryRoutine.binaryForClampedValues (emitStep tm)
        Work.loop₂ Work.horizon values)
      (fun code => width (Nat.unpair code).1) :=
    emitStep_spaceBoundByWidth tm hclampedClean hclampedHorizon
      hclampedEnvelope
  change BinaryRoutine.SpaceBoundByWidthAt (tableauTransitionSteps tm)
    initialSpace values width
  apply BinaryRoutine.SpaceBoundByWidthAt.restrict
  unfold emitTransitionSteps
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
    · exact hwidth
    · intro n count hcount
      have hcountHorizon : count < values n Work.horizon := by
        simpa [BinaryRoutine.binaryForCount, hloop n] using hcount
      have hinvariant := stepLoopValues_numeric_invariant tm (values n)
        (hclean n) (hhorizon n) n count (hloop n) (hconfigBase n)
        (havailable n)
      rw [hinvariant.2.2.1]
      exact (Nat.le_of_lt hcountHorizon).trans (hwidth n)
    · exact hbody
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro n
    have hcount : BinaryRoutine.binaryForCount Work.loop₂ Work.horizon
        (values n) = values n Work.horizon := by
      simp [BinaryRoutine.binaryForCount, hloop n]
    have hinvariant := stepLoopValues_numeric_invariant tm (values n)
      (hclean n) (hhorizon n) n (values n Work.horizon) (hloop n)
      (hconfigBase n) (havailable n)
    change
      BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ (values n)
          (BinaryRoutine.binaryForCount Work.loop₂ Work.horizon (values n))
          Work.loop₂ ≤ width n
    rw [hcount, hinvariant.2.2.1]
    exact hwidth n

theorem tableauTransitionSteps_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (tableauTransitionSteps tm)
      TM.binaryLengthSpace
      (fun n => (initialization tm).effect
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n))) := by
  exact (tableauTransitionSteps_spaceBoundByPolynomial_internal
    (initialSpace := TM.binaryLengthSpace) tm q).to_log
      TM.binaryLengthSpace_bigO_log (stepLoopWidthPolynomial tm q)
      (fun _ => le_rfl)

theorem tableauTransitionSteps_sound_internal (tm : TM k) :
    (tableauTransitionSteps tm).Sound :=
  (emitTransitionSteps_sound_internal tm).restrict (TransitionEntry tm)
    fun values hentry =>
      emitTransitionSteps_requires_internal tm values hentry.clean
        hentry.loop₂ hentry.horizon

theorem tableauFinalization_sound_internal (tm : TM k) :
    (tableauFinalization tm).Sound :=
  (finalization_sound tm).restrict FinalizationEntry fun values hentry =>
    finalization_requires tm values hentry.emitCounter hentry.copyCounter
      hentry.addCounter hentry.multiplyCounter hentry.available

theorem emitTransitionSteps_effect_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitTransitionSteps tm).effect values =
      Function.update
        (BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ values
          (values Work.horizon - values Work.loop₂)) Work.loop₂ 0 := by
  rfl

private theorem transitionFinalValues_le (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    let initial := (initialization tm).effect
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n))
    ∀ index, (emitTransitionSteps tm).effect initial index ≤
      (stepLoopWidthPolynomial tm q).eval n := by
  dsimp only
  let initial := (initialization tm).effect
    (preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n))
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let width := (stepLoopWidthPolynomial tm q).eval n
  have hinit : StepClean initial ∧ initial Work.horizon = T ∧
      initial Work.loop₂ = 0 ∧
      initial Work.frontier = n + tm.directUnrollingGateBound
        (TM.directSerializerHorizonPolynomial q).eval n ∧
      initial Work.configBase = n ∧
      initial Work.available = n + configWidth tm.toNTM T := by
    simpa only [initial, T] using initializationEndpoint tm q n
  have hhorizon : 0 < initial Work.horizon := by
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [hinit.2.1]
    dsimp only [T]
    omega
  have hinitAvailable : initial Work.available =
      n + configWidth tm.toNTM (initial Work.horizon) := by
    rw [hinit.2.1]
    exact hinit.2.2.2.2.2
  have hinitialValues : ∀ index, initial index ≤ width := by
    simpa only [initial, width] using stepLoopInitialValues_le tm q n
  have hendpointWidth :
      (stepLoopEndPolynomial tm q).eval n ≤ width := by
    dsimp only [width]
    rw [stepLoopWidthPolynomial_eval]
    omega
  have hend := stepLoopEnd_final_le tm q n
  have hendInitial :
      n + configWidth tm.toNTM (initial Work.horizon) +
          initial Work.horizon *
            directStepSize tm.toNTM (initial Work.horizon) ≤ width := by
    rw [hinit.2.1]
    have hend' :
        n + configWidth tm.toNTM T + T * directStepSize tm.toNTM T ≤
          (stepLoopEndPolynomial tm q).eval n := by
      simpa only [T] using hend
    exact hend'.trans hendpointWidth
  have hloopValues : ∀ index,
      BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ initial
          (initial Work.horizon) index ≤ width :=
    stepLoopValues_all_le tm initial hinit.1 hhorizon n width
      hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable hinitialValues
      hendInitial (initial Work.horizon) le_rfl
  rw [emitTransitionSteps_effect_internal]
  change ∀ index,
    Function.update
        (BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ initial
          (initial Work.horizon - initial Work.loop₂)) Work.loop₂ 0 index ≤
      width
  rw [hinit.2.2.1, Nat.sub_zero]
  exact BinaryRoutine.values_update_le Work.loop₂ hloopValues
    (Nat.zero_le _)

theorem emitTransitionSteps_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hloop : values Work.loop₂ = 0) :
    (emitTransitionSteps tm).emitted values =
      BinaryRoutine.binaryForEmitted (emitStep tm) Work.loop₂ values
        (values Work.horizon) := by
  simp [emitTransitionSteps, BinaryRoutine.seq, BinaryRoutine.binaryFor,
    BinaryRoutine.clear, BinaryRoutine.binaryForCount, hloop]

theorem emitTransitionSteps_endpoint_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    let final := (emitTransitionSteps tm).effect values
    StepClean final ∧ final Work.horizon = values Work.horizon ∧
      final Work.loop₂ = 0 ∧
      final Work.frontier = values Work.frontier ∧
      final Work.configBase = n + values Work.horizon *
        directStepSize tm.toNTM (values Work.horizon) ∧
      final Work.available =
        n + configWidth tm.toNTM (values Work.horizon) +
          values Work.horizon *
            directStepSize tm.toNTM (values Work.horizon) := by
  let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ values
    (values Work.horizon)
  have hinvariant := stepLoopValues_numeric_invariant tm values hclean hhorizon n
    (values Work.horizon) hloop hconfigBase havailable
  have hfinalClean : StepClean (Function.update current Work.loop₂ 0) :=
    hinvariant.1.updateOuter_forEffect_internal _ Work.loop₂ _
      (Or.inr (Or.inr (Or.inr rfl)))
  rw [emitTransitionSteps_effect_internal, hloop, Nat.sub_zero]
  refine ⟨hfinalClean, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Work.loop₂, Work.horizon] using hinvariant.2.1
  · simp
  · rw [Function.update_of_ne (by decide)]
    exact stepLoopValues_frontier tm values hclean hhorizon
      (values Work.horizon)
  · simpa [Work.loop₂, Work.configBase] using hinvariant.2.2.2.1
  · simpa [Work.loop₂, Work.available] using hinvariant.2.2.2.2

theorem emitTransitionSteps_emitted_exact_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    (emitTransitionSteps tm).emitted values =
      ((List.finRange (values Work.horizon)).flatMap
        (tm.directStepFragment (values Work.horizon) n)).flatMap
          CircuitCode.RawGate.encode := by
  rw [emitTransitionSteps_emitted_internal tm values hloop,
    stepLoopEmitted_eq_prefix tm values hclean hhorizon n
      (values Work.horizon) le_rfl hloop hconfigBase havailable]
  rw [List.take_of_length_le (by simp)]

theorem positiveTableauBody_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (positiveTableauBody tm)
      TM.binaryLengthSpace
      (fun n => preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n)) := by
  let entry := fun n => preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength n)
  let afterInit := fun n => (initialization tm).effect (entry n)
  let afterSteps := fun n =>
    (tableauTransitionSteps tm).effect (afterInit n)
  have hinitialization :
      BinaryRoutine.SpaceBoundInLogAt (initialization tm)
        TM.binaryLengthSpace entry := by
    simpa only [entry] using initialization_space_bigO_log_internal tm q
  have htransition :
      BinaryRoutine.SpaceBoundInLogAt (tableauTransitionSteps tm)
        TM.binaryLengthSpace afterInit := by
    simpa only [afterInit, entry] using
      tableauTransitionSteps_space_bigO_log_internal tm q
  have hafterSteps : ∀ n index,
      afterSteps n index ≤ (stepLoopWidthPolynomial tm q).eval n := by
    intro n index
    simpa only [afterSteps, afterInit, entry, tableauTransitionSteps,
      BinaryRoutine.restrict] using transitionFinalValues_le tm q n index
  have hfinalizationRaw :
      BinaryRoutine.SpaceBoundInLogAt (finalization tm)
        TM.binaryLengthSpace afterSteps :=
    finalization_space_bigO_log_internal tm (stepLoopWidthPolynomial tm q)
      TM.binaryLengthSpace_bigO_log hafterSteps
  have hfinalization :
      BinaryRoutine.SpaceBoundInLogAt (tableauFinalization tm)
        TM.binaryLengthSpace afterSteps := by
    unfold tableauFinalization
    exact hfinalizationRaw.restrict_internal
  unfold positiveTableauBody
  apply BinaryRoutine.SpaceBoundInLogAt.seq_internal hinitialization
  apply BinaryRoutine.SpaceBoundInLogAt.seq_internal htransition
  simpa only [afterSteps, afterInit, entry] using hfinalization

theorem positiveTableauBody_sound_internal (tm : TM k) :
    (positiveTableauBody tm).Sound :=
  (initialization_sound tm).seq
    ((tableauTransitionSteps_sound_internal tm).seq
      (tableauFinalization_sound_internal tm))

set_option maxHeartbeats 2000000 in
theorem positiveTableauBody_requires_internal (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (positiveTableauBody tm).requires
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n)) := by
  let entry := preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength n)
  let afterInit := (initialization tm).effect entry
  let afterSteps := (emitTransitionSteps tm).effect afterInit
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let f := (TM.directSerializerHorizonPolynomial q).eval
  have hinit : StepClean afterInit ∧ afterInit Work.horizon = T ∧
      afterInit Work.loop₂ = 0 ∧
      afterInit Work.frontier = n + tm.directUnrollingGateBound f n ∧
      afterInit Work.configBase = n ∧
      afterInit Work.available = n + configWidth tm.toNTM T := by
    simpa only [afterInit, entry, T, f] using initializationEndpoint tm q n
  have hhorizon : 0 < afterInit Work.horizon := by
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [hinit.2.1]
    omega
  have hinitAvailable : afterInit Work.available =
      n + configWidth tm.toNTM (afterInit Work.horizon) := by
    rw [hinit.2.1]
    exact hinit.2.2.2.2.2
  have hstepsRaw := emitTransitionSteps_endpoint_internal tm afterInit hinit.1
    hhorizon n hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable
  have hsteps : StepClean afterSteps ∧
      afterSteps Work.horizon = afterInit Work.horizon ∧
      afterSteps Work.loop₂ = 0 ∧
      afterSteps Work.frontier = afterInit Work.frontier ∧
      afterSteps Work.configBase = n + afterInit Work.horizon *
        directStepSize tm.toNTM (afterInit Work.horizon) ∧
      afterSteps Work.available =
        n + configWidth tm.toNTM (afterInit Work.horizon) +
          afterInit Work.horizon *
            directStepSize tm.toNTM (afterInit Work.horizon) := by
    simpa only [afterSteps] using hstepsRaw
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hrawBound := tm.directUnrollingRawCircuit_length_le_gateBound f n
  rw [directUnrollingRawCircuit_length_eq_original] at hrawBound
  have hfinalBound : afterSteps Work.available + 1 ≤
      afterSteps Work.frontier := by
    rw [hsteps.2.2.2.2.2, hsteps.2.2.2.1, hinit.2.2.2.1,
      hinit.2.1]
    unfold directOriginalRawGateCount at hrawBound
    dsimp only [f, T] at hrawBound ⊢
    omega
  have htransition : TransitionEntry tm afterInit :=
    ⟨hinit.1, hinit.2.2.1, hhorizon⟩
  have hfinal : FinalizationEntry afterSteps :=
    ⟨hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.emitCounter,
      hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.copyCounter,
      hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.addCounter,
      hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.multiplyCounter,
      hfinalBound⟩
  have hinitRequires : (initialization tm).requires entry :=
    initialization_requires_preambleValues tm q n hn
  unfold positiveTableauBody tableauTransitionSteps tableauFinalization
    BinaryRoutine.restrict
  exact ⟨hinitRequires, htransition, hfinal⟩

set_option maxHeartbeats 2000000 in
theorem positiveTableauBody_emitted_internal (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) [NeZero n] (hn : 0 < n) :
    (positiveTableauBody tm).emitted
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)) =
      (tm.paddedDirectUnrollingRawCircuit
        (TM.directSerializerHorizonPolynomial q).eval n).flatMap
          CircuitCode.RawGate.encode := by
  let entry := preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength n)
  let afterInit := (initialization tm).effect entry
  let afterSteps := (emitTransitionSteps tm).effect afterInit
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let f := (TM.directSerializerHorizonPolynomial q).eval
  let original := directOriginalRawGateCount tm T
  let bound := tm.directUnrollingGateBound f n
  have hinit : StepClean afterInit ∧ afterInit Work.horizon = T ∧
      afterInit Work.loop₂ = 0 ∧
      afterInit Work.frontier = n + bound ∧
      afterInit Work.configBase = n ∧
      afterInit Work.available = n + configWidth tm.toNTM T := by
    simpa only [afterInit, entry, T, f, bound] using
      initializationEndpoint tm q n
  have hhorizon : 0 < afterInit Work.horizon := by
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [hinit.2.1]
    omega
  have hinitAvailable : afterInit Work.available =
      n + configWidth tm.toNTM (afterInit Work.horizon) := by
    rw [hinit.2.1]
    exact hinit.2.2.2.2.2
  have hstepsRaw := emitTransitionSteps_endpoint_internal tm afterInit hinit.1
    hhorizon n hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable
  have hsteps : StepClean afterSteps ∧
      afterSteps Work.horizon = afterInit Work.horizon ∧
      afterSteps Work.loop₂ = 0 ∧
      afterSteps Work.frontier = afterInit Work.frontier ∧
      afterSteps Work.configBase = n + afterInit Work.horizon *
        directStepSize tm.toNTM (afterInit Work.horizon) ∧
      afterSteps Work.available =
        n + configWidth tm.toNTM (afterInit Work.horizon) +
          afterInit Work.horizon *
            directStepSize tm.toNTM (afterInit Work.horizon) := by
    simpa only [afterSteps] using hstepsRaw
  have hinitEmitted := initialization_emitted_preambleValues tm q n
  have hstepsEmitted := emitTransitionSteps_emitted_exact_internal tm afterInit
    hinit.1 hhorizon n hinit.2.2.1 hinit.2.2.2.2.1
      hinitAvailable
  rw [hinit.2.1] at hstepsEmitted
  have havailable : afterSteps Work.available = n + original - 1 := by
    rw [hsteps.2.2.2.2.2]
    rw [hinit.2.1]
    dsimp only [original, T]
    unfold directOriginalRawGateCount
    omega
  have hfrontier : afterSteps Work.frontier = n + bound := by
    rw [hsteps.2.2.2.1, hinit.2.2.2.1]
  have hhorizonFinal : afterSteps Work.horizon = T := by
    rw [hsteps.2.1, hinit.2.1]
  have hconfigFinal : afterSteps Work.configBase =
      n + T * directStepSize tm.toNTM T := by
    rw [hsteps.2.2.2.2.1, hinit.2.1]
  have hfinalEmitted := finalization_emitted_eq_numericSchedule tm afterSteps
    n original bound T (n + T * directStepSize tm.toNTM T) hn havailable
      hfrontier hhorizonFinal hconfigFinal
  have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
  have hschedule := paddedDirectUnrollingRawCircuit_eq_numericSchedule tm f n
    hinputBound
  simp only [positiveTableauBody, tableauTransitionSteps,
    tableauFinalization, BinaryRoutine.restrict, BinaryRoutine.seq]
  rw [hinitEmitted, hstepsEmitted, hfinalEmitted, hschedule]
  dsimp only [entry, T, f, original, bound] at *
  simp only [List.flatMap_append, List.flatMap_singleton]
  simp [directFinalizationSuffix, List.append_assoc]

theorem paddedDirectUnrollingProgram_sound_internal (tm : TM k)
    (q : Polynomial ℕ) : (paddedDirectUnrollingProgram tm q).Sound :=
  program_sound tm q (positiveTableauBody_sound_internal tm)

theorem paddedDirectUnrollingProgram_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.SpaceBoundInLogAt (paddedDirectUnrollingProgram tm q)
      TM.binaryLengthSpace
      (BinaryRoutine.inputLengthValues Work.inputLength) := by
  unfold paddedDirectUnrollingProgram
  exact program_space_bigO_log_internal tm q (positiveTableauBody tm)
    (positiveTableauBody_space_bigO_log_internal tm q)

theorem paddedDirectUnrollingGenerator_space_bigO_log_internal
    (tm : TM k) (q : Polynomial ℕ) :
    BinaryRoutine.afterInputLengthSpace Work.inputLength
        (paddedDirectUnrollingProgram tm q) =O
      (fun n => Nat.log 2 n) :=
  BinaryRoutine.afterInputLengthSpace_bigO_log Work.inputLength
    (paddedDirectUnrollingProgram tm q)
    (paddedDirectUnrollingProgram_space_bigO_log_internal tm q)

theorem paddedDirectUnrollingProgram_requires_inputLengthValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).requires
      (BinaryRoutine.inputLengthValues Work.inputLength n) := by
  apply program_requires_inputLengthValues tm q (positiveTableauBody tm)
  intro length hlength
  exact positiveTableauBody_requires_internal tm q length hlength

theorem paddedDirectUnrollingProgram_emitted_internal (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).emitted
        (BinaryRoutine.inputLengthValues Work.inputLength n) =
      tm.paddedDirectUnrollingCode
        (TM.directSerializerHorizonPolynomial q).eval n := by
  cases n with
  | zero =>
      unfold paddedDirectUnrollingProgram
      rw [program_emitted]
      simp [TM.paddedDirectUnrollingCode,
        BinaryRoutine.inputLengthValues, Work.inputLength]
  | succ n =>
      unfold paddedDirectUnrollingProgram
      rw [program_emitted]
      simp only [BinaryRoutine.inputLengthValues, Work.inputLength,
        Function.update_self, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte]
      have hbody := positiveTableauBody_emitted_internal tm q (n + 1)
        (by omega)
      simp only [BinaryRoutine.inputLengthValues, Work.inputLength] at hbody
      rw [hbody]
      simp [TM.paddedDirectUnrollingCode, CircuitCode.RawCircuit.encode,
        TM.directSerializerGateCountPolynomial_eval,
        tm.paddedDirectUnrollingRawCircuit_length]

theorem paddedDirectUnrollingGenerator_computesInSpace_internal
    (tm : TM k) (q : Polynomial ℕ) :
    (BinaryRoutine.afterInputLength Work.inputLength
      (paddedDirectUnrollingProgram tm q)).ComputesInSpace
        (fun input => tm.paddedDirectUnrollingCode
          (TM.directSerializerHorizonPolynomial q).eval input.length)
        (BinaryRoutine.afterInputLengthSpace Work.inputLength
          (paddedDirectUnrollingProgram tm q)) := by
  have hcomputes := BinaryRoutine.Sound.afterInputLength_computesInSpace
    (paddedDirectUnrollingProgram_sound_internal tm q) Work.inputLength
    (paddedDirectUnrollingProgram_requires_inputLengthValues_internal tm q)
  convert hcomputes using 1
  funext input
  simpa only [BinaryRoutine.afterInputLengthFunction] using
    (paddedDirectUnrollingProgram_emitted_internal tm q input.length).symm

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
