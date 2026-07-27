/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next.Internal

/-!
# Verified direct next-atom generation

This module exposes exact contracts for the four executable branches used by
the packed-step generator: state, head, immutable-cell copy, and writable-cell
update. The step dispatcher uses the update routine only at positive positions;
its numeric schedule contract itself remains valid at every in-range position.
Input cells and writable marker cells share the same copy routine because their
canonical raw schedules are literally identical.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- One immutable-cell copy is sound. -/
theorem emitNextCellCopy_sound
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).Sound :=
  emitNextCellCopy_sound_internal stateCount tapeCount tapeIndex symbolIndex

/-- The arithmetic and emission scratch required by an immutable-cell copy. -/
theorem emitNextCellCopy_requires
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).requires
      values :=
  emitNextCellCopy_requires_internal stateCount tapeCount tapeIndex symbolIndex
    values hcopy hadd hmultiply hemit

/-- An immutable-cell copy has an all-prefix width certificate when its fixed
selectors and the complete absolute-reference arithmetic fit one width. -/
theorem emitNextCellCopy_spaceBoundByWidth
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionCellRef stateCount tapeCount
          (values inputLength Work.horizon)
          (values inputLength Work.configBase) tapeIndex
          (values inputLength Work.position) symbolIndex +
          (tapeIndex * (values inputLength Work.horizon + 2) +
            values inputLength Work.position) +
          (values inputLength Work.horizon + 2) + tapeCount + tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex)
      initialSpace values width :=
  emitNextCellCopy_spaceBoundByWidth_internal stateCount tapeCount tapeIndex
    symbolIndex hvalues hcap

/-- An immutable-cell copy restores its scratch and advances the frontier by
exactly one gate. -/
@[simp] theorem emitNextCellCopy_effect
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (htape : values Work.tapeIndex = 0)
    (hsymbol : values Work.symbolIndex = 0)
    (htemporary₀ : values Work.temporary₀ = 0)
    (htemporary₁ : values Work.temporary₁ = 0)
    (htemporary₂ : values Work.temporary₂ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).effect values =
      Function.update values Work.available (values Work.available + 1) :=
  emitNextCellCopy_effect_internal stateCount tapeCount tapeIndex symbolIndex
    values htape hsymbol htemporary₀ htemporary₁ htemporary₂ hreference

/-- An immutable input or writable marker cell emits its literal canonical
one-gate copy schedule. -/
@[simp] theorem emitNextCellCopy_emitted
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).emitted values =
      (nextCellCopySchedule stateCount tapeCount (values Work.horizon)
        (values Work.configBase) tapeIndex (values Work.position)
        symbolIndex).flatMap CircuitCode.RawGate.encode :=
  emitNextCellCopy_emitted_internal stateCount tapeCount tapeIndex symbolIndex
    values

/-- Complete state-atom next-formula generation is sound. -/
theorem emitNextStateFormula_sound (tm : NTM k) (state : tm.Q) :
    (emitNextStateFormula tm state).Sound :=
  emitNextStateFormula_sound_internal tm state

/-- Clean case-formula scratch suffices for a complete state-atom formula. -/
theorem emitNextStateFormula_requires (tm : NTM k) (state : tm.Q)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitNextStateFormula tm state).requires values :=
  emitNextStateFormula_requires_internal tm state values hclean

/-- Complete state-atom generation has an all-prefix width certificate under
one envelope covering its frontier, nested selected-effect references, and
the fixed child-size polynomial evaluator. -/
theorem emitNextStateFormula_spaceBoundByWidth (tm : NTM k)
    (state : tm.Q) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        values inputLength Work.available +
            nextStateFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (effectCaseSelectedAt tm fun effect =>
                decide (effect.nextState = state))
              (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon +
          2 * TM.binaryPolynomialValueCap
            (stateNextChildPolynomial tm state)
            (values inputLength Work.horizon) ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitNextStateFormula tm state)
      initialSpace values width :=
  emitNextStateFormula_spaceBoundByWidth_internal tm state hclean hvalues
    hcap

/-- State-atom generation restores every owned register and advances only the
wire frontier by its exact schedule size. -/
@[simp] theorem emitNextStateFormula_effect (tm : NTM k) (state : tm.Q)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitNextStateFormula tm state).effect values =
      Function.update values Work.available
        (values Work.available +
          nextStateFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (effectCaseSelectedAt tm fun effect =>
              decide (effect.nextState = state))
            (effectCaseChoiceAt tm)) :=
  emitNextStateFormula_effect_internal tm state values hclean

/-- State-atom generation emits the canonical numeric halted-or schedule
byte for byte. -/
@[simp] theorem emitNextStateFormula_emitted (tm : NTM k) (state : tm.Q)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitNextStateFormula tm state).emitted values =
      (nextStateFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (stateIndex tm state)
        (stateIndex tm tm.qhalt)
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitNextStateFormula_emitted_internal tm state values hclean

/-- Complete head-atom next-formula generation is sound. -/
theorem emitNextHeadFormula_sound (tm : NTM k) (tape : TapeSlot k) :
    (emitNextHeadFormula tm tape).Sound :=
  emitNextHeadFormula_sound_internal tm tape

/-- Clean moved-head scratch, a positive horizon, and an in-range target
suffice for a complete head-atom formula. -/
theorem emitNextHeadFormula_requires (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitNextHeadFormula tm tape).requires values :=
  emitNextHeadFormula_requires_internal tm tape values hclean hhorizon htarget

/-- Complete head-atom generation has an all-prefix width certificate under
one envelope covering the moved-head child, predecessor arithmetic, both
polynomial evaluators, and every absolute configuration reference. -/
theorem emitNextHeadFormula_spaceBoundByWidth (tm : NTM k)
    (tape : TapeSlot k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      MovedHeadFormulaClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon + 1 →
        values inputLength Work.available +
            nextHeadFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
            (values inputLength Work.horizon) +
          2 * (values inputLength Work.horizon + 2) +
          values inputLength Work.horizon +
          2 * TM.binaryPolynomialValueCap (headNextChildPolynomial tm tape)
            (values inputLength Work.horizon) ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitNextHeadFormula tm tape)
      initialSpace values width :=
  emitNextHeadFormula_spaceBoundByWidth_internal tm tape hclean hhorizon
    htarget hvalues hcap

/-- Head-atom generation restores every owned register and advances only the
wire frontier by its exact schedule size. -/
@[simp] theorem emitNextHeadFormula_effect (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitNextHeadFormula tm tape).effect values =
      Function.update values Work.available
        (values Work.available +
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) :=
  emitNextHeadFormula_effect_internal tm tape values hclean hhorizon htarget

/-- Head-atom generation emits the canonical numeric moved-head wrapper
schedule byte for byte. -/
@[simp] theorem emitNextHeadFormula_emitted (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitNextHeadFormula tm tape).emitted values =
      (nextHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.index (values Work.position)
        (stateIndex tm tm.qhalt) (movedHeadCaseSelectedAt tm tape)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitNextHeadFormula_emitted_internal tm tape values hclean hhorizon htarget

/-- Complete positive writable-cell next-formula generation is sound. -/
theorem emitNextWrittenCellFormula_sound (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitNextWrittenCellFormula tm tape symbol).Sound :=
  emitNextWrittenCellFormula_sound_internal tm tape symbol

/-- Clean writable-cell scratch and an in-range position suffice for a
complete positive writable-cell formula. -/
theorem emitNextWrittenCellFormula_requires (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitNextWrittenCellFormula tm tape symbol).requires values :=
  emitNextWrittenCellFormula_requires_internal tm tape symbol values hclean
    hposition

/-- Complete writable-cell generation has an all-prefix width certificate
under one envelope covering its halted wrapper, nested selected-write child,
absolute references, and child-size polynomial evaluator. -/
theorem emitNextWrittenCellFormula_spaceBoundByWidth (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      WrittenCellFormulaClean (values inputLength))
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon + 1 →
        values inputLength Work.available +
            nextWrittenCellFormulaScheduleSize
              (transitionCases tm).length k
              (values inputLength Work.horizon)
              (writtenCellEffectSelectedAt tm tape symbol)
              (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon +
          2 * TM.binaryPolynomialValueCap
            (writtenNextChildPolynomial tm tape symbol)
            (values inputLength Work.horizon) ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitNextWrittenCellFormula tm tape symbol) initialSpace values width :=
  emitNextWrittenCellFormula_spaceBoundByWidth_internal tm tape symbol hclean
    hposition hvalues hcap

/-- Writable-cell generation restores every owned register and advances only
the wire frontier by its exact schedule size. -/
@[simp] theorem emitNextWrittenCellFormula_effect (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitNextWrittenCellFormula tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) :=
  emitNextWrittenCellFormula_effect_internal tm tape symbol values hclean

/-- Writable-cell generation emits the canonical numeric halted-or schedule
byte for byte. -/
@[simp] theorem emitNextWrittenCellFormula_emitted (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitNextWrittenCellFormula tm tape symbol).emitted values =
      (nextWrittenCellFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.toTapeSlot.index (values Work.position)
        (CircuitUnrolling.symbolIndex symbol) (stateIndex tm tm.qhalt)
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitNextWrittenCellFormula_emitted_internal tm tape symbol values hclean
    hposition

/-- Exact selected-effect child size for a state atom. -/
@[simp] theorem stateNextChildPolynomial_eval (tm : NTM k)
    (state : tm.Q) (T : ℕ) :
    (stateNextChildPolynomial tm state).eval T =
      effectFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) :=
  stateNextChildPolynomial_eval_internal tm state T

/-- Exact complete state-atom schedule size. -/
@[simp] theorem stateNextFormulaPolynomial_eval (tm : NTM k)
    (state : tm.Q) (T : ℕ) :
    (stateNextFormulaPolynomial tm state).eval T =
      nextStateFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) :=
  stateNextFormulaPolynomial_eval_internal tm state T

/-- Exact moved-head child size for a head atom. -/
@[simp] theorem headNextChildPolynomial_eval (tm : NTM k)
    (tape : TapeSlot k) (T : ℕ) :
    (headNextChildPolynomial tm tape).eval T =
      movedHeadFormulaScheduleSize (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) :=
  headNextChildPolynomial_eval_internal tm tape T

/-- Exact complete head-atom schedule size. -/
@[simp] theorem headNextFormulaPolynomial_eval (tm : NTM k)
    (tape : TapeSlot k) (T : ℕ) :
    (headNextFormulaPolynomial tm tape).eval T =
      nextHeadFormulaScheduleSize (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) :=
  headNextFormulaPolynomial_eval_internal tm tape T

/-- Exact written-cell child size for a writable-cell atom. -/
@[simp] theorem writtenNextChildPolynomial_eval (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) (T : ℕ) :
    (writtenNextChildPolynomial tm tape symbol).eval T =
      writtenCellScheduleSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) :=
  writtenNextChildPolynomial_eval_internal tm tape symbol T

/-- Exact complete writable-cell schedule size. -/
@[simp] theorem writtenNextFormulaPolynomial_eval (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) (T : ℕ) :
    (writtenNextFormulaPolynomial tm tape symbol).eval T =
      nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) :=
  writtenNextFormulaPolynomial_eval_internal tm tape symbol T

/-- A complete state-atom formula always emits at least one gate. -/
theorem stateNextFormulaPolynomial_eval_pos (tm : NTM k)
    (state : tm.Q) (T : ℕ) :
    0 < (stateNextFormulaPolynomial tm state).eval T :=
  stateNextFormulaPolynomial_eval_pos_internal tm state T

/-- A complete head-atom formula always emits at least one gate. -/
theorem headNextFormulaPolynomial_eval_pos (tm : NTM k)
    (tape : TapeSlot k) (T : ℕ) :
    0 < (headNextFormulaPolynomial tm tape).eval T :=
  headNextFormulaPolynomial_eval_pos_internal tm tape T

/-- A complete writable-cell formula always emits at least one gate. -/
theorem writtenNextFormulaPolynomial_eval_pos (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) (T : ℕ) :
    0 < (writtenNextFormulaPolynomial tm tape symbol).eval T :=
  writtenNextFormulaPolynomial_eval_pos_internal tm tape symbol T

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
