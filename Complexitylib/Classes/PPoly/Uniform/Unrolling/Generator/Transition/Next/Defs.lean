/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.WrittenCell.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next.Defs

/-!
# Direct-unrolling next-atom generator -- definitions

State, head, and positive writable-cell atoms share one executable halted-or
wrapper. Its two long-distance references are recovered by evaluating the
fixed child-size polynomial after child emission. Immutable input cells and
writable marker cells use a direct old-cell copy.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Scratch registers owned by the fixed halted-or wrapper. The old-value and
child routines may impose additional branch-specific cleanliness contracts. -/
structure HaltedOrFormulaClean (values : BinaryValues WorkCount) : Prop where
  /-- First raw-gate reference starts clear. -/
  reference₀ : values Work.reference₀ = 0
  /-- Second raw-gate reference starts clear. -/
  reference₁ : values Work.reference₁ = 0
  /-- Raw-gate emission counter is reusable. -/
  emitCounter : values Work.emitCounter = 0
  /-- Framed-copy counter is reusable. -/
  copyCounter : values Work.copyCounter = 0
  /-- Polynomial multiplication counter is reusable. -/
  multiplyCounter : values Work.multiplyCounter = 0
  /-- Polynomial addition counter is reusable. -/
  addCounter : values Work.addCounter = 0
  /-- Dynamic-offset predecessor counter starts clear. -/
  loop₃ : values Work.loop₃ = 0
  /-- Evaluated dynamic offset starts clear. -/
  temporary₃ : values Work.temporary₃ = 0
  /-- Polynomial evaluation accumulator starts clear. -/
  polynomialScratch : values Work.polynomialScratch = 0

/-- Fixed halted-or wrapper around a one-gate old-value routine and a nested
next-value routine with a known horizon-size polynomial. -/
noncomputable def emitHaltedOrFormula (haltStateIndex : ℕ)
    (childSize : Polynomial ℕ) (oldValue nextValue : BinaryRoutine WorkCount) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitStateReference haltStateIndex,
      oldValue,
      emitRecentGate .and false false 2 1,
      emitStateReference haltStateIndex,
      emitRecentGate .and true true 1 1,
      nextValue,
      emitPolynomialRecentGate childSize 1 .and false false 1,
      emitPolynomialRecentGate childSize 4 .or false false 1]

/-- Emit a state atom's old-value copy. -/
def emitOldStateValue (stateIndex : ℕ) : BinaryRoutine WorkCount :=
  emitStateReference stateIndex

/-- Emit a head atom's old-value copy while preserving its run-time target
position. -/
def emitOldHeadValue (stateCount tapeIndex : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.tapeIndex tapeIndex,
      emitHeadReference stateCount,
      BinaryRoutine.clear Work.tapeIndex]

/-- Emit a cell atom's old-value copy while preserving its run-time position. -/
def emitOldCellValue (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      emitCellReference stateCount tapeCount,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

/-- Fixed selected-effect size polynomial for one state atom. -/
noncomputable def stateNextChildPolynomial (tm : NTM k)
    (state : tm.Q) : Polynomial ℕ :=
  effectSchedulePolynomial (transitionCases tm).length k
    (effectCaseSelectedAt tm fun effect => decide (effect.nextState = state))
    (effectCaseChoiceAt tm)

/-- Complete halted-or state-formula size polynomial. -/
noncomputable def stateNextFormulaPolynomial (tm : NTM k)
    (state : tm.Q) : Polynomial ℕ :=
  stateNextChildPolynomial tm state + Polynomial.C 7

/-- Fixed selected-effect routine for one state atom. -/
noncomputable def emitStateNextChild (tm : NTM k)
    (state : tm.Q) : BinaryRoutine WorkCount :=
  emitEffectFormula tm fun effect => decide (effect.nextState = state)

/-- Emit a complete state-atom next formula. -/
noncomputable def emitNextStateFormula (tm : NTM k)
    (state : tm.Q) : BinaryRoutine WorkCount :=
  emitHaltedOrFormula (stateIndex tm tm.qhalt)
    (stateNextChildPolynomial tm state)
    (emitOldStateValue (stateIndex tm state))
    (emitStateNextChild tm state)

/-- Fixed moved-head size polynomial for one named tape. -/
noncomputable def headNextChildPolynomial (tm : NTM k)
    (tape : TapeSlot k) : Polynomial ℕ :=
  movedHeadSchedulePolynomial (transitionCases tm).length k
    (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)

/-- Complete halted-or head-formula size polynomial. -/
noncomputable def headNextFormulaPolynomial (tm : NTM k)
    (tape : TapeSlot k) : Polynomial ℕ :=
  headNextChildPolynomial tm tape + Polynomial.C 7

/-- Emit a complete head-atom next formula at the run-time target position. -/
noncomputable def emitNextHeadFormula (tm : NTM k)
    (tape : TapeSlot k) : BinaryRoutine WorkCount :=
  emitHaltedOrFormula (stateIndex tm tm.qhalt)
    (headNextChildPolynomial tm tape)
    (emitOldHeadValue (Fintype.card tm.Q) tape.index)
    (emitMovedHeadFormula tm tape)

/-- Fixed written-cell size polynomial for one writable tape and symbol. -/
noncomputable def writtenNextChildPolynomial (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) : Polynomial ℕ :=
  writtenCellSchedulePolynomial (transitionCases tm).length k
    (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)

/-- Complete halted-or positive writable-cell size polynomial. -/
noncomputable def writtenNextFormulaPolynomial (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) : Polynomial ℕ :=
  writtenNextChildPolynomial tm tape symbol + Polynomial.C 7

/-- Emit a complete positive writable-cell next formula at the run-time
position. -/
noncomputable def emitNextWrittenCellFormula (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) : BinaryRoutine WorkCount :=
  emitHaltedOrFormula (stateIndex tm tm.qhalt)
    (writtenNextChildPolynomial tm tape symbol)
    (emitOldCellValue (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
    (emitWrittenCellFormula tm tape symbol)

/-- Emit one immutable input or writable marker-cell old-value copy. -/
def emitNextCellCopy (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  emitOldCellValue stateCount tapeCount tapeIndex symbolIndex

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
