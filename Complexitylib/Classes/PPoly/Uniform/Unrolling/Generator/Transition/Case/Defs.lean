/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Defs

/-!
# Direct-unrolling transition-case generator -- definitions

A fixed transition case has a choice literal, a state literal, and one read
formula for every named tape. Machine-dependent state and symbol data are
unrolled when the generator is defined. The variable-width conjunction suffix
keeps one rolling member-output reference: it steps backward by the common
read-formula size, then by the final one-gate state member. No formula stack is
materialized on a work tape.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Clean entry state for one fixed transition-case formula. -/
structure CaseFormulaClean (values : BinaryValues WorkCount) : Prop
    extends ReadFormulaClean values where
  /-- The dynamic reference-decrement counter is reusable. -/
  loop₃ : values Work.loop₃ = 0
  /-- The rolling dynamic offset starts clear. -/
  temporary₃ : values Work.temporary₃ = 0
  /-- The fixed-polynomial evaluator scratch starts clear. -/
  polynomialScratch : values Work.polynomialScratch = 0
  /-- The numeric tape selector starts clear. -/
  tapeIndex : values Work.tapeIndex = 0
  /-- The numeric symbol selector starts clear. -/
  symbolIndex : values Work.symbolIndex = 0

/-- Emit the fixed choice literal on deterministic choice wire zero. A false
literal is compiled as a copy followed by a negated copy of that fresh wire. -/
def emitCaseChoice (choiceValue : Bool) : BinaryRoutine WorkCount :=
  if choiceValue then emitCopyGate Work.reference₀
  else
    BinaryRoutine.seq (emitCopyGate Work.reference₀)
      (emitRecentGate .and true true 1 1)

/-- Set the numeric tape and symbol selectors, then emit their complete read
formula. -/
def emitCaseRead (stateCount workCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      emitReadFormula stateCount (workCount + 2)]

/-- Emit a consecutive fixed block of tape-read formulas. Machine-specific
symbol data stays in the defining function and is never stored on tape. -/
def emitCaseReads (stateCount workCount : ℕ) :
    (count start : ℕ) → (ℕ → ℕ) → BinaryRoutine WorkCount
  | 0, _start, _symbolAt => BinaryRoutine.identity
  | count + 1, start, symbolAt =>
      BinaryRoutine.seq
        (emitCaseRead stateCount workCount start (symbolAt 0))
        (emitCaseReads stateCount workCount count (start + 1)
          (fun index => symbolAt (index + 1)))

/-- Fixed forward member stream in choice/state/input/work/output order. -/
def emitCaseMembers
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitCaseChoice choiceValue,
      emitStateReference stateIndex,
      emitCaseRead stateCount workCount 0 inputSymbolIndex,
      emitCaseReads stateCount workCount workCount 1 workSymbolIndexAt,
      emitCaseRead stateCount workCount (workCount + 1) outputSymbolIndex]

/-- Store the common read-formula gate count `4 * (T + 1) + 1` in
`temporary₃`, clearing the arithmetic coefficient temporary on exit. -/
def prepareCaseReadSize : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.temporary₃ 5,
      BinaryRoutine.set Work.temporary₂ 4,
      BinaryRoutine.mulAdd Work.horizon Work.temporary₂ Work.temporary₃
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.clear Work.temporary₂]

/-- Emit one conjunction connector from the retained member reference and the
immediately preceding identity or connector gate. -/
def emitCaseConnector : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareRecentReference Work.reference₁ 1,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.reference₀ Work.reference₁,
      BinaryRoutine.clear Work.reference₁]

/-- Move the rolling output reference back by one read-formula block and emit
the next conjunction connector. -/
def emitPreviousCaseReadConnector : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (decrementReferenceBy Work.reference₀ Work.temporary₃ Work.loop₃)
    emitCaseConnector

/-- Move from the state-member output to the preceding choice-member output
and emit the final conjunction connector. -/
def emitPreviousCaseChoiceConnector : BinaryRoutine WorkCount :=
  BinaryRoutine.seq (BinaryRoutine.binaryPred Work.reference₀)
    emitCaseConnector

/-- Emit a fixed number of equal-width predecessor-member connectors. -/
def emitPreviousCaseReadConnectors : ℕ → BinaryRoutine WorkCount
  | 0 => BinaryRoutine.identity
  | count + 1 =>
      BinaryRoutine.seq emitPreviousCaseReadConnector
        (emitPreviousCaseReadConnectors count)

/-- Emit one complete fixed transition-case schedule. The sole lasting effect
under `CaseFormulaClean` is the advance of `available`. -/
def emitCaseFormula
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt,
      emitConstantGate true,
      prepareCaseReadSize,
      prepareRecentReference Work.reference₀ 2,
      emitCaseConnector,
      emitPreviousCaseReadConnectors (workCount + 2),
      emitPreviousCaseChoiceConnector,
      BinaryRoutine.clear Work.reference₀,
      BinaryRoutine.clear Work.temporary₃,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
