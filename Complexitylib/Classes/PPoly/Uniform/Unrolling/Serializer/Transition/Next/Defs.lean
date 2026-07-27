/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell.Defs

/-!
# Numeric schedules for next-configuration atoms

This layer gives the five branches of `nextFormula` a common numeric
interface. An atom is represented by a natural kind code together with
natural state, tape, position, and symbol indices. A phase-indexed Boolean
oracle carries the fixed transition-case selection data needed by state,
head, and positive writable-cell branches.

The run-time schedule contains only natural numbers and Booleans. The fixed
machine and `ConfigAtom` appear solely in compile-time extractors used by the
literal proof adapter.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Numeric kind code for state atoms. -/
def nextStateAtomKind : ℕ := 0

/-- Numeric kind code for head atoms. -/
def nextHeadAtomKind : ℕ := 1

/-- Numeric kind code for immutable input-cell atoms. -/
def nextInputCellAtomKind : ℕ := 2

/-- Numeric kind code for immutable writable marker-cell atoms. -/
def nextWritableMarkerAtomKind : ℕ := 3

/-- Numeric kind code for positive writable-cell atoms. -/
def nextWritableCellAtomKind : ℕ := 4

/-- Numeric atom-kind extractor used only by the proof adapter. -/
def nextAtomKind {tm : NTM k} {T : ℕ} : ConfigAtom tm T → ℕ
  | .state _ => nextStateAtomKind
  | .head _ _ => nextHeadAtomKind
  | .cell .input _ _ => nextInputCellAtomKind
  | .cell (.work _) position _ =>
      if position.val = 0 then nextWritableMarkerAtomKind
      else nextWritableCellAtomKind
  | .cell .output position _ =>
      if position.val = 0 then nextWritableMarkerAtomKind
      else nextWritableCellAtomKind

/-- Numeric state index of a state atom; zero for every other atom kind. -/
noncomputable def nextAtomStateIndex (tm : NTM k) {T : ℕ} :
    ConfigAtom tm T → ℕ
  | .state state => stateIndex tm state
  | _ => 0

/-- Numeric tape index of a head or cell atom; zero for state atoms. -/
def nextAtomTapeIndex {tm : NTM k} {T : ℕ} : ConfigAtom tm T → ℕ
  | .state _ => 0
  | .head tape _ => tape.index.val
  | .cell tape _ _ => tape.index.val

/-- Numeric position of a head or cell atom; zero for state atoms. -/
def nextAtomPosition {tm : NTM k} {T : ℕ} : ConfigAtom tm T → ℕ
  | .state _ => 0
  | .head _ position => position.val
  | .cell _ position _ => position.val

/-- Numeric symbol index of a cell atom; zero for state and head atoms. -/
def nextAtomSymbolIndex {tm : NTM k} {T : ℕ} : ConfigAtom tm T → ℕ
  | .cell _ _ symbol => (symbolIndex symbol).val
  | _ => 0

/-- Numeric index of the fixed halted state. -/
noncomputable def nextHaltStateIndex (tm : NTM k) : ℕ :=
  stateIndex tm tm.qhalt

/-- Compile-time transition selection data specialized to one atom.

Phase zero is used by state and writable-cell schedules; head schedules use
the three movement-direction phase codes directly. -/
noncomputable def nextAtomEffectSelectedAt (tm : NTM k) {T : ℕ} :
    ConfigAtom tm T → ℕ → ℕ → Bool
  | .state state => fun _ =>
      effectCaseSelectedAt tm fun effect =>
        decide (effect.nextState = state)
  | .head tape _ => movedHeadCaseSelectedAt tm tape
  | .cell .input _ _ => fun _ _ => false
  | .cell (.work i) _ symbol => fun _ =>
      writtenCellEffectSelectedAt tm (.work i) symbol
  | .cell .output _ symbol => fun _ =>
      writtenCellEffectSelectedAt tm .output symbol

/-- The child of a halted-or wrapper begins five gates after the wrapper. -/
def nextFormulaChildAvailable (available : ℕ) : ℕ :=
  available + 5

/-- Numeric wire of the old atom selected by its kind and layout indices. -/
def nextAtomWire
    (stateCount tapeCount T configBase atomKind stateIndex tapeIndex position
      symbolIndex : ℕ) : ℕ :=
  if atomKind = nextStateAtomKind then configBase + stateIndex
  else if atomKind = nextHeadAtomKind then
    transitionHeadRef stateCount T configBase tapeIndex position
  else
    transitionCellRef stateCount tapeCount T configBase tapeIndex position
      symbolIndex

/-- Halted-or wrapper specialized to a one-gate old-atom copy. -/
def nextHaltedOrSchedule (haltWire available oldWire : ℕ)
    (nextSchedule : CircuitCode.RawCircuit) : CircuitCode.RawCircuit :=
  haltedOrSchedule haltWire available [CircuitCode.RawGate.copy oldWire]
    nextSchedule

/-- Exact size of a halted-or wrapper around a one-gate old atom. -/
def nextHaltedOrScheduleSize (nextSize : ℕ) : ℕ :=
  nextSize + 7

/-- Numeric schedule for a state atom. -/
def nextStateFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available
      stateIndex haltStateIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  nextHaltedOrSchedule (configBase + haltStateIndex) available
    (configBase + stateIndex)
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire (nextFormulaChildAvailable available) selectedAt choiceAt
      caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
      workSymbolIndexAt)

/-- Exact gate count of a numeric state-atom schedule. -/
def nextStateFormulaScheduleSize
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) : ℕ :=
  nextHaltedOrScheduleSize
    (effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt)

/-- Numeric schedule for a head atom. -/
def nextHeadFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      target haltStateIndex : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  nextHaltedOrSchedule (configBase + haltStateIndex) available
    (transitionHeadRef stateCount T configBase tapeIndex target)
    (movedHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire (nextFormulaChildAvailable available) tapeIndex target
      selectedAt choiceAt caseStateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt)

/-- Exact gate count of a numeric head-atom schedule. -/
def nextHeadFormulaScheduleSize
    (caseCount workCount T : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) : ℕ :=
  nextHaltedOrScheduleSize
    (movedHeadFormulaScheduleSize caseCount workCount T selectedAt choiceAt)

/-- One-gate schedule for an immutable input or writable marker cell. -/
def nextCellCopySchedule
    (stateCount tapeCount T configBase tapeIndex position symbolIndex : ℕ) :
    CircuitCode.RawCircuit :=
  [CircuitCode.RawGate.copy
    (transitionCellRef stateCount tapeCount T configBase tapeIndex position
      symbolIndex)]

/-- Exact gate count of an immutable cell schedule. -/
def nextCellCopyScheduleSize : ℕ := 1

/-- Numeric schedule for a positive writable-cell atom. -/
def nextWrittenCellFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex haltStateIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  nextHaltedOrSchedule (configBase + haltStateIndex) available
    (transitionCellRef stateCount (workCount + 2) T configBase tapeIndex
      position symbolIndex)
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire (nextFormulaChildAvailable available) tapeIndex position
      symbolIndex selectedAt choiceAt caseStateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt)

/-- Exact gate count of a positive writable-cell schedule. -/
def nextWrittenCellFormulaScheduleSize
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) : ℕ :=
  nextHaltedOrScheduleSize
    (writtenCellScheduleSize caseCount workCount T selectedAt choiceAt)

/-- Common numeric schedule interface for all five next-atom branches.

`selectedAt` is phase-indexed: phase zero supplies state/write selection, while
head atoms use direction phases zero through two. -/
def nextFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available atomKind
      stateIndex tapeIndex position symbolIndex haltStateIndex : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  if atomKind = nextStateAtomKind then
    nextStateFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available stateIndex haltStateIndex (selectedAt 0) choiceAt
      caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
  else if atomKind = nextHeadAtomKind then
    nextHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position haltStateIndex selectedAt choiceAt
      caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
  else if atomKind = nextWritableCellAtomKind then
    nextWrittenCellFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex haltStateIndex
      (selectedAt 0) choiceAt caseStateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt
  else
    nextCellCopySchedule stateCount (workCount + 2) T configBase tapeIndex
      position symbolIndex

/-- Exact gate count selected by the common numeric atom-kind interface. -/
def nextFormulaScheduleSize
    (caseCount workCount T atomKind : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) : ℕ :=
  if atomKind = nextStateAtomKind then
    nextStateFormulaScheduleSize caseCount workCount T (selectedAt 0) choiceAt
  else if atomKind = nextHeadAtomKind then
    nextHeadFormulaScheduleSize caseCount workCount T selectedAt choiceAt
  else if atomKind = nextWritableCellAtomKind then
    nextWrittenCellFormulaScheduleSize caseCount workCount T (selectedAt 0)
      choiceAt
  else nextCellCopyScheduleSize

end Serializer

end CircuitUnrolling

end Complexity
