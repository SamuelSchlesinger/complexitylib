/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next.Defs

/-!
# Numeric schedules for one packed transition step

This definitions layer streams one `nextFormula` schedule for every
configuration atom and then emits the packed successor copies in the same
order. Atom descriptors are exposed as natural-number oracles indexed by the
canonical atom counter. The fixed machine and `ConfigAtom` occur only in the
compile-time extractor definitions used by the literal adapter.

The run-time schedule state consists solely of natural numbers and Booleans:
numeric atom fields, numeric transition-case fields, prefix sizes, and Boolean
selection oracles.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Numeric number of atoms in one bounded configuration. -/
def stepAtomCount (stateCount workCount T : ℕ) : ℕ :=
  stateCount + (workCount + 2) * (T + 1) +
    4 * (workCount + 2) * (T + 2)

/-- Fixed compile-time atom lookup with an irrelevant start-state fallback
outside the canonical range. It never appears in run-time schedule state. -/
noncomputable def stepConfigAtomAt (tm : NTM k) (T index : ℕ) :
    ConfigAtom tm T :=
  if hindex : index < configWidth tm T then
    (configAtomEquiv tm T).symm ⟨index, hindex⟩
  else .state tm.qstart

/-- Compile-time numeric atom-kind oracle. -/
noncomputable def stepAtomKindAt (tm : NTM k) (T index : ℕ) : ℕ :=
  nextAtomKind (stepConfigAtomAt tm T index)

/-- Compile-time numeric state-index oracle. -/
noncomputable def stepAtomStateIndexAt
    (tm : NTM k) (T index : ℕ) : ℕ :=
  nextAtomStateIndex tm (stepConfigAtomAt tm T index)

/-- Compile-time numeric tape-index oracle. -/
noncomputable def stepAtomTapeIndexAt (tm : NTM k) (T index : ℕ) : ℕ :=
  nextAtomTapeIndex (stepConfigAtomAt tm T index)

/-- Compile-time numeric position oracle. -/
noncomputable def stepAtomPositionAt (tm : NTM k) (T index : ℕ) : ℕ :=
  nextAtomPosition (stepConfigAtomAt tm T index)

/-- Compile-time numeric symbol-index oracle. -/
noncomputable def stepAtomSymbolIndexAt
    (tm : NTM k) (T index : ℕ) : ℕ :=
  nextAtomSymbolIndex (stepConfigAtomAt tm T index)

/-- Compile-time atom/phase/case selection oracle. -/
noncomputable def stepAtomEffectSelectedAt
    (tm : NTM k) (T atomIndex phase caseIndex : ℕ) : Bool :=
  nextAtomEffectSelectedAt tm (stepConfigAtomAt tm T atomIndex) phase
    caseIndex

/-- Exact next-formula size at a numeric atom index, with zero outside the
canonical atom range. -/
def stepFormulaSizeAt
    (caseCount stateCount workCount T : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : ℕ) : ℕ :=
  if atomIndex < stepAtomCount stateCount workCount T then
    nextFormulaScheduleSize caseCount workCount T (kindAt atomIndex)
      (selectedAt atomIndex) choiceAt
  else 0

/-- First absolute wire available to one numeric next-atom schedule. -/
def stepFormulaAvailable
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : ℕ) : ℕ :=
  available + prefixSize
    (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
      choiceAt) atomIndex

/-- Numeric next-formula block at one canonical atom index. -/
def stepFormulaBlock
    (caseCount stateCount workCount T configBase choiceWire available
      haltStateIndex : ℕ)
    (kindAt atomStateIndexAt atomTapeIndexAt atomPositionAt
      atomSymbolIndexAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (atomIndex : ℕ) :
    CircuitCode.RawCircuit :=
  nextFormulaSchedule caseCount stateCount workCount T configBase choiceWire
    (stepFormulaAvailable caseCount stateCount workCount T available kindAt
      selectedAt choiceAt atomIndex)
    (kindAt atomIndex) (atomStateIndexAt atomIndex)
    (atomTapeIndexAt atomIndex) (atomPositionAt atomIndex)
    (atomSymbolIndexAt atomIndex) haltStateIndex (selectedAt atomIndex)
    choiceAt caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt

/-- Forward stream of every next-formula block in canonical atom order. -/
def stepFormulaGates
    (caseCount stateCount workCount T configBase choiceWire available
      haltStateIndex : ℕ)
    (kindAt atomStateIndexAt atomTapeIndexAt atomPositionAt
      atomSymbolIndexAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks (stepAtomCount stateCount workCount T) fun atomIndex =>
    stepFormulaBlock caseCount stateCount workCount T configBase choiceWire
      available haltStateIndex kindAt atomStateIndexAt atomTapeIndexAt
      atomPositionAt atomSymbolIndexAt selectedAt choiceAt caseStateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt atomIndex

/-- Absolute output reference of one compiled next formula. -/
def stepFormulaOutputRef
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : ℕ) : ℕ :=
  available + prefixSize
      (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
        choiceAt) (atomIndex + 1) -
    1

/-- Packed-output copy gate for one forward atom index. -/
def stepPackedCopyGate
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : ℕ) : CircuitCode.RawGate :=
  CircuitCode.RawGate.copy
    (stepFormulaOutputRef caseCount stateCount workCount T available kindAt
      selectedAt choiceAt atomIndex)

/-- Forward packed-copy suffix in canonical atom order. -/
def stepPackedCopies
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    CircuitCode.RawCircuit :=
  indexedBatchCopies available (stepAtomCount stateCount workCount T)
    (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
      choiceAt)

/-- First absolute wire of the packed successor-configuration block. -/
def stepScheduleOutputBase
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    ℕ :=
  available + prefixSize
    (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
      choiceAt) (stepAtomCount stateCount workCount T)

/-- Absolute packed successor wire of one canonical atom index. -/
def stepScheduleOutputRef
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : ℕ) : ℕ :=
  stepScheduleOutputBase caseCount stateCount workCount T available kindAt
      selectedAt choiceAt +
    atomIndex

/-- Complete numeric packed one-step schedule. -/
def stepSchedule
    (caseCount stateCount workCount T configBase choiceWire available
      haltStateIndex : ℕ)
    (kindAt atomStateIndexAt atomTapeIndexAt atomPositionAt
      atomSymbolIndexAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  stepFormulaGates caseCount stateCount workCount T configBase choiceWire
      available haltStateIndex kindAt atomStateIndexAt atomTapeIndexAt
      atomPositionAt atomSymbolIndexAt selectedAt choiceAt caseStateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt ++
    stepPackedCopies caseCount stateCount workCount T available kindAt
      selectedAt choiceAt

/-- Exact gate count of the complete numeric packed one-step schedule. -/
def stepScheduleSize
    (caseCount stateCount workCount T : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    ℕ :=
  prefixSize
      (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
        choiceAt) (stepAtomCount stateCount workCount T) +
    stepAtomCount stateCount workCount T

end Serializer

end CircuitUnrolling

end Complexity
