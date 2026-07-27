/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Defs

/-!
# Direct-unrolling initialization generator -- definitions

This module assembles the first positive tableau layer from proof-carrying
binary routines. Fixed machine state and tape multiplicities are unrolled at
definition time; input-dependent head and cell ranges use canonical binary
loops over natural counters.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Emit one raw constant gate and advance the first-unused-wire counter. -/
def emitConstantGate (value : Bool) : BinaryRoutine WorkCount :=
  BinaryRoutine.emitRawGateStep (if value then .or else .and) false true
    Work.emitCounter Work.available Work.reference₀ Work.reference₀

/-- Emit one possibly negated copy gate and advance the wire counter. -/
def emitCopyGate (reference : Fin WorkCount) (negated : Bool := false) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.emitRawGateStep .and negated negated Work.emitCounter
    Work.available reference reference

/-- Emit the four symbol gates of a left-marker cell. -/
def emitStartCell : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitConstantGate false, emitConstantGate false,
      emitConstantGate false, emitConstantGate true]

/-- Emit the four symbol gates of a blank cell. -/
def emitBlankCell : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitConstantGate false, emitConstantGate false,
      emitConstantGate true, emitConstantGate false]

/-- Emit one input data cell, using `loop₀` as its primary-input wire. -/
def emitInputDataCell : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitCopyGate Work.loop₀ true, emitCopyGate Work.loop₀,
      emitConstantGate false, emitConstantGate false]

/-- Emit the fixed initial-state one-hot segment. -/
noncomputable def emitInitialStates (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList <| List.ofFn fun index : Fin (Fintype.card tm.Q) =>
    emitConstantGate
      (decide (tm.qstart = (Fintype.equivFin tm.Q).symm index))

/-- Replace `limit₀` by the current horizon plus one. -/
def setHorizonLimit : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryCopy Work.horizon Work.limit₀ Work.copyCounter)
    (BinaryRoutine.addConst Work.limit₀ 1)

/-- Replace `limit₀` by the input length. -/
def setInputLimit : BinaryRoutine WorkCount :=
  BinaryRoutine.binaryCopy Work.inputLength Work.limit₀ Work.copyCounter

/-- Emit one initial head-position bit from the current position counter. -/
def emitHeadPosition : BinaryRoutine WorkCount :=
  BinaryRoutine.branchZero Work.loop₀ (emitConstantGate true)
    (emitConstantGate false)

/-- Emit all `T + 1` head-position gates for one named tape and restore the
position counter to zero. -/
def emitHeadTape : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryFor emitHeadPosition Work.loop₀ Work.limit₀)
    (BinaryRoutine.clear Work.loop₀)

/-- Emit the complete input-cell segment once `limit₀ = T + 1`. -/
def emitInputCells : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitStartCell,
      setInputLimit,
      BinaryRoutine.binaryFor emitInputDataCell Work.loop₀ Work.limit₀,
      setHorizonLimit,
      BinaryRoutine.binaryFor emitBlankCell Work.loop₀ Work.limit₀,
      BinaryRoutine.clear Work.loop₀]

/-- Emit one blank writable tape's marker and `T + 1` blank cells, restoring
the position counter to zero. -/
def emitBlankTape : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitStartCell,
      BinaryRoutine.binaryFor emitBlankCell Work.loop₀ Work.limit₀,
      BinaryRoutine.clear Work.loop₀]

/-- Emit the complete positive-input initialization raw-gate stream. The
entry contract is discharged later from `preambleValues`; on exit both loop
controller tapes are restored to zero for transition serialization. -/
noncomputable def initialization (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitInitialStates tm,
      setHorizonLimit,
      BinaryRoutine.repeatRoutine (k + 2) emitHeadTape,
      emitInputCells,
      BinaryRoutine.repeatRoutine (k + 1) emitBlankTape,
      BinaryRoutine.clear Work.limit₀]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
