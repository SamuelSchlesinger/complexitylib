/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell.Defs

/-!
# Direct-unrolling written-cell generator -- definitions

The run-time cell position is parked while the nested selected-write effect
reuses the read-formula counters. The first head-at-cell output is retained in
one enclosing register; the remaining six gates then stream with only recent
references. The final represented cell has no head wire, detected by a bounded
subtraction from `horizon + 1` rather than a general equality routine.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Scratch contract for one numeric head-at-current-cell test. The cell
position and tape selector are inputs and are deliberately preserved. -/
structure HeadAtCurrentCellClean (values : BinaryValues WorkCount) : Prop where
  /-- The bounded subtraction controller starts clear. -/
  loop₃ : values Work.loop₃ = 0
  /-- The horizon-gap temporary starts clear. -/
  temporary₃ : values Work.temporary₃ = 0
  /-- The canonical constant-gate reference starts clear. -/
  reference₀ : values Work.reference₀ = 0
  /-- The raw-gate emission counter is reusable. -/
  emitCounter : values Work.emitCounter = 0
  /-- The framed-copy counter is reusable. -/
  copyCounter : values Work.copyCounter = 0
  /-- The framed-multiplication counter is reusable. -/
  multiplyCounter : values Work.multiplyCounter = 0
  /-- The framed-addition counter is reusable. -/
  addCounter : values Work.addCounter = 0
  /-- The head-reference arithmetic temporary starts clear. -/
  temporary₀ : values Work.temporary₀ = 0

/-- Clean writable-cell entry, allowing `position` itself to hold the positive
cell position while every nested case scratch register is otherwise clear. -/
structure WrittenCellFormulaClean (values : BinaryValues WorkCount) : Prop where
  /-- Nested case emission is clean after parking the cell position. -/
  caseClean : CaseFormulaClean (Function.update values Work.position 0)
  /-- Position-save register starts clear. -/
  limit₂ : values Work.limit₂ = 0
  /-- First head-test output save register starts clear. -/
  savedOutput : values Work.savedOutput = 0

/-- Emit the final head-at-cell gate from a prepared horizon gap. A zero gap
means that the current cell has no represented old-head wire. -/
def emitHeadAtCurrentCellGate (stateCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.branchZero Work.temporary₃ (emitConstantGate false)
    (emitHeadReference stateCount)

/-- Emit the numeric head-at-cell gate at the current tape and cell position.
The final cell `horizon + 1` emits false; every earlier cell copies its head
wire. -/
def emitHeadAtCurrentCell (stateCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.horizon Work.temporary₃ Work.copyCounter,
      BinaryRoutine.addConst Work.temporary₃ 1,
      decrementReferenceBy Work.temporary₃ Work.position Work.loop₃,
      emitHeadAtCurrentCellGate stateCount,
      BinaryRoutine.clear Work.temporary₃]

/-- Emit the transition effect selected by a fixed writable tape and symbol. -/
noncomputable def emitWrittenCellEffect (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) : BinaryRoutine WorkCount :=
  emitEffectFormula tm fun effect =>
    decide ((effect.write tape).toΓ = symbol)

/-- Emit the complete positive writable-cell formula for fixed tape/symbol
data and the run-time position in `Work.position`. -/
noncomputable def emitWrittenCellFormula (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) : BinaryRoutine WorkCount :=
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      emitHeadAtCurrentCell (Fintype.card tm.Q),
      prepareRecentReference Work.savedOutput 1,
      BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter,
      BinaryRoutine.clear Work.position,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex,
      emitWrittenCellEffect tm tape symbol,
      BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
      BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      prepareRecentReference Work.reference₁ 1,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.savedOutput Work.reference₁,
      BinaryRoutine.clear Work.reference₁,
      emitHeadAtCurrentCell (Fintype.card tm.Q),
      emitRecentGate .and true true 1 1,
      emitCellReference (Fintype.card tm.Q) (k + 2),
      emitRecentGate .and false false 2 1,
      emitRecentGate .or false false 5 1,
      BinaryRoutine.clear Work.savedOutput,
      BinaryRoutine.clear Work.limit₂,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
