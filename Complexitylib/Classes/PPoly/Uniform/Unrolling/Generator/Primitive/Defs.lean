/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Defs

/-!
# Direct-unrolling generator primitives -- definitions

This layer turns the serializer's numeric wire formulas into executable
`BinaryRoutine`s over the fixed direct-generator work layout. Recent-wire
references are prepared by copying `available` and applying a fixed number of
positive predecessors. Configuration-wire references are assembled from the
run-time layout values and fixed state/tape counts with framed binary
arithmetic.

The arithmetic helpers clear every general-purpose temporary that they use.
Their exact effects below therefore make the usual zero-scratch convention
explicit instead of pretending that an arbitrary previous temporary value is
preserved. All framed copy, addition, multiplication, and emission counters
are restored by their underlying leaves.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Copy `available` into `reference` and subtract a fixed recent-wire offset.
The routine domain honestly requires every predecessor to remain positive. -/
def prepareRecentReference (reference : Fin WorkCount) (offset : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryCopy Work.available reference Work.copyCounter)
    (BinaryRoutine.repeatRoutine offset (BinaryRoutine.binaryPred reference))

/-- Emit a raw gate whose inputs are fixed offsets behind the current first
unused wire, then clear both prepared-reference tapes. -/
def emitRecentGate (op : AndOrOp) (negated₀ negated₁ : Bool)
    (offset₀ offset₁ : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareRecentReference Work.reference₀ offset₀,
      prepareRecentReference Work.reference₁ offset₁,
      BinaryRoutine.emitRawGateStep op negated₀ negated₁
        Work.emitCounter Work.available Work.reference₀ Work.reference₁,
      BinaryRoutine.clear Work.reference₀,
      BinaryRoutine.clear Work.reference₁]

/-- Prepare the absolute state-wire reference `configBase + stateIndex` in
`reference₀`. -/
def prepareStateReference (stateIndex : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.set Work.reference₀ stateIndex)
    (BinaryRoutine.add Work.configBase Work.reference₀ Work.addCounter)

/-- Prepare the absolute head-wire reference in `reference₀` from the
run-time horizon, tape index, and position. `temporary₀` is cleared on exit. -/
def prepareHeadReference (stateCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.reference₀ stateCount,
      BinaryRoutine.add Work.configBase Work.reference₀ Work.addCounter,
      BinaryRoutine.set Work.temporary₀ 1,
      BinaryRoutine.add Work.horizon Work.temporary₀ Work.addCounter,
      BinaryRoutine.mulAdd Work.tapeIndex Work.temporary₀ Work.reference₀
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.add Work.position Work.reference₀ Work.addCounter,
      BinaryRoutine.clear Work.temporary₀]

/-- Prepare `configBase + stateCount + tapeCount * (horizon + 1)` and retain
`horizon + 1` in `temporary₀`. -/
def prepareCellReferenceBase (stateCount tapeCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.reference₀ stateCount,
      BinaryRoutine.add Work.configBase Work.reference₀ Work.addCounter,
      BinaryRoutine.set Work.temporary₀ 1,
      BinaryRoutine.add Work.horizon Work.temporary₀ Work.addCounter,
      BinaryRoutine.set Work.temporary₁ tapeCount,
      BinaryRoutine.mulAdd Work.temporary₀ Work.temporary₁ Work.reference₀
        Work.multiplyCounter Work.addCounter]

/-- Prepare `tapeIndex * (horizon + 2) + position` in `temporary₂`, reusing
the two values left by `prepareCellReferenceBase`. -/
def prepareCellPositionOffset : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.addConst Work.temporary₀ 1,
      BinaryRoutine.binaryCopy Work.tapeIndex Work.temporary₁ Work.copyCounter,
      BinaryRoutine.clear Work.temporary₂,
      BinaryRoutine.mulAdd Work.temporary₁ Work.temporary₀ Work.temporary₂
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.add Work.position Work.temporary₂ Work.addCounter]

/-- Add the four-symbol cell offset and symbol index to `reference₀`, then
clear all three arithmetic temporaries. -/
def finishCellReference : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.temporary₁ 4,
      BinaryRoutine.mulAdd Work.temporary₂ Work.temporary₁ Work.reference₀
        Work.multiplyCounter Work.addCounter,
      BinaryRoutine.add Work.symbolIndex Work.reference₀ Work.addCounter,
      BinaryRoutine.clear Work.temporary₀,
      BinaryRoutine.clear Work.temporary₁,
      BinaryRoutine.clear Work.temporary₂]

/-- Prepare the absolute cell-symbol wire reference in `reference₀` from
the run-time horizon, tape index, position, and symbol index. Temporaries zero
through two are cleared on exit. -/
def prepareCellReference (stateCount tapeCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareCellReferenceBase stateCount tapeCount,
      prepareCellPositionOffset,
      finishCellReference]

/-- Emit a possibly-negated copy of the wire placed in `reference₀` by a
preparation routine, then clear that reference tape. -/
def emitPreparedReference (prepare : BinaryRoutine WorkCount)
    (negated : Bool := false) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepare,
      BinaryRoutine.emitRawGateStep .and negated negated Work.emitCounter
        Work.available Work.reference₀ Work.reference₀,
      BinaryRoutine.clear Work.reference₀]

/-- Prepare and emit one numeric state-wire reference. -/
def emitStateReference (stateIndex : ℕ) (negated : Bool := false) :
    BinaryRoutine WorkCount :=
  emitPreparedReference (prepareStateReference stateIndex) negated

/-- Prepare and emit one numeric head-wire reference. -/
def emitHeadReference (stateCount : ℕ) (negated : Bool := false) :
    BinaryRoutine WorkCount :=
  emitPreparedReference (prepareHeadReference stateCount) negated

/-- Prepare and emit one numeric cell-symbol wire reference. -/
def emitCellReference (stateCount tapeCount : ℕ)
    (negated : Bool := false) : BinaryRoutine WorkCount :=
  emitPreparedReference (prepareCellReference stateCount tapeCount) negated

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
