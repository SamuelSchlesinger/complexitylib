/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive.Defs

/-!
# Direct-unrolling read-formula generator -- definitions

This layer implements the horizon-dependent tape-read formula without a
run-time syntax tree or stack. A forward loop emits the three-gate member for
each possible head position. A false identity gate then seeds a stack-free
right fold: `reference₀` rolls backward through member outputs while the
current wire frontier supplies the preceding connector.

Only the first loop pair, the position counter, both references, and
temporaries zero through two are owned as scratch. In particular,
`temporary₃` remains available to an enclosing transition generator.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Clean entry state for the scratch tapes owned by read-formula emission.
Arithmetic and emission counters are included because the underlying framed
subroutines require them to be zero. -/
structure ReadFormulaClean (values : BinaryValues WorkCount) : Prop where
  /-- The member-position counter starts at zero. -/
  position : values Work.position = 0
  /-- The connector-rank counter starts at zero. -/
  loop₀ : values Work.loop₀ = 0
  /-- The shared dynamic-loop limit starts at zero. -/
  limit₀ : values Work.limit₀ = 0
  /-- The first prepared-reference tape starts at zero. -/
  reference₀ : values Work.reference₀ = 0
  /-- The second prepared-reference tape starts at zero. -/
  reference₁ : values Work.reference₁ = 0
  /-- The raw-gate emission counter is reusable. -/
  emitCounter : values Work.emitCounter = 0
  /-- The framed-copy counter is reusable. -/
  copyCounter : values Work.copyCounter = 0
  /-- The framed-multiplication counter is reusable. -/
  multiplyCounter : values Work.multiplyCounter = 0
  /-- The framed-addition counter is reusable. -/
  addCounter : values Work.addCounter = 0
  /-- The first arithmetic temporary starts at zero. -/
  temporary₀ : values Work.temporary₀ = 0
  /-- The second arithmetic temporary starts at zero. -/
  temporary₁ : values Work.temporary₁ = 0
  /-- The third arithmetic temporary starts at zero. -/
  temporary₂ : values Work.temporary₂ = 0

/-- Emit the three-gate read member at the current `position`. -/
def emitReadMember (stateCount tapeCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitHeadReference stateCount,
      emitCellReference stateCount tapeCount,
      emitRecentGate .and false false 2 1]

/-- Replace `limit₀` by the current horizon plus one. -/
def setReadFormulaLimit : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryCopy Work.horizon Work.limit₀ Work.copyCounter)
    (BinaryRoutine.addConst Work.limit₀ 1)

/-- Emit every read member while counting `position` from zero through the
horizon. -/
def emitReadMembers (stateCount tapeCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.binaryFor (emitReadMember stateCount tapeCount) Work.position
    Work.limit₀

/-- Emit the false identity gate used to seed the disjunction fold. -/
def emitReadIdentity : BinaryRoutine WorkCount :=
  BinaryRoutine.emitRawGateStep .and false true Work.emitCounter
    Work.available Work.reference₀ Work.reference₀

/-- Emit one connector from the member output held in `reference₀` and the
immediately preceding identity or connector gate. `reference₀` is retained
for the next reverse-rank iteration. -/
def emitReadConnector : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareRecentReference Work.reference₁ 1,
      BinaryRoutine.emitRawGateStep .or false false Work.emitCounter
        Work.available Work.reference₀ Work.reference₁,
      BinaryRoutine.clear Work.reference₁]

/-- Move the rolling member reference back by one three-gate block and emit
the next connector. -/
def emitReadNextConnector : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.repeatRoutine 3
      (BinaryRoutine.binaryPred Work.reference₀))
    emitReadConnector

/-- Emit one complete numeric read-formula schedule and restore all owned
scratch tapes. The sole lasting effect under `ReadFormulaClean` is advancing
`available`. -/
def emitReadFormula (stateCount tapeCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [setReadFormulaLimit,
      emitReadMembers stateCount tapeCount,
      BinaryRoutine.clear Work.position,
      emitReadIdentity,
      prepareRecentReference Work.reference₀ 2,
      emitReadConnector,
      BinaryRoutine.set Work.loop₀ 1,
      BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀ Work.limit₀,
      BinaryRoutine.clear Work.loop₀,
      BinaryRoutine.clear Work.limit₀,
      BinaryRoutine.clear Work.reference₀]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
