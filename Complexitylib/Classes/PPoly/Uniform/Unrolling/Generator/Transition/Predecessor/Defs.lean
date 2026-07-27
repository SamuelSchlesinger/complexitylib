/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead.Defs

/-!
# Direct predecessor-head formula generation -- definitions

The member phase exploits the three fixed movement cases instead of testing
source/target equality at every position. Constant runs surround at most two
head-wire copies. The right-fold suffix uses a dynamic recent-wire offset
`2 + 2 * rank`, which directly selects reverse member outputs while the fixed
offset one selects the preceding identity or connector.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Clean scratch contract for predecessor-head formula emission. The target
position itself is deliberately not scratch and is preserved. -/
structure PredecessorHeadClean (values : BinaryValues WorkCount) : Prop where
  loop₀ : values Work.loop₀ = 0
  limit₀ : values Work.limit₀ = 0
  loop₁ : values Work.loop₁ = 0
  reference₀ : values Work.reference₀ = 0
  reference₁ : values Work.reference₁ = 0
  emitCounter : values Work.emitCounter = 0
  copyCounter : values Work.copyCounter = 0
  multiplyCounter : values Work.multiplyCounter = 0
  addCounter : values Work.addCounter = 0
  temporary₀ : values Work.temporary₀ = 0
  temporary₃ : values Work.temporary₃ = 0

/-- Replace `limit₀` by `horizon + 1`. -/
def setPredecessorHorizonLimit : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryCopy Work.horizon Work.limit₀ Work.copyCounter)
    (BinaryRoutine.addConst Work.limit₀ 1)

/-- Emit false constants while `loop₀ < limit₀`, then restore `loop₀`. -/
def emitPredecessorFalseRange : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀ Work.limit₀)
    (BinaryRoutine.clear Work.loop₀)

/-- Stay-direction member stream: false prefix, target head copy, false suffix. -/
def emitStayPredecessorMembers (stateCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.position Work.limit₀ Work.copyCounter,
      emitPredecessorFalseRange,
      emitHeadReference stateCount,
      BinaryRoutine.binaryCopy Work.position Work.loop₀ Work.copyCounter,
      BinaryRoutine.addConst Work.loop₀ 1,
      setPredecessorHorizonLimit,
      emitPredecessorFalseRange]

/-- Right movement at target zero has no predecessor. -/
def emitRightZeroPredecessorMembers : BinaryRoutine WorkCount :=
  BinaryRoutine.seq setPredecessorHorizonLimit emitPredecessorFalseRange

/-- Right movement at a positive target has source `target - 1`. -/
def emitRightPositivePredecessorMembers (stateCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.position Work.limit₀ Work.copyCounter,
      BinaryRoutine.binaryPred Work.limit₀,
      emitPredecessorFalseRange,
      BinaryRoutine.binaryPred Work.position,
      emitHeadReference stateCount,
      BinaryRoutine.addConst Work.position 1,
      BinaryRoutine.binaryCopy Work.position Work.loop₀ Work.copyCounter,
      setPredecessorHorizonLimit,
      emitPredecessorFalseRange]

/-- Complete right-direction member stream, branching only at target zero. -/
def emitRightPredecessorMembers (stateCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.branchZero Work.position emitRightZeroPredecessorMembers
    (emitRightPositivePredecessorMembers stateCount)

/-- Left movement at target zero has the two boundary predecessors zero and
one, followed by a false suffix. -/
def emitLeftZeroPredecessorMembers (stateCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitHeadReference stateCount,
      BinaryRoutine.addConst Work.position 1,
      emitHeadReference stateCount,
      BinaryRoutine.binaryPred Work.position,
      BinaryRoutine.set Work.loop₀ 2,
      setPredecessorHorizonLimit,
      emitPredecessorFalseRange]

/-- Compute `horizon - position` in `temporary₃`, restoring `loop₀`. -/
def preparePredecessorHorizonGap : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃ Work.copyCounter)
    (decrementReferenceBy Work.temporary₃ Work.position Work.loop₀)

/-- Finish a positive-target left member stream from the prepared horizon
gap. A zero gap means the preceding false prefix already filled the stream. -/
def emitLeftPositivePredecessorTail (stateCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.branchZero Work.temporary₃
    (BinaryRoutine.clear Work.temporary₃)
    (BinaryRoutine.seqList
      [BinaryRoutine.addConst Work.position 1,
        emitHeadReference stateCount,
        BinaryRoutine.binaryPred Work.position,
        BinaryRoutine.binaryPred Work.temporary₃,
        BinaryRoutine.binaryFor (emitConstantGate false) Work.loop₀
          Work.temporary₃,
        BinaryRoutine.clear Work.loop₀,
        BinaryRoutine.clear Work.temporary₃])

/-- Positive-target left movement emits `target + 1` false members and then
uses the horizon gap to decide whether a source `target + 1` exists. -/
def emitLeftPositivePredecessorMembers (stateCount : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.position Work.limit₀ Work.copyCounter,
      BinaryRoutine.addConst Work.limit₀ 1,
      emitPredecessorFalseRange,
      preparePredecessorHorizonGap,
      emitLeftPositivePredecessorTail stateCount,
      setPredecessorHorizonLimit]

/-- Complete left-direction member stream, branching only at target zero. -/
def emitLeftPredecessorMembers (stateCount : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.branchZero Work.position
    (emitLeftZeroPredecessorMembers stateCount)
    (emitLeftPositivePredecessorMembers stateCount)

/-- Forward predecessor members for one fixed direction code. Codes zero and
one are left and right; every other code follows the schedule's stay case. -/
def emitPredecessorHeadMembers (stateCount directionCode : ℕ) :
    BinaryRoutine WorkCount :=
  if directionCode = 0 then emitLeftPredecessorMembers stateCount
  else if directionCode = 1 then emitRightPredecessorMembers stateCount
  else emitStayPredecessorMembers stateCount

/-- Emit one reverse-rank OR connector, then advance its dynamic member
offset by two for the next rank. -/
def emitPredecessorHeadConnector : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (emitDynamicRecentGate .or false false Work.temporary₃ Work.loop₁ 1)
    (BinaryRoutine.addConst Work.temporary₃ 2)

/-- Emit the complete predecessor-head member stream, false identity, and
right-fold connector suffix, restoring every owned scratch tape. -/
def emitPredecessorHeadFormula (stateCount directionCode : ℕ) :
    BinaryRoutine WorkCount :=
  let routine := BinaryRoutine.seqList
      [emitPredecessorHeadMembers stateCount directionCode,
        emitConstantGate false,
        setPredecessorHorizonLimit,
        BinaryRoutine.set Work.temporary₃ 2,
        BinaryRoutine.binaryFor emitPredecessorHeadConnector Work.loop₀
          Work.limit₀,
        BinaryRoutine.clear Work.loop₀,
        BinaryRoutine.clear Work.limit₀,
        BinaryRoutine.clear Work.temporary₃]
  { routine with
    requires := fun values =>
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon }

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
