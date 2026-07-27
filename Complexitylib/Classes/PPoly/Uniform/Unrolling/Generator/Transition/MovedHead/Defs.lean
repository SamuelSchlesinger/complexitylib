/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Defs

/-!
# Direct-unrolling moved-head generator -- definitions

The three fixed direction members are emitted in left/right/stay order. The
run-time target position is saved while nested effect formulas reuse the
position register. Each completed member output is retained in one otherwise
unused enclosing register, so the final three-way disjunction needs no dynamic
size recomputation.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Clean moved-head entry. Updating `position` to zero exposes exactly the
case-formula scratch convention required by each nested effect formula. -/
structure MovedHeadFormulaClean (values : BinaryValues WorkCount) : Prop where
  /-- Nested case emission is clean once the target position is parked. -/
  caseClean : CaseFormulaClean (Function.update values Work.position 0)
  /-- Target-position save register starts clear. -/
  limit₂ : values Work.limit₂ = 0
  /-- The predecessor connector-loop counter starts clear. -/
  loop₁ : values Work.loop₁ = 0
  /-- First direction-output save register starts clear. -/
  savedOutput : values Work.savedOutput = 0
  /-- Second direction-output save register starts clear. -/
  direction : values Work.direction = 0
  /-- Third direction-output save register starts clear. -/
  atomKind : values Work.atomKind = 0

/-- Emit the selected transition effect for one fixed movement direction. -/
noncomputable def emitMovedHeadEffect (tm : NTM k) (tape : TapeSlot k)
    (direction : Dir3) : BinaryRoutine WorkCount :=
  emitEffectFormula tm fun effect => decide (effect.move tape = direction)

/-- Combine the selected-effect output with the predecessor-head output. The
effect output is `predecessorSize + 1` wires behind the current frontier. -/
noncomputable def emitMovedHeadConjunction : BinaryRoutine WorkCount :=
  emitPolynomialRecentGate predecessorHeadSchedulePolynomial 1 .and false
    false 1

/-- Preserve the immediately preceding member output in a fixed enclosing
register without emitting any code bits. -/
def saveMovedHeadMemberOutput (save : Fin WorkCount) :
    BinaryRoutine WorkCount :=
  prepareRecentReference save 1

/-- Emit one direction member, restore the nested case scratch convention,
and retain its conjunction output in `save`. -/
noncomputable def emitMovedHeadMember (tm : NTM k) (tape : TapeSlot k)
    (direction : Dir3) (directionCode : ℕ) (save : Fin WorkCount) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitMovedHeadEffect tm tape direction,
      BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
      BinaryRoutine.set Work.tapeIndex tape.index,
      emitPredecessorHeadFormula (Fintype.card tm.Q) directionCode,
      emitMovedHeadConjunction,
      saveMovedHeadMemberOutput save,
      BinaryRoutine.clear Work.position,
      BinaryRoutine.clear Work.tapeIndex]

/-- Emit one disjunction connector from a saved member output and the
immediately preceding identity or connector. -/
def emitSavedMovedHeadConnector (save : Fin WorkCount) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareRecentReference Work.reference₁ 1,
      BinaryRoutine.emitRawGateStep .or false false Work.emitCounter
        Work.available save Work.reference₁,
      BinaryRoutine.clear Work.reference₁]

/-- Emit the complete left/right/stay moved-head formula and restore the
original target position. -/
noncomputable def emitMovedHeadFormula (tm : NTM k)
    (tape : TapeSlot k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter,
      BinaryRoutine.clear Work.position,
      emitMovedHeadMember tm tape .left 0 Work.savedOutput,
      emitMovedHeadMember tm tape .right 1 Work.direction,
      emitMovedHeadMember tm tape .stay 2 Work.atomKind,
      emitConstantGate false,
      emitSavedMovedHeadConnector Work.atomKind,
      emitSavedMovedHeadConnector Work.direction,
      emitSavedMovedHeadConnector Work.savedOutput,
      BinaryRoutine.clear Work.atomKind,
      BinaryRoutine.clear Work.direction,
      BinaryRoutine.clear Work.savedOutput,
      BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
      BinaryRoutine.clear Work.limit₂]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
