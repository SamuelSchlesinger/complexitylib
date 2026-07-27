/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect.Defs

/-!
# Direct-unrolling transition-effect generator -- definitions

An effect formula is a fixed disjunction over the finite transition table.
Selected cases use the executable case-formula routine; unselected cases emit
one false gate. The suffix traverses the hardwired case table in reverse and
rolls one output reference backward by each intervening case size.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Emit one numeric transition-table member, selected or replaced by false
at generator-definition time. -/
noncomputable def emitEffectCaseAt (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (caseIndex : ℕ) :
    BinaryRoutine WorkCount :=
  if effectCaseSelectedAt tm selects caseIndex then
    emitCaseFormula (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex)
  else emitConstantGate false

/-- Emit `count` consecutive forward effect members beginning at the numeric
case index `start`. -/
noncomputable def emitEffectMembersFrom (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (start : ℕ) :
    ℕ → BinaryRoutine WorkCount
  | 0 => BinaryRoutine.identity
  | count + 1 =>
      BinaryRoutine.seq (emitEffectCaseAt tm selects start)
        (emitEffectMembersFrom tm selects (start + 1) count)

/-- Emit every forward case member of one fixed effect formula. -/
noncomputable def emitEffectMembers (tm : NTM k)
    (selects : TransitionEffect tm → Bool) : BinaryRoutine WorkCount :=
  emitEffectMembersFrom tm selects 0 (transitionCases tm).length

/-- Prepare the gate count of one effect member in `temporary₃`. Selected
case sizes are affine in the run-time horizon; unselected members have size
one. -/
def prepareEffectCaseSize (workCount : ℕ)
    (selected choiceValue : Bool) : BinaryRoutine WorkCount :=
  if selected then
    BinaryRoutine.seqList
      [BinaryRoutine.set Work.temporary₃
          (6 * workCount + 16 + caseChoiceLiteralSize choiceValue),
        BinaryRoutine.set Work.temporary₂ (4 * (workCount + 2)),
        BinaryRoutine.mulAdd Work.horizon Work.temporary₂ Work.temporary₃
          Work.multiplyCounter Work.addCounter,
        BinaryRoutine.clear Work.temporary₂]
  else BinaryRoutine.set Work.temporary₃ 1

/-- Roll the retained case-output reference back by one complete member and
emit the next disjunction connector. -/
def emitPreviousEffectConnector (workCount : ℕ)
    (selected choiceValue : Bool) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [prepareEffectCaseSize workCount selected choiceValue,
      decrementReferenceBy Work.reference₀ Work.temporary₃ Work.loop₃,
      emitReadConnector,
      BinaryRoutine.clear Work.temporary₃]

/-- Emit `count` predecessor connectors, crossing case members with numeric
indices `count, ..., 1`. Index zero is omitted because no member precedes the
original first case. -/
noncomputable def emitPreviousEffectConnectorsCount (tm : NTM k)
    (selects : TransitionEffect tm → Bool) : ℕ → BinaryRoutine WorkCount
  | 0 => BinaryRoutine.identity
  | count + 1 =>
      BinaryRoutine.seq
        (emitPreviousEffectConnector k
          (effectCaseSelectedAt tm selects (count + 1))
          (effectCaseChoiceAt tm (count + 1)))
        (emitPreviousEffectConnectorsCount tm selects count)

/-- Reverse connector routines in the exact numeric right-fold order. A
table of `m` cases crosses the `m - 1` predecessor boundaries. -/
noncomputable def emitPreviousEffectConnectors (tm : NTM k)
    (selects : TransitionEffect tm → Bool) : BinaryRoutine WorkCount :=
  emitPreviousEffectConnectorsCount tm selects
    ((transitionCases tm).length - 1)

/-- Emit the connector suffix for a nonempty case table, or the routine
identity for the vacuous disjunction. -/
noncomputable def emitEffectConnectors (tm : NTM k)
    (selects : TransitionEffect tm → Bool) : BinaryRoutine WorkCount :=
  if (transitionCases tm).isEmpty then BinaryRoutine.identity
  else
    BinaryRoutine.seqList
      [prepareRecentReference Work.reference₀ 2,
        emitReadConnector,
        emitPreviousEffectConnectors tm selects,
        BinaryRoutine.clear Work.reference₀]

/-- Emit one complete transition-effect schedule. -/
noncomputable def emitEffectFormula (tm : NTM k)
    (selects : TransitionEffect tm → Bool) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [emitEffectMembers tm selects,
      emitConstantGate false,
      emitEffectConnectors tm selects]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
