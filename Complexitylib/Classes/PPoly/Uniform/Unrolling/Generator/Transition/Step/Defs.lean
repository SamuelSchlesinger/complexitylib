/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Step.Defs

/-!
# Direct-unrolling packed-step generator -- definitions

One step enumerates states, heads, and cells in the explicit configuration
wire order. After all next formulas have streamed, it replays the same compact
enumeration using only fixed size polynomials to emit the delayed packed-output
copies. `gateBound` temporarily saves the formula-stream base and `gateCount`
is reused, after its header has already been emitted, as the rolling source
cursor. Neither requires a new work tape.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Clean entry for one packed transition layer. The stronger moved-head
contract contains every scratch condition needed by the other next-atom
branches; `position` and the shared outer position limit are additionally
zero at whole-step entry. -/
structure StepClean (values : BinaryValues WorkCount) : Prop where
  /-- All nested next-formula scratch is reusable. -/
  movedHeadClean : MovedHeadFormulaClean values
  /-- The explicit atom-position counter starts clear. -/
  position : values Work.position = 0
  /-- The explicit atom-position limit starts clear. -/
  limit₁ : values Work.limit₁ = 0

/-- One shared numeric envelope for every prefix of a packed transition step.
The first field retains arbitrary incoming registers. The second dominates the
complete output frontier together with every absolute reference and polynomial
evaluator that can be live inside a nested next-formula or delayed-copy phase. -/
structure StepWidthEnvelope (tm : NTM k) (values : BinaryValues WorkCount)
    (width : ℕ) : Prop where
  /-- Every incoming register fits the common width. -/
  values_le : ∀ index, values index ≤ width
  /-- The complete step frontier and every nested arithmetic quantity fit
  simultaneously. -/
  cap : ∀ (state : tm.Q) (headTape : TapeSlot k)
      (writtenTape : WritableSlot k) (symbol : Γ)
      (stateIndex tapeIndex symbolIndex position : ℕ),
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 → position ≤ values Work.horizon + 1 →
        values Work.available +
              stepScheduleSize (transitionCases tm).length
                (Fintype.card tm.Q) k (values Work.horizon)
                (stepAtomKindAt tm (values Work.horizon))
                (stepAtomEffectSelectedAt tm (values Work.horizon))
                (effectCaseChoiceAt tm) +
            transitionStateRef (values Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q) (values Work.horizon)
                (values Work.configBase) tapeIndex position +
              tapeIndex + values Work.horizon + 1) +
        (transitionCellRef (Fintype.card tm.Q) (k + 2)
              (values Work.horizon) (values Work.configBase) tapeIndex
              position symbolIndex +
            (tapeIndex * (values Work.horizon + 2) + position) +
          (values Work.horizon + 2) + (k + 2) + tapeIndex + 4) +
        caseReadSize (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
          (values Work.horizon) +
        2 * (values Work.horizon + 2) + values Work.horizon +
        2 * TM.binaryPolynomialValueCap (stateNextChildPolynomial tm state)
          (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap
          (headNextChildPolynomial tm headTape) (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap
          (writtenNextChildPolynomial tm writtenTape symbol)
          (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap
          (stateNextFormulaPolynomial tm state) (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap
          (headNextFormulaPolynomial tm headTape) (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap
          (writtenNextFormulaPolynomial tm writtenTape symbol)
          (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap (Polynomial.C 1)
          (values Work.horizon) ≤ width

/-- Replace the outer position limit by `horizon + extra`. -/
def setStepPositionLimit (extra : ℕ) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryCopy Work.horizon Work.limit₁ Work.copyCounter)
    (BinaryRoutine.addConst Work.limit₁ extra)

/-- Emit all fixed state-atom next formulas. -/
noncomputable def emitStepStateFormulas (tm : NTM k) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList <| List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
    emitNextStateFormula tm ((Fintype.equivFin tm.Q).symm stateIndex)

/-- Emit the remaining head-position formulas for one fixed named tape,
starting at the current position and stopping at the shared limit. -/
noncomputable def emitStepHeadTapeFormulas (tm : NTM k)
    (tape : TapeSlot k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryFor (emitNextHeadFormula tm tape) Work.position
      Work.limit₁)
    (BinaryRoutine.clear Work.position)

/-- Emit the four immutable cell formulas at the current position. -/
noncomputable def emitStepImmutableCellPosition (tm : NTM k)
    (tape : TapeSlot k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList <| List.ofFn fun symbolIndex : Fin 4 =>
    emitNextCellCopy (Fintype.card tm.Q) (k + 2) tape.index
      (symbolEquiv.symm symbolIndex |> CircuitUnrolling.symbolIndex)

/-- Emit the four writable-cell formulas at the current position, using the
immutable marker schedule exactly at position zero. -/
noncomputable def emitStepWritableCellPosition (tm : NTM k)
    (tape : WritableSlot k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList <| List.ofFn fun symbolIndex : Fin 4 =>
    let symbol := symbolEquiv.symm symbolIndex
    BinaryRoutine.branchZero Work.position
      (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
        tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
      (emitNextWrittenCellFormula tm tape symbol)

/-- Emit the remaining cell-position formulas for one fixed named tape,
starting at the current position and stopping at the shared limit. -/
noncomputable def emitStepCellTapeFormulas (tm : NTM k) :
    TapeSlot k → BinaryRoutine WorkCount
  | .input =>
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor (emitStepImmutableCellPosition tm .input)
          Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position)
  | .work index =>
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor
          (emitStepWritableCellPosition tm (.work index)) Work.position
          Work.limit₁)
        (BinaryRoutine.clear Work.position)
  | .output =>
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor (emitStepWritableCellPosition tm .output)
          Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position)

/-- Emit the complete forward next-formula stream in canonical atom order. -/
noncomputable def emitStepFormulas (tm : NTM k) : BinaryRoutine WorkCount :=
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  BinaryRoutine.seqList
    ([emitStepStateFormulas tm,
        setStepPositionLimit 1] ++
      tapes.map (emitStepHeadTapeFormulas tm) ++
      [setStepPositionLimit 2] ++
      tapes.map (emitStepCellTapeFormulas tm) ++
      [BinaryRoutine.clear Work.limit₁])

/-- Emit all delayed state-formula output copies. -/
noncomputable def emitStepStateCopies (tm : NTM k) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList <| List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
    let state := (Fintype.equivFin tm.Q).symm stateIndex
    emitPackedFormulaCopy (stateNextFormulaPolynomial tm state)

/-- Emit the remaining delayed head-formula output copies for one fixed tape,
starting at the current position and stopping at the shared limit. -/
noncomputable def emitStepHeadTapeCopies (tm : NTM k)
    (tape : TapeSlot k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seq
    (BinaryRoutine.binaryFor
      (emitPackedFormulaCopy (headNextFormulaPolynomial tm tape)) Work.position
      Work.limit₁)
    (BinaryRoutine.clear Work.position)

/-- Emit four one-gate immutable-cell output copies at the current position. -/
noncomputable def emitStepImmutableCellCopies : BinaryRoutine WorkCount :=
  BinaryRoutine.repeatRoutine 4
    (emitPackedFormulaCopy (Polynomial.C 1))

/-- Emit four writable-cell output copies at the current position. -/
noncomputable def emitStepWritableCellCopies (tm : NTM k)
    (tape : WritableSlot k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList <| List.ofFn fun symbolIndex : Fin 4 =>
    let symbol := symbolEquiv.symm symbolIndex
    BinaryRoutine.branchZero Work.position
      (emitPackedFormulaCopy (Polynomial.C 1))
      (emitPackedFormulaCopy (writtenNextFormulaPolynomial tm tape symbol))

/-- Replay the remaining cell enumeration to emit delayed copies for one tape,
starting at the current position and stopping at the shared limit. -/
noncomputable def emitStepCellTapeCopies (tm : NTM k) :
    TapeSlot k → BinaryRoutine WorkCount
  | .input =>
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor emitStepImmutableCellCopies Work.position
          Work.limit₁)
        (BinaryRoutine.clear Work.position)
  | .work index =>
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor (emitStepWritableCellCopies tm (.work index))
          Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position)
  | .output =>
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor (emitStepWritableCellCopies tm .output)
          Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position)

/-- Emit the complete delayed packed-copy suffix in canonical atom order. -/
noncomputable def emitStepPackedCopies (tm : NTM k) :
    BinaryRoutine WorkCount :=
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  BinaryRoutine.seqList
    ([emitStepStateCopies tm,
        setStepPositionLimit 1] ++
      tapes.map (emitStepHeadTapeCopies tm) ++
      [setStepPositionLimit 2] ++
      tapes.map (emitStepCellTapeCopies tm) ++
      [BinaryRoutine.clear Work.limit₁])

/-- Emit one complete packed transition layer. On exit `configBase` is the
first wire of the packed successor configuration. -/
noncomputable def emitStep (tm : TM k) : BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.available Work.gateBound Work.copyCounter,
      emitStepFormulas tm.toNTM,
      BinaryRoutine.binaryCopy Work.available Work.configBase Work.copyCounter,
      BinaryRoutine.binaryCopy Work.gateBound Work.gateCount Work.copyCounter,
      emitStepPackedCopies tm.toNTM,
      BinaryRoutine.clear Work.gateBound,
      BinaryRoutine.clear Work.gateCount]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
