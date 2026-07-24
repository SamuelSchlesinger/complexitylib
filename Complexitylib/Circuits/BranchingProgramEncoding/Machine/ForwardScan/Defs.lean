/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch.Defs
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Forward postfix scan controller -- definitions

This layer implements the numeric update performed after one formula token has
been decoded. It updates the postfix stack height and token count, tests whether
the new height is one, and if so copies the current token and bit cursors into
the retained child-boundary registers.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Eight distinct work tapes used by the forward postfix scan state.

The role order is bit cursor, stack height, token count, last height-one token
count, last height-one bit cursor, constant one, equality verdict, and binary
copy scratch. -/
structure ForwardScanLayout (n : ℕ) where
  /-- Injective assignment of scan-state roles to physical work tapes. -/
  roles : Fin 8 ↪ Fin n

/-- Current absolute bit cursor in the encoded formula source. -/
def ForwardScanLayout.cursorIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 0

/-- Current postfix evaluation-stack height. -/
def ForwardScanLayout.heightIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 1

/-- Number of complete tokens consumed in the current segment. -/
def ForwardScanLayout.tokenCountIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 2

/-- Most recent token count at which the stack height became one. -/
def ForwardScanLayout.lastOneCountIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 3

/-- Absolute bit cursor at the matching height-one boundary. -/
def ForwardScanLayout.lastOneCursorIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 4

/-- Preserved canonical binary constant one. -/
def ForwardScanLayout.oneIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 5

/-- Reusable one-bit equality verdict. -/
def ForwardScanLayout.resultIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 6

/-- Reusable canonical-zero scratch for binary copies. -/
def ForwardScanLayout.copyScratchIdx (layout : ForwardScanLayout n) : Fin n :=
  layout.roles 7

/-- Canonical numeric contents of all eight forward-scan registers. -/
def ForwardScanFrame (layout : ForwardScanLayout n)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin n → Tape) : Prop :=
  (work layout.cursorIdx).HasBinaryNat cursor ∧
  (work layout.heightIdx).HasBinaryNat height ∧
  (work layout.tokenCountIdx).HasBinaryNat tokenCount ∧
  (work layout.lastOneCountIdx).HasBinaryNat lastOneCount ∧
  (work layout.lastOneCursorIdx).HasBinaryNat lastOneCursor ∧
  (work layout.oneIdx).HasBinaryNat 1 ∧
  (work layout.resultIdx).HasBinaryNat 0 ∧
  (work layout.copyScratchIdx).HasBinaryNat 0

/-- Literal work-tape update performed by the height-one branch. -/
def forwardScanBoundaryWork (layout : ForwardScanLayout n)
    (work : Fin n → Tape) (tokenCount cursor : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update
      (Function.update work layout.lastOneCountIdx
        ((Tape.init (tokenCount.bits.map Γ.ofBool)).move Dir3.right))
      layout.lastOneCursorIdx
      ((Tape.init (cursor.bits.map Γ.ofBool)).move Dir3.right))
    layout.resultIdx ((Tape.init []).move Dir3.right)

/-- Literal final work family after the post-height update. -/
def forwardScanAfterHeightWork (layout : ForwardScanLayout n)
    (work : Fin n → Tape) (height tokenCount cursor : ℕ) : Fin n → Tape :=
  let counted := Function.update work layout.tokenCountIdx
    ((Tape.init ((tokenCount + 1).bits.map Γ.ofBool)).move Dir3.right)
  let compared := Function.update counted layout.resultIdx
    ((Tape.init ([decide (height = 1)].map Γ.ofBool)).move Dir3.right)
  if height = 1 then
    forwardScanBoundaryWork layout compared (tokenCount + 1) cursor
  else
    Function.update compared layout.resultIdx
      ((Tape.init []).move Dir3.right)

/-- Literal final work family after one complete token-state update. -/
def forwardScanTokenStepWork (layout : ForwardScanLayout n)
    (work : Fin n → Tape) (arity height tokenCount cursor : ℕ) :
    Fin n → Tape :=
  let nextHeight := height + 1 - arity
  let heightUpdated := Function.update work layout.heightIdx
    ((Tape.init (nextHeight.bits.map Γ.ofBool)).move Dir3.right)
  forwardScanAfterHeightWork layout heightUpdated nextHeight tokenCount cursor

/-- Update the stack height for one token arity. A leaf increments, a unary
token leaves the height fixed, and a binary token decrements. Values above two
share the binary branch; promised formula codes never select them. -/
def forwardScanHeightTM (layout : ForwardScanLayout n) (arity : ℕ) : TM n :=
  match arity with
  | 0 => TM.binarySuccTM layout.heightIdx
  | 1 => TM.skipTM
  | _ => TM.binaryPredTM layout.heightIdx

/-- Copy both current boundaries into their retained registers, then clear the
one-bit equality verdict for the next token. -/
def forwardScanCopyBoundaryTM (layout : ForwardScanLayout n) : TM n :=
  TM.seqTM
    (TM.binaryCopyIntoTM layout.tokenCountIdx layout.lastOneCountIdx
      layout.copyScratchIdx)
    (TM.seqTM
      (TM.binaryCopyIntoTM layout.cursorIdx layout.lastOneCursorIdx
        layout.copyScratchIdx)
      (TM.clearWorkTM layout.resultIdx))

/-- Branch on the normalized equality verdict. Height one records the current
token and bit boundaries; every other height only clears the verdict. -/
def forwardScanRecordBoundaryTM (layout : ForwardScanLayout n) : TM n :=
  TM.branchWorkSymbolTM layout.resultIdx Γ.one
    (forwardScanCopyBoundaryTM layout)
    (TM.clearWorkTM layout.resultIdx)

/-- Increment the token count, compare the updated height with one, record a
height-one boundary when selected, and restore the equality scratch to zero. -/
def forwardScanAfterHeightTM (layout : ForwardScanLayout n) : TM n :=
  TM.seqTM (TM.binarySuccTM layout.tokenCountIdx)
    (TM.seqTM
      (TM.binaryEqRewindTM layout.heightIdx layout.oneIdx layout.resultIdx)
      (forwardScanRecordBoundaryTM layout))

/-- Complete numeric update after decoding one token of the given arity. -/
def forwardScanTokenStepTM (layout : ForwardScanLayout n) (arity : ℕ) : TM n :=
  TM.seqTM (forwardScanHeightTM layout arity)
    (forwardScanAfterHeightTM layout)

/-- Runtime of the arity-dependent height update. -/
def forwardScanHeightTime (arity height : ℕ) : ℕ :=
  match arity with
  | 0 => TM.binarySuccTime height
  | 1 => 1
  | _ => TM.binaryPredTime (height - 1)

/-- Runtime of the selected boundary-recording branch. -/
def forwardScanRecordBoundaryTime (isOne : Bool)
    (tokenCount cursor lastOneCount lastOneCursor : ℕ) : ℕ :=
  if isOne then
    TM.binaryCopyTime tokenCount lastOneCount + 1 +
      (TM.binaryCopyTime cursor lastOneCursor + 1 +
        TM.clearWorkTimeBound 1)
  else
    TM.clearWorkTimeBound 1

/-- Runtime after the stack-height update, parameterized by the resulting
numeric state. -/
def forwardScanAfterHeightTime (height tokenCount cursor lastOneCount
    lastOneCursor : ℕ) : ℕ :=
  TM.binarySuccTime tokenCount + 1 +
    (TM.binaryEqRewindTime height.bits (1 : ℕ).bits + 1 +
      (forwardScanRecordBoundaryTime (decide (height = 1))
        (tokenCount + 1) cursor lastOneCount lastOneCursor + 1))

/-- Runtime of one complete numeric token update. -/
def forwardScanTokenStepTime (arity height tokenCount cursor lastOneCount
    lastOneCursor : ℕ) : ℕ :=
  let nextHeight := height + 1 - arity
  forwardScanHeightTime arity height + 1 +
    forwardScanAfterHeightTime nextHeight tokenCount cursor lastOneCount
      lastOneCursor

end Machine

end BPCode

end Complexity
