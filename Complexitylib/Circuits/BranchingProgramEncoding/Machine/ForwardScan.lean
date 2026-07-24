/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan.Internal

/-!
# Forward postfix scan controller

This module exposes the concrete numeric controller used after each decoded
formula token in the forward child-boundary scan.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- The concrete arity update realizes saturated postfix-stack arithmetic on
canonical binary state, with an explicit positive-height premise for binary
operators. -/
theorem forwardScanHeightTM_hoareTime
    (layout : ForwardScanLayout n) (arity height : ℕ)
    (harity : arity ≤ 2) (hpositive : arity = 2 → 1 ≤ height)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hheight : (work₀ layout.heightIdx).HasBinaryNat height)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ layout.heightIdx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanHeightTM layout arity).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ layout.heightIdx
          ((Tape.init ((height + 1 - arity).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (forwardScanHeightTime arity height) :=
  forwardScanHeightTM_hoareTime_internal layout arity height harity hpositive
    inp₀ work₀ out₀ hheight hinput hother houtput

/-- The selected height-one branch copies both current boundaries and restores
the equality verdict to canonical zero. -/
theorem forwardScanCopyBoundaryTM_hoareTime
    (layout : ForwardScanLayout n)
    (tokenCount cursor lastOneCount lastOneCursor : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcount : (work₀ layout.tokenCountIdx).HasBinaryNat tokenCount)
    (hcursor : (work₀ layout.cursorIdx).HasBinaryNat cursor)
    (hlastCount :
      (work₀ layout.lastOneCountIdx).HasBinaryNat lastOneCount)
    (hlastCursor :
      (work₀ layout.lastOneCursorIdx).HasBinaryNat lastOneCursor)
    (hscratch : (work₀ layout.copyScratchIdx).HasBinaryNat 0)
    (hresult : (work₀ layout.resultIdx).HasBinaryString [true])
    (hresultStart : (work₀ layout.resultIdx).cells 0 = Γ.start)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanCopyBoundaryTM layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanBoundaryWork layout work₀ tokenCount cursor ∧
        out = out₀)
      (forwardScanRecordBoundaryTime true tokenCount cursor lastOneCount
        lastOneCursor) :=
  forwardScanCopyBoundaryTM_hoareTime_internal layout tokenCount cursor
    lastOneCount lastOneCursor inp₀ work₀ out₀ hcount hcursor hlastCount
    hlastCursor hscratch hresult hresultStart hinput hwork houtput

/-- After the stack-height update, the concrete controller increments the
token count, records both current boundaries exactly when the height is one,
and restores its verdict scratch. -/
theorem forwardScanAfterHeightTM_hoareTime
    (layout : ForwardScanLayout n)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hframe : ForwardScanFrame layout cursor height tokenCount lastOneCount
      lastOneCursor work₀)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanAfterHeightTM layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanAfterHeightWork layout work₀ height tokenCount
          cursor ∧
        out = out₀)
      (forwardScanAfterHeightTime height tokenCount cursor lastOneCount
        lastOneCursor) :=
  forwardScanAfterHeightTM_hoareTime_internal layout cursor height tokenCount
    lastOneCount lastOneCursor inp₀ work₀ out₀ hframe hinput hwork houtput

/-- One call realizes the complete numeric update of a decoded postfix token:
stack height, token count, conditional child-boundary copies, and scratch
restoration. -/
theorem forwardScanTokenStepTM_hoareTime
    (layout : ForwardScanLayout n) (arity height tokenCount cursor
      lastOneCount lastOneCursor : ℕ)
    (harity : arity ≤ 2) (hpositive : arity = 2 → 1 ≤ height)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hframe : ForwardScanFrame layout cursor height tokenCount lastOneCount
      lastOneCursor work₀)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanTokenStepTM layout arity).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanTokenStepWork layout work₀ arity height tokenCount
          cursor ∧
        out = out₀)
      (forwardScanTokenStepTime arity height tokenCount cursor lastOneCount
        lastOneCursor) :=
  forwardScanTokenStepTM_hoareTime_internal layout arity height tokenCount
    cursor lastOneCount lastOneCursor harity hpositive inp₀ work₀ out₀
    hframe hinput hwork houtput

/-- The arity-dependent stack-height update never moves output left. -/
theorem forwardScanHeightTM_isTransducer
    (layout : ForwardScanLayout n) (arity : ℕ) :
    (forwardScanHeightTM layout arity).IsTransducer :=
  forwardScanHeightTM_isTransducer_internal layout arity

/-- Copying a selected child boundary and clearing its verdict is append-only. -/
theorem forwardScanCopyBoundaryTM_isTransducer
    (layout : ForwardScanLayout n) :
    (forwardScanCopyBoundaryTM layout).IsTransducer :=
  forwardScanCopyBoundaryTM_isTransducer_internal layout

/-- Conditional child-boundary recording is append-only. -/
theorem forwardScanRecordBoundaryTM_isTransducer
    (layout : ForwardScanLayout n) :
    (forwardScanRecordBoundaryTM layout).IsTransducer :=
  forwardScanRecordBoundaryTM_isTransducer_internal layout

/-- The complete post-height numeric update is append-only. -/
theorem forwardScanAfterHeightTM_isTransducer
    (layout : ForwardScanLayout n) :
    (forwardScanAfterHeightTM layout).IsTransducer :=
  forwardScanAfterHeightTM_isTransducer_internal layout

/-- One complete numeric token update is append-only. -/
theorem forwardScanTokenStepTM_isTransducer
    (layout : ForwardScanLayout n) (arity : ℕ) :
    (forwardScanTokenStepTM layout arity).IsTransducer :=
  forwardScanTokenStepTM_isTransducer_internal layout arity

end Machine

end BPCode

end Complexity
