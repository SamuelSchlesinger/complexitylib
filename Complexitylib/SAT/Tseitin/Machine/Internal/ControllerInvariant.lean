/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Internal.Streaming
public import Complexitylib.SAT.Tseitin.Machine.Controller
public import Complexitylib.SAT.Tseitin.Machine.Internal.BufferSpecs

/-!
# Register invariant for the Tseitin streaming controller

This file connects the pure token transducer in `ThreeSAT.Streaming` to the
finite control and six unary registers of `validEmitterTM`. It deliberately
contains no execution simulation. The definitions here only say how a pure
streaming state is represented:

- pending literals retain their signs in `PendingSigns`;
- the parser scan becomes a `StreamMode`;
- unbounded variable indices occupy `freshReg`, `currentReg`, and the three
  pending-literal registers;
- the scratch register is zero; and
- the output tape is an append-only `TM.OutAcc` containing the encoding of
  the already-emitted tokens.

The projection and parked-tape lemmas are the glue needed to instantiate the
register-level Hoare specifications in `Machine.Internal.BufferSpecs`.

## Main definitions

- `PendingSigns.ofStreaming`
- `StreamMode.ofStreaming`
- `StreamMode.ofState`
- `BufferValues.ofStreaming`
- `StreamingStatePred`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Finite-control representation -/

/-- Forget the variable indices of a pure pending window, retaining exactly
the signs kept by the machine controller. -/
@[simp] def PendingSigns.ofStreaming : Streaming.Pending → PendingSigns
  | .zero => .zero
  | .one a => .one a.sign
  | .two a b => .two a.sign b.sign
  | .three a b c => .three a.sign b.sign c.sign

/-- Convert a pure parser scan to its finite controller mode under the signs
of the current pending window. -/
@[simp] def StreamMode.ofStreaming
    (pending : Streaming.Pending) : Streaming.Scan → StreamMode
  | .boundary => .boundary (PendingSigns.ofStreaming pending)
  | .literal sign _ => .literal (PendingSigns.ofStreaming pending) sign

/-- Finite controller mode represented by a complete pure streaming state. -/
def StreamMode.ofState (st : Streaming.State) : StreamMode :=
  .ofStreaming st.pending st.scan

@[simp] theorem StreamMode.ofState_mk (next : ℕ) (pending : Streaming.Pending)
    (scan : Streaming.Scan) (emitted : List EncToken) :
    StreamMode.ofState ⟨next, pending, scan, emitted⟩ =
      StreamMode.ofStreaming pending scan := rfl

/-- Sign control after a pure literal push agrees with `PendingSigns.push`. -/
theorem PendingSigns.ofStreaming_pushLiteral
    (st : Streaming.State) (lit : Lit) :
    PendingSigns.ofStreaming (Streaming.pushLiteral st lit).pending =
      (PendingSigns.ofStreaming st.pending).push lit.sign := by
  cases st with
  | mk next pending scan emitted =>
      cases pending <;> rfl

/-- A pure literal push returns the parser to the corresponding boundary
mode. -/
@[simp] theorem StreamMode.ofState_pushLiteral
    (st : Streaming.State) (lit : Lit) :
    StreamMode.ofState (Streaming.pushLiteral st lit) =
      .boundary ((PendingSigns.ofStreaming st.pending).push lit.sign) := by
  cases st with
  | mk next pending scan emitted =>
      cases pending <;> rfl

/-- Closing a pure clause resets both pending signs and parser mode. -/
@[simp] theorem StreamMode.ofState_closeClause (st : Streaming.State) :
    StreamMode.ofState (Streaming.closeClause st) = .boundary .zero := by
  cases st
  rfl

/-! ## Unary-register representation -/

/-- Unary value stored in `currentReg` for a pure parser scan. -/
@[simp] def streamingScanValue : Streaming.Scan → ℕ
  | .boundary => 0
  | .literal _ var => var

/-- Unary value stored in `bufferAReg` for a pending window. -/
@[simp] def streamingBufferA : Streaming.Pending → ℕ
  | .zero => 0
  | .one a => a.var
  | .two a _ => a.var
  | .three a _ _ => a.var

/-- Unary value stored in `bufferBReg` for a pending window. -/
@[simp] def streamingBufferB : Streaming.Pending → ℕ
  | .zero => 0
  | .one _ => 0
  | .two _ b => b.var
  | .three _ b _ => b.var

/-- Unary value stored in `bufferCReg` for a pending window. -/
@[simp] def streamingBufferC : Streaming.Pending → ℕ
  | .zero => 0
  | .one _ => 0
  | .two _ _ => 0
  | .three _ _ c => c.var

/-- Six unary-register values representing a pure streaming state. -/
def BufferValues.ofStreaming (st : Streaming.State) : BufferValues :=
  { fresh := st.next
    current := streamingScanValue st.scan
    a := streamingBufferA st.pending
    b := streamingBufferB st.pending
    c := streamingBufferC st.pending
    scratch := 0 }

@[simp] theorem BufferValues.ofStreaming_fresh (st : Streaming.State) :
    (BufferValues.ofStreaming st).fresh = st.next := rfl

@[simp] theorem BufferValues.ofStreaming_current (st : Streaming.State) :
    (BufferValues.ofStreaming st).current = streamingScanValue st.scan := rfl

@[simp] theorem BufferValues.ofStreaming_a (st : Streaming.State) :
    (BufferValues.ofStreaming st).a = streamingBufferA st.pending := rfl

@[simp] theorem BufferValues.ofStreaming_b (st : Streaming.State) :
    (BufferValues.ofStreaming st).b = streamingBufferB st.pending := rfl

@[simp] theorem BufferValues.ofStreaming_c (st : Streaming.State) :
    (BufferValues.ofStreaming st).c = streamingBufferC st.pending := rfl

@[simp] theorem BufferValues.ofStreaming_scratch (st : Streaming.State) :
    (BufferValues.ofStreaming st).scratch = 0 := rfl

/-- Every register tape in the representation of a pure state is parked. -/
theorem BufferValues.ofStreaming_work_parked (st : Streaming.State) :
    ∀ i, TM.Parked ((BufferValues.ofStreaming st).work i) :=
  (BufferValues.ofStreaming st).work_parked

/-! ## Complete tape predicate -/

/-- Tape-level representation of a pure streaming state. The input tape is a
fixed parked ghost for buffer operations; the work tapes are its six unary
registers; and the output accumulator contains exactly the emitted tokens. -/
def StreamingStatePred (inp : Tape) (st : Streaming.State) :
    TapePred workTapeCount :=
  BufferPred inp (BufferValues.ofStreaming st) (encodeTokens st.emitted)

@[simp] theorem streamingStatePred_eq_bufferPred (inp : Tape)
    (st : Streaming.State) :
    StreamingStatePred inp st =
      BufferPred inp (BufferValues.ofStreaming st) (encodeTokens st.emitted) := rfl

namespace StreamingStatePred

variable {inp actualInput out : Tape} {st : Streaming.State}
  {work : Fin workTapeCount → Tape}

/-- Project the fixed input tape from the streaming-state predicate. -/
theorem input_eq (h : StreamingStatePred inp st actualInput work out) :
    actualInput = inp :=
  h.1

/-- Project the six-register work-tape function. -/
theorem work_eq (h : StreamingStatePred inp st actualInput work out) :
    work = (BufferValues.ofStreaming st).work :=
  h.2.1

/-- Project the exact append-only encoded-token accumulator. -/
theorem outAcc (h : StreamingStatePred inp st actualInput work out) :
    TM.OutAcc (encodeTokens st.emitted) out :=
  h.2.2

/-- The represented input is parked whenever its fixed ghost is parked. -/
theorem input_parked (h : StreamingStatePred inp st actualInput work out)
    (hinp : TM.Parked inp) : TM.Parked actualInput := by
  rw [input_eq h]
  exact hinp

/-- Every represented work tape is parked. -/
theorem work_parked (h : StreamingStatePred inp st actualInput work out) :
    ∀ i, TM.Parked (work i) := by
  rw [work_eq h]
  exact BufferValues.ofStreaming_work_parked st

/-- The represented output accumulator is parked. -/
theorem output_parked (h : StreamingStatePred inp st actualInput work out) :
    TM.Parked out :=
  (outAcc h).parked

/-- Project the fresh-variable register. -/
theorem work_fresh (h : StreamingStatePred inp st actualInput work out) :
    work freshReg = TM.regTape st.next := by
  rw [work_eq h]
  simp

/-- Project the current-literal register. -/
theorem work_current (h : StreamingStatePred inp st actualInput work out) :
    work currentReg = TM.regTape (streamingScanValue st.scan) := by
  rw [work_eq h]
  simp

/-- Project the first pending-literal register. -/
theorem work_a (h : StreamingStatePred inp st actualInput work out) :
    work bufferAReg = TM.regTape (streamingBufferA st.pending) := by
  rw [work_eq h]
  simp

/-- Project the second pending-literal register. -/
theorem work_b (h : StreamingStatePred inp st actualInput work out) :
    work bufferBReg = TM.regTape (streamingBufferB st.pending) := by
  rw [work_eq h]
  simp

/-- Project the third pending-literal register. -/
theorem work_c (h : StreamingStatePred inp st actualInput work out) :
    work bufferCReg = TM.regTape (streamingBufferC st.pending) := by
  rw [work_eq h]
  simp

/-- Project the zero scratch register. -/
theorem work_scratch (h : StreamingStatePred inp st actualInput work out) :
    work scratchReg = TM.regTape 0 := by
  rw [work_eq h]
  simp

end StreamingStatePred

end Machine

end ThreeSAT

end SAT

end Complexity
