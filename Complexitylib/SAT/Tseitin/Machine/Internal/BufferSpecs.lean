/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Experimental.EmitSpec
public import Complexitylib.SAT.Tseitin.Machine.Defs

/-!
# Hoare specifications for Tseitin literal buffers and emitters

This file gives the register-level contracts used by the streaming-controller
induction. A `BufferValues` packages the values of all six unary registers;
`BufferValues.work` realizes it as the concrete work-tape function. Every
contract fixes a parked input tape, preserves the scratch register, and tracks
the append-only output word exactly.

Time bounds are explicit structural sums of the already-proved register and
emitter bounds. Keeping the composition overhead visible makes these theorems
stable under later polynomial rounding.

## Main results

- `emitClauseTM_hoareTime_internal`
- `emitWideLinkTM_hoareTime_internal`
- `emitPendingTM_hoareTime_internal`
- `clearBuffersTM_hoareTime_internal`
- `rollWideBuffersTM_hoareTime_internal`
- `commitLiteralTM_hoareTime_internal`
- `closeClauseTM_hoareTime_internal`
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Six-register model -/

/-- Values stored in the six fixed work registers of the streaming machine. -/
structure BufferValues where
  /-- First unused variable index. -/
  fresh : ℕ
  /-- Variable index currently being decoded. -/
  current : ℕ
  /-- First pending literal's variable index. -/
  a : ℕ
  /-- Second pending literal's variable index. -/
  b : ℕ
  /-- Third pending literal's variable index. -/
  c : ℕ
  /-- Temporary register, zero between controller operations. -/
  scratch : ℕ
  deriving DecidableEq

/-- Realize six values as the concrete fixed-layout unary-register tapes. -/
def BufferValues.work (v : BufferValues) (i : Fin workTapeCount) : Tape :=
  if i = freshReg then TM.regTape v.fresh
  else if i = currentReg then TM.regTape v.current
  else if i = bufferAReg then TM.regTape v.a
  else if i = bufferBReg then TM.regTape v.b
  else if i = bufferCReg then TM.regTape v.c
  else TM.regTape v.scratch

@[simp] theorem BufferValues.work_fresh (v : BufferValues) :
    v.work freshReg = TM.regTape v.fresh := by
  simp [BufferValues.work]

@[simp] theorem BufferValues.work_current (v : BufferValues) :
    v.work currentReg = TM.regTape v.current := by
  simp [BufferValues.work, freshReg, currentReg]

@[simp] theorem BufferValues.work_a (v : BufferValues) :
    v.work bufferAReg = TM.regTape v.a := by
  simp [BufferValues.work, freshReg, currentReg, bufferAReg]

@[simp] theorem BufferValues.work_b (v : BufferValues) :
    v.work bufferBReg = TM.regTape v.b := by
  simp [BufferValues.work, freshReg, currentReg, bufferAReg, bufferBReg]

@[simp] theorem BufferValues.work_c (v : BufferValues) :
    v.work bufferCReg = TM.regTape v.c := by
  simp [BufferValues.work, freshReg, currentReg, bufferAReg, bufferBReg, bufferCReg]

@[simp] theorem BufferValues.work_scratch (v : BufferValues) :
    v.work scratchReg = TM.regTape v.scratch := by
  simp [BufferValues.work, freshReg, currentReg, bufferAReg, bufferBReg,
    bufferCReg, scratchReg]

theorem BufferValues.work_parked (v : BufferValues) :
    ∀ i, TM.Parked (v.work i) := by
  intro i
  simp only [BufferValues.work]
  split_ifs <;> exact TM.parked_regTape _

@[simp] theorem BufferValues.update_fresh (v : BufferValues) (x : ℕ) :
    Function.update v.work freshReg (TM.regTape x) =
      ({ v with fresh := x } : BufferValues).work := by
  funext i
  fin_cases i <;> simp [BufferValues.work, freshReg, currentReg, bufferAReg,
    bufferBReg, bufferCReg]

@[simp] theorem BufferValues.update_current (v : BufferValues) (x : ℕ) :
    Function.update v.work currentReg (TM.regTape x) =
      ({ v with current := x } : BufferValues).work := by
  funext i
  fin_cases i <;> simp [BufferValues.work, freshReg, currentReg, bufferAReg,
    bufferBReg, bufferCReg]

@[simp] theorem BufferValues.update_a (v : BufferValues) (x : ℕ) :
    Function.update v.work bufferAReg (TM.regTape x) =
      ({ v with a := x } : BufferValues).work := by
  funext i
  fin_cases i <;> simp [BufferValues.work, freshReg, currentReg, bufferAReg,
    bufferBReg, bufferCReg]

@[simp] theorem BufferValues.update_b (v : BufferValues) (x : ℕ) :
    Function.update v.work bufferBReg (TM.regTape x) =
      ({ v with b := x } : BufferValues).work := by
  funext i
  fin_cases i <;> simp [BufferValues.work, freshReg, currentReg, bufferAReg,
    bufferBReg, bufferCReg]

@[simp] theorem BufferValues.update_c (v : BufferValues) (x : ℕ) :
    Function.update v.work bufferCReg (TM.regTape x) =
      ({ v with c := x } : BufferValues).work := by
  funext i
  fin_cases i <;> simp [BufferValues.work, freshReg, currentReg, bufferAReg,
    bufferBReg, bufferCReg]

/-- Standard Hoare predicate for a fixed input, six registers, and output
accumulator. -/
def BufferPred (inp : Tape) (v : BufferValues) (ys : List Bool) : TapePred workTapeCount :=
  TM.EmitPred inp v.work ys

/-! ## Encoded output words and structural time bounds -/

/-- Concrete encoded bits appended by `emitLitTM` for a literal. -/
def literalBits (sign : Bool) (var : ℕ) : List Bool :=
  [sign, sign] ++ List.replicate (2 * var) true ++ [false, true]

/-- Concrete encoding of one three-literal clause, including its clause
separator. -/
def clauseBits (aSign : Bool) (a : ℕ) (bSign : Bool) (b : ℕ)
    (cSign : Bool) (c : ℕ) : List Bool :=
  literalBits aSign a ++ literalBits bSign b ++ literalBits cSign c ++
    [true, false]

/-- Exact primitive bound for one literal emitter. -/
def literalTime (var : ℕ) : ℕ := 3 * var + 9

/-- Structural bound for three literal emitters and a clause separator. -/
def clauseTime (a b c : ℕ) : ℕ :=
  literalTime a + 1 + (literalTime b + 1 + (literalTime c + 1 + 2))

/-- Exact bound exposed by `copyIntoTM_hoareTime`. -/
def copyTime (src dst : ℕ) : ℕ :=
  (2 * dst + 4) + 1 + (src * ((2 * (0 + src) + 4) + 2) + (src + 2))

/-- Primitive increment/clear bound for a unary register. -/
def unaryUpdateTime (v : ℕ) : ℕ := 2 * v + 4

/-! ## Clause emitters -/

/-- Emit exactly one encoded three-literal clause, preserving every tape
except for append-only output growth. -/
theorem emitClauseTM_hoareTime_internal
    (aSign bSign cSign : Bool) (aReg bReg cReg : Fin workTapeCount)
    (a b c : ℕ) (inp : Tape) (work : Fin workTapeCount → Tape)
    (ys : List Bool) (hinp : TM.Parked inp)
    (hwork : ∀ i, TM.Parked (work i))
    (ha : work aReg = TM.regTape a) (hb : work bReg = TM.regTape b)
    (hc : work cReg = TM.regTape c) :
    (emitClauseTM aSign aReg bSign bReg cSign cReg).HoareTime
      (TM.EmitPred inp work ys)
      (TM.EmitPred inp work (ys ++ clauseBits aSign a bSign b cSign c))
      (clauseTime a b c) := by
  have hA := TM.emitLitTM_hoareTime aSign aReg a inp work ys hinp
    (fun i _ => hwork i) (by rw [ha]; exact TM.reg_regT a)
  have hB := TM.emitLitTM_hoareTime bSign bReg b inp work
    (ys ++ literalBits aSign a) hinp (fun i _ => hwork i)
    (by rw [hb]; exact TM.reg_regT b)
  have hC := TM.emitLitTM_hoareTime cSign cReg c inp work
    ((ys ++ literalBits aSign a) ++ literalBits bSign b) hinp
    (fun i _ => hwork i) (by rw [hc]; exact TM.reg_regT c)
  have hSep : (TM.emitBitsTM (n := workTapeCount) [true, false]).HoareTime
      (TM.EmitPred inp work
        (((ys ++ literalBits aSign a) ++ literalBits bSign b) ++ literalBits cSign c))
      (TM.EmitPred inp work
        ((((ys ++ literalBits aSign a) ++ literalBits bSign b) ++ literalBits cSign c) ++
          [true, false]))
      2 :=
    TM.emitBitsTM_hoareTime [true, false] inp work
      (((ys ++ literalBits aSign a) ++ literalBits bSign b) ++ literalBits cSign c)
      hinp hwork
  have hA' := TM.Experimental.EmitSpec.ofHoareTime hinp hwork
    (by simpa [literalBits] using hA)
  have hB' := TM.Experimental.EmitSpec.ofHoareTime hinp hwork
    (by simpa [literalBits] using hB)
  have hC' := TM.Experimental.EmitSpec.ofHoareTime hinp hwork
    (by simpa [literalBits] using hC)
  have hSep' := TM.Experimental.EmitSpec.ofHoareTime hinp hwork
    (by simpa [literalBits] using hSep)
  have hAll := hA'.seq (hB'.seq (hC'.seq hSep'))
  simpa [emitClauseTM, clauseBits, clauseTime, literalTime, literalBits,
    List.append_assoc] using hAll.hoareTime

/-- Specialized wide-link emitter `(a ∨ b ∨ fresh)`. -/
theorem emitWideLinkTM_hoareTime_internal
    (aSign bSign : Bool) (v : BufferValues) (inp : Tape) (ys : List Bool)
    (hinp : TM.Parked inp) :
    (emitWideLinkTM aSign bSign).HoareTime
      (BufferPred inp v ys)
      (BufferPred inp v
        (ys ++ clauseBits aSign v.a bSign v.b true v.fresh))
      (clauseTime v.a v.b v.fresh) := by
  simpa [emitWideLinkTM, BufferPred] using
    emitClauseTM_hoareTime_internal aSign bSign true bufferAReg bufferBReg freshReg
      v.a v.b v.fresh inp v.work ys hinp v.work_parked v.work_a v.work_b v.work_fresh

/-! ## Pending-clause emission -/

/-- Bits emitted when closing the pending finite-control clause shape. -/
def pendingBits (pending : PendingSigns) (v : BufferValues) : List Bool :=
  match pending with
  | .zero =>
      clauseBits true v.fresh true v.fresh true v.fresh ++
        clauseBits false v.fresh false v.fresh false v.fresh
  | .one aSign => clauseBits aSign v.a aSign v.a aSign v.a
  | .two aSign bSign => clauseBits aSign v.a bSign v.b bSign v.b
  | .three aSign bSign cSign => clauseBits aSign v.a bSign v.b cSign v.c

/-- Structural time bound for `emitPendingTM`. -/
def pendingTime (pending : PendingSigns) (v : BufferValues) : ℕ :=
  match pending with
  | .zero => clauseTime v.fresh v.fresh v.fresh + 1 +
      clauseTime v.fresh v.fresh v.fresh
  | .one _ => clauseTime v.a v.a v.a
  | .two _ _ => clauseTime v.a v.b v.b
  | .three _ _ _ => clauseTime v.a v.b v.c

/-- Emit the exact-3 gadget selected by `PendingSigns`, leaving all registers
unchanged. -/
theorem emitPendingTM_hoareTime_internal
    (pending : PendingSigns) (v : BufferValues) (inp : Tape) (ys : List Bool)
    (hinp : TM.Parked inp) :
    (emitPendingTM pending).HoareTime
      (BufferPred inp v ys)
      (BufferPred inp v (ys ++ pendingBits pending v))
      (pendingTime pending v) := by
  cases pending with
  | zero =>
      have hPos := emitClauseTM_hoareTime_internal true true true
        freshReg freshReg freshReg v.fresh v.fresh v.fresh inp v.work ys hinp
        v.work_parked v.work_fresh v.work_fresh v.work_fresh
      have hNeg := emitClauseTM_hoareTime_internal false false false
        freshReg freshReg freshReg v.fresh v.fresh v.fresh inp v.work
        (ys ++ clauseBits true v.fresh true v.fresh true v.fresh) hinp
        v.work_parked v.work_fresh v.work_fresh v.work_fresh
      have h := TM.seqTM_hoareTime
        (emitClauseTM true freshReg true freshReg true freshReg)
        (emitClauseTM false freshReg false freshReg false freshReg)
        (by simpa [BufferPred] using hPos)
        (TM.emitPred_transition hinp v.work_parked _)
        (by simpa [BufferPred] using hNeg)
      simpa [emitPendingTM, BufferPred, pendingBits, pendingTime,
        List.append_assoc] using h
  | one aSign =>
      simpa [emitPendingTM, BufferPred, pendingBits, pendingTime] using
        emitClauseTM_hoareTime_internal aSign aSign aSign
          bufferAReg bufferAReg bufferAReg v.a v.a v.a inp v.work ys hinp
          v.work_parked v.work_a v.work_a v.work_a
  | two aSign bSign =>
      simpa [emitPendingTM, BufferPred, pendingBits, pendingTime] using
        emitClauseTM_hoareTime_internal aSign bSign bSign
          bufferAReg bufferBReg bufferBReg v.a v.b v.b inp v.work ys hinp
          v.work_parked v.work_a v.work_b v.work_b
  | three aSign bSign cSign =>
      simpa [emitPendingTM, BufferPred, pendingBits, pendingTime] using
        emitClauseTM_hoareTime_internal aSign bSign cSign
          bufferAReg bufferBReg bufferCReg v.a v.b v.c inp v.work ys hinp
          v.work_parked v.work_a v.work_b v.work_c

/-! ## Buffer clearing -/

/-- Register values after clearing the current literal and three buffers. -/
def BufferValues.cleared (v : BufferValues) : BufferValues :=
  { v with current := 0, a := 0, b := 0, c := 0 }

/-- Structural time bound for `clearBuffersTM`. -/
def clearBuffersTime (v : BufferValues) : ℕ :=
  unaryUpdateTime v.current + 1 +
    (unaryUpdateTime v.a + 1 +
      (unaryUpdateTime v.b + 1 + unaryUpdateTime v.c))

/-- Clear all literal registers, preserving fresh/scratch and output. -/
theorem clearBuffersTM_hoareTime_internal
    (v : BufferValues) (inp : Tape) (ys : List Bool) (hinp : TM.Parked inp) :
    clearBuffersTM.HoareTime
      (BufferPred inp v ys)
      (BufferPred inp v.cleared ys)
      (clearBuffersTime v) := by
  let v₁ : BufferValues := { v with current := 0 }
  let v₂ : BufferValues := { v₁ with a := 0 }
  let v₃ : BufferValues := { v₂ with b := 0 }
  have hCurrent := TM.clearRegTM_hoareTime currentReg v.current inp v.work ys hinp
    (fun i _ => v.work_parked i) v.work_current
  have hA := TM.clearRegTM_hoareTime bufferAReg v₁.a inp v₁.work ys hinp
    (fun i _ => v₁.work_parked i) v₁.work_a
  have hB := TM.clearRegTM_hoareTime bufferBReg v₂.b inp v₂.work ys hinp
    (fun i _ => v₂.work_parked i) v₂.work_b
  have hC := TM.clearRegTM_hoareTime bufferCReg v₃.c inp v₃.work ys hinp
    (fun i _ => v₃.work_parked i) v₃.work_c
  have hBC := TM.seqTM_hoareTime (TM.clearRegTM bufferBReg)
    (TM.clearRegTM bufferCReg)
    (by simpa [BufferPred, v₂, v₃] using hB)
    (TM.emitPred_transition hinp v₃.work_parked ys)
    (by simpa [BufferPred, v₂, v₃] using hC)
  have hABC := TM.seqTM_hoareTime (TM.clearRegTM bufferAReg)
    (TM.seqTM (TM.clearRegTM bufferBReg) (TM.clearRegTM bufferCReg))
    (by simpa [BufferPred, v₁, v₂] using hA)
    (TM.emitPred_transition hinp v₂.work_parked ys)
    hBC
  have hAll := TM.seqTM_hoareTime (TM.clearRegTM currentReg)
    (TM.seqTM (TM.clearRegTM bufferAReg)
      (TM.seqTM (TM.clearRegTM bufferBReg) (TM.clearRegTM bufferCReg)))
    (by simpa [BufferPred, v₁] using hCurrent)
    (TM.emitPred_transition hinp v₁.work_parked ys)
    hABC
  simpa [clearBuffersTM, clearBuffersTime, unaryUpdateTime, BufferPred,
    BufferValues.cleared, v₁, v₂, v₃] using hAll

/-! ## Wide-window rotation -/

/-- Register values after rotating `(a,b,c,current,fresh)` to
`(fresh,c,current,0,fresh+1)`. -/
def BufferValues.rolled (v : BufferValues) : BufferValues :=
  { fresh := v.fresh + 1
    current := 0
    a := v.fresh
    b := v.c
    c := v.current
    scratch := v.scratch }

/-- Structural time bound for `rollWideBuffersTM`. -/
def rollWideBuffersTime (v : BufferValues) : ℕ :=
  copyTime v.fresh v.a + 1 +
    (copyTime v.c v.b + 1 +
      (copyTime v.current v.c + 1 +
        (unaryUpdateTime v.fresh + 1 + unaryUpdateTime v.current)))

/-- Rotate the three pending buffers after emitting a wide link. -/
theorem rollWideBuffersTM_hoareTime_internal
    (v : BufferValues) (inp : Tape) (ys : List Bool) (hinp : TM.Parked inp) :
    rollWideBuffersTM.HoareTime
      (BufferPred inp v ys)
      (BufferPred inp v.rolled ys)
      (rollWideBuffersTime v) := by
  let v₁ : BufferValues := { v with a := v.fresh }
  let v₂ : BufferValues := { v₁ with b := v.c }
  let v₃ : BufferValues := { v₂ with c := v.current }
  let v₄ : BufferValues := { v₃ with fresh := v.fresh + 1 }
  have hFA := TM.copyIntoTM_hoareTime freshReg bufferAReg (by decide)
    v.fresh v.a inp v.work ys hinp (fun i _ => v.work_parked i)
    v.work_fresh v.work_a
  have hCB := TM.copyIntoTM_hoareTime bufferCReg bufferBReg (by decide)
    v₁.c v₁.b inp v₁.work ys hinp (fun i _ => v₁.work_parked i)
    v₁.work_c v₁.work_b
  have hCurC := TM.copyIntoTM_hoareTime currentReg bufferCReg (by decide)
    v₂.current v₂.c inp v₂.work ys hinp (fun i _ => v₂.work_parked i)
    v₂.work_current v₂.work_c
  have hInc := TM.incRegTM_hoareTime freshReg v₃.fresh inp v₃.work ys hinp
    (fun i _ => v₃.work_parked i) v₃.work_fresh
  have hClear := TM.clearRegTM_hoareTime currentReg v₄.current inp v₄.work ys hinp
    (fun i _ => v₄.work_parked i) v₄.work_current
  have hFA' := TM.Experimental.EmitSpec.ofHoareTime hinp v₁.work_parked
    (by simpa [BufferPred, v₁] using hFA)
  have hCB' := TM.Experimental.EmitSpec.ofHoareTime hinp v₂.work_parked
    (by simpa [BufferPred, v₁, v₂] using hCB)
  have hCurC' := TM.Experimental.EmitSpec.ofHoareTime hinp v₃.work_parked
    (by simpa [BufferPred, v₂, v₃] using hCurC)
  have hInc' := TM.Experimental.EmitSpec.ofHoareTime hinp v₄.work_parked
    (by simpa [BufferPred, v₃, v₄] using hInc)
  have hClear' := TM.Experimental.EmitSpec.ofHoareTime hinp v.rolled.work_parked
    (by simpa [BufferPred, v₄, BufferValues.rolled] using hClear)
  have hAll := hFA'.seq (hCB'.seq (hCurC'.seq (hInc'.seq hClear')))
  simpa [rollWideBuffersTM, rollWideBuffersTime, copyTime, unaryUpdateTime,
    BufferPred, BufferValues.rolled, v₁, v₂, v₃, v₄] using hAll.hoareTime

/-! ## Literal commit -/

/-- Register values after committing `currentReg` under a pending shape. -/
def BufferValues.committed (pending : PendingSigns) (v : BufferValues) : BufferValues :=
  match pending with
  | .zero => { v with current := 0, a := v.current }
  | .one _ => { v with current := 0, b := v.current }
  | .two _ _ => { v with current := 0, c := v.current }
  | .three _ _ _ => v.rolled

/-- Bits emitted while committing a literal. Only the fourth-and-later case
emits a completed wide link. -/
def commitBits (pending : PendingSigns) (v : BufferValues) : List Bool :=
  match pending with
  | .three aSign bSign _ =>
      clauseBits aSign v.a bSign v.b true v.fresh
  | _ => []

/-- Structural time bound for `commitLiteralTM`. -/
def commitLiteralTime (pending : PendingSigns) (v : BufferValues) : ℕ :=
  match pending with
  | .zero => copyTime v.current v.a + 1 + unaryUpdateTime v.current
  | .one _ => copyTime v.current v.b + 1 + unaryUpdateTime v.current
  | .two _ _ => copyTime v.current v.c + 1 + unaryUpdateTime v.current
  | .three _ _ _ => clauseTime v.a v.b v.fresh + 1 + rollWideBuffersTime v

/-- Commit the current decoded literal: buffer it when fewer than three are
pending, or emit and roll a wide link otherwise. -/
theorem commitLiteralTM_hoareTime_internal
    (pending : PendingSigns) (v : BufferValues) (inp : Tape) (ys : List Bool)
    (hinp : TM.Parked inp) :
    (commitLiteralTM pending).HoareTime
      (BufferPred inp v ys)
      (BufferPred inp (v.committed pending) (ys ++ commitBits pending v))
      (commitLiteralTime pending v) := by
  cases pending with
  | zero =>
      let v₁ : BufferValues := { v with a := v.current }
      have hCopy := TM.copyIntoTM_hoareTime currentReg bufferAReg (by decide)
        v.current v.a inp v.work ys hinp (fun i _ => v.work_parked i)
        v.work_current v.work_a
      have hClear := TM.clearRegTM_hoareTime currentReg v₁.current inp v₁.work ys
        hinp (fun i _ => v₁.work_parked i) v₁.work_current
      have h := TM.seqTM_hoareTime (TM.copyIntoTM currentReg bufferAReg)
        (TM.clearRegTM currentReg)
        (by simpa [BufferPred, v₁] using hCopy)
        (TM.emitPred_transition hinp v₁.work_parked ys)
        (by simpa [BufferPred, v₁] using hClear)
      simpa [commitLiteralTM, BufferPred, BufferValues.committed, commitBits,
        commitLiteralTime, copyTime, unaryUpdateTime, v₁] using h
  | one aSign =>
      let v₁ : BufferValues := { v with b := v.current }
      have hCopy := TM.copyIntoTM_hoareTime currentReg bufferBReg (by decide)
        v.current v.b inp v.work ys hinp (fun i _ => v.work_parked i)
        v.work_current v.work_b
      have hClear := TM.clearRegTM_hoareTime currentReg v₁.current inp v₁.work ys
        hinp (fun i _ => v₁.work_parked i) v₁.work_current
      have h := TM.seqTM_hoareTime (TM.copyIntoTM currentReg bufferBReg)
        (TM.clearRegTM currentReg)
        (by simpa [BufferPred, v₁] using hCopy)
        (TM.emitPred_transition hinp v₁.work_parked ys)
        (by simpa [BufferPred, v₁] using hClear)
      simpa [commitLiteralTM, BufferPred, BufferValues.committed, commitBits,
        commitLiteralTime, copyTime, unaryUpdateTime, v₁] using h
  | two aSign bSign =>
      let v₁ : BufferValues := { v with c := v.current }
      have hCopy := TM.copyIntoTM_hoareTime currentReg bufferCReg (by decide)
        v.current v.c inp v.work ys hinp (fun i _ => v.work_parked i)
        v.work_current v.work_c
      have hClear := TM.clearRegTM_hoareTime currentReg v₁.current inp v₁.work ys
        hinp (fun i _ => v₁.work_parked i) v₁.work_current
      have h := TM.seqTM_hoareTime (TM.copyIntoTM currentReg bufferCReg)
        (TM.clearRegTM currentReg)
        (by simpa [BufferPred, v₁] using hCopy)
        (TM.emitPred_transition hinp v₁.work_parked ys)
        (by simpa [BufferPred, v₁] using hClear)
      simpa [commitLiteralTM, BufferPred, BufferValues.committed, commitBits,
        commitLiteralTime, copyTime, unaryUpdateTime, v₁] using h
  | three aSign bSign cSign =>
      have hEmit := emitWideLinkTM_hoareTime_internal aSign bSign v inp ys hinp
      have hRoll := rollWideBuffersTM_hoareTime_internal v inp
        (ys ++ clauseBits aSign v.a bSign v.b true v.fresh) hinp
      have h := TM.seqTM_hoareTime (emitWideLinkTM aSign bSign) rollWideBuffersTM
        hEmit (TM.emitPred_transition hinp v.work_parked _) hRoll
      simpa [commitLiteralTM, BufferValues.committed, commitBits,
        commitLiteralTime, BufferPred, List.append_assoc] using h

/-! ## Clause close -/

/-- Fresh-register value after the empty-clause advance phase. -/
def BufferValues.advanced (pending : PendingSigns) (v : BufferValues) : BufferValues :=
  match pending with
  | .zero => { v with fresh := v.fresh + 1 }
  | _ => v

/-- Final registers after closing and clearing a clause. -/
def BufferValues.closed (pending : PendingSigns) (v : BufferValues) : BufferValues :=
  (v.advanced pending).cleared

/-- Time for the fresh-advance phase selected by `closeClauseTM`. -/
def advanceFreshTime (pending : PendingSigns) (v : BufferValues) : ℕ :=
  match pending with
  | .zero => unaryUpdateTime v.fresh
  | _ => 1

/-- Structural time bound for closing a clause. -/
def closeClauseTime (pending : PendingSigns) (v : BufferValues) : ℕ :=
  pendingTime pending v + 1 +
    (advanceFreshTime pending v + 1 + clearBuffersTime (v.advanced pending))

/-- Emit the pending clause, perform the empty-clause fresh increment when
needed, and reset all literal buffers. -/
theorem closeClauseTM_hoareTime_internal
    (pending : PendingSigns) (v : BufferValues) (inp : Tape) (ys : List Bool)
    (hinp : TM.Parked inp) :
    (closeClauseTM pending).HoareTime
      (BufferPred inp v ys)
      (BufferPred inp (v.closed pending) (ys ++ pendingBits pending v))
      (closeClauseTime pending v) := by
  have hEmit := emitPendingTM_hoareTime_internal pending v inp ys hinp
  cases pending with
  | zero =>
      let v₁ : BufferValues := { v with fresh := v.fresh + 1 }
      have hAdvance := TM.incRegTM_hoareTime freshReg v.fresh inp v.work
        (ys ++ pendingBits .zero v) hinp (fun i _ => v.work_parked i) v.work_fresh
      have hClear := clearBuffersTM_hoareTime_internal v₁ inp
        (ys ++ pendingBits .zero v) hinp
      have hAdvanceClear := TM.seqTM_hoareTime (TM.incRegTM freshReg) clearBuffersTM
        (by simpa [BufferPred, v₁] using hAdvance)
        (TM.emitPred_transition hinp v₁.work_parked _)
        hClear
      have h := TM.seqTM_hoareTime (emitPendingTM .zero)
        (TM.seqTM (TM.incRegTM freshReg) clearBuffersTM)
        hEmit (TM.emitPred_transition hinp v.work_parked _) hAdvanceClear
      simpa [closeClauseTM, BufferValues.advanced, BufferValues.closed,
        closeClauseTime, advanceFreshTime, unaryUpdateTime, BufferPred, v₁,
        List.append_assoc] using h
  | one aSign =>
      have hAdvance := TM.skipTM_hoareTime inp v.work
        (ys ++ pendingBits (.one aSign) v) hinp v.work_parked
      have hClear := clearBuffersTM_hoareTime_internal v inp
        (ys ++ pendingBits (.one aSign) v) hinp
      have hAdvanceClear := TM.seqTM_hoareTime TM.skipTM clearBuffersTM hAdvance
        (TM.emitPred_transition hinp v.work_parked _) hClear
      have h := TM.seqTM_hoareTime (emitPendingTM (.one aSign))
        (TM.seqTM TM.skipTM clearBuffersTM) hEmit
        (TM.emitPred_transition hinp v.work_parked _) hAdvanceClear
      simpa [closeClauseTM, BufferValues.advanced, BufferValues.closed,
        closeClauseTime, advanceFreshTime, BufferPred, List.append_assoc] using h
  | two aSign bSign =>
      have hAdvance := TM.skipTM_hoareTime inp v.work
        (ys ++ pendingBits (.two aSign bSign) v) hinp v.work_parked
      have hClear := clearBuffersTM_hoareTime_internal v inp
        (ys ++ pendingBits (.two aSign bSign) v) hinp
      have hAdvanceClear := TM.seqTM_hoareTime TM.skipTM clearBuffersTM hAdvance
        (TM.emitPred_transition hinp v.work_parked _) hClear
      have h := TM.seqTM_hoareTime (emitPendingTM (.two aSign bSign))
        (TM.seqTM TM.skipTM clearBuffersTM) hEmit
        (TM.emitPred_transition hinp v.work_parked _) hAdvanceClear
      simpa [closeClauseTM, BufferValues.advanced, BufferValues.closed,
        closeClauseTime, advanceFreshTime, BufferPred, List.append_assoc] using h
  | three aSign bSign cSign =>
      have hAdvance := TM.skipTM_hoareTime inp v.work
        (ys ++ pendingBits (.three aSign bSign cSign) v) hinp v.work_parked
      have hClear := clearBuffersTM_hoareTime_internal v inp
        (ys ++ pendingBits (.three aSign bSign cSign) v) hinp
      have hAdvanceClear := TM.seqTM_hoareTime TM.skipTM clearBuffersTM hAdvance
        (TM.emitPred_transition hinp v.work_parked _) hClear
      have h := TM.seqTM_hoareTime (emitPendingTM (.three aSign bSign cSign))
        (TM.seqTM TM.skipTM clearBuffersTM) hEmit
        (TM.emitPred_transition hinp v.work_parked _) hAdvanceClear
      simpa [closeClauseTM, BufferValues.advanced, BufferValues.closed,
        closeClauseTime, advanceFreshTime, BufferPred, List.append_assoc] using h

end Machine

end ThreeSAT

end SAT

end Complexity
