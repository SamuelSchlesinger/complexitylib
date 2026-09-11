/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Defs

/-!
# Streaming serialized-circuit evaluator core

This file defines the finite controller that evaluates an already-staged
tagged circuit code. The code tape is parsed once from left to right. The wire
tape begins with the primary input and receives one appended Boolean value per
gate. Unary references walk that memo tape directly, while the third work tape
stores and consumes the declared unary gate count.

The local `TapeAction` layer packages the one-sided-tape safety obligation with
each head action. Consequently `evalFamilyCoreTM` satisfies
`TM.δ_right_of_start` structurally rather than through a large case proof.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

/-- One tape-head action together with its left-end safety proof. -/
structure TapeAction (head : Γ) where
  /-- Writable symbol emitted at the current head. -/
  write : Γw
  /-- Direction taken after the write. -/
  dir : Dir3
  /-- The action moves right whenever it reads the left-end marker. -/
  rightOfStart : head = Γ.start → dir = Dir3.right

namespace TapeAction

/-- Preserve the scanned cell and keep an off-marker head stationary. -/
def preserve (head : Γ) : TapeAction head where
  write := TM.readBackWrite head
  dir := TM.idleDir head
  rightOfStart := TM.idleDir_right_of_start

/-- Preserve the scanned cell and move right. -/
def moveRight (head : Γ) : TapeAction head where
  write := TM.readBackWrite head
  dir := .right
  rightOfStart := fun _ => rfl

/-- Preserve the scanned cell and move left, bouncing right at `▷`. -/
def moveLeft (head : Γ) : TapeAction head where
  write := TM.readBackWrite head
  dir := TM.moveLeftDir head
  rightOfStart := by
    intro h
    simp [TM.moveLeftDir, h]

/-- Write a symbol and move right. -/
def writeRight (head : Γ) (symbol : Γw) : TapeAction head where
  write := symbol
  dir := .right
  rightOfStart := fun _ => rfl

/-- Write a symbol and keep an off-marker head stationary. -/
def writeStay (head : Γ) (symbol : Γw) : TapeAction head where
  write := symbol
  dir := TM.idleDir head
  rightOfStart := TM.idleDir_right_of_start

end TapeAction

/-- Finite phases of the fused tagged-code parser and memoized evaluator. -/
inductive CorePhase where
  | rewindCode
  | rewindWires
  | familyTag
  | emptyAnswer
  | emptyEnd (answer : Bool)
  | count
  | rewindCounter
  | gateCheck (sawGate : Bool)
  | gateOp
  | gateNeg0 (op : Bool)
  | gateNeg1 (op negated0 : Bool)
  | rewindRef0 (op negated0 negated1 : Bool)
  | ref0 (op negated0 negated1 : Bool)
  | rewindRef1 (op negated1 value0 : Bool)
  | ref1 (op negated1 value0 : Bool)
  | seekAppend (value : Bool)
  | done
  deriving DecidableEq, Fintype, Repr

/-- Named actions for the three evaluator work tapes and the output tape. -/
structure CoreAction (wHeads : Fin workTapeCount → Γ) (oHead : Γ) where
  /-- Controller phase entered after this action. -/
  next : CorePhase
  /-- Action for the serialized-code tape. -/
  code : TapeAction (wHeads codeIdx)
  /-- Action for the input-and-memo wire tape. -/
  wires : TapeAction (wHeads wiresIdx)
  /-- Action for the unary gate-counter tape. -/
  counter : TapeAction (wHeads counterIdx)
  /-- Action for the Boolean verdict output tape. -/
  output : TapeAction oHead

namespace CoreAction

/-- Change only the controller phase and install `TapeAction.preserve` on
every tape. This is exact tape preservation when the framed heads are off the
left marker. -/
def preserve (next : CorePhase) (wHeads : Fin workTapeCount → Γ)
    (oHead : Γ) : CoreAction wHeads oHead where
  next := next
  code := TapeAction.preserve _
  wires := TapeAction.preserve _
  counter := TapeAction.preserve _
  output := TapeAction.preserve _

/-- Project the writable symbol for a named work tape. -/
def workWrite {wHeads : Fin workTapeCount → Γ} {oHead : Γ}
    (action : CoreAction wHeads oHead) (i : Fin workTapeCount) : Γw :=
  if i = codeIdx then action.code.write
  else if i = wiresIdx then action.wires.write
  else action.counter.write

/-- Project the direction for a named work tape. -/
def workDir {wHeads : Fin workTapeCount → Γ} {oHead : Γ}
    (action : CoreAction wHeads oHead) (i : Fin workTapeCount) : Dir3 :=
  if i = codeIdx then action.code.dir
  else if i = wiresIdx then action.wires.dir
  else action.counter.dir

/-- Every projected work action moves right when its head reads `▷`. -/
theorem workDir_rightOfStart {wHeads : Fin workTapeCount → Γ} {oHead : Γ}
    (action : CoreAction wHeads oHead) :
    ∀ i, wHeads i = Γ.start → action.workDir i = Dir3.right := by
  intro i hi
  by_cases hcode : i = codeIdx
  · subst i
    simpa [workDir] using action.code.rightOfStart hi
  by_cases hwires : i = wiresIdx
  · subst i
    simpa [workDir, hcode] using action.wires.rightOfStart hi
  have hne0 : i.val ≠ 0 := by
    intro hval
    apply hcode
    apply Fin.ext
    exact hval
  have hne1 : i.val ≠ 1 := by
    intro hval
    apply hwires
    apply Fin.ext
    exact hval
  have hcounter : i = counterIdx := by
    apply Fin.ext
    change i.val = 2
    have hi : i.val < 3 := by
      exact i.isLt
    omega
  subst i
  simpa [workDir, codeIdx, wiresIdx, counterIdx] using
    action.counter.rightOfStart hi

end CoreAction

/-- Boolean AND/OR selected by the serialized operation bit. -/
def evalOpBit (op value0 value1 : Bool) : Bool :=
  if op then value0 && value1 else value0 || value1

namespace CoreAction

/-- Halt with an explicit rejecting write, installing `TapeAction.preserve` on
the work tapes. -/
def reject (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  { CoreAction.preserve .done wHeads oHead with
    output := TapeAction.writeStay oHead .zero }

/-- Halt with the supplied Boolean write, installing `TapeAction.preserve` on
the work tapes. -/
def finish (answer : Bool) (wHeads : Fin workTapeCount → Γ)
    (oHead : Γ) : CoreAction wHeads oHead :=
  { CoreAction.preserve .done wHeads oHead with
    output := TapeAction.writeStay oHead (Γw.ofBool answer) }

/-- Move the code head right and install `TapeAction.preserve` on every other
tape. -/
def moveCodeRight (next : CorePhase)
    (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  { CoreAction.preserve next wHeads oHead with
    code := TapeAction.moveRight _ }

/-- Move the wire head right and install `TapeAction.preserve` on every other
tape. -/
def moveWiresRight (next : CorePhase)
    (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  { CoreAction.preserve next wHeads oHead with
    wires := TapeAction.moveRight _ }

/-- Read one Boolean code symbol, moving right on success and rejecting any
non-Boolean symbol. -/
def readCodeBit (next : Bool → CorePhase)
    (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  match wHeads codeIdx with
  | .zero => moveCodeRight (next false) wHeads oHead
  | .one => moveCodeRight (next true) wHeads oHead
  | _ => reject wHeads oHead

end CoreAction

/-- One finite-control action of the streaming evaluator. -/
def coreAction (phase : CorePhase) (wHeads : Fin workTapeCount → Γ)
    (oHead : Γ) : CoreAction wHeads oHead :=
  let codeHead := wHeads codeIdx
  let wiresHead := wHeads wiresIdx
  let counterHead := wHeads counterIdx
  match phase with
  | .rewindCode =>
      if codeHead = Γ.start then
        { CoreAction.preserve .rewindWires wHeads oHead with
          code := TapeAction.moveRight codeHead }
      else
        { CoreAction.preserve .rewindCode wHeads oHead with
          code := TapeAction.moveLeft codeHead }
  | .rewindWires =>
      if wiresHead = Γ.start then
        CoreAction.moveWiresRight .familyTag wHeads oHead
      else
        { CoreAction.preserve .rewindWires wHeads oHead with
          wires := TapeAction.moveLeft wiresHead }
  | .familyTag =>
      match wiresHead, codeHead with
      | .blank, .zero => CoreAction.moveCodeRight .emptyAnswer wHeads oHead
      | .zero, .one => CoreAction.moveCodeRight .count wHeads oHead
      | .one, .one => CoreAction.moveCodeRight .count wHeads oHead
      | _, _ => CoreAction.reject wHeads oHead
  | .emptyAnswer => CoreAction.readCodeBit .emptyEnd wHeads oHead
  | .emptyEnd answer =>
      if codeHead = Γ.blank then CoreAction.finish answer wHeads oHead
      else CoreAction.reject wHeads oHead
  | .count =>
      match codeHead with
      | .one =>
          { CoreAction.preserve .count wHeads oHead with
            code := TapeAction.moveRight codeHead
            counter := TapeAction.writeRight counterHead .one }
      | .zero => CoreAction.moveCodeRight .rewindCounter wHeads oHead
      | _ => CoreAction.reject wHeads oHead
  | .rewindCounter =>
      if counterHead = Γ.start then
        { CoreAction.preserve (.gateCheck false) wHeads oHead with
          counter := TapeAction.moveRight counterHead }
      else
        { CoreAction.preserve .rewindCounter wHeads oHead with
          counter := TapeAction.moveLeft counterHead }
  | .gateCheck sawGate =>
      match counterHead with
      | .one =>
          { CoreAction.preserve .gateOp wHeads oHead with
            counter := TapeAction.writeRight counterHead .blank }
      | .blank =>
          if sawGate && codeHead = Γ.blank then
            CoreAction.preserve .done wHeads oHead
          else
            CoreAction.reject wHeads oHead
      | _ => CoreAction.reject wHeads oHead
  | .gateOp => CoreAction.readCodeBit .gateNeg0 wHeads oHead
  | .gateNeg0 op => CoreAction.readCodeBit (.gateNeg1 op) wHeads oHead
  | .gateNeg1 op negated0 =>
      CoreAction.readCodeBit (.rewindRef0 op negated0) wHeads oHead
  | .rewindRef0 op negated0 negated1 =>
      if wiresHead = Γ.start then
        { CoreAction.preserve (.ref0 op negated0 negated1) wHeads oHead with
          wires := TapeAction.moveRight wiresHead }
      else
        { CoreAction.preserve (.rewindRef0 op negated0 negated1) wHeads oHead with
          wires := TapeAction.moveLeft wiresHead }
  | .ref0 op negated0 negated1 =>
      match codeHead, wiresHead with
      | .one, .zero =>
          { CoreAction.preserve (.ref0 op negated0 negated1) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .one, .one =>
          { CoreAction.preserve (.ref0 op negated0 negated1) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .zero, .zero =>
          CoreAction.moveCodeRight
            (.rewindRef1 op negated1 (negated0.xor false))
            wHeads oHead
      | .zero, .one =>
          CoreAction.moveCodeRight
            (.rewindRef1 op negated1 (negated0.xor true))
            wHeads oHead
      | _, _ => CoreAction.reject wHeads oHead
  | .rewindRef1 op negated1 value0 =>
      if wiresHead = Γ.start then
        { CoreAction.preserve (.ref1 op negated1 value0) wHeads oHead with
          wires := TapeAction.moveRight wiresHead }
      else
        { CoreAction.preserve (.rewindRef1 op negated1 value0) wHeads oHead with
          wires := TapeAction.moveLeft wiresHead }
  | .ref1 op negated1 value0 =>
      match codeHead, wiresHead with
      | .one, .zero =>
          { CoreAction.preserve (.ref1 op negated1 value0) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .one, .one =>
          { CoreAction.preserve (.ref1 op negated1 value0) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .zero, .zero =>
          CoreAction.moveCodeRight
            (.seekAppend (evalOpBit op value0 (negated1.xor false))) wHeads oHead
      | .zero, .one =>
          CoreAction.moveCodeRight
            (.seekAppend (evalOpBit op value0 (negated1.xor true))) wHeads oHead
      | _, _ => CoreAction.reject wHeads oHead
  | .seekAppend value =>
      match wiresHead with
      | .zero => CoreAction.moveWiresRight (.seekAppend value) wHeads oHead
      | .one => CoreAction.moveWiresRight (.seekAppend value) wHeads oHead
      | .blank =>
          { CoreAction.preserve (.gateCheck true) wHeads oHead with
            wires := TapeAction.writeRight wiresHead (Γw.ofBool value)
            output := TapeAction.writeStay oHead (Γw.ofBool value) }
      | .start => CoreAction.reject wHeads oHead
  | .done => CoreAction.preserve .done wHeads oHead

/-- Streaming evaluator for a valid outer pair after `validPairStageTM`.

The core itself remains total: malformed tagged codes and invalid references
write zero and halt. -/
def evalFamilyCoreTM : TM workTapeCount where
  Q := CorePhase
  qstart := .rewindCode
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    let action := coreAction phase wHeads oHead
    (action.next, action.workWrite, action.output.write,
      TM.idleDir iHead, action.workDir, action.output.dir)
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    let action := coreAction phase wHeads oHead
    exact ⟨TM.idleDir_right_of_start, action.workDir_rightOfStart,
      action.output.rightOfStart⟩

/-- Uniform quadratic time budget for evaluating a staged tagged-family code.
The arguments are the serialized code length and primary-input length. -/
def evalFamilyCoreTime (codeLength inputLength : ℕ) : ℕ :=
  20 * (codeLength + inputLength + 1) ^ 2

/-- Staged tapes expected by the serialized-family evaluator core. The input
tape is threaded as an explicit frame while the code and primary-input work
tapes are parked at their append frontiers and the counter tape is fresh. -/
def FamilyCorePre (codeBits inputBits : List Bool) (initialInput : Tape)
    (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp = initialInput ∧
  inp.read ≠ Γ.start ∧
  (work codeIdx).cells 0 = Γ.start ∧
  (work codeIdx).HasBinaryPrefix codeBits ∧
  (work wiresIdx).cells 0 = Γ.start ∧
  (work wiresIdx).HasBinaryPrefix inputBits ∧
  work counterIdx = (Tape.init []).move Dir3.right ∧
  out.head = 1 ∧
  out.StartInvariant

/-- Halted defaulted-verdict contract for the serialized-family evaluator
core. Malformed codes and successful false evaluations both write zero. The
terminal work tapes are intentionally unconstrained because rejecting parses
halt at different code, memo, and counter cursor positions. -/
def FamilyCorePost (codeBits inputBits : List Bool) (initialInput : Tape)
    (inp : Tape) (_work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp = initialInput ∧
  out.head = 1 ∧
  out.StartInvariant ∧
  out.cells 1 = Γ.ofBool ((evalFamilyCode codeBits inputBits).getD false)

/-- Total serialized-family evaluator: validate and stage the outer pair, then
run the streaming core only on the valid branch. -/
def evalFamilyTM : TM workTapeCount :=
  evalFamilyTMWith evalFamilyCoreTM

/-- Concrete end-to-end time budget for validating, staging, and evaluating a
serialized circuit-family input of length `n`. -/
def evalFamilyTime (n : ℕ) : ℕ :=
  evalFamilyTMWithTime n (evalFamilyCoreTime n 0)

/-- Halted end-to-end contract for the serialized-family evaluator. The input
cells retain the original encoding and the output carries the defaulted paired
evaluation verdict with its canonical head and left-marker invariant. Terminal
work tapes are intentionally unconstrained across valid and rejecting branches. -/
def EvalFamilyPost (bits : List Bool) (inp : Tape)
    (_work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
  out.head = 1 ∧
  out.StartInvariant ∧
  out.cells 1 = Γ.ofBool ((evalFamilyPair? bits).getD false)

end Machine

end CircuitCode

end Complexity
