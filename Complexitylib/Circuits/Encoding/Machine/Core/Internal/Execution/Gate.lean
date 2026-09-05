/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution

/-!
# One-gate execution for the streaming circuit evaluator

This file proves the machine-level execution of one valid serialized gate.
The proof follows the controller's dependency order: consume one gate-count
mark, read the three fixed gate bits, rewind and resolve the first reference,
rewind and resolve the second reference, then append the computed value to the
wire memo.

The small named-action lemmas at the start are deliberately phase-generic
within this controller. They are the reusable proof-engineering seam between
`CoreAction` and exact named configurations.
-/


public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Applying a named preserve action changes only the controller phase when
all parked heads are away from the left marker. -/
theorem coreCfg_step_preserve (phase next : CorePhase)
    (input code wires counter output : Tape)
    (hphase : phase ≠ CorePhase.done)
    (haction : coreAction phase (coreHeads code wires counter) output.read =
      CoreAction.preserve next (coreHeads code wires counter) output.read)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step (coreCfg phase input code wires counter output) =
      some (coreCfg next input code wires counter output) := by
  rw [coreCfg_step phase input code wires counter output hphase, haction]
  simp only [CoreAction.preserve, TapeAction.preserve, coreHeads_codeIdx,
    coreHeads_wiresIdx, coreHeads_counterIdx]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Applying a named code-right action advances exactly the code tape and
changes the controller phase. -/
theorem coreCfg_step_moveCodeRight (phase next : CorePhase)
    (input code wires counter output : Tape)
    (hphase : phase ≠ CorePhase.done)
    (haction : coreAction phase (coreHeads code wires counter) output.read =
      CoreAction.moveCodeRight next (coreHeads code wires counter) output.read)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step (coreCfg phase input code wires counter output) =
      some (coreCfg next input (code.move Dir3.right) wires counter output) := by
  rw [coreCfg_step phase input code wires counter output hphase, haction]
  simp only [CoreAction.moveCodeRight, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight, coreHeads_codeIdx,
    coreHeads_wiresIdx, coreHeads_counterIdx]
  rw [TM.writeAndMove_readBack code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Applying a named wire-right action advances exactly the wire tape and
changes the controller phase. -/
theorem coreCfg_step_moveWiresRight (phase next : CorePhase)
    (input code wires counter output : Tape)
    (hphase : phase ≠ CorePhase.done)
    (haction : coreAction phase (coreHeads code wires counter) output.read =
      CoreAction.moveWiresRight next (coreHeads code wires counter) output.read)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step (coreCfg phase input code wires counter output) =
      some (coreCfg next input code (wires.move Dir3.right) counter output) := by
  rw [coreCfg_step phase input code wires counter output hphase, haction]
  simp only [CoreAction.moveWiresRight, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight, coreHeads_codeIdx,
    coreHeads_wiresIdx, coreHeads_counterIdx]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [TM.writeAndMove_readBack wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- A positive gate-check consumes one unary counter mark and enters the
fixed-width gate header. -/
theorem gateCheck_step_one (sawGate : Bool) (used total : ℕ)
    (input code wires counter output : Tape)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateCheck sawGate) input code wires counter output) =
      some (coreCfg .gateOp input code wires
        (counter.writeAndMove Γ.blank Dir3.right) output) := by
  have hcounterRead : counter.read = Γ.one :=
    Tape.hasCounterRemainder_read_one_of_remaining hcounter hremaining
  rw [coreCfg_step (.gateCheck sawGate) input code wires counter output
    (by cases sawGate <;> decide)]
  simp only [coreAction, coreHeads_counterIdx, hcounterRead,
    CoreAction.preserve, TapeAction.preserve, TapeAction.writeRight,
    coreHeads_codeIdx, coreHeads_wiresIdx]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- The gate-operation phase consumes the operation bit. -/
theorem gateOp_step (op : Bool) (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (op :: rest))
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .gateOp input code wires counter output) =
      some (coreCfg (.gateNeg0 op) input (code.move Dir3.right)
        wires counter output) := by
  apply coreCfg_step_moveCodeRight .gateOp (.gateNeg0 op)
    input code wires counter output (by decide)
  · have hread : code.read = Γ.ofBool op := hcode.read_cons
    cases op <;> simp [coreAction, CoreAction.readCodeBit, hread, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires
  · exact hcounter
  · exact houtput

/-- The first-negation phase consumes the first negation bit. -/
theorem gateNeg0_step (op negated0 : Bool) (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (negated0 :: rest))
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateNeg0 op) input code wires counter output) =
      some (coreCfg (.gateNeg1 op negated0) input (code.move Dir3.right)
        wires counter output) := by
  apply coreCfg_step_moveCodeRight (.gateNeg0 op) (.gateNeg1 op negated0)
    input code wires counter output (by cases op <;> decide)
  · have hread : code.read = Γ.ofBool negated0 := hcode.read_cons
    cases negated0 <;>
      simp [coreAction, CoreAction.readCodeBit, hread, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires
  · exact hcounter
  · exact houtput

/-- The second-negation phase consumes the second negation bit and begins
the first wire rewind. -/
theorem gateNeg1_step (op negated0 negated1 : Bool) (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (negated1 :: rest))
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.gateNeg1 op negated0) input code wires counter output) =
      some (coreCfg (.rewindRef0 op negated0 negated1) input
        (code.move Dir3.right) wires counter output) := by
  apply coreCfg_step_moveCodeRight (.gateNeg1 op negated0)
    (.rewindRef0 op negated0 negated1) input code wires counter output
    (by cases op <;> cases negated0 <;> decide)
  · have hread : code.read = Γ.ofBool negated1 := hcode.read_cons
    cases negated1 <;>
      simp [coreAction, CoreAction.readCodeBit, hread, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires
  · exact hcounter
  · exact houtput

/-- Consuming a counter mark and the three fixed gate bits reaches the first
reference rewind in exactly four steps. -/
theorem gateHeader_run (sawGate op negated0 negated1 : Bool)
    (rest : List Bool) {wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (op :: negated0 :: negated1 :: rest))
    (hwires : BinaryCursor wires wireBits position)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ code',
      evalFamilyCoreTM.reachesIn 4
        (coreCfg (.gateCheck sawGate) input code wires counter output)
        (coreCfg (.rewindRef0 op negated0 negated1) input code' wires
          (counter.writeAndMove Γ.blank Dir3.right) output) ∧
      code'.HasBinarySuffix rest ∧
      (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
        (used + 1) total := by
  have hcounterNext :=
    Tape.hasCounterRemainder_consume hcounter hremaining
  have hcounterNextRead :=
    Tape.hasCounterRemainder_read_ne_start hcounterNext
  have hstep0 := gateCheck_step_one sawGate used total
    input code wires counter output hcounter hremaining hinput
    hcode.read_ne_start hwires.read_ne_start houtput
  have hstep1 := gateOp_step op (negated0 :: negated1 :: rest)
    input code wires (counter.writeAndMove Γ.blank Dir3.right) output
    hcode hinput hwires.read_ne_start hcounterNextRead houtput
  have hcode1 := hcode.move_right_cons
  have hstep2 := gateNeg0_step op negated0 (negated1 :: rest)
    input (code.move Dir3.right) wires
    (counter.writeAndMove Γ.blank Dir3.right) output hcode1 hinput
    hwires.read_ne_start hcounterNextRead houtput
  have hcode2 := hcode1.move_right_cons
  have hstep3 := gateNeg1_step op negated0 negated1 rest
    input ((code.move Dir3.right).move Dir3.right) wires
    (counter.writeAndMove Γ.blank Dir3.right) output hcode2 hinput
    hwires.read_ne_start hcounterNextRead houtput
  have hcode3 := hcode2.move_right_cons
  refine ⟨((code.move Dir3.right).move Dir3.right).move Dir3.right,
    ?_, hcode3, hcounterNext⟩
  simpa using TM.reachesIn.step hstep0
    (TM.reachesIn.step hstep1
      (TM.reachesIn.step hstep2
        (TM.reachesIn.step hstep3 TM.reachesIn.zero)))

/-- An off-marker first-reference rewind takes one ordinary wire-left step. -/
theorem rewindRef0_step_cursor (op negated0 negated1 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.rewindRef0 op negated0 negated1)
          input code wires counter output) =
      some (coreCfg (.rewindRef0 op negated0 negated1)
        input code (wires.move Dir3.left) counter output) := by
  rw [coreCfg_step (.rewindRef0 op negated0 negated1)
    input code wires counter output
    (by cases op <;> cases negated0 <;> cases negated1 <;> decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwires.read_ne_start, ite_false,
    coreHeads_codeIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveLeft]
  rw [hwires.applyMoveLeft]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Reaching the wire marker ends the first-reference rewind and returns the
wire head to its first bit. -/
theorem rewindRef0_step_marker (op negated0 negated1 : Bool)
    {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hwires : BinaryAtMarker wires wireBits)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.rewindRef0 op negated0 negated1)
          input code wires counter output) =
      some (coreCfg (.ref0 op negated0 negated1)
        input code (wires.move Dir3.right) counter output) := by
  rw [coreCfg_step (.rewindRef0 op negated0 negated1)
    input code wires counter output
    (by cases op <;> cases negated0 <;> cases negated1 <;> decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwires.read_start, ite_true,
    coreHeads_codeIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight]
  have hwiresMove :
      wires.writeAndMove (TM.readBackWrite Γ.start) Dir3.right =
        wires.move Dir3.right := by
    rw [← hwires.read_start]
    exact hwires.applyMoveRight
  rw [hwiresMove]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Rewinding for the first reference takes exactly `position + 2` steps
and returns the wire tape to position zero. -/
theorem rewindRef0_run (op negated0 negated1 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ wires',
      evalFamilyCoreTM.reachesIn (position + 2)
        (coreCfg (.rewindRef0 op negated0 negated1)
          input code wires counter output)
        (coreCfg (.ref0 op negated0 negated1)
          input code wires' counter output) ∧
      BinaryCursor wires' wireBits 0 := by
  induction position generalizing wires with
  | zero =>
      have hstep1 := rewindRef0_step_cursor op negated0 negated1
        input code wires counter output hwires hinput hcode hcounter houtput
      have hmarker := hwires.toMarker
      rw [hwires.applyMoveLeft] at hmarker
      have hstep2 := rewindRef0_step_marker op negated0 negated1
        input code (wires.move Dir3.left) counter output hmarker hinput hcode
        hcounter houtput
      have hfirst := hmarker.returnToFirstBit
      rw [hmarker.applyMoveRight] at hfirst
      refine ⟨(wires.move Dir3.left).move Dir3.right, ?_, hfirst⟩
      simpa using TM.reachesIn.step hstep1
        (TM.reachesIn.step hstep2 TM.reachesIn.zero)
  | succ position ih =>
      have hstep := rewindRef0_step_cursor op negated0 negated1
        input code wires counter output hwires hinput hcode hcounter houtput
      have hnext := hwires.moveLeft (by omega)
      obtain ⟨wires', hreach, hfirst⟩ :=
        ih (wires := wires.move Dir3.left) hnext
      refine ⟨wires', ?_, hfirst⟩
      simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach

/-- An off-marker second-reference rewind takes one ordinary wire-left step. -/
theorem rewindRef1_step_cursor (op negated1 value0 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.rewindRef1 op negated1 value0)
          input code wires counter output) =
      some (coreCfg (.rewindRef1 op negated1 value0)
        input code (wires.move Dir3.left) counter output) := by
  rw [coreCfg_step (.rewindRef1 op negated1 value0)
    input code wires counter output
    (by cases op <;> cases negated1 <;> cases value0 <;> decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwires.read_ne_start, ite_false,
    coreHeads_codeIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveLeft]
  rw [hwires.applyMoveLeft]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Reaching the wire marker ends the second-reference rewind and returns the
wire head to its first bit. -/
theorem rewindRef1_step_marker (op negated1 value0 : Bool)
    {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hwires : BinaryAtMarker wires wireBits)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.rewindRef1 op negated1 value0)
          input code wires counter output) =
      some (coreCfg (.ref1 op negated1 value0)
        input code (wires.move Dir3.right) counter output) := by
  rw [coreCfg_step (.rewindRef1 op negated1 value0)
    input code wires counter output
    (by cases op <;> cases negated1 <;> cases value0 <;> decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwires.read_start, ite_true,
    coreHeads_codeIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight]
  have hwiresMove :
      wires.writeAndMove (TM.readBackWrite Γ.start) Dir3.right =
        wires.move Dir3.right := by
    rw [← hwires.read_start]
    exact hwires.applyMoveRight
  rw [hwiresMove]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Rewinding for the second reference takes exactly `position + 2` steps
and returns the wire tape to position zero. -/
theorem rewindRef1_run (op negated1 value0 : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ wires',
      evalFamilyCoreTM.reachesIn (position + 2)
        (coreCfg (.rewindRef1 op negated1 value0)
          input code wires counter output)
        (coreCfg (.ref1 op negated1 value0)
          input code wires' counter output) ∧
      BinaryCursor wires' wireBits 0 := by
  induction position generalizing wires with
  | zero =>
      have hstep1 := rewindRef1_step_cursor op negated1 value0
        input code wires counter output hwires hinput hcode hcounter houtput
      have hmarker := hwires.toMarker
      rw [hwires.applyMoveLeft] at hmarker
      have hstep2 := rewindRef1_step_marker op negated1 value0
        input code (wires.move Dir3.left) counter output hmarker hinput hcode
        hcounter houtput
      have hfirst := hmarker.returnToFirstBit
      rw [hmarker.applyMoveRight] at hfirst
      refine ⟨(wires.move Dir3.left).move Dir3.right, ?_, hfirst⟩
      simpa using TM.reachesIn.step hstep1
        (TM.reachesIn.step hstep2 TM.reachesIn.zero)
  | succ position ih =>
      have hstep := rewindRef1_step_cursor op negated1 value0
        input code wires counter output hwires hinput hcode hcounter houtput
      have hnext := hwires.moveLeft (by omega)
      obtain ⟨wires', hreach, hfirst⟩ :=
        ih (wires := wires.move Dir3.left) hnext
      refine ⟨wires', ?_, hfirst⟩
      simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach

/-- Reading a unary one in the first reference advances both the code and
wire cursors. -/
theorem ref0_step_one (op negated0 negated1 : Bool) (rest : List Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (true :: rest))
    (hwires : BinaryCursor wires wireBits position)
    (hposition : position < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output) =
      some (coreCfg (.ref0 op negated0 negated1) input
        (code.move Dir3.right) (wires.move Dir3.right) counter output) := by
  have hcodeRead : code.read = Γ.one := by
    simpa [Γ.ofBool] using hcode.read_cons
  have hwiresRead : wires.read = Γ.ofBool (wireBits[position]'hposition) :=
    hwires.read_of_lt hposition
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.one) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact TM.writeAndMove_readBack code hcode.read_ne_start Dir3.right
  have hwiresMove :
      wires.writeAndMove
          (TM.readBackWrite (Γ.ofBool (wireBits[position]'hposition)))
          Dir3.right = wires.move Dir3.right := by
    rw [← hwiresRead]
    exact hwires.applyMoveRight
  rw [coreCfg_step (.ref0 op negated0 negated1)
    input code wires counter output
    (by cases op <;> cases negated0 <;> cases negated1 <;> decide)]
  cases hvalue : wireBits[position]'hposition <;>
    simp only [coreAction, coreHeads_codeIdx, hcodeRead, coreHeads_wiresIdx,
      hwiresRead, hvalue, Γ.ofBool, coreHeads_counterIdx,
      CoreAction.preserve, TapeAction.preserve, TapeAction.moveRight]
  all_goals
    simp only [hvalue, Γ.ofBool] at hwiresMove
    rw [hcodeMove, hwiresMove]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
    simp [TM.idleDir, hinput, Tape.move]

/-- The zero delimiter of the first reference captures the selected wire
value and advances only the code cursor. -/
theorem ref0_step_zero (op negated0 negated1 : Bool) (rest : List Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (false :: rest))
    (hwires : BinaryCursor wires wireBits position)
    (hposition : position < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output) =
      some (coreCfg
        (.rewindRef1 op negated1
          (negated0.xor (wireBits[position]'hposition)))
        input (code.move Dir3.right) wires counter output) := by
  have hcodeRead : code.read = Γ.zero := by
    simpa [Γ.ofBool] using hcode.read_cons
  have hwiresRead : wires.read = Γ.ofBool (wireBits[position]'hposition) :=
    hwires.read_of_lt hposition
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.zero) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact TM.writeAndMove_readBack code hcode.read_ne_start Dir3.right
  have hwiresKeep :
      wires.writeAndMove
          (TM.readBackWrite (Γ.ofBool (wireBits[position]'hposition)))
          (TM.idleDir (Γ.ofBool (wireBits[position]'hposition))) = wires := by
    rw [← hwiresRead]
    exact hwires.preserve
  rw [coreCfg_step (.ref0 op negated0 negated1)
    input code wires counter output
    (by cases op <;> cases negated0 <;> cases negated1 <;> decide)]
  cases hvalue : wireBits[position]'hposition <;>
    simp only [coreAction, coreHeads_codeIdx, hcodeRead, coreHeads_wiresIdx,
      hwiresRead, hvalue, Γ.ofBool, Bool.xor_false, Bool.xor_true,
      coreHeads_counterIdx, CoreAction.moveCodeRight, CoreAction.preserve,
      TapeAction.preserve, TapeAction.moveRight]
  all_goals
    simp only [hvalue, Γ.ofBool] at hwiresKeep
    rw [hcodeMove, hwiresKeep]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
    simp [TM.idleDir, hinput, Tape.move]

/-- Resolve a terminated-unary first reference after `used` wire positions
have already been traversed. -/
private theorem ref0_run_aux (op negated0 negated1 : Bool)
    (rest : List Bool) {wireBits : List Bool} (used remaining : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix
      (List.replicate remaining true ++ false :: rest))
    (hwires : BinaryCursor wires wireBits used)
    (hreference : used + remaining < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (remaining + 1)
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output)
        (coreCfg
          (.rewindRef1 op negated1
            (negated0.xor (wireBits[used + remaining]'hreference)))
          input code' wires' counter output) ∧
      code'.HasBinarySuffix rest ∧
      BinaryCursor wires' wireBits (used + remaining) := by
  induction remaining generalizing code wires used with
  | zero =>
      have hzero : code.HasBinarySuffix (false :: rest) := by
        simpa using hcode
      have hstep := ref0_step_zero op negated0 negated1 rest
        input code wires counter output hzero hwires (by simpa using hreference)
        hinput hcounter houtput
      refine ⟨code.move Dir3.right, wires, ?_, hzero.move_right_cons, ?_⟩
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
      · simpa using hwires
  | succ remaining ih =>
      have hone : code.HasBinarySuffix
          (true :: (List.replicate remaining true ++ false :: rest)) := by
        simpa [List.replicate_succ] using hcode
      have hstep := ref0_step_one op negated0 negated1
        (List.replicate remaining true ++ false :: rest)
        input code wires counter output hone hwires (by omega)
        hinput hcounter houtput
      have hcodeNext := hone.move_right_cons
      have hwiresNext := hwires.moveRight (by omega)
      obtain ⟨code', wires', hreach, hcodeFinal, hwiresFinal⟩ :=
        ih (used := used + 1) (code := code.move Dir3.right)
          (wires := wires.move Dir3.right) hcodeNext hwiresNext (by omega)
      refine ⟨code', wires', ?_, hcodeFinal, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          TM.reachesIn.step hstep hreach
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hwiresFinal

/-- A complete first reference is resolved in exactly `reference + 1` steps,
leaving the wire cursor at the referenced position. -/
theorem ref0_run (op negated0 negated1 : Bool) (reference : ℕ)
    (rest : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (NatCode.encode reference ++ rest))
    (hwires : BinaryCursor wires wireBits 0)
    (hreference : reference < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (reference + 1)
        (coreCfg (.ref0 op negated0 negated1)
          input code wires counter output)
        (coreCfg
          (.rewindRef1 op negated1
            (negated0.xor (wireBits[reference]'hreference)))
          input code' wires' counter output) ∧
      code'.HasBinarySuffix rest ∧
      BinaryCursor wires' wireBits reference := by
  have hcode' : code.HasBinarySuffix
      (List.replicate reference true ++ false :: rest) := by
    simpa [NatCode.encode, List.append_assoc] using hcode
  simpa using ref0_run_aux op negated0 negated1 rest 0 reference
    input code wires counter output hcode' hwires (by simpa using hreference)
    hinput hcounter houtput

/-- Reading a unary one in the second reference advances both the code and
wire cursors. -/
theorem ref1_step_one (op negated1 value0 : Bool) (rest : List Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (true :: rest))
    (hwires : BinaryCursor wires wireBits position)
    (hposition : position < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output) =
      some (coreCfg (.ref1 op negated1 value0) input
        (code.move Dir3.right) (wires.move Dir3.right) counter output) := by
  have hcodeRead : code.read = Γ.one := by
    simpa [Γ.ofBool] using hcode.read_cons
  have hwiresRead : wires.read = Γ.ofBool (wireBits[position]'hposition) :=
    hwires.read_of_lt hposition
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.one) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact TM.writeAndMove_readBack code hcode.read_ne_start Dir3.right
  have hwiresMove :
      wires.writeAndMove
          (TM.readBackWrite (Γ.ofBool (wireBits[position]'hposition)))
          Dir3.right = wires.move Dir3.right := by
    rw [← hwiresRead]
    exact hwires.applyMoveRight
  rw [coreCfg_step (.ref1 op negated1 value0)
    input code wires counter output
    (by cases op <;> cases negated1 <;> cases value0 <;> decide)]
  cases hvalue : wireBits[position]'hposition <;>
    simp only [coreAction, coreHeads_codeIdx, hcodeRead, coreHeads_wiresIdx,
      hwiresRead, hvalue, Γ.ofBool, coreHeads_counterIdx,
      CoreAction.preserve, TapeAction.preserve, TapeAction.moveRight]
  all_goals
    simp only [hvalue, Γ.ofBool] at hwiresMove
    rw [hcodeMove, hwiresMove]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
    simp [TM.idleDir, hinput, Tape.move]

/-- The zero delimiter of the second reference captures the selected wire
value, computes the gate, and advances only the code cursor. -/
theorem ref1_step_zero (op negated1 value0 : Bool) (rest : List Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (false :: rest))
    (hwires : BinaryCursor wires wireBits position)
    (hposition : position < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output) =
      some (coreCfg
        (.seekAppend
          (evalOpBit op value0
            (negated1.xor (wireBits[position]'hposition))))
        input (code.move Dir3.right) wires counter output) := by
  have hcodeRead : code.read = Γ.zero := by
    simpa [Γ.ofBool] using hcode.read_cons
  have hwiresRead : wires.read = Γ.ofBool (wireBits[position]'hposition) :=
    hwires.read_of_lt hposition
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.zero) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact TM.writeAndMove_readBack code hcode.read_ne_start Dir3.right
  have hwiresKeep :
      wires.writeAndMove
          (TM.readBackWrite (Γ.ofBool (wireBits[position]'hposition)))
          (TM.idleDir (Γ.ofBool (wireBits[position]'hposition))) = wires := by
    rw [← hwiresRead]
    exact hwires.preserve
  rw [coreCfg_step (.ref1 op negated1 value0)
    input code wires counter output
    (by cases op <;> cases negated1 <;> cases value0 <;> decide)]
  cases hvalue : wireBits[position]'hposition <;>
    simp only [coreAction, coreHeads_codeIdx, hcodeRead, coreHeads_wiresIdx,
      hwiresRead, hvalue, Γ.ofBool, Bool.xor_false, Bool.xor_true,
      coreHeads_counterIdx, CoreAction.moveCodeRight, CoreAction.preserve,
      TapeAction.preserve, TapeAction.moveRight]
  all_goals
    simp only [hvalue, Γ.ofBool] at hwiresKeep
    rw [hcodeMove, hwiresKeep]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
    simp [TM.idleDir, hinput, Tape.move]

/-- Resolve a terminated-unary second reference after `used` wire positions
have already been traversed. -/
private theorem ref1_run_aux (op negated1 value0 : Bool)
    (rest : List Bool) {wireBits : List Bool} (used remaining : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix
      (List.replicate remaining true ++ false :: rest))
    (hwires : BinaryCursor wires wireBits used)
    (hreference : used + remaining < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (remaining + 1)
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output)
        (coreCfg
          (.seekAppend
            (evalOpBit op value0
              (negated1.xor
                (wireBits[used + remaining]'hreference))))
          input code' wires' counter output) ∧
      code'.HasBinarySuffix rest ∧
      BinaryCursor wires' wireBits (used + remaining) := by
  induction remaining generalizing code wires used with
  | zero =>
      have hzero : code.HasBinarySuffix (false :: rest) := by
        simpa using hcode
      have hstep := ref1_step_zero op negated1 value0 rest
        input code wires counter output hzero hwires (by simpa using hreference)
        hinput hcounter houtput
      refine ⟨code.move Dir3.right, wires, ?_, hzero.move_right_cons, ?_⟩
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
      · simpa using hwires
  | succ remaining ih =>
      have hone : code.HasBinarySuffix
          (true :: (List.replicate remaining true ++ false :: rest)) := by
        simpa [List.replicate_succ] using hcode
      have hstep := ref1_step_one op negated1 value0
        (List.replicate remaining true ++ false :: rest)
        input code wires counter output hone hwires (by omega)
        hinput hcounter houtput
      have hcodeNext := hone.move_right_cons
      have hwiresNext := hwires.moveRight (by omega)
      obtain ⟨code', wires', hreach, hcodeFinal, hwiresFinal⟩ :=
        ih (used := used + 1) (code := code.move Dir3.right)
          (wires := wires.move Dir3.right) hcodeNext hwiresNext (by omega)
      refine ⟨code', wires', ?_, hcodeFinal, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          TM.reachesIn.step hstep hreach
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hwiresFinal

/-- A complete second reference is resolved in exactly `reference + 1`
steps, leaving the wire cursor at the referenced position. -/
theorem ref1_run (op negated1 value0 : Bool) (reference : ℕ)
    (rest : List Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (NatCode.encode reference ++ rest))
    (hwires : BinaryCursor wires wireBits 0)
    (hreference : reference < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (reference + 1)
        (coreCfg (.ref1 op negated1 value0)
          input code wires counter output)
        (coreCfg
          (.seekAppend
            (evalOpBit op value0
              (negated1.xor (wireBits[reference]'hreference))))
          input code' wires' counter output) ∧
      code'.HasBinarySuffix rest ∧
      BinaryCursor wires' wireBits reference := by
  have hcode' : code.HasBinarySuffix
      (List.replicate reference true ++ false :: rest) := by
    simpa [NatCode.encode, List.append_assoc] using hcode
  simpa using ref1_run_aux op negated1 value0 rest 0 reference
    input code wires counter output hcode' hwires (by simpa using hreference)
    hinput hcounter houtput

/-- Seeking the append frontier across an existing wire advances only the
wire cursor. -/
theorem seekAppend_step_bit (value : Bool)
    {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hposition : position < wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.seekAppend value) input code wires counter output) =
      some (coreCfg (.seekAppend value) input code
        (wires.move Dir3.right) counter output) := by
  have hwiresRead : wires.read = Γ.ofBool (wireBits[position]'hposition) :=
    hwires.read_of_lt hposition
  apply coreCfg_step_moveWiresRight (.seekAppend value) (.seekAppend value)
    input code wires counter output (by cases value <;> decide)
  · cases hbit : wireBits[position]'hposition <;>
      simp [coreAction, hwiresRead, hbit, Γ.ofBool]
  · exact hinput
  · exact hcode
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- At the first blank after the wire memo, the controller appends the new
wire value, mirrors it to the current output cell, and returns to gate check. -/
theorem seekAppend_step_frontier (value : Bool) {wireBits : List Bool}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.seekAppend value) input code wires counter output) =
      some (coreCfg (.gateCheck true) input code
        (wires.writeAndMove (Γ.ofBool value) Dir3.right) counter
        (output.write (Γ.ofBool value))) := by
  have hwiresRead : wires.read = Γ.blank := hwires.read_frontier
  rw [coreCfg_step (.seekAppend value) input code wires counter output
    (by cases value <;> decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwiresRead,
    coreHeads_codeIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.writeRight, TapeAction.writeStay,
    Γw.ofBool_toΓ]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  simp [TM.idleDir, hinput, houtput, Tape.move]

/-- Seek and append when `remaining` existing wire cells lie at or after the
current cursor position. -/
private theorem seekAppend_run_aux (value : Bool) {wireBits : List Bool}
    (position remaining : ℕ) (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hlength : position + remaining = wireBits.length)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ wires',
      evalFamilyCoreTM.reachesIn (remaining + 1)
        (coreCfg (.seekAppend value) input code wires counter output)
        (coreCfg (.gateCheck true) input code wires' counter
          (output.write (Γ.ofBool value))) ∧
      BinaryCursor wires' (wireBits ++ [value])
        (wireBits ++ [value]).length := by
  induction remaining generalizing position wires with
  | zero =>
      have hposition : position = wireBits.length := by omega
      subst position
      have hstep := seekAppend_step_frontier value input code wires counter
        output hwires hinput hcode hcounter houtput
      refine ⟨wires.writeAndMove (Γ.ofBool value) Dir3.right, ?_, ?_⟩
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
      · simpa [← Γw.ofBool_toΓ] using hwires.appendWritable value
  | succ remaining ih =>
      have hposition : position < wireBits.length := by omega
      have hstep := seekAppend_step_bit value input code wires counter output
        hwires hposition hinput hcode hcounter houtput
      have hwiresNext := hwires.moveRight hposition
      obtain ⟨wires', hreach, hwiresFinal⟩ :=
        ih (position := position + 1) (wires := wires.move Dir3.right)
          hwiresNext (by omega)
      refine ⟨wires', ?_, hwiresFinal⟩
      simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach

/-- Seeking from an arbitrary in-bounds wire cursor appends in exactly
`wireBits.length - position + 1` steps. -/
theorem seekAppend_run (value : Bool) {wireBits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires wireBits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ wires',
      evalFamilyCoreTM.reachesIn (wireBits.length - position + 1)
        (coreCfg (.seekAppend value) input code wires counter output)
        (coreCfg (.gateCheck true) input code wires' counter
          (output.write (Γ.ofBool value))) ∧
      BinaryCursor wires' (wireBits ++ [value])
        (wireBits ++ [value]).length := by
  have hposition : position ≤ wireBits.length := hwires.1
  exact seekAppend_run_aux value position (wireBits.length - position)
    input code wires counter output hwires (by omega) hinput hcode hcounter
    houtput

/-- Evaluating the serialized operation bit of a raw gate agrees with the raw
gate evaluator. -/
theorem evalOpBit_opBit_eq_eval (gate : RawGate) (value0 value1 : Bool) :
    evalOpBit gate.opBit (gate.negated₀.xor value0)
        (gate.negated₁.xor value1) =
      gate.eval value0 value1 := by
  cases gate with
  | mk op input0 input1 negated0 negated1 =>
      cases op <;> rfl

/-- One canonical, in-range serialized gate executes in controller order with
an exact aggregate cost. The second-reference traversal cancels against the
remaining append seek, so the total depends only on the initial wire position,
the first reference, and the memo length. -/
theorem gateAttempt_run_encoded (sawGate : Bool) (gate : RawGate)
    (rest : List Bool) {wireBits : List Bool} {position used total : ℕ}
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (gate.encode ++ rest))
    (hwires : BinaryCursor wires wireBits position)
    (hgate : gate.WellFormedAt wireBits.length)
    (hcounter : counter.HasCounterRemainder used total)
    (hremaining : used < total)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn
        (position + 2 * gate.input₀ + wireBits.length + 11)
        (coreCfg (.gateCheck sawGate) input code wires counter output)
        (coreCfg (.gateCheck true) input code' wires'
          (counter.writeAndMove Γ.blank Dir3.right)
          (output.write (Γ.ofBool
            (gate.eval (wireBits[gate.input₀]'hgate.1)
              (wireBits[gate.input₁]'hgate.2))))) ∧
      code'.HasBinarySuffix rest ∧
      BinaryCursor wires'
        (wireBits ++ [gate.eval (wireBits[gate.input₀]'hgate.1)
          (wireBits[gate.input₁]'hgate.2)])
        (wireBits ++ [gate.eval (wireBits[gate.input₀]'hgate.1)
          (wireBits[gate.input₁]'hgate.2)]).length ∧
      (counter.writeAndMove Γ.blank Dir3.right).HasCounterRemainder
        (used + 1) total := by
  have hinput0 : gate.input₀ < wireBits.length := hgate.1
  have hinput1 : gate.input₁ < wireBits.length := hgate.2
  have hcodeHeader : code.HasBinarySuffix
      (gate.opBit :: gate.negated₀ :: gate.negated₁ ::
        (NatCode.encode gate.input₀ ++ NatCode.encode gate.input₁ ++ rest)) := by
    simpa [RawGate.encode, List.append_assoc] using hcode
  obtain ⟨code0, hheader, hcode0, hcounterNext⟩ :=
    gateHeader_run sawGate gate.opBit gate.negated₀ gate.negated₁
      (NatCode.encode gate.input₀ ++ NatCode.encode gate.input₁ ++ rest)
      input code wires counter output hcodeHeader hwires hcounter hremaining
      hinput houtput
  have hcounterRead := Tape.hasCounterRemainder_read_ne_start hcounterNext
  obtain ⟨wires0, hrewind0, hwires0⟩ :=
    rewindRef0_run gate.opBit gate.negated₀ gate.negated₁
      input code0 wires (counter.writeAndMove Γ.blank Dir3.right) output
      hwires hinput hcode0.read_ne_start hcounterRead houtput
  obtain ⟨code1, wires1, href0, hcode1, hwires1⟩ :=
    ref0_run gate.opBit gate.negated₀ gate.negated₁ gate.input₀
      (NatCode.encode gate.input₁ ++ rest) input code0 wires0
      (counter.writeAndMove Γ.blank Dir3.right) output
      (by simpa [List.append_assoc] using hcode0) hwires0 hinput0 hinput
      hcounterRead houtput
  obtain ⟨wires2, hrewind1, hwires2⟩ :=
    rewindRef1_run gate.opBit gate.negated₁
      (gate.negated₀.xor (wireBits[gate.input₀]'hgate.1))
      input code1 wires1 (counter.writeAndMove Γ.blank Dir3.right) output
      hwires1 hinput hcode1.read_ne_start hcounterRead houtput
  obtain ⟨code2, wires3, href1, hcode2, hwires3⟩ :=
    ref1_run gate.opBit gate.negated₁
      (gate.negated₀.xor (wireBits[gate.input₀]'hgate.1)) gate.input₁ rest
      input code1 wires2 (counter.writeAndMove Γ.blank Dir3.right) output
      hcode1 hwires2 hinput1 hinput hcounterRead houtput
  let value := evalOpBit gate.opBit
    (gate.negated₀.xor (wireBits[gate.input₀]'hgate.1))
    (gate.negated₁.xor (wireBits[gate.input₁]'hgate.2))
  obtain ⟨wires4, hseek, hwires4⟩ :=
    seekAppend_run value input code2 wires3
      (counter.writeAndMove Γ.blank Dir3.right) output hwires3 hinput
      hcode2.read_ne_start hcounterRead houtput
  have hvalue : value = gate.eval (wireBits[gate.input₀]'hgate.1)
      (wireBits[gate.input₁]'hgate.2) := by
    exact evalOpBit_opBit_eq_eval gate _ _
  refine ⟨code2, wires4, ?_, hcode2, ?_, hcounterNext⟩
  · have hrun0 := evalFamilyCoreTM.reachesIn_trans hheader hrewind0
    have hrun1 := evalFamilyCoreTM.reachesIn_trans hrun0 href0
    have hrun2 := evalFamilyCoreTM.reachesIn_trans hrun1 hrewind1
    have hrun3 := evalFamilyCoreTM.reachesIn_trans hrun2 href1
    have hrun4 := evalFamilyCoreTM.reachesIn_trans hrun3 hseek
    rw [hvalue] at hrun4
    convert hrun4 using 1
    omega
  · simpa [hvalue] using hwires4

end Internal

end Machine

end CircuitCode

end Complexity
