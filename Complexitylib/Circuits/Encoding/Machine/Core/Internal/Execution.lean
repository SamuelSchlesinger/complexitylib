/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Action
public import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Tape
public import Complexitylib.Models.TuringMachine.Subroutines.Counter

/-!
# Execution seams for the streaming circuit evaluator

The evaluator has three semantically named work tapes, while `Cfg` exposes work
tapes through `Fin 3`. This file packages that representation boundary once.
Later phase proofs can state exact configurations using named tape arguments and
reduce one machine step to the corresponding named `CoreAction`, without
reopening the finite-index projection plumbing.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- Work-tape family assembled from the evaluator's three named tapes. -/
def coreWork (code wires counter : Tape) : Fin workTapeCount → Tape :=
  fun i =>
    if i = codeIdx then code
    else if i = wiresIdx then wires
    else counter

/-- Symbols read from the evaluator's three named work tapes. -/
def coreHeads (code wires counter : Tape) : Fin workTapeCount → Γ :=
  fun i => (coreWork code wires counter i).read

/-- Exact evaluator configuration with named work-tape arguments. -/
def coreCfg (phase : CorePhase) (input code wires counter output : Tape) :
    Cfg workTapeCount evalFamilyCoreTM.Q :=
  { state := phase
    input := input
    work := coreWork code wires counter
    output := output }

/-- Project the code tape from a named evaluator work family. -/
@[simp] theorem coreWork_codeIdx (code wires counter : Tape) :
    coreWork code wires counter codeIdx = code := by
  simp [coreWork, codeIdx]

/-- Project the wire tape from a named evaluator work family. -/
@[simp] theorem coreWork_wiresIdx (code wires counter : Tape) :
    coreWork code wires counter wiresIdx = wires := by
  simp [coreWork, codeIdx, wiresIdx]

/-- Project the counter tape from a named evaluator work family. -/
@[simp] theorem coreWork_counterIdx (code wires counter : Tape) :
    coreWork code wires counter counterIdx = counter := by
  simp [coreWork, codeIdx, wiresIdx, counterIdx]

/-- Project the code-head symbol from the named evaluator heads. -/
@[simp] theorem coreHeads_codeIdx (code wires counter : Tape) :
    coreHeads code wires counter codeIdx = code.read := by
  simp [coreHeads]

/-- Project the wire-head symbol from the named evaluator heads. -/
@[simp] theorem coreHeads_wiresIdx (code wires counter : Tape) :
    coreHeads code wires counter wiresIdx = wires.read := by
  simp [coreHeads]

/-- Project the counter-head symbol from the named evaluator heads. -/
@[simp] theorem coreHeads_counterIdx (code wires counter : Tape) :
    coreHeads code wires counter counterIdx = counter.read := by
  simp [coreHeads]

/-- Reassembling all three named tapes recovers an arbitrary evaluator work
family. -/
theorem coreWork_eta (work : Fin workTapeCount → Tape) :
    coreWork (work codeIdx) (work wiresIdx) (work counterIdx) = work := by
  funext i
  fin_cases i <;> simp [coreWork, codeIdx, wiresIdx, counterIdx]

/-- Reassembling the named fields of a configuration recovers the original
configuration. -/
theorem coreCfg_eta (c : Cfg workTapeCount evalFamilyCoreTM.Q) :
    coreCfg c.state c.input (c.work codeIdx) (c.work wiresIdx)
      (c.work counterIdx) c.output = c := by
  exact Cfg.ext rfl rfl (coreWork_eta c.work) rfl

/-- Writing a Boolean verdict at output cell one preserves its parked head and
left-marker invariant and records the exact verdict cell. -/
theorem outputWriteBool_frame (value : Bool) (output : Tape)
    (hhead : output.head = 1) (hinvariant : output.StartInvariant) :
    (output.write (Γ.ofBool value)).head = 1 ∧
    (output.write (Γ.ofBool value)).StartInvariant ∧
    (output.write (Γ.ofBool value)).cells 1 = Γ.ofBool value := by
  refine ⟨by simpa [Tape.write_head] using hhead, ?_, ?_⟩
  · rw [← Γw.ofBool_toΓ]
    exact hinvariant.write (Γw.ofBool value)
  · simp [Tape.write, hhead]

/-- Zero-verdict specialization of `outputWriteBool_frame`, matching every
controller rejection action. -/
theorem outputWriteZero_frame (output : Tape) (hhead : output.head = 1)
    (hinvariant : output.StartInvariant) :
    (output.write Γ.zero).head = 1 ∧
    (output.write Γ.zero).StartInvariant ∧
    (output.write Γ.zero).cells 1 = Γ.zero := by
  simpa [Γ.ofBool] using outputWriteBool_frame false output hhead hinvariant

/-- A unary-prefix counter with its canonical left marker is the corresponding
binary cursor over `true` bits at its append frontier. -/
theorem binaryCursor_of_hasUnaryPrefix {counter : Tape} {count : ℕ}
    (hcounter : counter.HasUnaryPrefix count)
    (hcounter0 : counter.cells 0 = Γ.start) :
    BinaryCursor counter (List.replicate count true) count := by
  have hprefix : counter.HasBinaryPrefix (List.replicate count true) := by
    refine ⟨by simpa using hcounter.1, ?_, ?_⟩
    · intro i hi
      have hi' : i < count := by simpa using hi
      have hcell := hcounter.2.1 i hi'
      simpa [Γ.ofBool] using hcell
    · intro i hi
      exact hcounter.2.2 i (by simpa using hi)
  simpa using BinaryCursor.ofHasBinaryPrefix hprefix hcounter0

/-- A rewound binary cursor of `true` bits is the public unary-counter shape. -/
theorem hasUnaryCounter_of_binaryCursor {counter : Tape} {count : ℕ}
    (hcounter : BinaryCursor counter (List.replicate count true) 0) :
    counter.HasUnaryCounter count := by
  have hstring := hcounter.hasBinaryString
  refine ⟨hstring.1, ?_, ?_⟩
  · intro i hi
    have hcell := hstring.2.1 i (by simpa using hi)
    simpa [Γ.ofBool] using hcell
  · simpa using hstring.2.2 count (by simp)

/-- One evaluator step on a named configuration applies the four named tape
actions directly. This is the representation seam used by every phase proof. -/
theorem coreCfg_step (phase : CorePhase) (input code wires counter output : Tape)
    (hphase : phase ≠ CorePhase.done) :
    evalFamilyCoreTM.step (coreCfg phase input code wires counter output) =
      let action := coreAction phase (coreHeads code wires counter) output.read
      some (coreCfg action.next
        (input.move (TM.idleDir input.read))
        (code.writeAndMove action.code.write action.code.dir)
        (wires.writeAndMove action.wires.write action.wires.dir)
        (counter.writeAndMove action.counter.write action.counter.dir)
        (output.writeAndMove action.output.write action.output.dir)) := by
  rw [evalFamilyCoreTM_step]
  · unfold coreHeads
    dsimp only [coreCfg]
    congr 1
    refine Cfg.ext rfl rfl ?_ rfl
    funext i
    by_cases hcode : i = codeIdx
    · subst i
      simp
    by_cases hwires : i = wiresIdx
    · subst i
      simp
    have hcounter : i = counterIdx := by
      apply Fin.ext
      have hi : i.val < 3 := i.isLt
      have hne0 : i.val ≠ 0 := by
        intro h
        apply hcode
        exact Fin.ext h
      have hne1 : i.val ≠ 1 := by
        intro h
        apply hwires
        exact Fin.ext h
      change i.val = 2
      omega
    subst i
    simp
  · simp [coreCfg]
    exact hphase

/-- Any controller branch selecting `CoreAction.reject` halts in one step,
writes zero at the current output head, and preserves the named work tapes. -/
theorem coreCfg_step_reject (phase : CorePhase)
    (input code wires counter output : Tape)
    (hphase : phase ≠ CorePhase.done)
    (haction : coreAction phase (coreHeads code wires counter) output.read =
      CoreAction.reject (coreHeads code wires counter) output.read)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step (coreCfg phase input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  rw [coreCfg_step phase input code wires counter output hphase, haction]
  simp only [CoreAction.reject, coreHeads_codeIdx, coreHeads_wiresIdx,
    coreHeads_counterIdx, CoreAction.preserve, TapeAction.preserve,
    TapeAction.writeStay]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  simp [TM.idleDir, hinput, houtput, Tape.move]

/-- In the code-rewind phase, an off-marker code cursor takes one ordinary
left step while every framed tape remains unchanged. -/
theorem rewindCode_step_cursor {bits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code bits position)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .rewindCode input code wires counter output) =
      some (coreCfg .rewindCode input (code.move Dir3.left) wires counter output) := by
  rw [coreCfg_step .rewindCode input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_codeIdx, hcode.read_ne_start, ite_false,
    coreHeads_wiresIdx, coreHeads_counterIdx, TapeAction.moveLeft,
    CoreAction.preserve, TapeAction.preserve]
  rw [hcode.applyMoveLeft]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- On the left marker, the code rewind bounces to the first code bit and
hands control to the wire-rewind phase. -/
theorem rewindCode_step_marker {bits : List Bool}
    (input code wires counter output : Tape)
    (hcode : BinaryAtMarker code bits)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .rewindCode input code wires counter output) =
      some (coreCfg .rewindWires input (code.move Dir3.right)
        wires counter output) := by
  rw [coreCfg_step .rewindCode input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_codeIdx, hcode.read_start, ite_true,
    coreHeads_wiresIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight]
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.start) Dir3.right =
        code.move Dir3.right := by
    rw [← hcode.read_start]
    exact hcode.applyMoveRight
  rw [hcodeMove]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Rewinding a code cursor takes exactly `position + 2` steps and enters the
wire-rewind phase with the code head on its first bit. -/
theorem rewindCode_run {bits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code bits position)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ code',
      evalFamilyCoreTM.reachesIn (position + 2)
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .rewindWires input code' wires counter output) ∧
      BinaryCursor code' bits 0 := by
  induction position generalizing code with
  | zero =>
      have hstep₁ := rewindCode_step_cursor input code wires counter output
        hcode hinput hwires hcounter houtput
      have hmarker := hcode.toMarker
      rw [hcode.applyMoveLeft] at hmarker
      have hstep₂ := rewindCode_step_marker input (code.move Dir3.left)
        wires counter output hmarker hinput hwires hcounter houtput
      have hfirst := hmarker.returnToFirstBit
      rw [hmarker.applyMoveRight] at hfirst
      refine ⟨(code.move Dir3.left).move Dir3.right, ?_, hfirst⟩
      simpa using TM.reachesIn.step hstep₁
        (TM.reachesIn.step hstep₂ TM.reachesIn.zero)
  | succ position ih =>
      have hstep := rewindCode_step_cursor input code wires counter output
        hcode hinput hwires hcounter houtput
      have hnext := hcode.moveLeft (by omega)
      obtain ⟨code', hreach, hfirst⟩ :=
        ih (code := code.move Dir3.left) hnext
      refine ⟨code', ?_, hfirst⟩
      simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach

/-- In the wire-rewind phase, an off-marker wire cursor takes one ordinary
left step while every framed tape remains unchanged. -/
theorem rewindWires_step_cursor {bits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires bits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .rewindWires input code wires counter output) =
      some (coreCfg .rewindWires input code (wires.move Dir3.left)
        counter output) := by
  rw [coreCfg_step .rewindWires input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwires.read_ne_start, ite_false,
    coreHeads_codeIdx, coreHeads_counterIdx, TapeAction.moveLeft,
    CoreAction.preserve, TapeAction.preserve]
  rw [hwires.applyMoveLeft]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- On the left marker, the wire rewind bounces to the first wire and enters
the family-tag phase. -/
theorem rewindWires_step_marker {bits : List Bool}
    (input code wires counter output : Tape)
    (hwires : BinaryAtMarker wires bits)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .rewindWires input code wires counter output) =
      some (coreCfg .familyTag input code (wires.move Dir3.right)
        counter output) := by
  rw [coreCfg_step .rewindWires input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_wiresIdx, hwires.read_start, ite_true,
    CoreAction.moveWiresRight, coreHeads_codeIdx, coreHeads_counterIdx,
    CoreAction.preserve, TapeAction.preserve, TapeAction.moveRight]
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

/-- Rewinding a wire cursor takes exactly `position + 2` steps and enters the
family-tag phase with the wire head on its first bit. -/
theorem rewindWires_run {bits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hwires : BinaryCursor wires bits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hcounter : counter.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ wires',
      evalFamilyCoreTM.reachesIn (position + 2)
        (coreCfg .rewindWires input code wires counter output)
        (coreCfg .familyTag input code wires' counter output) ∧
      BinaryCursor wires' bits 0 := by
  induction position generalizing wires with
  | zero =>
      have hstep₁ := rewindWires_step_cursor input code wires counter output
        hwires hinput hcode hcounter houtput
      have hmarker := hwires.toMarker
      rw [hwires.applyMoveLeft] at hmarker
      have hstep₂ := rewindWires_step_marker input code
        (wires.move Dir3.left) counter output hmarker hinput hcode hcounter houtput
      have hfirst := hmarker.returnToFirstBit
      rw [hmarker.applyMoveRight] at hfirst
      refine ⟨(wires.move Dir3.left).move Dir3.right, ?_, hfirst⟩
      simpa using TM.reachesIn.step hstep₁
        (TM.reachesIn.step hstep₂ TM.reachesIn.zero)
  | succ position ih =>
      have hstep := rewindWires_step_cursor input code wires counter output
        hwires hinput hcode hcounter houtput
      have hnext := hwires.moveLeft (by omega)
      obtain ⟨wires', hreach, hfirst⟩ :=
        ih (wires := wires.move Dir3.left) hnext
      refine ⟨wires', ?_, hfirst⟩
      simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach

/-- From the two staged append frontiers, the evaluator reaches its first
family-tag read in exactly `code.length + input.length + 4` steps, retaining
both canonical tape contents. -/
theorem initialRewinds_run (codeBits inputBits : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code codeBits codeBits.length)
    (hwires : BinaryCursor wires inputBits inputBits.length)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn (codeBits.length + inputBits.length + 4)
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .familyTag input code' wires' counter output) ∧
      BinaryCursor code' codeBits 0 ∧
      BinaryCursor wires' inputBits 0 := by
  obtain ⟨code', hcodeRun, hcodeFirst⟩ :=
    rewindCode_run input code wires counter output hcode hinput
      hwires.read_ne_start hcounter houtput
  obtain ⟨wires', hwiresRun, hwiresFirst⟩ :=
    rewindWires_run input code' wires counter output hwires hinput
      hcodeFirst.read_ne_start hcounter houtput
  refine ⟨code', wires', ?_, hcodeFirst, hwiresFirst⟩
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    evalFamilyCoreTM.reachesIn_trans hcodeRun hwiresRun

/-- An empty-input family tagged with zero enters the explicit empty-answer
branch and advances past the tag. -/
theorem familyTag_step_empty (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code (false :: rest) 0)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .familyTag input code wires counter output) =
      some (coreCfg .emptyAnswer input (code.move Dir3.right)
        wires counter output) := by
  have hcodeRead : code.read = Γ.zero := by
    exact hcode.read_of_lt (by simp)
  have hwiresRead : wires.read = Γ.blank := hwires.read_frontier
  rw [coreCfg_step .familyTag input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_codeIdx, coreHeads_wiresIdx, hcodeRead,
    hwiresRead, CoreAction.moveCodeRight, coreHeads_counterIdx,
    CoreAction.preserve, TapeAction.preserve, TapeAction.moveRight]
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.zero) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact hcode.applyMoveRight
  have hwiresKeep :
      wires.writeAndMove (TM.readBackWrite Γ.blank) (TM.idleDir Γ.blank) =
        wires := by
    rw [← hwiresRead]
    exact Tape.writeAndMove_readBack_idle_of_ne_start wires
      hwires.read_ne_start
  rw [hcodeMove]
  rw [hwiresKeep]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- A nonempty input paired with a positive-family tag enters the unary gate
count phase and advances past the tag. -/
theorem familyTag_step_positive (circuitCode inputRest : List Bool)
    (input code wires counter output : Tape) (bit : Bool)
    (hcode : BinaryCursor code (true :: circuitCode) 0)
    (hwires : BinaryCursor wires (bit :: inputRest) 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .familyTag input code wires counter output) =
      some (coreCfg .count input (code.move Dir3.right)
        wires counter output) := by
  have hcodeRead : code.read = Γ.one := by
    exact hcode.read_of_lt (by simp)
  have hwiresRead : wires.read = Γ.ofBool bit := by
    exact hwires.read_of_lt (by simp)
  have hwiresKeep :
      wires.writeAndMove (TM.readBackWrite (Γ.ofBool bit))
          (TM.idleDir (Γ.ofBool bit)) = wires := by
    rw [← hwiresRead]
    exact Tape.writeAndMove_readBack_idle_of_ne_start wires
      hwires.read_ne_start
  rw [coreCfg_step .familyTag input code wires counter output (by decide)]
  cases bit <;>
    simp only [coreAction, coreHeads_codeIdx, coreHeads_wiresIdx, hcodeRead,
      hwiresRead, Γ.ofBool, CoreAction.moveCodeRight, coreHeads_counterIdx,
      CoreAction.preserve, TapeAction.preserve, TapeAction.moveRight]
  all_goals
    simp only [Γ.ofBool] at hwiresKeep
    have hcodeMove :
        code.writeAndMove (TM.readBackWrite Γ.one) Dir3.right =
          code.move Dir3.right := by
      rw [← hcodeRead]
      exact hcode.applyMoveRight
    rw [hcodeMove]
    rw [hwiresKeep]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
    simp [TM.idleDir, hinput, Tape.move]

/-- Reading one unary gate-count mark advances the code cursor and extends the
counter by one mark. -/
theorem count_step_one (rest : List Bool) (used : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (true :: rest))
    (hcounter : counter.HasUnaryPrefix used)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .count input code wires counter output) =
      some (coreCfg .count input (code.move Dir3.right) wires
        (counter.writeAndMove Γ.one Dir3.right) output) := by
  have hcodeRead : code.read = Γ.one := by
    simpa [Γ.ofBool] using hcode.read_cons
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 used le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  rw [coreCfg_step .count input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_codeIdx, hcodeRead, coreHeads_counterIdx,
    hcounterRead, coreHeads_wiresIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight, TapeAction.writeRight]
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.one) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact TM.writeAndMove_readBack code hcode.read_ne_start Dir3.right
  rw [hcodeMove]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- The zero delimiter ends unary gate-count construction and advances the
code cursor to the first serialized gate. -/
theorem count_step_zero (rest : List Bool) (used : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix (false :: rest))
    (hcounter : counter.HasUnaryPrefix used)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .count input code wires counter output) =
      some (coreCfg .rewindCounter input (code.move Dir3.right)
        wires counter output) := by
  have hcodeRead : code.read = Γ.zero := by
    simpa [Γ.ofBool] using hcode.read_cons
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 used le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  rw [coreCfg_step .count input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_codeIdx, hcodeRead,
    CoreAction.moveCodeRight,
    coreHeads_wiresIdx, coreHeads_counterIdx, hcounterRead,
    CoreAction.preserve, TapeAction.preserve, TapeAction.moveRight]
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite Γ.zero) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact TM.writeAndMove_readBack code hcode.read_ne_start Dir3.right
  have hcounterKeep :
      counter.writeAndMove (TM.readBackWrite Γ.blank)
          (TM.idleDir Γ.blank) = counter := by
    rw [← hcounterRead]
    exact Tape.writeAndMove_readBack_idle_of_ne_start counter
      (by rw [hcounterRead]; decide)
  rw [hcodeMove]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [hcounterKeep]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Scanning a terminated unary gate count takes exactly `remaining + 1`
steps. It leaves the code at the gate stream and materializes all marks on the
counter tape. -/
theorem count_run (gateCode : List Bool) (used remaining : ℕ)
    (input code wires counter output : Tape)
    (hcode : code.HasBinarySuffix
      (List.replicate remaining true ++ false :: gateCode))
    (hcounter : counter.HasUnaryPrefix used)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start) (hwires : wires.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    ∃ code' counter',
      evalFamilyCoreTM.reachesIn (remaining + 1)
        (coreCfg .count input code wires counter output)
        (coreCfg .rewindCounter input code' wires counter' output) ∧
      code'.HasBinarySuffix gateCode ∧
      counter'.HasUnaryPrefix (used + remaining) ∧
      counter'.cells 0 = Γ.start := by
  induction remaining generalizing code counter used with
  | zero =>
      have hzero : code.HasBinarySuffix (false :: gateCode) := by
        simpa using hcode
      have hstep := count_step_zero gateCode used input code wires counter
        output hzero hcounter hinput hwires houtput
      refine ⟨code.move Dir3.right, counter, ?_, hzero.move_right_cons,
        ?_, hcounter0⟩
      · simpa using TM.reachesIn.step hstep TM.reachesIn.zero
      · simpa using hcounter
  | succ remaining ih =>
      have hone : code.HasBinarySuffix
          (true :: (List.replicate remaining true ++ false :: gateCode)) := by
        simpa [List.replicate_succ] using hcode
      have hstep := count_step_one
        (List.replicate remaining true ++ false :: gateCode) used
        input code wires counter output hone hcounter hinput hwires houtput
      have hcodeNext := hone.move_right_cons
      have hcounterNext := Tape.hasUnaryPrefix_write_one hcounter
      have hcounter0Next :=
        Tape.hasUnaryPrefix_write_one_cell0 hcounter hcounter0
      obtain ⟨code', counter', hreach, hcodeFinal, hcounterFinal,
          hcounter0Final⟩ :=
        ih (code := code.move Dir3.right)
          (counter := counter.writeAndMove Γ.one Dir3.right)
          (used := used + 1) hcodeNext hcounterNext hcounter0Next
      refine ⟨code', counter', ?_, hcodeFinal, ?_, hcounter0Final⟩
      · simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hcounterFinal

/-- In the counter-rewind phase, an off-marker counter cursor takes one
ordinary left step while every framed tape remains unchanged. -/
theorem rewindCounter_step_cursor {bits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcounter : BinaryCursor counter bits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .rewindCounter input code wires counter output) =
      some (coreCfg .rewindCounter input code wires
        (counter.move Dir3.left) output) := by
  rw [coreCfg_step .rewindCounter input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_counterIdx, hcounter.read_ne_start,
    ite_false, coreHeads_codeIdx, coreHeads_wiresIdx, TapeAction.moveLeft,
    CoreAction.preserve, TapeAction.preserve]
  rw [hcounter.applyMoveLeft]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- On the left marker, the counter rewind bounces to its first mark and
enters the initial gate-check phase. -/
theorem rewindCounter_step_marker {bits : List Bool}
    (input code wires counter output : Tape)
    (hcounter : BinaryAtMarker counter bits)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .rewindCounter input code wires counter output) =
      some (coreCfg (.gateCheck false) input code wires
        (counter.move Dir3.right) output) := by
  rw [coreCfg_step .rewindCounter input code wires counter output (by decide)]
  simp only [coreAction, coreHeads_counterIdx, hcounter.read_start, ite_true,
    coreHeads_codeIdx, coreHeads_wiresIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.moveRight]
  have hcounterMove :
      counter.writeAndMove (TM.readBackWrite Γ.start) Dir3.right =
        counter.move Dir3.right := by
    rw [← hcounter.read_start]
    exact hcounter.applyMoveRight
  rw [hcounterMove]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start code hcode]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires hwires]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
  simp [TM.idleDir, hinput, Tape.move]

/-- Rewinding a counter cursor takes exactly `position + 2` steps and enters
the first gate check with the counter at position zero. -/
theorem rewindCounter_run {bits : List Bool} {position : ℕ}
    (input code wires counter output : Tape)
    (hcounter : BinaryCursor counter bits position)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ counter',
      evalFamilyCoreTM.reachesIn (position + 2)
        (coreCfg .rewindCounter input code wires counter output)
        (coreCfg (.gateCheck false) input code wires counter' output) ∧
      BinaryCursor counter' bits 0 := by
  induction position generalizing counter with
  | zero =>
      have hstep₁ := rewindCounter_step_cursor input code wires counter
        output hcounter hinput hcode hwires houtput
      have hmarker := hcounter.toMarker
      rw [hcounter.applyMoveLeft] at hmarker
      have hstep₂ := rewindCounter_step_marker input code wires
        (counter.move Dir3.left) output hmarker hinput hcode hwires houtput
      have hfirst := hmarker.returnToFirstBit
      rw [hmarker.applyMoveRight] at hfirst
      refine ⟨(counter.move Dir3.left).move Dir3.right, ?_, hfirst⟩
      simpa using TM.reachesIn.step hstep₁
        (TM.reachesIn.step hstep₂ TM.reachesIn.zero)
  | succ position ih =>
      have hstep := rewindCounter_step_cursor input code wires counter output
        hcounter hinput hcode hwires houtput
      have hnext := hcounter.moveLeft (by omega)
      obtain ⟨counter', hreach, hfirst⟩ :=
        ih (counter := counter.move Dir3.left) hnext
      refine ⟨counter', ?_, hfirst⟩
      simpa [Nat.add_assoc] using TM.reachesIn.step hstep hreach

/-- A built unary prefix rewinds in exactly `count + 2` steps to the public
counter shape expected by the gate loop. -/
theorem rewindBuiltCounter_run (count : ℕ)
    (input code wires counter output : Tape)
    (hcounter : counter.HasUnaryPrefix count)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start) (hcode : code.read ≠ Γ.start)
    (hwires : wires.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ counter',
      evalFamilyCoreTM.reachesIn (count + 2)
        (coreCfg .rewindCounter input code wires counter output)
        (coreCfg (.gateCheck false) input code wires counter' output) ∧
      counter'.HasUnaryCounter count := by
  have hcursor := binaryCursor_of_hasUnaryPrefix hcounter hcounter0
  obtain ⟨counter', hreach, hfirst⟩ :=
    rewindCounter_run input code wires counter output hcursor hinput hcode
      hwires houtput
  exact ⟨counter', hreach, hasUnaryCounter_of_binaryCursor hfirst⟩

/-- A well-formed positive-family header builds and rewinds its declared unary
gate counter in exactly `2 * count + 4` steps, stopping at the first gate
check with the code cursor at the serialized gate stream. -/
theorem positiveHeader_run (count : ℕ) (gateCode inputRest : List Bool)
    (input code wires counter output : Tape) (bit : Bool)
    (hcode : BinaryCursor code
      (true :: (NatCode.encode count ++ gateCode)) 0)
    (hwires : BinaryCursor wires (bit :: inputRest) 0)
    (hcounter : counter.HasUnaryPrefix 0)
    (hcounter0 : counter.cells 0 = Γ.start)
    (hinput : input.read ≠ Γ.start) (houtput : output.read ≠ Γ.start) :
    ∃ code' counter',
      evalFamilyCoreTM.reachesIn (2 * count + 4)
        (coreCfg .familyTag input code wires counter output)
        (coreCfg (.gateCheck false) input code' wires counter' output) ∧
      code'.HasBinarySuffix gateCode ∧
      counter'.HasUnaryCounter count := by
  have hcounterRead : counter.read = Γ.blank := by
    have hcell := hcounter.2.2 0 le_rfl
    simpa [Tape.read, hcounter.1] using hcell
  have hcounterNe : counter.read ≠ Γ.start := by
    rw [hcounterRead]
    decide
  have htag := familyTag_step_positive (NatCode.encode count ++ gateCode)
    inputRest input code wires counter output bit hcode hwires hinput
    hcounterNe houtput
  have hcodeAfterTag := hcode.hasBinarySuffix.move_right_cons
  have hcountCode : (code.move Dir3.right).HasBinarySuffix
      (List.replicate count true ++ false :: gateCode) := by
    simpa [NatCode.encode, List.append_assoc] using hcodeAfterTag
  obtain ⟨code', builtCounter, hcountRun, hcodeFinal, hcounterFinal,
      hcounter0Final⟩ :=
    count_run gateCode 0 count input (code.move Dir3.right) wires counter
      output hcountCode hcounter hcounter0 hinput hwires.read_ne_start houtput
  have hcounterFinal' : builtCounter.HasUnaryPrefix count := by
    simpa using hcounterFinal
  obtain ⟨counter', hrewind, hcounterReady⟩ :=
    rewindBuiltCounter_run count input code' wires builtCounter output
      hcounterFinal' hcounter0Final hinput hcodeFinal.read_ne_start
      hwires.read_ne_start houtput
  refine ⟨code', counter', ?_, hcodeFinal, hcounterReady⟩
  have htail := evalFamilyCoreTM.reachesIn_trans hcountRun hrewind
  convert TM.reachesIn.step htag htail using 1
  all_goals omega

/-- A positive-family tag is invalid on the empty input and rejects in one
step. -/
theorem familyTag_step_reject_positive_empty (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code (true :: rest) 0)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .familyTag input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.one := by
    exact hcode.read_of_lt (by simp)
  have hwiresRead : wires.read = Γ.blank := hwires.read_frontier
  apply coreCfg_step_reject .familyTag input code wires counter output
    (by decide)
  · simp [coreAction, hcodeRead, hwiresRead]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- An empty-family tag is invalid on a nonempty input and rejects in one
step. -/
theorem familyTag_step_reject_empty_nonempty (rest inputRest : List Bool)
    (input code wires counter output : Tape) (bit : Bool)
    (hcode : BinaryCursor code (false :: rest) 0)
    (hwires : BinaryCursor wires (bit :: inputRest) 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .familyTag input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.zero := by
    exact hcode.read_of_lt (by simp)
  have hwiresRead : wires.read = Γ.ofBool bit := by
    exact hwires.read_of_lt (by simp)
  apply coreCfg_step_reject .familyTag input code wires counter output
    (by decide)
  · cases bit <;> simp [coreAction, hcodeRead, hwiresRead, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- A missing family tag rejects in one step for either input arity. -/
theorem familyTag_step_reject_missing (inputBits : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code [] 0)
    (hwires : BinaryCursor wires inputBits 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .familyTag input code wires counter output) =
      some (coreCfg .done input code wires counter (output.write Γ.zero)) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_frontier
  apply coreCfg_step_reject .familyTag input code wires counter output
    (by decide)
  · cases inputBits with
    | nil =>
        have hwiresRead : wires.read = Γ.blank := hwires.read_frontier
        simp [coreAction, hcodeRead, hwiresRead]
    | cons bit rest =>
        have hwiresRead : wires.read = Γ.ofBool bit := by
          exact hwires.read_of_lt (by simp)
        cases bit <;> simp [coreAction, hcodeRead, hwiresRead, Γ.ofBool]
  · exact hinput
  · exact hcode.read_ne_start
  · exact hwires.read_ne_start
  · exact hcounter
  · exact houtput

/-- The empty-family answer phase consumes its Boolean answer bit, independently
of the remaining serialized suffix. -/
theorem emptyAnswer_step (answer : Bool) (rest : List Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code (false :: answer :: rest) 1)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg .emptyAnswer input code wires counter output) =
      some (coreCfg (.emptyEnd answer) input (code.move Dir3.right)
        wires counter output) := by
  have hcodeRead : code.read = Γ.ofBool answer := by
    exact hcode.read_of_lt (by simp)
  have hcodeMove :
      code.writeAndMove (TM.readBackWrite (Γ.ofBool answer)) Dir3.right =
        code.move Dir3.right := by
    rw [← hcodeRead]
    exact hcode.applyMoveRight
  rw [coreCfg_step .emptyAnswer input code wires counter output (by decide)]
  cases answer <;>
    simp only [coreAction, CoreAction.readCodeBit, coreHeads_codeIdx,
      hcodeRead, Γ.ofBool, CoreAction.moveCodeRight, coreHeads_wiresIdx,
      coreHeads_counterIdx, CoreAction.preserve, TapeAction.preserve,
      TapeAction.moveRight]
  all_goals
    simp only [Γ.ofBool] at hcodeMove
    rw [hcodeMove]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start wires
      hwires.read_ne_start]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
    rw [Tape.writeAndMove_readBack_idle_of_ne_start output houtput]
    simp [TM.idleDir, hinput, Tape.move]

/-- At the exact end of an empty-family code, the controller writes the
answer and halts. -/
theorem emptyEnd_step (answer : Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code [false, answer] 2)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.step
        (coreCfg (.emptyEnd answer) input code wires counter output) =
      some (coreCfg .done input code wires counter
        (output.write (Γ.ofBool answer))) := by
  have hcodeRead : code.read = Γ.blank := hcode.read_frontier
  rw [coreCfg_step (.emptyEnd answer) input code wires counter output
    (by cases answer <;> decide)]
  simp only [coreAction, coreHeads_codeIdx, hcodeRead, ite_true,
    CoreAction.finish,
    coreHeads_wiresIdx, coreHeads_counterIdx, CoreAction.preserve,
    TapeAction.preserve, TapeAction.writeStay, Γw.ofBool_toΓ]
  have hcodeKeep :
      code.writeAndMove (TM.readBackWrite Γ.blank) (TM.idleDir Γ.blank) =
        code := by
    rw [← hcodeRead]
    exact Tape.writeAndMove_readBack_idle_of_ne_start code
      hcode.read_ne_start
  rw [hcodeKeep]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start wires
    hwires.read_ne_start]
  rw [Tape.writeAndMove_readBack_idle_of_ne_start counter hcounter]
  simp [TM.idleDir, hinput, houtput, Tape.move]

/-- A well-formed empty-input family code runs from its tag read to a halted
configuration in exactly three steps. -/
theorem emptyFamily_run (answer : Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code [false, answer] 0)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtput : output.read ≠ Γ.start) :
    evalFamilyCoreTM.reachesIn 3
      (coreCfg .familyTag input code wires counter output)
      (coreCfg .done input ((code.move Dir3.right).move Dir3.right)
        wires counter (output.write (Γ.ofBool answer))) := by
  have hstep₁ := familyTag_step_empty [answer] input code wires counter output
    hcode hwires hinput hcounter houtput
  have hcode₁ := hcode.moveRight (by simp)
  have hstep₂ := emptyAnswer_step answer [] input (code.move Dir3.right)
    wires counter output hcode₁ hwires hinput hcounter houtput
  have hcode₂ := hcode₁.moveRight (by simp)
  have hstep₃ := emptyEnd_step answer input
    ((code.move Dir3.right).move Dir3.right) wires counter output
    hcode₂ hwires hinput hcounter houtput
  simpa using TM.reachesIn.step hstep₁
    (TM.reachesIn.step hstep₂
      (TM.reachesIn.step hstep₃ TM.reachesIn.zero))

/-- From the staging frontiers, a well-formed empty-input family code reaches
its exact halted verdict in nine steps. This is the first complete branch of
the streaming controller's machine semantics. -/
theorem emptyFamily_fromFrontiers_run (answer : Bool)
    (input code wires counter output : Tape)
    (hcode : BinaryCursor code [false, answer] 2)
    (hwires : BinaryCursor wires [] 0)
    (hinput : input.read ≠ Γ.start) (hcounter : counter.read ≠ Γ.start)
    (houtputInv : output.StartInvariant) (houtputHead : output.head = 1) :
    ∃ code' wires',
      evalFamilyCoreTM.reachesIn 9
        (coreCfg .rewindCode input code wires counter output)
        (coreCfg .done input
          ((code'.move Dir3.right).move Dir3.right) wires' counter
          (output.write (Γ.ofBool answer))) ∧
      BinaryCursor code' [false, answer] 0 ∧
      BinaryCursor wires' [] 0 ∧
      (output.write (Γ.ofBool answer)).head = 1 ∧
      (output.write (Γ.ofBool answer)).StartInvariant ∧
      (output.write (Γ.ofBool answer)).cells 1 = Γ.ofBool answer := by
  have houtput : output.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  obtain ⟨code', wires', hrewind, hcodeFirst, hwiresFirst⟩ :=
    initialRewinds_run [false, answer] [] input code wires counter output
      hcode hwires hinput hcounter houtput
  have hbranch := emptyFamily_run answer input code' wires' counter output
    hcodeFirst hwiresFirst hinput hcounter houtput
  refine ⟨code', wires', ?_, hcodeFirst, hwiresFirst, ?_, ?_, ?_⟩
  · simpa using evalFamilyCoreTM.reachesIn_trans hrewind hbranch
  · simpa [Tape.write_head] using houtputHead
  · rw [← Γw.ofBool_toΓ]
    exact houtputInv.write (Γw.ofBool answer)
  · simp [Tape.write, houtputHead]


end Internal

end Machine

end CircuitCode

end Complexity
