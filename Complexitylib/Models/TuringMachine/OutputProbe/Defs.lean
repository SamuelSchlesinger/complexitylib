/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputCursor
import Complexitylib.Models.TuringMachine.Combinators.Started
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs

/-!
# Random-access probes for append-only transducer output -- definitions

`TM.outputProbeTM` simulates a source transducer without materializing its
output. One additional work tape holds a canonical positive binary cell
position. Every right move of the simulated output head runs the verified
binary predecessor controller on that tape. Once the counter is zero, leaving
the selected logical cell captures its final written bit; halting on that cell
captures the cursor's current bit.

The machine-level correctness and resource theorems live in the internal and
surface modules. This file contains only the finite controller and transition
construction.
-/

namespace Complexity

namespace TM

/-- Which source tapes were parked on the left-end marker before a binary
countdown phase. The probe normalizes those heads to cell one, then uses this
finite mask to restore them exactly after the predecessor halts. -/
structure OutputProbeStartMask (n : ℕ) where
  /-- Whether the source input head was on the left-end marker. -/
  input : Bool
  /-- Whether each source work head was on the left-end marker. -/
  work : Fin n → Bool
  deriving DecidableEq

instance : Fintype (OutputProbeStartMask n) :=
  Fintype.ofEquiv (Bool × (Fin n → Bool))
    { toFun := fun data => ⟨data.1, data.2⟩
      invFun := fun mask => (mask.input, mask.work)
      left_inv := fun data => by cases data; rfl
      right_inv := fun mask => by cases mask; rfl }

/-- Finite control of the output-position probe. -/
inductive OutputProbeQ (n : ℕ) (State : Type) where
  /-- Simulate one source transition with a finite output cursor. -/
  | source (state : State) (cursor : OutputCursor)
  /-- Record source heads on `▷` and normalize them to cell one. -/
  | prepare (state : State) (cursor : OutputCursor)
  /-- Run binary predecessor while the source configuration is frozen. -/
  | pred (state : State) (cursor : OutputCursor)
      (mask : OutputProbeStartMask n)
      (phase : BinaryPredPhase)
  /-- Restore source heads that were normalized away from `▷`. -/
  | restore (state : State) (cursor : OutputCursor)
      (mask : OutputProbeStartMask n)
  /-- Emit a captured Boolean result on the physical output tape. -/
  | capture (bit : Bool)
  /-- The requested position did not contain a Boolean symbol. -/
  | missing
  /-- Unique normalized halt state. -/
  | done
  deriving DecidableEq

/-- The probe controller is finite whenever the source controller is finite. -/
instance [Fintype State] [DecidableEq State] :
    Fintype (OutputProbeQ n State) where
  elems :=
    (Finset.univ.image fun pair : State × OutputCursor =>
      OutputProbeQ.source pair.1 pair.2) ∪
    (Finset.univ.image fun pair : State × OutputCursor =>
      OutputProbeQ.prepare pair.1 pair.2) ∪
    (Finset.univ.image fun data :
        State × OutputCursor × OutputProbeStartMask n × BinaryPredPhase =>
      OutputProbeQ.pred data.1 data.2.1 data.2.2.1 data.2.2.2) ∪
    (Finset.univ.image fun data :
        State × OutputCursor × OutputProbeStartMask n =>
      OutputProbeQ.restore data.1 data.2.1 data.2.2) ∪
    {.capture false, .capture true, .missing, .done}
  complete := by
    intro state
    cases state <;> simp

/-- The final work tape is the probe's canonical binary countdown. -/
def outputProbeCounterIdx (n : ℕ) : Fin (n + 1) :=
  Fin.last n

/-- Canonical rewound binary countdown supplied to the probe. -/
def outputProbeCounterTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

/-- All-prefix auxiliary-space budget for one positive countdown invocation.
The source/counter configuration starts inside `initialSpace`; the three probe
seams plus binary predecessor add only the represented binary width. -/
def outputProbePositiveSpace (initialSpace value : ℕ) : ℕ :=
  binaryPredSpace initialSpace value + 3

/-- Uniform auxiliary-space budget for replay while the countdown never
exceeds `maxCounter`. -/
def outputProbeReplaySpace (sourceSpace maxCounter : ℕ) : ℕ :=
  outputProbePositiveSpace sourceSpace maxCounter

/-- All-prefix auxiliary-space budget for a successful replay followed by the
two transitions that select and emit the captured bit. -/
def outputProbeCaptureSpace (sourceSpace maxCounter : ℕ) : ℕ :=
  outputProbeReplaySpace sourceSpace maxCounter + 2

/-- Read the source machine's work heads from the prefix of the probe layout. -/
def outputProbeSourceHeads {n : ℕ} (workHeads : Fin (n + 1) → Γ) :
    Fin n → Γ :=
  fun i => workHeads (Fin.castAdd 1 i)

/-- Apply source work writes to the prefix and preserve the countdown tape. -/
def outputProbeSourceWrites {n : ℕ} (sourceWrites : Fin n → Γw)
    (workHeads : Fin (n + 1) → Γ) : Fin (n + 1) → Γw :=
  fun i =>
    if h : i.val < n then sourceWrites ⟨i.val, h⟩
    else readBackWrite (workHeads i)

/-- Apply source work directions to the prefix and park the countdown tape. -/
def outputProbeSourceDirs {n : ℕ} (sourceDirs : Fin n → Dir3)
    (workHeads : Fin (n + 1) → Γ) : Fin (n + 1) → Dir3 :=
  fun i =>
    if h : i.val < n then sourceDirs ⟨i.val, h⟩
    else idleDir (workHeads i)

/-- A source-simulation action with suppressed physical output. -/
def outputProbeSourceAction {n : ℕ} {State : Type}
    (nextState : OutputProbeQ n State) (sourceWrites : Fin n → Γw)
    (inputDir : Dir3) (sourceDirs : Fin n → Dir3)
    (workHeads : Fin (n + 1) → Γ) (outputHead : Γ) :
    OutputProbeQ n State × (Fin (n + 1) → Γw) × Γw × Dir3 ×
      (Fin (n + 1) → Dir3) × Dir3 :=
  (nextState, outputProbeSourceWrites sourceWrites workHeads,
    readBackWrite outputHead, inputDir,
    outputProbeSourceDirs sourceDirs workHeads, idleDir outputHead)

/-- Choose the result state for a symbol finalized by a right move. -/
def outputProbeCaptureWrite {n : ℕ} {State : Type} :
    Γw → OutputProbeQ n State
  | .zero => .capture false
  | .one => .capture true
  | .blank => .missing

/-- Choose the result state for the symbol under a halted source cursor. -/
def outputProbeCaptureCursor {n : ℕ} {State : Type} :
    OutputCursor → OutputProbeQ n State
  | .cell .zero => .capture false
  | .cell .one => .capture true
  | .start | .cell .blank | .cell .start => .missing

/-- Select the probe phase after one nonhalting source transition. -/
def outputProbeAfterSourceTransition {n : ℕ} {State : Type}
    (nextState : State)
    (cursor nextCursor : OutputCursor) (outputWrite : Γw)
    (outputDir : Dir3) (counterHead : Γ) : OutputProbeQ n State :=
  if outputDir = Dir3.right then
    match cursor with
    | .start => .prepare nextState nextCursor
    | .cell _ =>
        if counterHead = Γ.blank then outputProbeCaptureWrite outputWrite
        else .prepare nextState nextCursor
  else .source nextState nextCursor

/-- Record which source heads currently read the left-end marker. -/
def outputProbeStartMask {n : ℕ} (inputHead : Γ)
    (workHeads : Fin (n + 1) → Γ) : OutputProbeStartMask n where
  input := inputHead == Γ.start
  work := fun i => outputProbeSourceHeads workHeads i == Γ.start

/-- Record the source-prefix start-marker mask of concrete probe tapes. -/
def outputProbeCfgStartMask {n : ℕ} (input : Tape)
    (work : Fin (n + 1) → Tape) : OutputProbeStartMask n :=
  outputProbeStartMask input.read (fun i => (work i).read)

/-- Normalize one tape away from `▷` using the standard read-back idle
action. Off the marker this is the identity; on the marker it moves to cell
one. -/
def outputProbeNormalizeTape (tape : Tape) : Tape :=
  tape.writeAndMove (readBackWrite tape.read) (idleDir tape.read)

/-- Normalize the read-only input head away from `▷`. -/
def outputProbeNormalizeInput (input : Tape) : Tape :=
  input.move (idleDir input.read)

/-- Normalize all probe work tapes before running binary predecessor. -/
def outputProbeNormalizeWork {n : ℕ} (work : Fin (n + 1) → Tape) :
    Fin (n + 1) → Tape :=
  fun i => outputProbeNormalizeTape (work i)

/-- Wrap the next predecessor phase, entering a restoration seam as soon as
the canonical countdown has been rewound to cell one. -/
def outputProbeAfterPred {n : ℕ} {State : Type} (sourceState : State)
    (cursor : OutputCursor) (mask : OutputProbeStartMask n)
    (phase : BinaryPredPhase) : OutputProbeQ n State :=
  if phase = .done then .restore sourceState cursor mask
  else .pred sourceState cursor mask phase

/-- Restore a head recorded on `▷`, while retaining structural safety on
malformed configurations that still read `▷` during restoration. -/
def outputProbeRestoreDir (wasStart : Bool) (head : Γ) : Dir3 :=
  if head = Γ.start then .right
  else if wasStart then .left else .stay

/-- Restore source work heads and leave the countdown head parked. -/
def outputProbeRestoreWorkDirs {n : ℕ} (mask : OutputProbeStartMask n)
    (workHeads : Fin (n + 1) → Γ) : Fin (n + 1) → Dir3 :=
  fun i =>
    if h : i.val < n then
      outputProbeRestoreDir (mask.work ⟨i.val, h⟩) (workHeads i)
    else idleDir (workHeads i)

/-- Apply the restoration transition to one tape. -/
def outputProbeRestoreTape (wasStart : Bool) (tape : Tape) : Tape :=
  tape.writeAndMove (readBackWrite tape.read)
    (outputProbeRestoreDir wasStart tape.read)

/-- Apply the restoration direction to the read-only input head. -/
def outputProbeRestoreInput (wasStart : Bool) (input : Tape) : Tape :=
  input.move (outputProbeRestoreDir wasStart input.read)

/-- Restore source-prefix work heads while leaving the countdown parked. -/
def outputProbeRestoreWork {n : ℕ} (mask : OutputProbeStartMask n)
    (work : Fin (n + 1) → Tape) : Fin (n + 1) → Tape :=
  fun i =>
    if h : i.val < n then
      outputProbeRestoreTape (mask.work ⟨i.val, h⟩) (work i)
    else outputProbeNormalizeTape (work i)

private theorem outputProbeSourceAction_right_of_start
    {n : ℕ}
    {sourceOutputSafe : Prop}
    {inputDir : Dir3}
    {sourceDirs : Fin n → Dir3} {inputHead outputHead : Γ}
    {workHeads : Fin (n + 1) → Γ}
    (hsource :
      (inputHead = Γ.start → inputDir = Dir3.right) ∧
      (∀ i, outputProbeSourceHeads workHeads i = Γ.start →
        sourceDirs i = Dir3.right) ∧ sourceOutputSafe) :
    (inputHead = Γ.start → inputDir = Dir3.right) ∧
      (∀ i, workHeads i = Γ.start →
        outputProbeSourceDirs sourceDirs workHeads i = Dir3.right) ∧
      (outputHead = Γ.start →
        idleDir outputHead = Dir3.right) := by
  refine ⟨hsource.1, fun i hi => ?_, idleDir_right_of_start⟩
  unfold outputProbeSourceDirs
  split
  · next hlt =>
    apply hsource.2.1 ⟨i.val, hlt⟩
    simpa [outputProbeSourceHeads] using hi
  · exact idleDir_right_of_start hi

/-- Simulate a source transducer while probing one output cell.

The first `n` work tapes are the source tapes. Work tape `n` is a canonical
binary countdown initialized by the caller. The physical output tape is not
used by the source simulation; it receives exactly the captured result bit.
Correctness is specified for positive requested cell positions and canonical
countdown tapes. -/
def outputProbeTM (tm : TM n) : TM (n + 1) :=
  haveI : Fintype tm.Q := tm.finQ
  haveI : DecidableEq tm.Q := tm.decEq
  haveI : Fintype (OutputProbeQ n tm.Q) := inferInstance
  haveI : DecidableEq (OutputProbeQ n tm.Q) := inferInstance
  { Q := OutputProbeQ n tm.Q
    qstart := .source tm.qstart .start
    qhalt := .done
    δ := fun phase inputHead workHeads outputHead =>
      match phase with
      | .source sourceState cursor =>
          if sourceState = tm.qhalt then
            if workHeads (outputProbeCounterIdx n) = Γ.blank then
              allReadBack (outputProbeCaptureCursor cursor)
                inputHead workHeads outputHead
            else
              allReadBack OutputProbeQ.missing inputHead workHeads outputHead
          else
            let (nextState, sourceWrites, outputWrite, inputDir,
              sourceDirs, outputDir) :=
                tm.δ sourceState inputHead
                  (outputProbeSourceHeads workHeads) cursor.read
            let nextCursor := cursor.next outputWrite outputDir
            let nextPhase := outputProbeAfterSourceTransition nextState
              cursor nextCursor outputWrite outputDir
              (workHeads (outputProbeCounterIdx n))
            outputProbeSourceAction nextPhase sourceWrites inputDir
              sourceDirs workHeads outputHead
      | .prepare sourceState cursor =>
          let mask := outputProbeStartMask inputHead workHeads
          allReadBack (.pred sourceState cursor mask .borrow)
            inputHead workHeads outputHead
      | .pred sourceState cursor mask predPhase =>
          let transition :=
            (binaryPredTM (outputProbeCounterIdx n)).δ predPhase inputHead
              workHeads outputHead
          (outputProbeAfterPred sourceState cursor mask transition.1,
            transition.2.1, transition.2.2.1, transition.2.2.2.1,
            transition.2.2.2.2.1, transition.2.2.2.2.2)
      | .restore sourceState cursor mask =>
          (.source sourceState cursor,
            fun i => readBackWrite (workHeads i),
            readBackWrite outputHead,
            outputProbeRestoreDir mask.input inputHead,
            outputProbeRestoreWorkDirs mask workHeads,
            idleDir outputHead)
      | .capture bit =>
          if outputHead = Γ.start then
            allReadBack (.capture bit) inputHead workHeads outputHead
          else
            (.done, fun i => readBackWrite (workHeads i),
              if bit then .one else .zero, idleDir inputHead,
              fun i => idleDir (workHeads i), .right)
      | .missing =>
          if outputHead = Γ.start then
            allReadBack .missing inputHead workHeads outputHead
          else
            (.done, fun i => readBackWrite (workHeads i), .zero,
              idleDir inputHead, fun i => idleDir (workHeads i), .right)
      | .done =>
          allIdle .done inputHead workHeads outputHead
    δ_right_of_start := by
      intro phase inputHead workHeads outputHead
      match phase with
      | .source sourceState cursor =>
          dsimp only
          split
          · split
            · exact rightOfStart_allReadBack inputHead workHeads outputHead
            · exact rightOfStart_allReadBack inputHead workHeads outputHead
          · generalize htransition :
                tm.δ sourceState inputHead
                  (outputProbeSourceHeads workHeads) cursor.read = transition
            obtain ⟨nextState, sourceWrites, outputWrite, inputDir,
              sourceDirs, outputDir⟩ := transition
            have hsource := tm.δ_right_of_start sourceState inputHead
              (outputProbeSourceHeads workHeads) cursor.read
            rw [htransition] at hsource
            simp only [htransition]
            change
              (inputHead = Γ.start → inputDir = Dir3.right) ∧
                (∀ i, workHeads i = Γ.start →
                  outputProbeSourceDirs sourceDirs workHeads i =
                    Dir3.right) ∧
                (outputHead = Γ.start →
                  idleDir outputHead = Dir3.right)
            exact outputProbeSourceAction_right_of_start hsource
      | .prepare sourceState cursor =>
          exact rightOfStart_allReadBack inputHead workHeads outputHead
      | .pred sourceState cursor mask predPhase =>
          dsimp only
          generalize htransition :
            (binaryPredTM (outputProbeCounterIdx n)).δ predPhase inputHead
              workHeads outputHead = transition
          obtain ⟨nextPhase, workWrites, outputWrite, inputDir,
            workDirs, outputDir⟩ := transition
          have hpred :=
            (binaryPredTM (outputProbeCounterIdx n)).δ_right_of_start
              predPhase inputHead workHeads outputHead
          rw [htransition] at hpred
          exact hpred
      | .restore sourceState cursor mask =>
          refine ⟨?_, ?_, idleDir_right_of_start⟩
          · intro hinput
            simp [outputProbeRestoreDir, hinput]
          · intro i hi
            unfold outputProbeRestoreWorkDirs
            split
            · simp [outputProbeRestoreDir, hi]
            · exact idleDir_right_of_start hi
      | .capture bit =>
          dsimp only
          split
          · exact rightOfStart_allReadBack inputHead workHeads outputHead
          · next houtput =>
            exact ⟨idleDir_right_of_start, fun i hi =>
              idleDir_right_of_start hi, fun _ => rfl⟩
      | .missing =>
          dsimp only
          split
          · exact rightOfStart_allReadBack inputHead workHeads outputHead
          · next houtput =>
            exact ⟨idleDir_right_of_start, fun i hi =>
              idleDir_right_of_start hi, fun _ => rfl⟩
      | .done =>
          exact rightOfStart_allIdle inputHead workHeads outputHead }

/-- The output probe resumed after its compulsory first source/sentinel
transition. This form can be invoked repeatedly from parked tape frames. -/
abbrev outputProbeStartedTM (tm : TM n) : TM (n + 1) :=
  (outputProbeTM tm).startedTM

/-- Canonical restartable probe entry: source input and scratch tapes are
parked at cell one, the caller supplies a parked binary countdown, and the
physical one-bit output is blank and parked. -/
def outputProbeStartedCfg (tm : TM n) (input : List Bool)
    (counter : Tape) : Cfg (n + 1) (outputProbeStartedTM tm).Q where
  state := (outputProbeStartedTM tm).qstart
  input := (Tape.init (input.map Γ.ofBool)).move Dir3.right
  work := fun i =>
    if i.val < n then (Tape.init []).move Dir3.right else counter
  output := (Tape.init []).move Dir3.right

/-- Embed a source cursor configuration, a physical binary countdown, and an
independent real output tape into the source-simulation phase of the probe. -/
def outputProbeCfg (tm : TM n) (cfg : CursorCfg n tm.Q)
    (counter output : Tape) : Cfg (n + 1) (outputProbeTM tm).Q where
  state := .source cfg.state cfg.output
  input := cfg.input
  work := fun i =>
    if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter
  output := output

/-- Configuration immediately after one simulated source step, before any
requested predecessor phase has run. -/
def outputProbeSourceResultCfg (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := outputProbeAfterSourceTransition after.state before.output
    after.output (tm.cursorOutputWrite before)
    (tm.cursorOutputDirection before) counter.read
  input := after.input
  work := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩ else counter
  output := output

/-- Configuration that records and normalizes source heads before a
predecessor phase. -/
def outputProbePrepareCfg (tm : TM n) (sourceState : tm.Q)
    (cursor : OutputCursor) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .prepare sourceState cursor
  input := input
  work := work
  output := output

/-- Canonical predecessor start obtained by normalizing every framed tape. -/
def outputProbePredStartCfg {n : ℕ} (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (binaryPredTM (outputProbeCounterIdx n)).Q where
  state := BinaryPredPhase.borrow
  input := outputProbeNormalizeInput input
  work := outputProbeNormalizeWork work
  output := outputProbeNormalizeTape output

/-- View a predecessor-machine configuration inside the probe controller. Its
halt phase is collapsed directly into the restoration seam. -/
def outputProbePredCfg (tm : TM n) (sourceState : tm.Q)
    (cursor : OutputCursor) (mask : OutputProbeStartMask n)
    (cfg : Cfg (n + 1) (binaryPredTM (outputProbeCounterIdx n)).Q) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := outputProbeAfterPred sourceState cursor mask cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output

/-- Configuration that restores the source heads recorded on the left-end
marker before returning to source simulation. -/
def outputProbeRestoreCfg (tm : TM n) (sourceState : tm.Q)
    (cursor : OutputCursor) (mask : OutputProbeStartMask n)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .restore sourceState cursor mask
  input := input
  work := work
  output := output

/-- Configuration that is ready to emit a successfully captured bit. -/
def outputProbeCaptureCfg (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .capture bit
  input := input
  work := work
  output := output

/-- Configuration reached when a requested output position is absent. -/
def outputProbeMissingCfg (tm : TM n) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .missing
  input := input
  work := work
  output := output

/-- Halted configuration after an absent-position result. -/
def outputProbeMissingDoneCfg (tm : TM n) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .done
  input := input.move (idleDir input.read)
  work := fun i =>
    (work i).writeAndMove (readBackWrite (work i).read)
      (idleDir (work i).read)
  output := output.writeAndMove Γw.zero Dir3.right

/-- Halted configuration after emitting a captured bit from an off-marker
physical output head. -/
def outputProbeDoneCfg (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape) :
    Cfg (n + 1) (outputProbeTM tm).Q where
  state := .done
  input := input.move (idleDir input.read)
  work := fun i =>
    (work i).writeAndMove (readBackWrite (work i).read)
      (idleDir (work i).read)
  output := output.writeAndMove (if bit then Γw.one else Γw.zero)
    Dir3.right

end TM

end Complexity
