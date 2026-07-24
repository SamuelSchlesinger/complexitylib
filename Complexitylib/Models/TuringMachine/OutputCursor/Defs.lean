/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.SpaceTime.Internal.OutputFrontier
import Mathlib.Data.Fintype.Prod

/-!
# Finite cursors for append-only output tapes -- definitions

An append-only output computation never needs its already-written prefix to
determine the next transition. It needs only to distinguish the exceptional
left-end cell from an ordinary cell and to remember the symbol under the
current head. `TM.OutputCursor` is exactly that finite summary.
-/

namespace Complexity

namespace TM

/-- Finite observable state of an append-only output head. -/
inductive OutputCursor where
  /-- The head is on the immutable left-end marker. -/
  | start
  /-- The head is on an ordinary cell reading `symbol`. -/
  | cell (symbol : Γ)
  deriving DecidableEq, Repr

instance : Fintype OutputCursor where
  elems := {.start, .cell Γ.zero, .cell Γ.one, .cell Γ.blank,
    .cell Γ.start}
  complete := by
    intro cursor
    cases cursor with
    | start => simp
    | cell symbol => cases symbol <;> simp

namespace OutputCursor

/-- Symbol presented to a simulated transition. -/
def read : OutputCursor → Γ
  | .start => Γ.start
  | .cell symbol => symbol

/-- Update the finite cursor after one write-and-move action. The `.left`
case is deliberately assigned a dummy ordinary blank cursor: correctness is
claimed only for the non-left directions allowed by `TM.IsTransducer`. -/
def next (cursor : OutputCursor) (write : Γw) (direction : Dir3) :
    OutputCursor :=
  match cursor, direction with
  | .start, .right => .cell Γ.blank
  | .start, .stay => .start
  | .start, .left => .cell Γ.blank
  | .cell _, .right => .cell Γ.blank
  | .cell _, .stay => .cell write.toΓ
  | .cell _, .left => .cell Γ.blank

/-- Whether the logical output frontier advanced in this transition. -/
def advanced (direction : Dir3) : Bool :=
  direction == Dir3.right

/-- Numeric contribution of one output move to the append-only frontier. -/
def advanceCount : Dir3 → ℕ
  | .right => 1
  | .left | .stay => 0

/-- Observable output effect of one source transition. `finalized` is present
exactly when a right move leaves an ordinary output cell, at which point the
written symbol can no longer be changed by an append-only transducer. -/
structure Event where
  /-- Zero-or-one frontier contribution of the output direction. -/
  advance : ℕ
  /-- Symbol finalized by leaving an ordinary cell to the right. -/
  finalized : Option Γw
  deriving DecidableEq

end OutputCursor

end TM

namespace Tape

/-- Observe only the finite state relevant to future append-only output
transitions. -/
def outputCursor (tape : Tape) : TM.OutputCursor :=
  if tape.head = 0 then .start else .cell tape.read

end Tape

namespace TM

/-- A machine configuration with its append-only output tape quotiented to a
finite cursor. The input and work tapes remain concrete. -/
structure CursorCfg (n : ℕ) (Q : Type) where
  /-- Simulated finite-control state. -/
  state : Q
  /-- Simulated read-only input tape. -/
  input : Tape
  /-- Simulated work tapes. -/
  work : Fin n → Tape
  /-- Finite state of the suppressed append-only output tape. -/
  output : OutputCursor

namespace CursorCfg

/-- Quotient a concrete configuration's output tape to its finite cursor. -/
def ofCfg {n : ℕ} {State : Type} (cfg : Cfg n State) :
    CursorCfg n State where
  state := cfg.state
  input := cfg.input
  work := cfg.work
  output := cfg.output.outputCursor

end CursorCfg

/-- One pure source-machine step with the append-only output tape represented
only by a finite cursor. A right output move records a fresh blank cell; a
stay records the symbol just written. Correctness for concrete executions is
proved under `IsTransducer` and the blank-frontier invariant. -/
def cursorStep (tm : TM n) (cfg : CursorCfg n tm.Q) :
    Option (CursorCfg n tm.Q) :=
  if cfg.state = tm.qhalt then none
  else
    let (state, workWrites, outputWrite, inputDir, workDirs, outputDir) :=
      tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
        cfg.output.read
    some
      { state := state
        input := cfg.input.move inputDir
        work := fun i =>
          (cfg.work i).writeAndMove (workWrites i) (workDirs i)
        output := cfg.output.next outputWrite outputDir }

/-- Output direction selected by the source transition visible from a cursor
configuration. It is observed only when `cursorStep` succeeds. -/
def cursorOutputDirection (tm : TM n) (cfg : CursorCfg n tm.Q) : Dir3 :=
  let (_, _, _, _, _, outputDir) :=
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read
  outputDir

/-- Output symbol selected by the source transition visible from a cursor
configuration. -/
def cursorOutputWrite (tm : TM n) (cfg : CursorCfg n tm.Q) : Γw :=
  let (_, _, outputWrite, _, _, _) :=
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read
  outputWrite

/-- Complete observable output event selected at a cursor configuration. -/
def cursorOutputEvent (tm : TM n) (cfg : CursorCfg n tm.Q) :
    OutputCursor.Event :=
  let direction := tm.cursorOutputDirection cfg
  { advance := OutputCursor.advanceCount direction
    finalized :=
      if direction = Dir3.right then
        match cfg.output with
        | .start => none
        | .cell _ => some (tm.cursorOutputWrite cfg)
      else none }

/-- One cursor step paired with the number of newly crossed output cells.
For a transducer this is exactly zero or one. -/
def cursorStepObserved (tm : TM n) (cfg : CursorCfg n tm.Q) :
    Option (CursorCfg n tm.Q × OutputCursor.Event) :=
  (tm.cursorStep cfg).map fun next =>
    (next, tm.cursorOutputEvent cfg)

/-- Execute an exact number of pure cursor steps, failing if the simulated
source machine halts before the requested horizon. -/
def cursorTrace (tm : TM n) : ℕ → CursorCfg n tm.Q →
    Option (CursorCfg n tm.Q)
  | 0, cfg => some cfg
  | steps + 1, cfg => do
      let cfg ← tm.cursorStep cfg
      tm.cursorTrace steps cfg

/-- Execute an exact cursor run while counting output-frontier advances. -/
def cursorTraceObserved (tm : TM n) : ℕ → CursorCfg n tm.Q →
    Option (CursorCfg n tm.Q × ℕ)
  | 0, cfg => some (cfg, 0)
  | steps + 1, cfg => do
      let (next, event) ← tm.cursorStepObserved cfg
      let (final, later) ← tm.cursorTraceObserved steps next
      pure (final, event.advance + later)

/-- Finite-control states of the output-suppressing realization. The left
summand carries the simulated source state and output cursor; the right
summand is the unique normalized halt state. -/
abbrev SuppressOutputQ (State : Type) :=
  (State × OutputCursor) ⊕ Unit

/-- Execute a source machine while suppressing its append-only output prefix
into `OutputCursor`. Input and work-tape actions are those of the source;
the real output tape is kept idle and blank. Source-halt detection takes one
normalizing seam step to the unique target halt state. Correct simulation
requires the source to satisfy `IsTransducer`. -/
def suppressOutputTM (tm : TM n) : TM n :=
  haveI : Fintype tm.Q := tm.finQ
  haveI : DecidableEq tm.Q := tm.decEq
  haveI : Fintype (SuppressOutputQ tm.Q) := inferInstance
  haveI : DecidableEq (SuppressOutputQ tm.Q) := inferInstance
  { Q := SuppressOutputQ tm.Q
    qstart := Sum.inl (tm.qstart, .start)
    qhalt := Sum.inr ()
    δ := fun state inputHead workHeads outputHead =>
      match state with
      | Sum.inl (sourceState, cursor) =>
          if sourceState = tm.qhalt then
            allReadBack (Sum.inr ()) inputHead workHeads outputHead
          else
            let (nextState, workWrites, outputWrite, inputDir, workDirs,
              outputDir) :=
                tm.δ sourceState inputHead workHeads cursor.read
            (Sum.inl (nextState, cursor.next outputWrite outputDir),
              workWrites, readBackWrite outputHead, inputDir, workDirs,
              idleDir outputHead)
      | Sum.inr _ =>
          allIdle (Sum.inr ()) inputHead workHeads outputHead
    δ_right_of_start := by
      intro state inputHead workHeads outputHead
      match state with
      | Sum.inl (sourceState, cursor) =>
          dsimp only
          split
          · exact rightOfStart_allReadBack inputHead workHeads outputHead
          · generalize htransition :
              tm.δ sourceState inputHead workHeads cursor.read = transition
            obtain ⟨nextState, workWrites, outputWrite, inputDir,
              workDirs, outputDir⟩ := transition
            have hsource := tm.δ_right_of_start sourceState inputHead
              workHeads cursor.read
            rw [htransition] at hsource
            simp only [htransition]
            exact ⟨hsource.1, hsource.2.1, idleDir_right_of_start⟩
      | Sum.inr _ =>
          exact rightOfStart_allIdle inputHead workHeads outputHead }

/-- Embed a cursor configuration into the simulating phase of
`suppressOutputTM`, with an independently supplied real output tape. -/
def suppressOutputCfg (tm : TM n) (cfg : CursorCfg n tm.Q)
    (realOutput : Tape) : Cfg n (suppressOutputTM tm).Q where
  state := by
    change SuppressOutputQ tm.Q
    exact Sum.inl (cfg.state, cfg.output)
  input := cfg.input
  work := cfg.work
  output := realOutput

/-- Normalized halted configuration after the suppressing machine detects a
source halt. The seam uses the standard read-back/idle tape action. -/
def suppressOutputDoneCfg (tm : TM n) (cfg : CursorCfg n tm.Q)
    (realOutput : Tape) : Cfg n (suppressOutputTM tm).Q where
  state := by
    change SuppressOutputQ tm.Q
    exact Sum.inr ()
  input := cfg.input.move (idleDir cfg.input.read)
  work := fun i =>
    (cfg.work i).writeAndMove (readBackWrite (cfg.work i).read)
      (idleDir (cfg.work i).read)
  output := realOutput.writeAndMove (readBackWrite realOutput.read)
    (idleDir realOutput.read)

/-- One idle physical-output transition used by the suppressing machine. -/
def suppressOutputTapeStep (tape : Tape) : Tape :=
  tape.writeAndMove (readBackWrite tape.read) (idleDir tape.read)

/-- Physical-output evolution across a fixed number of suppressed source
steps. -/
def suppressOutputTapeTrace : ℕ → Tape → Tape
  | 0, tape => tape
  | steps + 1, tape =>
      suppressOutputTapeTrace steps (suppressOutputTapeStep tape)

end TM

end Complexity
