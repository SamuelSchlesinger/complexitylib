/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Repetition.Internal

/-!
# Fresh-bank frame invariants for fixed-time repetition

This internal layer tracks the parts of a repetition configuration not owned by
the active trial. It proves that input contents, strictly future tape banks, and
the real output tape survive simulation and rewind steps, and that a nonfinal
finish transition initializes the next trial exactly at the source machine's
initial configuration.

## Main results

- `NTM.RepeatFrame` — invariant for input cells, future banks, and real output
- `NTM.RepeatFrame.run`, `.rewind`, `.finish` — one-step frame preservation
- `NTM.RepeatFrame.finish_next_project` — exact next-trial initialization
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- A blank tape parked at cell one. -/
def parkedBlank : Tape := (Tape.init []).move .right

/-- The source input tape parked at cell one. -/
def parkedInput (x : List Bool) : Tape :=
  (Tape.init (x.map Γ.ofBool)).move .right

/-- Frame facts not owned by the currently active trial: input contents stay
unchanged, every strictly later bank is still parked and blank, and the real
output is still parked and blank. -/
def RepeatFrame (x : List Bool) (j : Fin k)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) : Prop :=
  C.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
    (∀ (l : Fin k), j.val < l.val → ∀ i : Fin (n + 1),
      C.work (repeatTapeIdx l i) = parkedBlank) ∧
    C.output = parkedBlank

/-- The parked blank tape reads blank. -/
@[simp] theorem parkedBlank_read : parkedBlank.read = Γ.blank := rfl

/-- The parked blank tape's head is at cell one. -/
@[simp] theorem parkedBlank_head : parkedBlank.head = 1 := rfl

/-- A guarded idle write-and-move preserves the parked blank tape. -/
theorem parkedBlank_write_idle :
    parkedBlank.writeAndMove (TM.readBackWrite parkedBlank.read).toΓ
      (repeatSafeDir parkedBlank.read (TM.idleDir parkedBlank.read)) = parkedBlank := by
  rw [repeatSafeDir_eq _ _ (fun h => (by simp at h))]
  rw [TM.writeAndMove_readBack parkedBlank (by simp)]
  rfl

/-- Reduced form of guarded idle preservation for the parked blank tape. -/
@[simp] theorem parkedBlank_guardedIdle :
    parkedBlank.writeAndMove Γ.blank
      (repeatSafeDir Γ.blank (TM.idleDir Γ.blank)) = parkedBlank := by
  simpa [TM.readBackWrite, Γw.toΓ] using parkedBlank_write_idle

/-- Positioning a parked blank tape reconstructs the initial blank tape. -/
theorem parkedBlank_position :
    parkedBlank.writeAndMove (TM.readBackWrite parkedBlank.read).toΓ
      (repeatSafeDir parkedBlank.read (TM.moveLeftDir parkedBlank.read)) = Tape.init [] := by
  exact repeatPositionBlank_init

/-- Positioning a parked input with write-back reconstructs the initial input. -/
theorem parkedInput_position (x : List Bool) :
    (parkedInput x).writeAndMove (TM.readBackWrite (parkedInput x).read).toΓ
      (repeatSafeDir (parkedInput x).read (TM.moveLeftDir (parkedInput x).read)) =
        Tape.init (x.map Γ.ofBool) := by
  exact repeatPositionInput_init x

/-- Positioning the read-only parked input reconstructs the initial input. -/
theorem parkedInput_move_position (x : List Bool) :
    (parkedInput x).move
      (repeatSafeDir (parkedInput x).read (TM.moveLeftDir (parkedInput x).read)) =
        Tape.init (x.map Γ.ofBool) := by
  have hread := Tape.init_ofBool_move_right_read_ne_start x
  rw [show repeatSafeDir (parkedInput x).read (TM.moveLeftDir (parkedInput x).read) =
      .left by simp [parkedInput, repeatSafeDir, TM.moveLeftDir, hread]]
  rfl

/-- The configuration after setup satisfies the frame for every trial index. -/
theorem RepeatFrame.parked (tm : NTM n) (x : List Bool) (j : Fin k) :
    RepeatFrame (tm := tm) (T := T) x j (repeatParkedCfg tm k T x) := by
  refine ⟨rfl, ?_, rfl⟩
  intro l _ i
  rfl

/-- Every wrapper transition preserves the cells of the read-only input tape. -/
theorem trace_one_input_cells (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (choice : Fin 1 → Bool) :
    ((repeatAtTime tm k T).trace 1 choice C).input.cells = C.input.cells := by
  by_cases hhalt : C.state = RepeatQ.halt
  · simp [trace, repeatAtTime, hhalt]
  · simp [trace, repeatAtTime, hhalt, Tape.move_cells]

/-- The setup transition establishes the frame for any prospective first trial. -/
theorem trace_setup_frame (tm : NTM n) (x : List Bool) (j : Fin k)
    (choice : Fin 1 → Bool) :
    RepeatFrame (tm := tm) (T := T) x j
      ((repeatAtTime tm k T).trace 1 choice ((repeatAtTime tm k T).initCfg x)) := by
  rw [repeatAtTime_trace_setup]
  exact RepeatFrame.parked tm x j

/-- A simulation transition leaves every inactive parked bank unchanged. -/
theorem trace_run_inactive_bank (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (j l : Fin k) (t : Fin T) (q : tm.Q) (votes : Fin k → Bool)
    (choice : Fin 1 → Bool) (hstate : C.state = .run j t q votes)
    (hne : l ≠ j) (hparked : ∀ i : Fin (n + 1),
      C.work (repeatTapeIdx l i) = parkedBlank) :
    ∀ i : Fin (n + 1),
      ((repeatAtTime tm k T).trace 1 choice C).work (repeatTapeIdx l i) =
        parkedBlank := by
  intro i
  have hcoord : (repeatTapeCoord (repeatTapeIdx l i)).1 ≠ j := by
    simp only [repeatTapeCoord_repeatTapeIdx]
    exact hne
  cases C with
  | mk state input work output =>
    simp only at hstate hparked ⊢
    subst state
    by_cases hq : q = tm.qhalt
    · simp [trace, repeatAtTime, repeatGuardTransition, hq, repeatPaddingDirs,
        hparked i, TM.readBackWrite, Γw.toΓ]
    · simp [trace, repeatAtTime, repeatGuardTransition, hq, repeatBankWrites,
        repeatBankDirs, hne, hparked i, TM.readBackWrite, Γw.toΓ]

/-- A rewind transition leaves every inactive parked bank unchanged. -/
theorem trace_rewind_inactive_bank (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (j l : Fin k) (r : Fin (T + 1)) (q : tm.Q) (votes : Fin k → Bool)
    (inputDone : Bool) (bankDone : Fin (n + 1) → Bool)
    (choice : Fin 1 → Bool)
    (hstate : C.state = .rewind j r q votes inputDone bankDone)
    (hne : l ≠ j) (hparked : ∀ i : Fin (n + 1),
      C.work (repeatTapeIdx l i) = parkedBlank) :
    ∀ i : Fin (n + 1),
      ((repeatAtTime tm k T).trace 1 choice C).work (repeatTapeIdx l i) =
        parkedBlank := by
  intro i
  have hcoord : (repeatTapeCoord (repeatTapeIdx l i)).1 ≠ j := by
    simp only [repeatTapeCoord_repeatTapeIdx]
    exact hne
  cases C with
  | mk state input work output =>
    simp only at hstate hparked ⊢
    subst state
    simp [trace, repeatAtTime, repeatGuardTransition, repeatRewindBankDirs,
      hne, hparked i, TM.readBackWrite, Γw.toΓ]

/-- A nonfinal finish leaves banks after the next active bank parked. -/
theorem trace_finish_future_bank (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (j l : Fin k) (q : tm.Q) (votes : Fin k → Bool)
    (choice : Fin 1 → Bool) (hstate : C.state = .finish j q votes)
    (hj : j.val + 1 < k) (hl : j.val + 1 < l.val)
    (hparked : ∀ i : Fin (n + 1),
      C.work (repeatTapeIdx l i) = parkedBlank) :
    ∀ i : Fin (n + 1),
      ((repeatAtTime tm k T).trace 1 choice C).work (repeatTapeIdx l i) =
        parkedBlank := by
  intro i
  let j' : Fin k := ⟨j.val + 1, hj⟩
  have hcoord : (repeatTapeCoord (repeatTapeIdx l i)).1 ≠ j' := by
    simp only [repeatTapeCoord_repeatTapeIdx]
    intro h
    have : l.val = j'.val := congrArg Fin.val h
    simp only [j'] at this
    omega
  have hlne : l ≠ j' := by
    intro h
    have : l.val = j'.val := congrArg Fin.val h
    simp only [j'] at this
    omega
  have hlval : l.val ≠ j.val + 1 := by omega
  cases C with
  | mk state input work output =>
    simp only at hstate hparked ⊢
    subst state
    simp [trace, repeatAtTime, repeatGuardTransition, hj, repeatPositionBankDirs,
      Fin.ext_iff, hlval, hparked i, TM.readBackWrite, Γw.toΓ]

/-- The real output tape remains parked and blank through a run step. -/
theorem trace_run_output (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (j : Fin k) (t : Fin T) (q : tm.Q) (votes : Fin k → Bool)
    (choice : Fin 1 → Bool) (hstate : C.state = .run j t q votes)
    (hout : C.output = parkedBlank) :
    ((repeatAtTime tm k T).trace 1 choice C).output = parkedBlank := by
  cases C with
  | mk state input work output =>
    simp only at hstate hout ⊢
    subst state
    by_cases hq : q = tm.qhalt
    · simp [trace, repeatAtTime, repeatGuardTransition, hq, repeatPaddingDirs,
        hout, TM.readBackWrite, Γw.toΓ]
    · simp [trace, repeatAtTime, repeatGuardTransition, hq, hout,
        TM.readBackWrite, Γw.toΓ]

/-- The real output tape remains parked and blank through a rewind step. -/
theorem trace_rewind_output (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (j : Fin k) (r : Fin (T + 1)) (q : tm.Q) (votes : Fin k → Bool)
    (inputDone : Bool) (bankDone : Fin (n + 1) → Bool)
    (choice : Fin 1 → Bool)
    (hstate : C.state = .rewind j r q votes inputDone bankDone)
    (hout : C.output = parkedBlank) :
    ((repeatAtTime tm k T).trace 1 choice C).output = parkedBlank := by
  cases C with
  | mk state input work output =>
    simp only at hstate hout ⊢
    subst state
    simp [trace, repeatAtTime, repeatGuardTransition, hout, TM.readBackWrite,
      Γw.toΓ]

/-- A nonfinal finish transition preserves the real output tape. -/
theorem trace_finish_output (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (j : Fin k) (q : tm.Q) (votes : Fin k → Bool)
    (choice : Fin 1 → Bool) (hstate : C.state = .finish j q votes)
    (hj : j.val + 1 < k) (hout : C.output = parkedBlank) :
    ((repeatAtTime tm k T).trace 1 choice C).output = parkedBlank := by
  cases C with
  | mk state input work output =>
    simp only at hstate hout ⊢
    subst state
    simp [trace, repeatAtTime, repeatGuardTransition, hj, hout, TM.readBackWrite,
      Γw.toΓ]

/-- Run steps preserve the complete fresh-bank frame for the active trial. -/
theorem RepeatFrame.run (tm : NTM n) {x : List Bool}
    {C : Cfg (k * (n + 1)) (RepeatQ tm k T)} {j : Fin k} {t : Fin T}
    {q : tm.Q} {votes : Fin k → Bool} (hframe : RepeatFrame x j C)
    (hstate : C.state = .run j t q votes) (choice : Fin 1 → Bool) :
    RepeatFrame x j ((repeatAtTime tm k T).trace 1 choice C) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trace_one_input_cells]
    exact hframe.1
  · intro l hjl i
    apply trace_run_inactive_bank tm C j l t q votes choice hstate
    · intro h
      subst l
      omega
    · exact hframe.2.1 l hjl
  · exact trace_run_output tm C j t q votes choice hstate hframe.2.2

/-- Rewind steps preserve the complete fresh-bank frame for the active trial. -/
theorem RepeatFrame.rewind (tm : NTM n) {x : List Bool}
    {C : Cfg (k * (n + 1)) (RepeatQ tm k T)} {j : Fin k} {r : Fin (T + 1)}
    {q : tm.Q} {votes : Fin k → Bool} {inputDone : Bool}
    {bankDone : Fin (n + 1) → Bool} (hframe : RepeatFrame x j C)
    (hstate : C.state = .rewind j r q votes inputDone bankDone)
    (choice : Fin 1 → Bool) :
    RepeatFrame x j ((repeatAtTime tm k T).trace 1 choice C) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trace_one_input_cells]
    exact hframe.1
  · intro l hjl i
    apply trace_rewind_inactive_bank tm C j l r q votes inputDone bankDone choice hstate
    · intro h
      subst l
      omega
    · exact hframe.2.1 l hjl
  · exact trace_rewind_output tm C j r q votes inputDone bankDone choice hstate
      hframe.2.2

/-- A nonfinal finish advances the frame boundary to the next trial. -/
theorem RepeatFrame.finish (tm : NTM n) {x : List Bool}
    {C : Cfg (k * (n + 1)) (RepeatQ tm k T)} {j : Fin k} {q : tm.Q}
    {votes : Fin k → Bool} (hframe : RepeatFrame x j C)
    (hstate : C.state = .finish j q votes) (hj : j.val + 1 < k)
    (choice : Fin 1 → Bool) :
    let j' : Fin k := ⟨j.val + 1, hj⟩
    RepeatFrame x j' ((repeatAtTime tm k T).trace 1 choice C) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [trace_one_input_cells]
    exact hframe.1
  · intro l hjl i
    change j.val + 1 < l.val at hjl
    apply trace_finish_future_bank tm C j l q votes choice hstate hj
    · exact hjl
    · apply hframe.2.1 l
      omega
  · exact trace_finish_output tm C j q votes choice hstate hj hframe.2.2

/-- A nonfinal finish positions the input tape exactly at the source initial tape. -/
theorem trace_finish_next_input (tm : NTM n) (x : List Bool)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (choice : Fin 1 → Bool)
    (hstate : C.state = .finish j q votes) (hj : j.val + 1 < k)
    (hin : C.input = parkedInput x) :
    ((repeatAtTime tm k T).trace 1 choice C).input =
      (tm.initCfg x).input := by
  cases C with
  | mk state input work output =>
    simp only at hstate hin ⊢
    subst state
    simpa [trace, repeatAtTime, repeatGuardTransition, hj, hin] using
      parkedInput_move_position x

/-- A nonfinal finish positions every tape of the next fresh bank at its source
initial blank tape. -/
theorem trace_finish_next_bank (tm : NTM n)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (choice : Fin 1 → Bool)
    (hstate : C.state = .finish j q votes) (hj : j.val + 1 < k)
    (hbank : ∀ i : Fin (n + 1),
      C.work (repeatTapeIdx ⟨j.val + 1, hj⟩ i) = parkedBlank) :
    ∀ i : Fin (n + 1),
      ((repeatAtTime tm k T).trace 1 choice C).work
          (repeatTapeIdx ⟨j.val + 1, hj⟩ i) = Tape.init [] := by
  intro i
  cases C with
  | mk state input work output =>
    simp only at hstate hbank ⊢
    subst state
    simpa [trace, repeatAtTime, repeatGuardTransition, hj, repeatPositionBankDirs,
      hbank i] using parkedBlank_position

/-- The nonfinal finish handoff initializes the complete source projection for
the next trial. -/
theorem trace_finish_next_project (tm : NTM n) (x : List Bool)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (choice : Fin 1 → Bool)
    (hstate : C.state = .finish j q votes) (hj : j.val + 1 < k)
    (hin : C.input = parkedInput x)
    (hbank : ∀ i : Fin (n + 1),
      C.work (repeatTapeIdx ⟨j.val + 1, hj⟩ i) = parkedBlank) :
    repeatProjectCfg tm ⟨j.val + 1, hj⟩ tm.qstart
        ((repeatAtTime tm k T).trace 1 choice C) = tm.initCfg x := by
  apply (Cfg.mk.injEq ..).mpr
  refine ⟨rfl, trace_finish_next_input tm x C j q votes choice hstate hj hin, ?_, ?_⟩
  · funext i
    exact trace_finish_next_bank tm C j q votes choice hstate hj hbank i.castSucc
  · exact trace_finish_next_bank tm C j q votes choice hstate hj hbank (Fin.last n)

/-- Once rewind has parked the input, a nonfinal finish starts the next trial at
exactly the source initial configuration. -/
theorem RepeatFrame.finish_next_project (tm : NTM n) {x : List Bool}
    {C : Cfg (k * (n + 1)) (RepeatQ tm k T)} {j : Fin k} {q : tm.Q}
    {votes : Fin k → Bool} (hframe : RepeatFrame x j C)
    (hstate : C.state = .finish j q votes) (hj : j.val + 1 < k)
    (hin : C.input = parkedInput x) (choice : Fin 1 → Bool) :
    repeatProjectCfg tm ⟨j.val + 1, hj⟩ tm.qstart
        ((repeatAtTime tm k T).trace 1 choice C) = tm.initCfg x := by
  apply trace_finish_next_project tm x C j q votes choice hstate hj hin
  intro i
  apply hframe.2.1 ⟨j.val + 1, hj⟩
  change j.val < j.val + 1
  omega

end NTM

end Complexity
