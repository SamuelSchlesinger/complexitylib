/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal

/-!
# Fixed-time rewind correctness for PTM repetition

This internal module lifts the one-tape fixed-rewind theorem to the complete
`NTM.repeatAtTime` wrapper configuration. A snapshot packages the input tape,
all work-tape banks, the real output tape, and the per-tape completion flags.
Its deterministic step commutes with one wrapper `.rewind` transition.

After exactly `T + 1` rewind transitions, every active tape is parked at cell
one with its contents unchanged, the control enters `.finish`, and the inactive
tapes and real output tape are exactly preserved. Choice bits are arbitrary in
this administrative phase.

## Main definitions and results

- `NTM.RepeatRewindSnapshot` — simultaneous tape-and-flag rewind state
- `NTM.repeatRewindSnapshotStep`, `NTM.repeatRewindSnapshotIter` — pure dynamics
- `NTM.repeatAtTime_trace_one_rewind` — one wrapper step matches one snapshot step
- `NTM.repeatAtTime_trace_rewind_snapshot` — exact `T + 1` snapshot correspondence
- `NTM.repeatAtTime_trace_rewind_bound` — finish state, parked active tapes, frame
-/


@[expose] public section

namespace Complexity

namespace NTM

/-- Pure data advanced during the simultaneous fixed rewind of one repetition
bank. The control state and completed-run votes remain external constants. -/
structure RepeatRewindSnapshot (n k : ℕ) where
  /-- Shared read-only input tape. -/
  input : Tape
  /-- All physical work-tape banks. -/
  work : Fin (k * (n + 1)) → Tape
  /-- Real wrapper output tape, framed throughout rewind. -/
  output : Tape
  /-- Whether the input head has already bounced from cell zero. -/
  inputDone : Bool
  /-- Per-local-tape bounce flags for the active bank. -/
  bankDone : Fin (n + 1) → Bool

/-- A framed tape is off the start marker and satisfies its uniqueness
invariant, hence the wrapper's idle action preserves it exactly. -/
def RepeatParked (t : Tape) : Prop :=
  t.StartInvariant ∧ 1 ≤ t.head

/-- Snapshot well-formedness: input and active tapes satisfy the start-marker
invariant, while inactive tapes and real output are parked for exact framing. -/
def RepeatRewindSnapshot.WellFormed
    (j : Fin k) (S : RepeatRewindSnapshot n k) : Prop :=
  S.input.StartInvariant ∧
    (∀ i, (S.work (repeatTapeIdx j i)).StartInvariant) ∧
    (∀ i, (repeatTapeCoord i).1 ≠ j → RepeatParked (S.work i)) ∧
    RepeatParked S.output

/-- Advance every active tape and completion flag by one fixed rewind step. -/
def repeatRewindSnapshotStep (j : Fin k)
    (S : RepeatRewindSnapshot n k) : RepeatRewindSnapshot n k where
  input := (repeatFixedRewindTapeStep (S.input, S.inputDone)).1
  work := fun i =>
    let c := repeatTapeCoord i
    if _h : c.1 = j then
      (repeatFixedRewindTapeStep (S.work i, S.bankDone c.2)).1
    else S.work i
  output := S.output
  inputDone := (repeatFixedRewindTapeStep (S.input, S.inputDone)).2
  bankDone := fun i =>
    (repeatFixedRewindTapeStep (S.work (repeatTapeIdx j i), S.bankDone i)).2

/-- Iterate the simultaneous rewind snapshot dynamics. -/
def repeatRewindSnapshotIter (j : Fin k) :
    ℕ → RepeatRewindSnapshot n k → RepeatRewindSnapshot n k
  | 0, S => S
  | m + 1, S =>
      repeatRewindSnapshotIter j m (repeatRewindSnapshotStep j S)

/-- Pointwise form of `repeatRewindBankDone` on tape reads. -/
@[simp] theorem repeatRewindBankDone_apply
    (work : Fin (k * (n + 1)) → Tape) (j : Fin k)
    (done : Fin (n + 1) → Bool) :
    repeatRewindBankDone (fun i => (work i).read) j done = fun i =>
      repeatRewindDone (done i) (work (repeatTapeIdx j i)).read := rfl

/-- Embed a rewind snapshot at counter `r` into the wrapper configuration. -/
def repeatRewindCfg (tm : NTM n) (j : Fin k) (r : Fin (T + 1))
    (q : tm.Q) (votes : Fin k → Bool) (S : RepeatRewindSnapshot n k) :
    Cfg (k * (n + 1)) (RepeatQ tm k T) where
  state := .rewind j r q votes S.inputDone S.bankDone
  input := S.input
  work := S.work
  output := S.output

/-- Embed a completed rewind snapshot in the wrapper's finish state. -/
def repeatFinishCfg (tm : NTM n) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (S : RepeatRewindSnapshot n k) :
    Cfg (k * (n + 1)) (RepeatQ tm k T) where
  state := .finish j q votes
  input := S.input
  work := S.work
  output := S.output

/-- The tape component of `repeatFixedRewindTapeStep` is its guarded movement:
writing the current symbol back is cell-preserving under `StartInvariant`. -/
theorem repeatFixedRewindTapeStep_fst_eq_move (t : Tape) (done : Bool)
    (h : t.StartInvariant) :
    (repeatFixedRewindTapeStep (t, done)).1 =
      t.move (repeatSafeDir t.read (repeatRewindDir done t.read)) := by
  by_cases ht0 : t.head = 0
  · simp [repeatFixedRewindTapeStep, Tape.writeAndMove, Tape.write, ht0]
  · have hr : t.read ≠ Γ.start := h.read_ne_start (by omega)
    simp only [repeatFixedRewindTapeStep]
    rw [TM.writeAndMove_readBack t hr]

/-- One simultaneous snapshot step preserves snapshot well-formedness. -/
theorem repeatRewindSnapshotStep_wellFormed (j : Fin k)
    (S : RepeatRewindSnapshot n k) (h : S.WellFormed j) :
    (repeatRewindSnapshotStep j S).WellFormed j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [repeatRewindSnapshotStep,
      repeatFixedRewindTapeStep_fst_eq_move S.input S.inputDone h.1]
    exact h.1.move _
  · intro i
    simp only [repeatRewindSnapshotStep, repeatTapeCoord_repeatTapeIdx,
      ↓reduceDIte]
    exact Tape.StartInvariant.writeAndMove (h.2.1 i) _ _
  · intro i hi
    simp [repeatRewindSnapshotStep, hi]
    exact h.2.2.1 i hi
  · exact h.2.2.2

/-- Every finite snapshot iteration preserves well-formedness. -/
theorem repeatRewindSnapshotIter_wellFormed (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) (h : S.WellFormed j) :
    (repeatRewindSnapshotIter j m S).WellFormed j := by
  induction m generalizing S with
  | zero => exact h
  | succ m ih =>
    exact ih (repeatRewindSnapshotStep j S)
      (repeatRewindSnapshotStep_wellFormed j S h)

/-- A snapshot step commutes with any number of iterations of itself. -/
theorem repeatRewindSnapshotStep_iter (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) :
    repeatRewindSnapshotStep j (repeatRewindSnapshotIter j m S) =
      repeatRewindSnapshotIter j m (repeatRewindSnapshotStep j S) := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    simp only [repeatRewindSnapshotIter]
    exact ih (repeatRewindSnapshotStep j S)

/-- Snoc form of the snapshot iterator recursion. -/
theorem repeatRewindSnapshotIter_succ_snoc (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) :
    repeatRewindSnapshotStep j (repeatRewindSnapshotIter j m S) =
      repeatRewindSnapshotIter j (m + 1) S := by
  rw [repeatRewindSnapshotStep_iter]
  rfl

/-- The input tape and flag project to the pure one-tape rewind iterator. -/
theorem repeatRewindSnapshotIter_input (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) :
    ((repeatRewindSnapshotIter j m S).input,
        (repeatRewindSnapshotIter j m S).inputDone) =
      repeatFixedRewindTapeIter m (S.input, S.inputDone) := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    exact ih (repeatRewindSnapshotStep j S)

/-- Each active bank tape and flag project to the pure one-tape iterator. -/
theorem repeatRewindSnapshotIter_active (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) (i : Fin (n + 1)) :
    ((repeatRewindSnapshotIter j m S).work (repeatTapeIdx j i),
        (repeatRewindSnapshotIter j m S).bankDone i) =
      repeatFixedRewindTapeIter m (S.work (repeatTapeIdx j i), S.bankDone i) := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    have hstep : ((repeatRewindSnapshotStep j S).work (repeatTapeIdx j i),
        (repeatRewindSnapshotStep j S).bankDone i)
        = repeatFixedRewindTapeStep (S.work (repeatTapeIdx j i), S.bankDone i) := by
      simp [repeatRewindSnapshotStep]
    rw [repeatFixedRewindTapeIter, ← hstep]
    exact ih (repeatRewindSnapshotStep j S)

/-- Snapshot iteration preserves every inactive physical work tape exactly. -/
theorem repeatRewindSnapshotIter_inactive (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) (i : Fin (k * (n + 1)))
    (hi : (repeatTapeCoord i).1 ≠ j) :
    (repeatRewindSnapshotIter j m S).work i = S.work i := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    rw [repeatRewindSnapshotIter, ih]
    simp [repeatRewindSnapshotStep, hi]

/-- Snapshot iteration preserves the real output tape exactly. -/
@[simp] theorem repeatRewindSnapshotIter_output (j : Fin k) (m : ℕ)
    (S : RepeatRewindSnapshot n k) :
    (repeatRewindSnapshotIter j m S).output = S.output := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    rw [repeatRewindSnapshotIter, ih]
    rfl

set_option linter.unusedSimpArgs false in
/-- One wrapper rewind transition commutes with one simultaneous snapshot step.
The choice bit is arbitrary because the administrative phase ignores it. -/
theorem repeatAtTime_trace_one_rewind (tm : NTM n)
    (j : Fin k) (r : Fin (T + 1)) (q : tm.Q) (votes : Fin k → Bool)
    (S : RepeatRewindSnapshot n k) (hS : S.WellFormed j)
    (choice : Fin 1 → Bool) :
    (repeatAtTime tm k T).trace 1 choice (repeatRewindCfg tm j r q votes S) =
      if hr : r.val + 1 < T + 1 then
        repeatRewindCfg tm j ⟨r.val + 1, hr⟩ q votes
          (repeatRewindSnapshotStep j S)
      else repeatFinishCfg tm j q votes (repeatRewindSnapshotStep j S) := by
  split
  all_goals
    rename_i hr
    apply (Cfg.mk.injEq ..).mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [repeatAtTime, repeatRewindCfg,
        repeatFinishCfg, repeatGuardTransition, repeatAfterRewindState,
        repeatRewindSnapshotStep, repeatFixedRewindTapeStep,
        repeatRewindBankDone, hr]
    · simp [repeatAtTime, repeatRewindCfg,
        repeatFinishCfg, repeatGuardTransition,
        repeatRewindSnapshotStep, hr,
        repeatFixedRewindTapeStep_fst_eq_move S.input S.inputDone hS.1]
    · funext i
      by_cases hi : (repeatTapeCoord i).1 = j
      · simp [repeatAtTime, repeatRewindCfg,
          repeatFinishCfg, repeatGuardTransition,
          repeatRewindSnapshotStep, repeatRewindBankDirs,
          repeatFixedRewindTapeStep, hi, hr]
      · have hp := hS.2.2.1 i hi
        have hread : (S.work i).read ≠ Γ.start := hp.1.read_ne_start hp.2
        have hstable := TM.tape_writeAndMove_stable (S.work i) hp.2 hp.1.2
        simp [repeatAtTime, repeatRewindCfg,
          repeatFinishCfg, repeatGuardTransition,
          repeatRewindSnapshotStep, repeatRewindBankDirs, hi, hr,
          repeatSafeDir, hread, TM.idleDir, hstable]
        simpa [TM.idleDir, hread] using hstable
    · have hp := hS.2.2.2
      have hread : S.output.read ≠ Γ.start := hp.1.read_ne_start hp.2
      have hstable := TM.tape_writeAndMove_stable S.output hp.2 hp.1.2
      simp [repeatAtTime, repeatRewindCfg,
        repeatFinishCfg, repeatGuardTransition,
        repeatRewindSnapshotStep, repeatSafeDir, hread, TM.idleDir,
        hstable, hr]
      simpa [TM.idleDir, hread] using hstable

/-- Before the final rewind slot, an `m`-step wrapper trace agrees exactly with
`m` pure snapshot steps and carries rewind counter `m`. -/
theorem repeatAtTime_trace_rewind_prefix (tm : NTM n)
    (j : Fin k) (q : tm.Q) (votes : Fin k → Bool)
    (S : RepeatRewindSnapshot n k) (hS : S.WellFormed j)
    (m : ℕ) (hm : m < T + 1) (choices : Fin m → Bool) :
    (repeatAtTime tm k T).trace m choices
        (repeatRewindCfg tm j ⟨0, by omega⟩ q votes S) =
      repeatRewindCfg tm j ⟨m, hm⟩ q votes
        (repeatRewindSnapshotIter j m S) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    erw [(repeatAtTime tm k T).trace_snoc m choices]
    rw [ih (by omega) (fun i => choices i.castSucc)]
    rw [repeatAtTime_trace_one_rewind tm j ⟨m, by omega⟩ q votes
      (repeatRewindSnapshotIter j m S)
      (repeatRewindSnapshotIter_wellFormed j m S hS)
      (fun _ => choices (Fin.last m))]
    simp only [dite_eq_left hm]
    rw [repeatRewindSnapshotIter_succ_snoc]

/-- Exactly `T + 1` wrapper rewind transitions produce the finish configuration
associated with `T + 1` simultaneous snapshot steps. -/
theorem repeatAtTime_trace_rewind_snapshot (tm : NTM n)
    (j : Fin k) (q : tm.Q) (votes : Fin k → Bool)
    (S : RepeatRewindSnapshot n k) (hS : S.WellFormed j)
    (choices : Fin (T + 1) → Bool) :
    (repeatAtTime tm k T).trace (T + 1) choices
        (repeatRewindCfg tm j ⟨0, by omega⟩ q votes S) =
      repeatFinishCfg tm j q votes
        (repeatRewindSnapshotIter j (T + 1) S) := by
  erw [(repeatAtTime tm k T).trace_snoc T choices]
  rw [repeatAtTime_trace_rewind_prefix tm j q votes S hS T (by omega)
    (fun i => choices i.castSucc)]
  rw [repeatAtTime_trace_one_rewind tm j ⟨T, by omega⟩ q votes
    (repeatRewindSnapshotIter j T S)
    (repeatRewindSnapshotIter_wellFormed j T S hS)
    (fun _ => choices (Fin.last T))]
  rw [dite_eq_right (by omega : ¬(T + 1 < T + 1))]
  rw [repeatRewindSnapshotIter_succ_snoc]

/-- **Fixed rewind correctness.** Starting from rewind counter zero with all
completion flags false, `T + 1` administrative steps enter `.finish`, park the
input and every active-bank tape at cell one without changing their cells, and
preserve every inactive tape and the real output tape exactly. -/
theorem repeatAtTime_trace_rewind_bound (tm : NTM n)
    (j : Fin k) (q : tm.Q) (votes : Fin k → Bool)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C.state = .rewind j ⟨0, by omega⟩ q votes false (fun _ => false))
    (hinv : C.input.StartInvariant)
    (hactiveInv : ∀ i, (C.work (repeatTapeIdx j i)).StartInvariant)
    (hinputHead : C.input.head ≤ T)
    (hactiveHead : ∀ i, (C.work (repeatTapeIdx j i)).head ≤ T)
    (hinactive : ∀ i, (repeatTapeCoord i).1 ≠ j → RepeatParked (C.work i))
    (hout : RepeatParked C.output)
    (choices : Fin (T + 1) → Bool) :
    let C' := (repeatAtTime tm k T).trace (T + 1) choices C
    C'.state = .finish j q votes ∧
      C'.input.head = 1 ∧ C'.input.cells = C.input.cells ∧
      (∀ i, (C'.work (repeatTapeIdx j i)).head = 1 ∧
        (C'.work (repeatTapeIdx j i)).cells = (C.work (repeatTapeIdx j i)).cells) ∧
      (∀ i, (repeatTapeCoord i).1 ≠ j → C'.work i = C.work i) ∧
      C'.output = C.output := by
  let S : RepeatRewindSnapshot n k :=
    { input := C.input
      work := C.work
      output := C.output
      inputDone := false
      bankDone := fun _ => false }
  let Sf := repeatRewindSnapshotIter j (T + 1) S
  have hS : S.WellFormed j := ⟨hinv, hactiveInv, hinactive, hout⟩
  have hC : C = repeatRewindCfg tm j ⟨0, by omega⟩ q votes S := by
    apply (Cfg.mk.injEq ..).mpr
    exact ⟨hstate, rfl, rfl, rfl⟩
  have hfinal : (repeatAtTime tm k T).trace (T + 1) choices C =
      repeatFinishCfg tm j q votes Sf := by
    rw [hC]
    exact repeatAtTime_trace_rewind_snapshot tm j q votes S hS choices
  have hinputBound := repeatFixedRewindTapeIter_bound T C.input hinv hinputHead
  dsimp only at hinputBound
  have hinputProj := repeatRewindSnapshotIter_input j (T + 1) S
  change (Sf.input, Sf.inputDone) =
    repeatFixedRewindTapeIter (T + 1) (C.input, false) at hinputProj
  have hinputHead' : Sf.input.head = 1 := by
    rw [show Sf.input.head =
        (repeatFixedRewindTapeIter (T + 1) (C.input, false)).1.head from
      congrArg (fun p : Tape × Bool => p.1.head) hinputProj]
    exact hinputBound.2.1
  have hinputCells' : Sf.input.cells = C.input.cells := by
    rw [show Sf.input.cells =
        (repeatFixedRewindTapeIter (T + 1) (C.input, false)).1.cells from
      congrArg (fun p : Tape × Bool => p.1.cells) hinputProj]
    exact hinputBound.2.2
  have hactive : ∀ i, (Sf.work (repeatTapeIdx j i)).head = 1 ∧
      (Sf.work (repeatTapeIdx j i)).cells = (C.work (repeatTapeIdx j i)).cells := by
    intro i
    have hbound := repeatFixedRewindTapeIter_bound T (C.work (repeatTapeIdx j i))
      (hactiveInv i) (hactiveHead i)
    dsimp only at hbound
    have hproj := repeatRewindSnapshotIter_active j (T + 1) S i
    change (Sf.work (repeatTapeIdx j i), Sf.bankDone i) =
      repeatFixedRewindTapeIter (T + 1) (C.work (repeatTapeIdx j i), false) at hproj
    constructor
    · rw [show (Sf.work (repeatTapeIdx j i)).head =
          (repeatFixedRewindTapeIter (T + 1)
            (C.work (repeatTapeIdx j i), false)).1.head from
        congrArg (fun p : Tape × Bool => p.1.head) hproj]
      exact hbound.2.1
    · rw [show (Sf.work (repeatTapeIdx j i)).cells =
          (repeatFixedRewindTapeIter (T + 1)
            (C.work (repeatTapeIdx j i), false)).1.cells from
        congrArg (fun p : Tape × Bool => p.1.cells) hproj]
      exact hbound.2.2
  have hinactive' : ∀ i, (repeatTapeCoord i).1 ≠ j → Sf.work i = C.work i := by
    intro i hi
    simpa [Sf, S] using repeatRewindSnapshotIter_inactive j (T + 1) S i hi
  have hout' : Sf.output = C.output := by
    simp [Sf, S]
  dsimp only
  rw [hfinal]
  exact ⟨rfl, hinputHead', hinputCells', hactive, hinactive', hout'⟩

end NTM

end Complexity
