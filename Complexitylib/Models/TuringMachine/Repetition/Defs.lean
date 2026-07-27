/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.FiniteCounting
public import Complexitylib.Models.TuringMachine.Combinators
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Fixed-time repetition of probabilistic Turing machines

This file defines the machine underlying bounded-error amplification. For a
machine `tm : NTM n`, a repetition count `k`, and a fixed per-run time `T`,
`NTM.repeatAtTime tm k T` performs `k` sequential `T`-step runs and returns
their strict-majority verdict.

Every run gets a fresh bank of `n + 1` work tapes: `n` tapes simulate `tm`'s
work tapes and the last tape simulates its output tape. The real input tape is
rewound between runs, while the real output tape is reserved for the final
majority bit. Each run occupies exactly `2 * T + 2` transitions: `T` simulated
steps, `T + 1` fixed rewind steps, and one finish step. In particular, early
halting does not shift the random-bit slots used by later runs.

The two leading transitions park every tape at cell one and then position the
first simulated configuration at cell zero. Thus the complete fixed schedule
has length `2 + k * (2 * T + 2)`, and simulated choice `(j, t)` is consumed at
global position `2 + j * (2 * T + 2) + t`.

The degenerate cases are intentional: zero repetitions output `0`, and a
zero-step run votes according to the initial configuration of `tm`.

## Main definitions

- `NTM.RepeatQ` — finite control states for fixed-time repetition
- `NTM.repeatTapeIdx`, `NTM.repeatWorkIdx`, `NTM.repeatOutputIdx` — fresh-bank layout
- `NTM.repeatAtTimeStride`, `NTM.repeatAtTimeSteps`, `NTM.repeatChoiceIdx` — schedule
- `NTM.repeatAcceptEvent` — the source machine's single-run accepting event
- `NTM.repeatAtTime` — the repeated majority-vote machine
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n : ℕ}

/-! ### Tape-bank layout and fixed schedule -/

/-- Index a local tape in repetition `j`'s fresh bank. The local bank has
`n + 1` tapes: the first `n` simulate work tapes and the last simulates the
output tape. -/
def repeatTapeIdx (j : Fin k) (i : Fin (n + 1)) : Fin (k * (n + 1)) :=
  finProdFinEquiv (j, i)

/-- Physical work-tape index simulating work tape `i` in repetition `j`. -/
def repeatWorkIdx (j : Fin k) (i : Fin n) : Fin (k * (n + 1)) :=
  repeatTapeIdx j i.castSucc

/-- Physical work-tape index simulating the output tape in repetition `j`. -/
def repeatOutputIdx (j : Fin k) : Fin (k * (n + 1)) :=
  repeatTapeIdx j (Fin.last n)

/-- The bank and local index represented by a physical repetition tape. -/
def repeatTapeCoord (i : Fin (k * (n + 1))) : Fin k × Fin (n + 1) :=
  finProdFinEquiv.symm i

/-- Decoding a freshly constructed bank index recovers its two coordinates. -/
@[simp] theorem repeatTapeCoord_repeatTapeIdx (j : Fin k) (i : Fin (n + 1)) :
    repeatTapeCoord (repeatTapeIdx j i) = (j, i) := by
  simp [repeatTapeCoord, repeatTapeIdx]

/-- Fresh-bank indexing is injective in the pair of coordinates. -/
theorem repeatTapeIdx_injective :
    Function.Injective (fun p : Fin k × Fin (n + 1) => repeatTapeIdx p.1 p.2) := by
  intro a b h
  simpa [repeatTapeIdx] using h

/-- Number of transitions from the beginning of one simulated run to the next. -/
def repeatAtTimeStride (T : ℕ) : ℕ := 2 * T + 2

/-- Exact number of transitions used by `repeatAtTime tm k T`. -/
def repeatAtTimeSteps (k T : ℕ) : ℕ := 2 + k * repeatAtTimeStride T

/-- Global choice position used for simulated step `t` of repetition `j`. -/
def repeatChoiceIdx (T : ℕ) (j : Fin k) (t : Fin T) :
    Fin (repeatAtTimeSteps k T) :=
  ⟨2 + j.val * repeatAtTimeStride T + t.val, by
    rw [repeatAtTimeSteps]
    rw [Nat.add_assoc]
    apply Nat.add_lt_add_left
    calc
      j.val * repeatAtTimeStride T + t.val <
          j.val * repeatAtTimeStride T + repeatAtTimeStride T := by
        apply Nat.add_lt_add_left
        simp only [repeatAtTimeStride]
        omega
      _ = (j.val + 1) * repeatAtTimeStride T := by rw [Nat.add_mul, one_mul]
      _ ≤ k * repeatAtTimeStride T :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr j.isLt)⟩

/-- The single-run accepting event on `T` source-machine choices. -/
def repeatAcceptEvent (tm : NTM n) (x : List Bool) (T : ℕ) :
    Finset (Fin T → Bool) :=
  Finset.univ.filter fun choices =>
    let c := tm.trace T choices (tm.initCfg x)
    c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one

/-! ### Control state and transition helpers -/

/-- Finite control for `repeatAtTime`. `votes` records completed-run verdicts.
During `rewind`, the Boolean flags say which heads have already bounced off
cell zero and are parked at cell one. -/
inductive RepeatQ (tm : NTM n) (k T : ℕ) where
  | setup
  | begin
  | run (j : Fin k) (t : Fin T) (q : tm.Q) (votes : Fin k → Bool)
  | rewind (j : Fin k) (r : Fin (T + 1)) (q : tm.Q) (votes : Fin k → Bool)
      (inputDone : Bool) (bankDone : Fin (n + 1) → Bool)
  | finish (j : Fin k) (q : tm.Q) (votes : Fin k → Bool)
  | halt
  deriving DecidableEq

/-- The repetition control is finite because every phase datum is finite. -/
instance instFintypeRepeatQ (tm : NTM n) (k T : ℕ) : Fintype (RepeatQ tm k T) where
  elems :=
    {RepeatQ.setup, .begin, .halt} ∪
    (Finset.univ.image fun x : Fin k × Fin T × tm.Q × (Fin k → Bool) =>
      RepeatQ.run x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
    (Finset.univ.image fun x : Fin k × Fin (T + 1) × tm.Q × (Fin k → Bool) ×
        Bool × (Fin (n + 1) → Bool) =>
      RepeatQ.rewind x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) ∪
    (Finset.univ.image fun x : Fin k × tm.Q × (Fin k → Bool) =>
      RepeatQ.finish x.1 x.2.1 x.2.2)
  complete := by
    intro q
    cases q <;> simp

/-- Advance the fixed simulation counter after one source-machine transition,
entering the rewind phase after the last of the `T` simulation slots. -/
def repeatAfterRunState (tm : NTM n) (j : Fin k) (t : Fin T)
    (q : tm.Q) (votes : Fin k → Bool) : RepeatQ tm k T :=
  if ht : t.val + 1 < T then .run j ⟨t.val + 1, ht⟩ q votes
  else .rewind j ⟨0, by omega⟩ q votes false (fun _ => false)

/-- Advance the fixed rewind counter using the completion flags computed by
the current rewind transition, entering `finish` after the last rewind slot. -/
def repeatAfterRewindState (tm : NTM n) (j : Fin k) (r : Fin (T + 1))
    (q : tm.Q) (votes : Fin k → Bool) (inputDone : Bool)
    (bankDone : Fin (n + 1) → Bool) : RepeatQ tm k T :=
  if hr : r.val + 1 < T + 1 then
    .rewind j ⟨r.val + 1, hr⟩ q votes inputDone bankDone
  else .finish j q votes

/-- Update a rewind-completion flag after observing a tape head. -/
def repeatRewindDone (done : Bool) (head : Γ) : Bool :=
  done || decide (head = Γ.start)

/-- Rewind an unfinished tape toward cell zero, bounce to cell one on `▷`, and
park a finished tape. The `▷` case always moves right, including on malformed
control states, so the machine satisfies `δ_right_of_start` globally. -/
def repeatRewindDir (done : Bool) (head : Γ) : Dir3 :=
  if head = Γ.start then .right else if done then .stay else .left

/-- Guard an arbitrary proposed direction with the machine model's mandatory
rightward move on the left-end marker. -/
def repeatSafeDir (head : Γ) (dir : Dir3) : Dir3 :=
  if head = Γ.start then .right else dir

/-- Apply `repeatSafeDir` to every direction in a transition result. -/
def repeatGuardTransition {Q : Type} {m : ℕ}
    (iHead : Γ) (wHeads : Fin m → Γ) (oHead : Γ)
    (r : Q × (Fin m → Γw) × Γw × Dir3 × (Fin m → Dir3) × Dir3) :
    Q × (Fin m → Γw) × Γw × Dir3 × (Fin m → Dir3) × Dir3 :=
  let (q, workWrites, outputWrite, inputDir, workDirs, outputDir) := r
  (q, workWrites, outputWrite, repeatSafeDir iHead inputDir,
    fun i => repeatSafeDir (wHeads i) (workDirs i), repeatSafeDir oHead outputDir)

/-- Guarded transitions satisfy the left-end direction condition independently
of the unguarded transition. -/
theorem repeatGuardTransition_right_of_start {Q : Type} {m : ℕ}
    (iHead : Γ) (wHeads : Fin m → Γ) (oHead : Γ)
    (r : Q × (Fin m → Γw) × Γw × Dir3 × (Fin m → Dir3) × Dir3) :
    let (_, _, _, inputDir, workDirs, outputDir) :=
      repeatGuardTransition iHead wHeads oHead r
    (iHead = Γ.start → inputDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outputDir = Dir3.right) := by
  rcases r with ⟨q, workWrites, outputWrite, inputDir, workDirs, outputDir⟩
  simp only [repeatGuardTransition]
  refine ⟨?_, fun i => ?_, ?_⟩
  · intro h
    simp [repeatSafeDir, h]
  · intro h
    simp [repeatSafeDir, h]
  · intro h
    simp [repeatSafeDir, h]

/-- Read the simulated work heads in repetition `j`'s bank. -/
def repeatWorkReads (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k) (i : Fin n) : Γ :=
  wHeads (repeatWorkIdx j i)

/-- Apply an action to every tape in bank `j`, preserving every other bank. -/
def repeatBankWrites (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (workWrites : Fin n → Γw) (outputWrite : Γw) : Fin (k * (n + 1)) → Γw :=
  fun i =>
    let c := repeatTapeCoord i
    if c.1 = j then
      if h : c.2.val < n then workWrites ⟨c.2.val, h⟩ else outputWrite
    else TM.readBackWrite (wHeads i)

/-- Apply directions to every tape in bank `j`, idling every other bank. -/
def repeatBankDirs (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (workDirs : Fin n → Dir3) (outputDir : Dir3) : Fin (k * (n + 1)) → Dir3 :=
  fun i =>
    let c := repeatTapeCoord i
    if c.1 = j then
      if h : c.2.val < n then workDirs ⟨c.2.val, h⟩ else outputDir
    else TM.idleDir (wHeads i)

/-- Bank writes reproduce the simulated action on an active work tape. -/
@[simp] theorem repeatBankWrites_work (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (workWrites : Fin n → Γw) (outputWrite : Γw) (i : Fin n) :
    repeatBankWrites wHeads j workWrites outputWrite (repeatWorkIdx j i) = workWrites i := by
  simp [repeatBankWrites, repeatWorkIdx, repeatTapeIdx, repeatTapeCoord]

/-- Bank writes reproduce the simulated action on the redirected output tape. -/
@[simp] theorem repeatBankWrites_output (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (workWrites : Fin n → Γw) (outputWrite : Γw) :
    repeatBankWrites wHeads j workWrites outputWrite (repeatOutputIdx j) = outputWrite := by
  simp [repeatBankWrites, repeatOutputIdx, repeatTapeIdx, repeatTapeCoord]

/-- Bank directions reproduce the simulated action on an active work tape. -/
@[simp] theorem repeatBankDirs_work (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (workDirs : Fin n → Dir3) (outputDir : Dir3) (i : Fin n) :
    repeatBankDirs wHeads j workDirs outputDir (repeatWorkIdx j i) = workDirs i := by
  simp [repeatBankDirs, repeatWorkIdx, repeatTapeIdx, repeatTapeCoord]

/-- Bank directions reproduce the simulated action on the redirected output tape. -/
@[simp] theorem repeatBankDirs_output (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (workDirs : Fin n → Dir3) (outputDir : Dir3) :
    repeatBankDirs wHeads j workDirs outputDir (repeatOutputIdx j) = outputDir := by
  simp [repeatBankDirs, repeatOutputIdx, repeatTapeIdx, repeatTapeCoord]

/-- Position every tape of bank `j` at cell zero; all other banks idle. -/
def repeatPositionBankDirs (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k) :
    Fin (k * (n + 1)) → Dir3 :=
  fun i =>
    if (repeatTapeCoord i).1 = j then TM.moveLeftDir (wHeads i)
    else TM.idleDir (wHeads i)

/-- Fixed-time rewind directions for the active bank. -/
def repeatRewindBankDirs (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (done : Fin (n + 1) → Bool) : Fin (k * (n + 1)) → Dir3 :=
  fun i =>
    let c := repeatTapeCoord i
    if _h : c.1 = j then repeatRewindDir (done c.2) (wHeads i)
    else TM.idleDir (wHeads i)

/-- Updated rewind-completion flags for the active bank. -/
def repeatRewindBankDone (wHeads : Fin (k * (n + 1)) → Γ) (j : Fin k)
    (done : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  fun i => repeatRewindDone (done i) (wHeads (repeatTapeIdx j i))

/-- Choices are ignored after the simulated machine halts, but cells are
preserved and any head on `▷` bounces right. This consumes the rest of the
run's fixed `T`-bit slot without shifting later blocks. -/
def repeatPaddingDirs (iHead : Γ) (wHeads : Fin (k * (n + 1)) → Γ)
    (oHead : Γ) : Dir3 × (Fin (k * (n + 1)) → Dir3) × Dir3 :=
  (TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)

/-! ### Repetition machine -/

/-- Repeat `tm` exactly `k` times for `T` simulated transitions per run and
write the strict-majority verdict to the real output tape.

The machine has `k * (n + 1)` work tapes, split into fresh banks. Its exact
fixed running time is `repeatAtTimeSteps k T`; only the positions specified by
`repeatChoiceIdx` affect simulated runs. -/
def repeatAtTime (tm : NTM n) (k T : ℕ) : NTM (k * (n + 1)) :=
  haveI : DecidableEq tm.Q := tm.decEq
  haveI : Fintype tm.Q := tm.finQ
  { Q := RepeatQ tm k T
    qstart := .setup
    qhalt := .halt
    δ := fun b state iHead wHeads oHead => repeatGuardTransition iHead wHeads oHead <|
      let preserveWrites := fun i => TM.readBackWrite (wHeads i)
      let preserveOutput := TM.readBackWrite oHead
      match state with
      | .setup =>
          (.begin, preserveWrites, preserveOutput, TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
      | .begin =>
          if hk : 0 < k then
            let j : Fin k := ⟨0, hk⟩
            let votes : Fin k → Bool := fun _ => false
            let next :=
              if hT : 0 < T then
                RepeatQ.run j ⟨0, hT⟩ tm.qstart votes
              else
                RepeatQ.rewind j ⟨0, by omega⟩ tm.qstart votes false (fun _ => false)
            (next, preserveWrites, preserveOutput, TM.moveLeftDir iHead,
              repeatPositionBankDirs wHeads j, TM.idleDir oHead)
          else
            (.halt, preserveWrites, .zero, TM.idleDir iHead,
              fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
      | .run j t q votes =>
          if hq : q = tm.qhalt then
            let dirs := repeatPaddingDirs iHead wHeads oHead
            (repeatAfterRunState tm j t q votes, preserveWrites, preserveOutput,
              dirs.1, dirs.2.1, dirs.2.2)
          else
            let (q', workWrites, outputWrite, inputDir, workDirs, outputDir) :=
              tm.δ b q iHead (repeatWorkReads wHeads j) (wHeads (repeatOutputIdx j))
            (repeatAfterRunState tm j t q' votes,
              repeatBankWrites wHeads j workWrites outputWrite, preserveOutput,
              inputDir, repeatBankDirs wHeads j workDirs outputDir, TM.idleDir oHead)
      | .rewind j r q votes inputDone bankDone =>
          let inputDone' := repeatRewindDone inputDone iHead
          let bankDone' := repeatRewindBankDone wHeads j bankDone
          (repeatAfterRewindState tm j r q votes inputDone' bankDone',
            preserveWrites, preserveOutput, repeatRewindDir inputDone iHead,
            repeatRewindBankDirs wHeads j bankDone, TM.idleDir oHead)
      | .finish j q votes =>
          let accepted := decide (q = tm.qhalt ∧ wHeads (repeatOutputIdx j) = Γ.one)
          let votes' := Function.update votes j accepted
          if hj : j.val + 1 < k then
            let j' : Fin k := ⟨j.val + 1, hj⟩
            let next :=
              if hT : 0 < T then
                RepeatQ.run j' ⟨0, hT⟩ tm.qstart votes'
              else
                RepeatQ.rewind j' ⟨0, by omega⟩ tm.qstart votes' false (fun _ => false)
            (next, preserveWrites, preserveOutput, TM.moveLeftDir iHead,
              repeatPositionBankDirs wHeads j', TM.idleDir oHead)
          else
            (.halt, preserveWrites, if majority votes' then .one else .zero,
              TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
      | .halt =>
          (.halt, preserveWrites, preserveOutput, TM.idleDir iHead,
            fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
    δ_right_of_start := by
      intro b state iHead wHeads oHead
      exact repeatGuardTransition_right_of_start iHead wHeads oHead _ }

end NTM

end Complexity
