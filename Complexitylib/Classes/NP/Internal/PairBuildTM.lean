/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Trace
public import Complexitylib.Encoding.Pairing
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring.RingNF

/-!
# `pairBuildTM`: construct `pair x y` on a work tape

The DTM `pairBuildTM k yIdx pIdx` assumes:
- `x` lives on the **input tape** (standard layout: head 0 on ▷, `x` in
  cells 1..|x|, blanks beyond),
- `y` lives on **work tape `yIdx`** (same layout: head 0 on ▷, `y` in
  cells 1..|y|, blanks beyond),
- **work tape `pIdx`** is the empty `Tape.init []`.

After running, work tape `pIdx` carries `pair x y` — the doubled-bits
encoding of `x` followed by the `[false, true]` separator followed by
`y` verbatim — with head positioned at cell `1`, matching the convention
used by the other `rewindWorkTM`-based subroutines.

## Phase structure

```
init        advance every ▷-reading tape past ▷ (one step)
copyX1      if input blank → writeSep1; else write bit to pIdx, advance pIdx
copyX2      write the same bit to pIdx, advance input *and* pIdx
writeSep1   write `false` to pIdx, advance pIdx
writeSep2   write `true`  to pIdx, advance pIdx
copyY       if y blank → rewindP1; else write y-bit to pIdx, advance y+pIdx
rewindP1    if pIdx reads ▷ → rewindP2; else move pIdx left
rewindP2    one extra right step, transition to done (leaves pIdx head=1)
done        halt
```

Total running time: linear in `|x| + |y|` (see `pairBuildTM_hoareTime`).

## Status

Everything in this file is fully proved (no `sorry`). The main contents:

- **Machine**: `pairBuildTM` (with `δ_right_of_start`), the phase type
  `PairBuildPhase`, and the running-time bound `pairBuildTime`.
- **Init-step variants** for phase composition:
  `pairBuild_init_step_started` (pair tape still fresh at head 0) and
  `pairBuild_init_step_all_started` (all tracked tapes already past `▷`).
- **Tape helper**: `Tape.eq_init_move_right_of_binary`, identifying a
  head-1 binary tape with a standard `Tape.init` moved right once.
- **Main correctness**: `pairBuildTM_hoareTime`, a `HoareTime` triple
  stating that from `x` on the input tape, `y` on work tape `yIdx`, and an
  empty work tape `pIdx`, the machine halts within
  `pairBuildTime |x| |y|` steps with `pair x y` on tape `pIdx`.
- **Corollaries**: `pairBuildTM_hoareTime_initTape_move_right` (the pair
  tape equals `Tape.init` of the encoding moved right once),
  `pairBuildTM_hoareTime_all_started_initTape_move_right` (same, from the
  all-started layout), its NTM lift
  `pairBuildTM_toNTM_hoareTime_all_started_initTape_move_right`, and
  `pairBuildTM_hoareTime_hasOutput` (`Tape.HasOutput` form).
- **Frame lemmas** for NTM traces: `pairBuildTM_trace_one_preserves_output`
  / `pairBuildTM_trace_preserves_output` (the output tape is untouched) and
  `pairBuildTM_trace_one_preserves_other_work` /
  `pairBuildTM_trace_preserves_other_work` (work tapes other than `yIdx`
  and `pIdx` are untouched), each assuming the tape's head is past `▷`.
-/


@[expose] public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `pairBuildTM`, one per phase of the construction:
    advance past `▷` (`init`), double each input bit onto the pair tape
    (`copyX1`/`copyX2`), write the `[false, true]` separator
    (`writeSep1`/`writeSep2`), copy the witness verbatim (`copyY`), rewind
    the pair tape to cell 1 (`rewindP1`/`rewindP2`), and halt (`done`). -/
inductive PairBuildPhase where
  | init
  | copyX1 | copyX2
  | writeSep1 | writeSep2
  | copyY
  | rewindP1 | rewindP2
  | done
  deriving DecidableEq

instance : Fintype PairBuildPhase where
  elems := {.init, .copyX1, .copyX2, .writeSep1, .writeSep2,
            .copyY, .rewindP1, .rewindP2, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- Definition
-- ════════════════════════════════════════════════════════════════════════

variable {k : ℕ}

/-- Build `pair x y` on work tape `pIdx`, reading `x` from the input tape
    and `y` from work tape `yIdx`. Requires `yIdx ≠ pIdx` for the
    construction to make sense; the definition itself is valid for any
    indices. -/
def pairBuildTM (yIdx pIdx : Fin k) : TM k where
  Q := PairBuildPhase
  qstart := .init
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    -- Step 0: advance every tape currently reading ▷ past it.
    -- Input, pIdx, yIdx, and output all start at ▷; `idleDir` sends them right.
    | .init =>
      (.copyX1,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => idleDir (wHeads i),
       idleDir oHead)
    -- copyX1: "new iteration" state. Decides continue-vs-switch based on input.
    | .copyX1 =>
      if iHead = Γ.blank then
        -- End of x: transition to separator writing.
        (.writeSep1,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        -- Write the current input bit to pIdx, advance pIdx only.
        (.copyX2,
         fun i => if i = pIdx then readBackWrite iHead
                  else readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    -- copyX2: write the *second* copy of the current bit to pIdx; advance input+pIdx.
    | .copyX2 =>
      (.copyX1,
       fun i => if i = pIdx then readBackWrite iHead
                else readBackWrite (wHeads i),
       readBackWrite oHead,
       Dir3.right,                                           -- input advances
       fun i => if i = pIdx then Dir3.right
                else idleDir (wHeads i),
       idleDir oHead)
    -- writeSep1: write the `false` (= Γw.zero) bit of the separator.
    | .writeSep1 =>
      (.writeSep2,
       fun i => if i = pIdx then Γw.zero else readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    -- writeSep2: write the `true` (= Γw.one) bit of the separator.
    | .writeSep2 =>
      (.copyY,
       fun i => if i = pIdx then Γw.one else readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    -- copyY: copy y-bits from work[yIdx] to pIdx until blank.
    | .copyY =>
      if wHeads yIdx = Γ.blank then
        (.rewindP1,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => idleDir (wHeads i),
         idleDir oHead)
      else
        (.copyY,
         fun i => if i = pIdx then readBackWrite (wHeads yIdx)
                  else readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.right
                  else if i = yIdx then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
    -- rewindP1: move pIdx left until reading ▷.
    | .rewindP1 =>
      if wHeads pIdx = Γ.start then
        (.rewindP2,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewindP1,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = pIdx then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    -- rewindP2: one more step, go to done. Leaves pIdx head at 1.
    -- (Uses readBackWrite so non-pIdx tapes are preserved even if mid-tape.)
    | .rewindP2 =>
      (.done,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => idleDir (wHeads i),
       idleDir oHead)
    -- done: halt. δ never actually fires; we just need δ_right_of_start to hold.
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .init =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; exact idleDir_right_of_start hwi
    | .copyX1 =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .copyX2 =>
      refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .writeSep1 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .writeSep2 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .copyY =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []
        split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hwi
    | .rewindP1 =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rename_i heq; subst heq; contradiction
        · exact idleDir_right_of_start hwi
    | .rewindP2 =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Phase lemmas (building blocks for the main correctness theorem)
-- ════════════════════════════════════════════════════════════════════════

/-- **init step.** From the `.init` state with input, `yIdx`, and `pIdx`
    all at head 0 on ▷, one step transitions to `.copyX1` with all three
    heads at cell 1 and cells unchanged. -/
private theorem pairBuild_init_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .init)
    (hi0 : c.input.head = 0) (hic0 : c.input.cells 0 = Γ.start)
    (hyi0 : (c.work yIdx).head = 0) (hyic0 : (c.work yIdx).cells 0 = Γ.start)
    (hpi0 : (c.work pIdx).head = 0) (hpic0 : (c.work pIdx).cells 0 = Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX1 ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (c'.work yIdx).head = 1 ∧ (c'.work yIdx).cells = (c.work yIdx).cells ∧
      (c'.work pIdx).head = 1 ∧ (c'.work pIdx).cells = (c.work pIdx).cells := by
  have hiread : c.input.read = Γ.start := by simp [Tape.read, hi0, hic0]
  have hyread : (c.work yIdx).read = Γ.start := by simp [Tape.read, hyi0, hyic0]
  have hpread : (c.work pIdx).read = Γ.start := by simp [Tape.read, hpi0, hpic0]
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- input.head = 1
    show (c.input.move (idleDir c.input.read)).head = 1
    simp [idleDir, hiread, Tape.move, hi0]
  · -- input.cells unchanged
    exact Tape.move_cells _ _
  · -- (work yIdx).head = 1
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
          (idleDir (c.work yIdx).read)).head = 1
    simp [idleDir, hyread, Tape.writeAndMove, Tape.write, Tape.move, hyi0]
  · -- (work yIdx).cells unchanged
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
          (idleDir (c.work yIdx).read)).cells = (c.work yIdx).cells
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hyi0]
  · -- (work pIdx).head = 1
    show ((c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
          (idleDir (c.work pIdx).read)).head = 1
    simp [idleDir, hpread, Tape.writeAndMove, Tape.write, Tape.move, hpi0]
  · -- (work pIdx).cells unchanged
    show ((c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
          (idleDir (c.work pIdx).read)).cells = (c.work pIdx).cells
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hpi0]

/-- Variant of the init step for phase composition: input and witness tapes
    may already be positioned at their first data cells, while the pair tape
    is still the fresh head-0 tape. -/
theorem pairBuild_init_step_started {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input.read ≠ Γ.start)
    (hy : (c.work yIdx).read ≠ Γ.start)
    (hpi0 : (c.work pIdx).head = 0) (hpic0 : (c.work pIdx).cells 0 = Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = 1 ∧
      (c'.work pIdx).cells = (c.work pIdx).cells := by
  have hpread : (c.work pIdx).read = Γ.start := by
    simp [Tape.read, hpi0, hpic0]
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show c.input.move (idleDir c.input.read) = c.input
    exact transitionInput_eq_self hinp
  · show (c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
        (idleDir (c.work yIdx).read) = c.work yIdx
    exact transitionTape_eq_self hy
  · show ((c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
        (idleDir (c.work pIdx).read)).head = 1
    simp [idleDir, hpread, Tape.writeAndMove, Tape.write, Tape.move, hpi0]
  · show ((c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
        (idleDir (c.work pIdx).read)).cells = (c.work pIdx).cells
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hpi0]

/-- Variant of the init step for fully-started phase composition: input,
    witness, and pair tapes may all already be positioned past `▷`. -/
theorem pairBuild_init_step_all_started {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input.read ≠ Γ.start)
    (hy : (c.work yIdx).read ≠ Γ.start)
    (hp : (c.work pIdx).read ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · show c.input.move (idleDir c.input.read) = c.input
    exact transitionInput_eq_self hinp
  · show (c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read)
        (idleDir (c.work yIdx).read) = c.work yIdx
    exact transitionTape_eq_self hy
  · show (c.work pIdx).writeAndMove (readBackWrite (c.work pIdx).read)
        (idleDir (c.work pIdx).read) = c.work pIdx
    exact transitionTape_eq_self hp

/-- **copyX1 halt step.** In `.copyX1` reading blank on input, transition
    to `.writeSep1`. All three tracked tapes unchanged (they're past ▷ so
    `tape_writeAndMove_stable` applies). -/
private theorem pairBuild_copyX1_halt_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyX1) (hread : c.input.read = Γ.blank)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .writeSep1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM, ite_eq_left hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · exact tape_writeAndMove_stable (c.work pIdx) hph hpns

/-- **copyX1 continue step.** In `.copyX1` reading a data bit on input,
    transition to `.copyX2`, writing that bit to `pIdx`, advancing `pIdx`.
    Input head unchanged; yIdx unchanged. -/
private theorem pairBuild_copyX1_cont_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyX1) (hread_nb : c.input.read ≠ Γ.blank)
    (hread_ns : c.input.read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (_hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX2 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head c.input.read := by
  simp only [TM.step, hst, pairBuildTM, ite_eq_right hread_nb]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    rw [toΓ_readBackWrite_of_ne_start hread_ns]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **copyX2 step.** In `.copyX2` (reading the same data bit), transition
    back to `.copyX1`, writing that bit to `pIdx` (second copy), advancing
    both input and `pIdx`. yIdx unchanged. -/
private theorem pairBuild_copyX2_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyX2)
    (hread_ns : c.input.read ≠ Γ.start)
    (_hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyX1 ∧
      c'.input.head = c.input.head + 1 ∧
      c'.input.cells = c.input.cells ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head c.input.read := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move .right).head = c.input.head + 1
    simp [Tape.move]
  · exact Tape.move_cells _ _
  · simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    rw [toΓ_readBackWrite_of_ne_start hread_ns]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **writeSep1 step.** Write `0` (the `false` bit of the separator) to
    pIdx, advancing pIdx. Input and yIdx stable. -/
private theorem pairBuild_writeSep1_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .writeSep1)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .writeSep2 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head Γ.zero := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega]

/-- **writeSep2 step.** Write `1` (the `true` bit of the separator) to
    pIdx, advancing pIdx. Transition to `.copyY`. -/
private theorem pairBuild_writeSep2_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .writeSep2)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyY ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head Γ.one := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega]

/-- **copyY halt step.** In `.copyY` with work tape `yIdx` reading blank,
    transition to `.rewindP1`. All tapes stable. -/
private theorem pairBuild_copyY_halt_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyY) (hyread : (c.work yIdx).read = Γ.blank)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .rewindP1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM, ite_eq_left hyread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · exact tape_writeAndMove_stable (c.work pIdx) hph hpns

/-- **copyY continue step.** In `.copyY` with `yIdx` reading a data bit,
    copy that bit to pIdx, advancing both yIdx and pIdx. Input stable. -/
private theorem pairBuild_copyY_cont_step {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .copyY) (hyread_nb : (c.work yIdx).read ≠ Γ.blank)
    (hyread_ns : (c.work yIdx).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (_hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .copyY ∧
      c'.input = c.input ∧
      (c'.work yIdx).head = (c.work yIdx).head + 1 ∧
      (c'.work yIdx).cells = (c.work yIdx).cells ∧
      (c'.work pIdx).head = (c.work pIdx).head + 1 ∧
      (c'.work pIdx).cells =
        Function.update (c.work pIdx).cells (c.work pIdx).head (c.work yIdx).read := by
  simp only [TM.step, hst, pairBuildTM, ite_eq_right hyread_nb]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · -- yIdx head advances (yIdx ≠ pIdx, condition picks the else branch, which is Dir3.right)
    simp only [ite_eq_right hne]
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read).toΓ Dir3.right).head
         = (c.work yIdx).head + 1
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work yIdx).head ≠ 0 from by omega]
  · -- yIdx cells unchanged (readBackWrite preserves non-▷ symbols)
    simp only [ite_eq_right hne]
    show ((c.work yIdx).writeAndMove (readBackWrite (c.work yIdx).read).toΓ Dir3.right).cells
         = (c.work yIdx).cells
    rw [toΓ_readBackWrite_of_ne_start hyread_ns]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work yIdx).head ≠ 0 from by omega, Tape.read]
  · -- pIdx head advances
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · -- pIdx cells updated with yIdx.read
    simp only [↓reduceIte]
    rw [toΓ_readBackWrite_of_ne_start hyread_ns]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **rewindP1 continue step.** pIdx reads non-▷; move pIdx left one cell;
    stay in `.rewindP1`. Input, yIdx, pIdx-cells unchanged. -/
private theorem pairBuild_rewindP1_step_cont {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .rewindP1) (hpread_ns : (c.work pIdx).read ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .rewindP1 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = (c.work pIdx).head - 1 ∧
      (c'.work pIdx).cells = (c.work pIdx).cells := by
  simp only [TM.step, hst, pairBuildTM, ite_eq_right hpread_ns]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · -- yIdx stable (yIdx ≠ pIdx picks else branch; readBackWrite + idle)
    simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · -- pIdx head = head - 1
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move,
          show (c.work pIdx).head ≠ 0 from by omega]
  · -- pIdx cells unchanged (readBackWrite preserves at non-start read)
    simp only [↓reduceIte]
    rw [toΓ_readBackWrite_of_ne_start hpread_ns]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write,
          show (c.work pIdx).head ≠ 0 from by omega, Tape.read]

/-- **rewindP1 base step.** pIdx reads ▷ (head=0); transition to
    `.rewindP2` with pIdx advancing to head=1. All other tapes stable. -/
private theorem pairBuild_rewindP1_step_base {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .rewindP1) (hpread : (c.work pIdx).read = Γ.start)
    (hph0 : (c.work pIdx).head = 0)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .rewindP2 ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      (c'.work pIdx).head = 1 ∧
      (c'.work pIdx).cells = (c.work pIdx).cells := by
  simp only [TM.step, hst, pairBuildTM, ite_eq_left hpread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · -- yIdx stable (yIdx ≠ pIdx picks else branch)
    simp only [ite_eq_right hne]
    exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · -- pIdx head = 1
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.write, Tape.move, hph0]
  · -- pIdx cells unchanged (write at head=0 is no-op)
    simp only [↓reduceIte]
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hph0]

/-- **rewindP2 step.** Transition to `.done`; all tapes stable
    (head ≥ 1 and cells ≥ 1 ≠ start). -/
private theorem pairBuild_rewindP2_step {k : ℕ} (yIdx pIdx : Fin k)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hst : c.state = .rewindP2)
    (hih : c.input.head ≥ 1) (hyh : (c.work yIdx).head ≥ 1)
    (hph : (c.work pIdx).head ≥ 1)
    (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hyns : ∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start)
    (hpns : ∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) :
    ∃ c', (pairBuildTM yIdx pIdx).step c = some c' ∧
      c'.state = .done ∧
      c'.input = c.input ∧
      c'.work yIdx = c.work yIdx ∧
      c'.work pIdx = c.work pIdx := by
  simp only [TM.step, hst, pairBuildTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · exact tape_move_idleDir_stable c.input hih hins
  · exact tape_writeAndMove_stable (c.work yIdx) hyh hyns
  · exact tape_writeAndMove_stable (c.work pIdx) hph hpns

/-- **rewindP1 loop.** From `.rewindP1` with pIdx at head=`p`, in `p+1`
    steps reach `.rewindP2` with pIdx at head=1 and all pIdx/input/yIdx
    cells preserved. -/
private theorem pairBuild_rewindP1_loop {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx) :
    ∀ (p : ℕ) (c : Cfg k (pairBuildTM yIdx pIdx).Q),
      c.state = .rewindP1 →
      (c.work pIdx).head = p →
      (c.work pIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) →
      c.input.head ≥ 1 → (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (c.work yIdx).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) →
      ∃ c',
        (pairBuildTM yIdx pIdx).reachesIn (p + 1) c c' ∧
        c'.state = .rewindP2 ∧
        c'.input = c.input ∧
        c'.work yIdx = c.work yIdx ∧
        (c'.work pIdx).head = 1 ∧
        (c'.work pIdx).cells = (c.work pIdx).cells := by
  intro p
  induction p with
  | zero =>
    intro c hst hhead hcell0 _ hih hins hyh hyns
    have hpread : (c.work pIdx).read = Γ.start := by
      simp [Tape.read, hhead, hcell0]
    obtain ⟨c', hstep, hst', hinp, hyw, hph, hpcells⟩ :=
      pairBuild_rewindP1_step_base yIdx pIdx hne c hst hpread hhead hih hyh hins hyns
    exact ⟨c', .step hstep .zero, hst', hinp, hyw, hph, hpcells⟩
  | succ p ih =>
    intro c hst hhead hcell0 hnostart hih hins hyh hyns
    have hph_ge : (c.work pIdx).head ≥ 1 := by omega
    have hpread_ns : (c.work pIdx).read ≠ Γ.start := by
      simp only [Tape.read, hhead]; exact hnostart (p + 1) (by omega)
    obtain ⟨c₁, hstep, hst₁, hinp₁, hyw₁, hph₁, hpcells₁⟩ :=
      pairBuild_rewindP1_step_cont yIdx pIdx hne c hst hpread_ns hih hyh hph_ge hins hyns
    have hhead₁ : (c₁.work pIdx).head = p := by rw [hph₁, hhead]; omega
    have hcell0₁ : (c₁.work pIdx).cells 0 = Γ.start := by rw [hpcells₁]; exact hcell0
    have hnostart₁ : ∀ j, j ≥ 1 → (c₁.work pIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hpcells₁]; exact hnostart j hj
    have hih₁ : c₁.input.head ≥ 1 := hinp₁ ▸ hih
    have hins₁ : ∀ j, j ≥ 1 → c₁.input.cells j ≠ Γ.start := by
      intro j hj; rw [hinp₁]; exact hins j hj
    have hyh₁ : (c₁.work yIdx).head ≥ 1 := by rw [hyw₁]; exact hyh
    have hyns₁ : ∀ j, j ≥ 1 → (c₁.work yIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hyw₁]; exact hyns j hj
    obtain ⟨c', hreach, hst', hinp', hyw', hph', hpcells'⟩ :=
      ih c₁ hst₁ hhead₁ hcell0₁ hnostart₁ hih₁ hins₁ hyh₁ hyns₁
    exact ⟨c', .step hstep hreach, hst',
      hinp'.trans hinp₁, hyw'.trans hyw₁, hph',
      by rw [hpcells', hpcells₁]⟩

-- ════════════════════════════════════════════════════════════════════════
-- Loop lemmas: copyX and copyY
-- ════════════════════════════════════════════════════════════════════════

/-- **copyX loop.** Starting from `.copyX1` with input head at `q`, pIdx
    head at `p`, and the next `m` input cells being data bits (non-blank,
    non-start), after `2m` steps we return to `.copyX1` with:
    - input head at `q + m`, cells unchanged,
    - yIdx unchanged,
    - pIdx head at `p + 2m`, with cells below `p` and at `≥ p + 2m`
      unchanged, and cells in between doubly populated with the
      corresponding input data bit. -/
private theorem pairBuild_copyX_loop {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx) :
    ∀ (m : ℕ) (c : Cfg k (pairBuildTM yIdx pIdx).Q),
      c.state = .copyX1 →
      c.input.head ≥ 1 →
      c.input.cells 0 = Γ.start →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (∀ i, i < m → c.input.cells (c.input.head + i) ≠ Γ.blank ∧
                      c.input.cells (c.input.head + i) ≠ Γ.start) →
      (c.work yIdx).head ≥ 1 →
      (∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) →
      (c.work pIdx).head ≥ 1 →
      (c.work pIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) →
      ∃ c',
        (pairBuildTM yIdx pIdx).reachesIn (2 * m) c c' ∧
        c'.state = .copyX1 ∧
        c'.input.cells = c.input.cells ∧
        c'.input.head = c.input.head + m ∧
        c'.work yIdx = c.work yIdx ∧
        (c'.work pIdx).head = (c.work pIdx).head + 2 * m ∧
        (c'.work pIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work pIdx).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work pIdx).head → (c'.work pIdx).cells j = (c.work pIdx).cells j) ∧
        (∀ j, j ≥ (c.work pIdx).head + 2 * m →
            (c'.work pIdx).cells j = (c.work pIdx).cells j) ∧
        (∀ i, i < m →
            (c'.work pIdx).cells ((c.work pIdx).head + 2 * i) =
              c.input.cells (c.input.head + i) ∧
            (c'.work pIdx).cells ((c.work pIdx).head + 2 * i + 1) =
              c.input.cells (c.input.head + i)) := by
  intro m
  induction m with
  | zero =>
    intro c hst hih _hic0 _hins _hdata hyh hyns hph hpc0 hpns
    refine ⟨c, .zero, hst, rfl, by omega, rfl, by omega, hpc0, hpns, ?_, ?_, ?_⟩
    · intro j _; rfl
    · intro j _; rfl
    · intro i hi; exact absurd hi (by omega)
  | succ m ih =>
    intro c hst hih hic0 hins hdata hyh hyns hph hpc0 hpns
    -- Read the current input bit.
    have hread : c.input.read = c.input.cells c.input.head := rfl
    have hread_nb : c.input.read ≠ Γ.blank := (hdata 0 (by omega)).1
    have hread_ns : c.input.read ≠ Γ.start := by
      rw [hread]; have h := hins c.input.head hih; exact h
    -- One `copyX1` step (writes to pIdx, advances pIdx).
    obtain ⟨c1, hstep1, hst1, hinp1, hyw1, hph1, hpc1⟩ :=
      pairBuild_copyX1_cont_step yIdx pIdx hne c hst hread_nb hread_ns
        hih hyh hph hins hyns hpns
    -- One `copyX2` step (writes second copy, advances input and pIdx).
    have hih1 : c1.input.head ≥ 1 := by rw [hinp1]; exact hih
    have hyh1 : (c1.work yIdx).head ≥ 1 := by rw [hyw1]; exact hyh
    have hph1_ge : (c1.work pIdx).head ≥ 1 := by rw [hph1]; omega
    have hyns1 : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hyw1]; exact hyns j hj
    -- c1.input.read = c.input.read (input hasn't moved).
    have hc1_iread : c1.input.read = c.input.read := by
      rw [Tape.read, Tape.read, hinp1]
    have hread1_ns : c1.input.read ≠ Γ.start := by rw [hc1_iread]; exact hread_ns
    obtain ⟨c2, hstep2, hst2, hinp2h, hinp2c, hyw2, hph2, hpc2⟩ :=
      pairBuild_copyX2_step yIdx pIdx hne c1 hst1 hread1_ns hih1 hyh1 hph1_ge hyns1
    -- Derive invariants on c2.
    have hih2 : c2.input.head ≥ 1 := by rw [hinp2h]; omega
    have hic02 : c2.input.cells 0 = Γ.start := by rw [hinp2c, hinp1]; exact hic0
    have hins2 : ∀ j, j ≥ 1 → c2.input.cells j ≠ Γ.start := by
      intro j hj; rw [hinp2c, hinp1]; exact hins j hj
    have hyh2 : (c2.work yIdx).head ≥ 1 := by rw [hyw2]; exact hyh1
    have hyns2 : ∀ j, j ≥ 1 → (c2.work yIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hyw2]; exact hyns1 j hj
    have hph2_ge : (c2.work pIdx).head ≥ 1 := by rw [hph2, hph1]; omega
    have hpc02 : (c2.work pIdx).cells 0 = Γ.start := by
      rw [hpc2, Function.update_of_ne (by omega), hpc1,
          Function.update_of_ne (by omega)]; exact hpc0
    have hpns2 : ∀ j, j ≥ 1 → (c2.work pIdx).cells j ≠ Γ.start := by
      intro j hj
      rw [hpc2]
      by_cases hj1 : j = (c1.work pIdx).head
      · rw [hj1, Function.update_self, hc1_iread]; exact hread_ns
      · rw [Function.update_of_ne hj1, hpc1]
        by_cases hj2 : j = (c.work pIdx).head
        · rw [hj2, Function.update_self]; exact hread_ns
        · rw [Function.update_of_ne hj2]; exact hpns j hj
    -- The next `m` data bits: starting from c2.input.head = c.input.head + 1.
    have hdata2 : ∀ i, i < m →
        c2.input.cells (c2.input.head + i) ≠ Γ.blank ∧
        c2.input.cells (c2.input.head + i) ≠ Γ.start := by
      intro i hi
      have hrw : c2.input.head + i = c.input.head + (i + 1) := by
        rw [hinp2h, hinp1]; omega
      rw [hinp2c, hinp1, hrw]
      exact hdata (i + 1) (by omega)
    -- Apply IH.
    obtain ⟨c', hreach, hst', hc_ic, hc_ih, hc_yw, hc_ph, hc_pc0, hc_pns,
            hc_below, hc_above, hc_data⟩ :=
      ih c2 hst2 hih2 hic02 hins2 hdata2 hyh2 hyns2 hph2_ge hpc02 hpns2
    -- Assemble.
    have hstep_total : (pairBuildTM yIdx pIdx).reachesIn (2 * (m + 1)) c c' := by
      have h1 : (pairBuildTM yIdx pIdx).reachesIn 2 c c2 :=
        .step hstep1 (.step hstep2 .zero)
      have htot : (pairBuildTM yIdx pIdx).reachesIn (2 + 2 * m) c c' :=
        reachesIn_trans _ h1 hreach
      have heq : 2 * (m + 1) = 2 + 2 * m := by ring
      rw [heq]; exact htot
    refine ⟨c', hstep_total, hst', ?_, ?_, ?_, ?_, hc_pc0, hc_pns, ?_, ?_, ?_⟩
    · rw [hc_ic, hinp2c, hinp1]
    · rw [hc_ih, hinp2h, hinp1]; omega
    · rw [hc_yw, hyw2, hyw1]
    · rw [hc_ph, hph2, hph1]; ring
    · -- cells below c.work pIdx .head unchanged
      intro j hj
      have hj1 : j < (c2.work pIdx).head := by rw [hph2, hph1]; omega
      rw [hc_below j hj1, hpc2, Function.update_of_ne (by rw [hph1]; omega),
          hpc1, Function.update_of_ne (by omega)]
    · -- cells ≥ c.work pIdx .head + 2*(m+1) unchanged
      intro j hj
      have hj2 : j ≥ (c2.work pIdx).head + 2 * m := by
        rw [hph2, hph1]; omega
      rw [hc_above j hj2, hpc2, Function.update_of_ne (by rw [hph1]; omega),
          hpc1, Function.update_of_ne (by omega)]
    · -- Cells at 2i positions
      intro i hi
      by_cases hi_zero : i = 0
      · subst hi_zero
        refine ⟨?_, ?_⟩
        · -- cells at c.pIdx.head = c.input.cells c.input.head
          have hj1 : (c.work pIdx).head + 2 * 0 < (c2.work pIdx).head := by
            rw [hph2, hph1]; omega
          rw [hc_below _ hj1, hpc2]
          have hne1 : (c.work pIdx).head + 2 * 0 ≠ (c1.work pIdx).head := by
            rw [hph1]; omega
          rw [Function.update_of_ne hne1, hpc1]
          have heq0 : (c.work pIdx).head + 2 * 0 = (c.work pIdx).head := by omega
          rw [heq0, Function.update_self]
          have hhead_eq : c.input.head + 0 = c.input.head := by omega
          rw [hhead_eq]
          rfl
        · -- cells at c.pIdx.head + 1 = c1.pIdx.head = c.input.cells (c.input.head + 0)
          -- But c.input.head + 0 = c.input.head.
          have hj1 : (c.work pIdx).head + 2 * 0 + 1 < (c2.work pIdx).head := by
            rw [hph2, hph1]; omega
          rw [hc_below _ hj1, hpc2]
          have heq1 : (c.work pIdx).head + 2 * 0 + 1 = (c1.work pIdx).head := by
            rw [hph1]
          rw [heq1, Function.update_self, hc1_iread]
          have hhead_eq : c.input.head + 0 = c.input.head := by omega
          rw [hhead_eq]
          rfl
      · -- i ≥ 1. Use hc_data on i - 1 with c2.
        have hi_pred : i - 1 < m := by omega
        have ⟨h_a, h_b⟩ := hc_data (i - 1) hi_pred
        refine ⟨?_, ?_⟩
        · have heq_pos : (c.work pIdx).head + 2 * i =
                 (c2.work pIdx).head + 2 * (i - 1) := by
            rw [hph2, hph1]; omega
          rw [heq_pos, h_a, hinp2c, hinp1, hinp2h, hinp1]
          congr 1; omega
        · have heq_pos : (c.work pIdx).head + 2 * i + 1 =
                 (c2.work pIdx).head + 2 * (i - 1) + 1 := by
            rw [hph2, hph1]; omega
          rw [heq_pos, h_b, hinp2c, hinp1, hinp2h, hinp1]
          congr 1; omega

/-- **copyY loop.** Starting from `.copyY` with yIdx head at `q`, pIdx
    head at `p`, and the next `m` yIdx cells being data bits (non-blank,
    non-start), after `m` steps we return to `.copyY` with:
    - input unchanged,
    - yIdx head at `q + m`, cells unchanged,
    - pIdx head at `p + m`, with cells below `p` and at `≥ p + m`
      unchanged, and cells in between populated with the corresponding
      yIdx data bits. -/
private theorem pairBuild_copyY_loop {k : ℕ} (yIdx pIdx : Fin k)
    (hne : yIdx ≠ pIdx) :
    ∀ (m : ℕ) (c : Cfg k (pairBuildTM yIdx pIdx).Q),
      c.state = .copyY →
      c.input.head ≥ 1 →
      (∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start) →
      (c.work yIdx).head ≥ 1 →
      (c.work yIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work yIdx).cells j ≠ Γ.start) →
      (∀ i, i < m → (c.work yIdx).cells ((c.work yIdx).head + i) ≠ Γ.blank ∧
                      (c.work yIdx).cells ((c.work yIdx).head + i) ≠ Γ.start) →
      (c.work pIdx).head ≥ 1 →
      (c.work pIdx).cells 0 = Γ.start →
      (∀ j, j ≥ 1 → (c.work pIdx).cells j ≠ Γ.start) →
      ∃ c',
        (pairBuildTM yIdx pIdx).reachesIn m c c' ∧
        c'.state = .copyY ∧
        c'.input = c.input ∧
        (c'.work yIdx).head = (c.work yIdx).head + m ∧
        (c'.work yIdx).cells = (c.work yIdx).cells ∧
        (c'.work pIdx).head = (c.work pIdx).head + m ∧
        (c'.work pIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (c'.work pIdx).cells j ≠ Γ.start) ∧
        (∀ j, j < (c.work pIdx).head → (c'.work pIdx).cells j = (c.work pIdx).cells j) ∧
        (∀ j, j ≥ (c.work pIdx).head + m →
            (c'.work pIdx).cells j = (c.work pIdx).cells j) ∧
        (∀ i, i < m →
            (c'.work pIdx).cells ((c.work pIdx).head + i) =
              (c.work yIdx).cells ((c.work yIdx).head + i)) := by
  intro m
  induction m with
  | zero =>
    intro c hst _ _ _ _ _ _ _ _ hpns
    refine ⟨c, .zero, hst, rfl, by omega, rfl, by omega, ‹_›, hpns, ?_, ?_, ?_⟩
    · intro j _; rfl
    · intro j _; rfl
    · intro i hi; exact absurd hi (by omega)
  | succ m ih =>
    intro c hst hih hins hyh hyc0 hyns hdata hph hpc0 hpns
    -- Read the current yIdx bit.
    have hyread : (c.work yIdx).read = (c.work yIdx).cells (c.work yIdx).head := rfl
    have hyread_nb : (c.work yIdx).read ≠ Γ.blank := (hdata 0 (by omega)).1
    have hyread_ns : (c.work yIdx).read ≠ Γ.start := by
      rw [hyread]; exact hyns (c.work yIdx).head hyh
    -- One `copyY` step (writes to pIdx, advances yIdx and pIdx).
    obtain ⟨c1, hstep1, hst1, hinp1, hyh1, hyc1, hph1, hpc1⟩ :=
      pairBuild_copyY_cont_step yIdx pIdx hne c hst hyread_nb hyread_ns
        hih hyh hph hins hyns
    -- Derive invariants on c1.
    have hih1 : c1.input.head ≥ 1 := by rw [hinp1]; exact hih
    have hins1 : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
      intro j hj; rw [hinp1]; exact hins j hj
    have hyh1_ge : (c1.work yIdx).head ≥ 1 := by rw [hyh1]; omega
    have hyc01 : (c1.work yIdx).cells 0 = Γ.start := by rw [hyc1]; exact hyc0
    have hyns1 : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
      intro j hj; rw [hyc1]; exact hyns j hj
    have hph1_ge : (c1.work pIdx).head ≥ 1 := by rw [hph1]; omega
    have hpc01 : (c1.work pIdx).cells 0 = Γ.start := by
      rw [hpc1, Function.update_of_ne (by omega)]; exact hpc0
    have hpns1 : ∀ j, j ≥ 1 → (c1.work pIdx).cells j ≠ Γ.start := by
      intro j hj
      rw [hpc1]
      by_cases hj1 : j = (c.work pIdx).head
      · rw [hj1, Function.update_self]; exact hyread_ns
      · rw [Function.update_of_ne hj1]; exact hpns j hj
    have hdata1 : ∀ i, i < m →
        (c1.work yIdx).cells ((c1.work yIdx).head + i) ≠ Γ.blank ∧
        (c1.work yIdx).cells ((c1.work yIdx).head + i) ≠ Γ.start := by
      intro i hi
      have hrw : (c1.work yIdx).head + i = (c.work yIdx).head + (i + 1) := by
        rw [hyh1]; omega
      rw [hyc1, hrw]
      exact hdata (i + 1) (by omega)
    -- Apply IH.
    obtain ⟨c', hreach, hst', hc_inp, hc_yh, hc_yc, hc_ph, hc_pc0, hc_pns,
            hc_below, hc_above, hc_data⟩ :=
      ih c1 hst1 hih1 hins1 hyh1_ge hyc01 hyns1 hdata1 hph1_ge hpc01 hpns1
    -- Assemble.
    have hstep_total : (pairBuildTM yIdx pIdx).reachesIn (m + 1) c c' := by
      have h1 : (pairBuildTM yIdx pIdx).reachesIn 1 c c1 := .step hstep1 .zero
      have htot : (pairBuildTM yIdx pIdx).reachesIn (1 + m) c c' :=
        reachesIn_trans _ h1 hreach
      have heq : m + 1 = 1 + m := by ring
      rw [heq]; exact htot
    refine ⟨c', hstep_total, hst', ?_, ?_, ?_, ?_, hc_pc0, hc_pns, ?_, ?_, ?_⟩
    · rw [hc_inp, hinp1]
    · rw [hc_yh, hyh1]; omega
    · rw [hc_yc, hyc1]
    · rw [hc_ph, hph1]; omega
    · -- cells below (c.work pIdx).head unchanged
      intro j hj
      have hj1 : j < (c1.work pIdx).head := by rw [hph1]; omega
      rw [hc_below j hj1, hpc1, Function.update_of_ne (by omega)]
    · -- cells ≥ (c.work pIdx).head + (m+1) unchanged
      intro j hj
      have hj2 : j ≥ (c1.work pIdx).head + m := by rw [hph1]; omega
      rw [hc_above j hj2, hpc1, Function.update_of_ne (by omega)]
    · -- Cells at the m+1 written positions
      intro i hi
      by_cases hi_zero : i = 0
      · subst hi_zero
        have hj1 : (c.work pIdx).head + 0 < (c1.work pIdx).head := by
          rw [hph1]; omega
        rw [hc_below _ hj1, hpc1]
        have hheadeq : (c.work pIdx).head + 0 = (c.work pIdx).head := by omega
        rw [hheadeq, Function.update_self]
        have hyhead0 : (c.work yIdx).head + 0 = (c.work yIdx).head := by omega
        rw [hyhead0]
        rfl
      · have hi_pred : i - 1 < m := by omega
        have h_d := hc_data (i - 1) hi_pred
        have heq_p : (c.work pIdx).head + i = (c1.work pIdx).head + (i - 1) := by
          rw [hph1]; omega
        have heq_y : (c.work yIdx).head + i = (c1.work yIdx).head + (i - 1) := by
          rw [hyh1]; omega
        rw [heq_p, h_d, hyc1, heq_y]

-- ════════════════════════════════════════════════════════════════════════
-- Indexing lemmas for `pair x y`
-- ════════════════════════════════════════════════════════════════════════

/-- Helper: `pair (b :: xs) y = b :: b :: pair xs y`. -/
private theorem pair_build_cons_eq (b : Bool) (xs y : List Bool) :
    pair (b :: xs) y = b :: b :: pair xs y := by
  simp [pair]

/-- Shift lemma: accessing `pair (b :: xs) y` at index `k+2` is the same as
    accessing `pair xs y` at index `k`. -/
private theorem pair_getElem_cons_shift (b : Bool) (xs y : List Bool) (k : ℕ)
    (hk : k < (pair xs y).length) :
    (pair (b :: xs) y)[k + 2]'(by
      rw [pair_build_cons_eq, List.length_cons, List.length_cons]; omega) =
      (pair xs y)[k]'hk := by
  rw [List.getElem_of_eq (pair_build_cons_eq b xs y)]
  rfl

/-- In `pair x y`, the cell at even position `2*j` (j < |x|) equals `x[j]`. -/
private theorem pair_getElem_doubled_even (x y : List Bool) (j : ℕ)
    (hj : j < x.length) :
    (pair x y)[2 * j]'(by rw [pair_length]; omega) = x[j]'hj := by
  induction x generalizing j with
  | nil => simp at hj
  | cons b xs ih =>
    match j with
    | 0 =>
      rw [List.getElem_of_eq (pair_build_cons_eq b xs y)]; rfl
    | j + 1 =>
      have hj' : j < xs.length := by rw [List.length_cons] at hj; omega
      have hbound : 2 * j < (pair xs y).length := by rw [pair_length]; omega
      have h1 : (pair (b :: xs) y)[2 * (j + 1)]'(by rw [pair_length]; simp; omega)
                = (pair xs y)[2 * j]'hbound := by
        show (pair (b :: xs) y)[2 * j + 2]'_ = _
        exact pair_getElem_cons_shift b xs y (2 * j) hbound
      rw [h1, ih j hj']
      rfl

/-- In `pair x y`, the cell at odd position `2*j + 1` (j < |x|) also equals `x[j]`. -/
private theorem pair_getElem_doubled_odd (x y : List Bool) (j : ℕ)
    (hj : j < x.length) :
    (pair x y)[2 * j + 1]'(by rw [pair_length]; omega) = x[j]'hj := by
  induction x generalizing j with
  | nil => simp at hj
  | cons b xs ih =>
    match j with
    | 0 =>
      rw [List.getElem_of_eq (pair_build_cons_eq b xs y)]; rfl
    | j + 1 =>
      have hj' : j < xs.length := by rw [List.length_cons] at hj; omega
      have hbound : 2 * j + 1 < (pair xs y).length := by rw [pair_length]; omega
      have h1 : (pair (b :: xs) y)[2 * (j + 1) + 1]'(by rw [pair_length]; simp; omega)
                = (pair xs y)[2 * j + 1]'hbound := by
        show (pair (b :: xs) y)[(2 * j + 1) + 2]'_ = _
        exact pair_getElem_cons_shift b xs y (2 * j + 1) hbound
      rw [h1, ih j hj']
      rfl

/-- In `pair x y`, the cell at position `2 * |x|` is the first separator bit `false`. -/
private theorem pair_getElem_sep0 (x y : List Bool) :
    (pair x y)[2 * x.length]'(by rw [pair_length]; omega) = false := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    have hbound : 2 * xs.length < (pair xs y).length := by rw [pair_length]; omega
    have h1 : (pair (b :: xs) y)[2 * (b :: xs).length]'(by rw [pair_length]; omega)
              = (pair xs y)[2 * xs.length]'hbound := by
      show (pair (b :: xs) y)[2 * xs.length + 2]'_ = _
      exact pair_getElem_cons_shift b xs y (2 * xs.length) hbound
    rw [h1, ih]

/-- In `pair x y`, the cell at position `2 * |x| + 1` is the second separator bit `true`. -/
private theorem pair_getElem_sep1 (x y : List Bool) :
    (pair x y)[2 * x.length + 1]'(by rw [pair_length]; omega) = true := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    have hbound : 2 * xs.length + 1 < (pair xs y).length := by rw [pair_length]; omega
    have h1 : (pair (b :: xs) y)[2 * (b :: xs).length + 1]'(by rw [pair_length]; omega)
              = (pair xs y)[2 * xs.length + 1]'hbound := by
      show (pair (b :: xs) y)[2 * xs.length + 1 + 2]'_ = _
      exact pair_getElem_cons_shift b xs y (2 * xs.length + 1) hbound
    rw [h1, ih]

-- ════════════════════════════════════════════════════════════════════════
-- Correctness specification
-- ════════════════════════════════════════════════════════════════════════

/-- Running-time bound: `pairBuildTM` finishes in `4·|x| + 2·|y| + 10` steps.

    Breakdown:
    - `init`: 1 step.
    - `copyX1`+`copyX2`: 2·|x| + 1 steps (one final `copyX1` detects blank).
    - `writeSep1`+`writeSep2`: 2 steps.
    - `copyY`: |y| + 1 steps.
    - `rewindP1`: one step per cell left from `2|x|+2+|y|+1` to `0`,
      so `2|x|+|y|+3` steps; plus the `rewindP2` step; plus the
      `done` transition step. -/
def pairBuildTime (xLen yLen : ℕ) : ℕ :=
  4 * xLen + 2 * yLen + 10

-- ════════════════════════════════════════════════════════════════════════
-- `pair x y` indexing in the y-tail region, via decomposition
-- ════════════════════════════════════════════════════════════════════════

/-- Length of `x.flatMap (fun b => [b, b])` is `2 * |x|`. -/
private theorem flatMap_doubled_length (x : List Bool) :
    (x.flatMap fun b => [b, b]).length = 2 * x.length := by
  induction x with
  | nil => simp
  | cons b xs ih =>
    show (List.flatMap (fun b => [b, b]) (b :: xs)).length = 2 * (xs.length + 1)
    rw [List.flatMap_cons, List.length_append, ih,
        show ([b, b] : List Bool).length = 2 from rfl]; omega

/-- In `pair x y`, the cell at position `2*|x| + 2 + j` (j < |y|) equals `y[j]`. -/
private theorem pair_getElem_y (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    (pair x y)[2 * x.length + 2 + j]'(by rw [pair_length]; omega) = y[j]'hj := by
  have hdecomp : pair x y = (x.flatMap fun b => [b, b]) ++ [false, true] ++ y := rfl
  have hflat_len := flatMap_doubled_length x
  have hprefix_len : ((x.flatMap fun b => [b, b]) ++ [false, true]).length =
      2 * x.length + 2 := by rw [List.length_append, hflat_len]; rfl
  have hge : ((x.flatMap fun b => [b, b]) ++ [false, true]).length ≤
      2 * x.length + 2 + j := by rw [hprefix_len]; omega
  have hjbound : (2 * x.length + 2 + j) -
      ((x.flatMap fun b => [b, b]) ++ [false, true]).length < y.length := by
    rw [hprefix_len]; omega
  calc (pair x y)[2 * x.length + 2 + j]'_
      = ((x.flatMap fun b => [b, b]) ++ [false, true] ++ y)[2 * x.length + 2 + j]'
          (by rw [← hdecomp, pair_length]; omega) := by
        exact List.getElem_of_eq hdecomp _
    _ = y[(2 * x.length + 2 + j) -
          ((x.flatMap fun b => [b, b]) ++ [false, true]).length]'hjbound :=
        List.getElem_append_right hge
    _ = y[j]'hj := by congr 1; rw [hprefix_len]; omega

-- ════════════════════════════════════════════════════════════════════════
-- Tape.init helpers
-- ════════════════════════════════════════════════════════════════════════

/-- A tape with head at cell 1, a start marker at cell 0, binary contents
    `bits`, and a blank tail is exactly the standard initialized tape for
    `bits`, moved right once. -/
theorem Tape.eq_init_move_right_of_binary {t : Tape} {bits : List Bool}
    (hhead : t.head = 1)
    (h0 : t.cells 0 = Γ.start)
    (hbits : ∀ i : ℕ, (h : i < bits.length) →
      t.cells (i + 1) = Γ.ofBool (bits[i]'h))
    (htail : ∀ i : ℕ, bits.length ≤ i → t.cells (i + 1) = Γ.blank) :
    t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  cases t with
  | mk head cells =>
    simp only at hhead h0 hbits htail
    subst head
    simp only [Tape.move]
    congr
    funext j
    by_cases hj0 : j = 0
    · subst hj0
      simp [Tape.init, h0]
    · let i := j - 1
      have hj : j = i + 1 := by omega
      rw [hj]
      by_cases hi : i < bits.length
      · rw [hbits i hi, Tape.init_ofBool_cells_lt bits i hi]
      · have hge : bits.length ≤ i := by omega
        rw [htail i hge, Tape.init_ofBool_cells_ge bits i hge]

/-- Core correctness for the post-init state of `pairBuildTM`. This is the
    phase-composition entry point: all tracked tapes are already positioned at
    cell `1`, so execution begins in `.copyX1` with no dependence on a fresh
    head-0 setup step. -/
private theorem pairBuildTM_from_copyX1_initTape_move_right
    {k : ℕ} (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx)
    (x y : List Bool)
    (c1 : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hc1_state : c1.state = .copyX1)
    (hc1_input : c1.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right)
    (hc1_yw : c1.work yIdx = (Tape.init (y.map Γ.ofBool)).move Dir3.right)
    (hc1_pw : c1.work pIdx = (Tape.init []).move Dir3.right) :
    ∃ c9 t, t ≤ 4 * x.length + 2 * y.length + 9 ∧
      (pairBuildTM yIdx pIdx).reachesIn t c1 c9 ∧
      (pairBuildTM yIdx pIdx).halted c9 ∧
      (c9.work pIdx).head = 1 ∧
      (c9.work pIdx).cells 0 = Γ.start ∧
      (∀ i : ℕ, (h : i < (pair x y).length) →
        (c9.work pIdx).cells (i + 1) = Γ.ofBool ((pair x y)[i]'h)) ∧
      (∀ i : ℕ, (pair x y).length ≤ i →
        (c9.work pIdx).cells (i + 1) = Γ.blank) := by
  have hc1_ih : c1.input.head = 1 := by
    rw [hc1_input]
    rfl
  have hc1_ic : c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
    rw [hc1_input]
    exact Tape.move_cells _ _
  have hc1_ih_ge : c1.input.head ≥ 1 := by rw [hc1_ih]
  have hc1_ic0 : c1.input.cells 0 = Γ.start := by
    rw [hc1_ic]
    rfl
  have hc1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_ic]
    exact Tape.init_ofBool_cells_ne_start x j hj
  have hc1_yh : (c1.work yIdx).head = 1 := by
    rw [hc1_yw]
    rfl
  have hc1_yc : (c1.work yIdx).cells =
      (Tape.init (y.map Γ.ofBool)).cells := by
    rw [hc1_yw]
    exact Tape.move_cells _ _
  have hc1_yh_ge : (c1.work yIdx).head ≥ 1 := by rw [hc1_yh]
  have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_yc]
    exact Tape.init_ofBool_cells_ne_start y j hj
  have hc1_ph : (c1.work pIdx).head = 1 := by
    rw [hc1_pw]
    rfl
  have hc1_pc : (c1.work pIdx).cells = (Tape.init []).cells := by
    rw [hc1_pw]
    exact Tape.move_cells _ _
  have hc1_ph_ge : (c1.work pIdx).head ≥ 1 := by rw [hc1_ph]
  have hc1_pc0 : (c1.work pIdx).cells 0 = Γ.start := by
    rw [hc1_pc]
    rfl
  have hc1_pns : ∀ j, j ≥ 1 → (c1.work pIdx).cells j ≠ Γ.start := by
    intro j hj
    rw [hc1_pc]
    show (Tape.init []).cells j ≠ Γ.start
    show (if j = 0 then Γ.start else ([][j - 1]?).getD Γ.blank) ≠ Γ.start
    rw [ite_eq_right (by omega)]
    simp
  have hc1_input_data : ∀ i, i < x.length →
      c1.input.cells (c1.input.head + i) ≠ Γ.blank ∧
      c1.input.cells (c1.input.head + i) ≠ Γ.start := by
    intro i hi
    rw [hc1_ic, hc1_ih]
    have heq :
        (Tape.init (x.map Γ.ofBool)).cells (1 + i) = Γ.ofBool (x[i]'hi) := by
      rw [show 1 + i = i + 1 from by omega]
      exact Tape.init_ofBool_cells_lt x i hi
    refine ⟨?_, ?_⟩
    · rw [heq]; exact Γ.ofBool_ne_blank _
    · rw [heq]; exact Γ.ofBool_ne_start _
  have hc1_yw_data : ∀ i, i < y.length →
      (c1.work yIdx).cells ((c1.work yIdx).head + i) ≠ Γ.blank ∧
      (c1.work yIdx).cells ((c1.work yIdx).head + i) ≠ Γ.start := by
    intro i hi
    rw [hc1_yc, hc1_yh]
    have heq :
        (Tape.init (y.map Γ.ofBool)).cells (1 + i) = Γ.ofBool (y[i]'hi) := by
      rw [show 1 + i = i + 1 from by omega]
      exact Tape.init_ofBool_cells_lt y i hi
    refine ⟨?_, ?_⟩
    · rw [heq]; exact Γ.ofBool_ne_blank _
    · rw [heq]; exact Γ.ofBool_ne_start _
  obtain ⟨c2, hreach_copyX, hc2_state, hc2_ic, hc2_ih, hc2_yw, hc2_ph, hc2_pc0,
          hc2_pns, hc2_below, hc2_above, hc2_data⟩ :=
    pairBuild_copyX_loop yIdx pIdx hne x.length c1 hc1_state hc1_ih_ge hc1_ic0
      hc1_ins hc1_input_data hc1_yh_ge hc1_yns hc1_ph_ge hc1_pc0 hc1_pns
  have hc2_ih_val : c2.input.head = 1 + x.length := by rw [hc2_ih, hc1_ih]
  have hc2_ph_val : (c2.work pIdx).head = 1 + 2 * x.length := by
    rw [hc2_ph, hc1_ph]
  have hc2_ih_ge : c2.input.head ≥ 1 := by rw [hc2_ih_val]; omega
  have hc2_yh_ge : (c2.work yIdx).head ≥ 1 := by rw [hc2_yw]; exact hc1_yh_ge
  have hc2_ph_ge : (c2.work pIdx).head ≥ 1 := by rw [hc2_ph_val]; omega
  have hc2_ic0 : c2.input.cells 0 = Γ.start := by rw [hc2_ic]; exact hc1_ic0
  have hc2_ins : ∀ j, j ≥ 1 → c2.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc2_ic]; exact hc1_ins j hj
  have hc2_yns : ∀ j, j ≥ 1 → (c2.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc2_yw]; exact hc1_yns j hj
  have hc2_iread : c2.input.read = Γ.blank := by
    show c2.input.cells c2.input.head = Γ.blank
    rw [hc2_ic, hc1_ic, hc2_ih_val]
    rw [show 1 + x.length = x.length + 1 from by omega]
    exact Tape.init_ofBool_cells_ge x x.length (le_refl _)
  obtain ⟨c3, hstep3, hc3_state, hc3_inp, hc3_yw, hc3_pw⟩ :=
    pairBuild_copyX1_halt_step yIdx pIdx c2 hc2_state hc2_iread
      hc2_ih_ge hc2_yh_ge hc2_ph_ge hc2_ins hc2_yns hc2_pns
  have hc3_ih : c3.input.head = 1 + x.length := by rw [hc3_inp]; exact hc2_ih_val
  have hc3_ic : c3.input.cells = c2.input.cells := by rw [hc3_inp]
  have hc3_ih_ge : c3.input.head ≥ 1 := by rw [hc3_ih]; omega
  have hc3_ic0 : c3.input.cells 0 = Γ.start := by rw [hc3_ic]; exact hc2_ic0
  have hc3_ins : ∀ j, j ≥ 1 → c3.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc3_ic]; exact hc2_ins j hj
  have hc3_yw_head : (c3.work yIdx).head ≥ 1 := by rw [hc3_yw]; exact hc2_yh_ge
  have hc3_yw_cells : (c3.work yIdx).cells = (c2.work yIdx).cells := by rw [hc3_yw]
  have hc3_yns : ∀ j, j ≥ 1 → (c3.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc3_yw]; exact hc2_yns j hj
  have hc3_pw_head : (c3.work pIdx).head = 1 + 2 * x.length := by
    rw [hc3_pw]; exact hc2_ph_val
  have hc3_pw_cells : (c3.work pIdx).cells = (c2.work pIdx).cells := by rw [hc3_pw]
  have hc3_ph_ge : (c3.work pIdx).head ≥ 1 := by rw [hc3_pw_head]; omega
  have hc3_pc0 : (c3.work pIdx).cells 0 = Γ.start := by rw [hc3_pw_cells]; exact hc2_pc0
  have hc3_pns : ∀ j, j ≥ 1 → (c3.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc3_pw]; exact hc2_pns j hj
  obtain ⟨c4, hstep4, hc4_state, hc4_inp, hc4_yw, hc4_ph, hc4_pc⟩ :=
    pairBuild_writeSep1_step yIdx pIdx hne c3 hc3_state
      hc3_ih_ge hc3_yw_head hc3_ph_ge hc3_ins hc3_yns
  have hc4_ih_val : c4.input.head = 1 + x.length := by rw [hc4_inp]; exact hc3_ih
  have hc4_ic : c4.input.cells = c3.input.cells := by rw [hc4_inp]
  have hc4_ih_ge : c4.input.head ≥ 1 := by rw [hc4_ih_val]; omega
  have hc4_ic0 : c4.input.cells 0 = Γ.start := by rw [hc4_ic]; exact hc3_ic0
  have hc4_ins : ∀ j, j ≥ 1 → c4.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc4_ic]; exact hc3_ins j hj
  have hc4_yh_ge : (c4.work yIdx).head ≥ 1 := by rw [hc4_yw]; exact hc3_yw_head
  have hc4_yw_cells : (c4.work yIdx).cells = (c3.work yIdx).cells := by rw [hc4_yw]
  have hc4_yns : ∀ j, j ≥ 1 → (c4.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc4_yw]; exact hc3_yns j hj
  have hc4_ph_val : (c4.work pIdx).head = 2 + 2 * x.length := by
    rw [hc4_ph, hc3_pw_head]; omega
  have hc4_ph_ge : (c4.work pIdx).head ≥ 1 := by rw [hc4_ph_val]; omega
  have hc4_pc_zero : (c4.work pIdx).cells (1 + 2 * x.length) = Γ.zero := by
    rw [hc4_pc, ← hc3_pw_head, Function.update_self]
  have hc4_pc_other : ∀ j, j ≠ 1 + 2 * x.length →
      (c4.work pIdx).cells j = (c3.work pIdx).cells j := by
    intro j hj
    rw [hc4_pc, Function.update_of_ne (by rw [hc3_pw_head]; exact hj)]
  have hc4_pc0 : (c4.work pIdx).cells 0 = Γ.start := by
    rw [hc4_pc_other 0 (by omega)]; exact hc3_pc0
  have hc4_pns : ∀ j, j ≥ 1 → (c4.work pIdx).cells j ≠ Γ.start := by
    intro j hj
    by_cases heq : j = 1 + 2 * x.length
    · rw [heq, hc4_pc_zero]; decide
    · rw [hc4_pc_other j heq]; exact hc3_pns j hj
  obtain ⟨c5, hstep5, hc5_state, hc5_inp, hc5_yw, hc5_ph, hc5_pc⟩ :=
    pairBuild_writeSep2_step yIdx pIdx hne c4 hc4_state
      hc4_ih_ge hc4_yh_ge hc4_ph_ge hc4_ins hc4_yns
  have hc5_ih_val : c5.input.head = 1 + x.length := by rw [hc5_inp]; exact hc4_ih_val
  have hc5_ic : c5.input.cells = c4.input.cells := by rw [hc5_inp]
  have hc5_ih_ge : c5.input.head ≥ 1 := by rw [hc5_ih_val]; omega
  have hc5_ic0 : c5.input.cells 0 = Γ.start := by rw [hc5_ic]; exact hc4_ic0
  have hc5_ins : ∀ j, j ≥ 1 → c5.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc5_ic]; exact hc4_ins j hj
  have hc5_yh_ge : (c5.work yIdx).head ≥ 1 := by rw [hc5_yw]; exact hc4_yh_ge
  have hc5_yw_cells : (c5.work yIdx).cells = (c4.work yIdx).cells := by rw [hc5_yw]
  have hc5_yns : ∀ j, j ≥ 1 → (c5.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc5_yw]; exact hc4_yns j hj
  have hc5_ph_val : (c5.work pIdx).head = 3 + 2 * x.length := by
    rw [hc5_ph, hc4_ph_val]
    omega
  have hc5_ph_ge : (c5.work pIdx).head ≥ 1 := by rw [hc5_ph_val]; omega
  have hc5_pc_one : (c5.work pIdx).cells (2 + 2 * x.length) = Γ.one := by
    rw [hc5_pc, ← hc4_ph_val, Function.update_self]
  have hc5_pc_other : ∀ j, j ≠ 2 + 2 * x.length →
      (c5.work pIdx).cells j = (c4.work pIdx).cells j := by
    intro j hj
    rw [hc5_pc, Function.update_of_ne (by rw [hc4_ph_val]; exact hj)]
  have hc5_pc0 : (c5.work pIdx).cells 0 = Γ.start := by
    rw [hc5_pc_other 0 (by omega)]; exact hc4_pc0
  have hc5_pns : ∀ j, j ≥ 1 → (c5.work pIdx).cells j ≠ Γ.start := by
    intro j hj
    by_cases heq : j = 2 + 2 * x.length
    · rw [heq, hc5_pc_one]; decide
    · rw [hc5_pc_other j heq]; exact hc4_pns j hj
  have hc5_yh_val : (c5.work yIdx).head = 1 := by
    rw [hc5_yw, hc4_yw, hc3_yw, hc2_yw, hc1_yh]
  have hc5_yw_cells_eq : (c5.work yIdx).cells =
      (Tape.init (y.map Γ.ofBool)).cells := by
    rw [hc5_yw_cells, hc4_yw_cells, hc3_yw_cells, hc2_yw, hc1_yc]
  have hc5_yw_data : ∀ i, i < y.length →
      (c5.work yIdx).cells ((c5.work yIdx).head + i) ≠ Γ.blank ∧
      (c5.work yIdx).cells ((c5.work yIdx).head + i) ≠ Γ.start := by
    intro i hi
    rw [hc5_yw_cells_eq, hc5_yh_val]
    have heq :
        (Tape.init (y.map Γ.ofBool)).cells (1 + i) = Γ.ofBool (y[i]'hi) := by
      rw [show 1 + i = i + 1 from by omega]
      exact Tape.init_ofBool_cells_lt y i hi
    exact ⟨by rw [heq]; exact Γ.ofBool_ne_blank _,
           by rw [heq]; exact Γ.ofBool_ne_start _⟩
  have hc5_yw_cell0 : (c5.work yIdx).cells 0 = Γ.start := by
    rw [hc5_yw_cells_eq]
    rfl
  obtain ⟨c6, hreach_copyY, hc6_state, hc6_inp, hc6_yh, hc6_yc, hc6_ph, hc6_pc0,
          hc6_pns, hc6_below, hc6_above, hc6_data⟩ :=
    pairBuild_copyY_loop yIdx pIdx hne y.length c5 hc5_state hc5_ih_ge
      hc5_ins hc5_yh_ge hc5_yw_cell0 hc5_yns hc5_yw_data hc5_ph_ge hc5_pc0 hc5_pns
  have hc6_yh_val : (c6.work yIdx).head = 1 + y.length := by
    rw [hc6_yh, hc5_yh_val]
  have hc6_ph_val : (c6.work pIdx).head = 3 + 2 * x.length + y.length := by
    rw [hc6_ph, hc5_ph_val]
  have hc6_ih_val : c6.input.head = 1 + x.length := by rw [hc6_inp]; exact hc5_ih_val
  have hc6_ih_ge : c6.input.head ≥ 1 := by rw [hc6_ih_val]; omega
  have hc6_yh_ge : (c6.work yIdx).head ≥ 1 := by rw [hc6_yh_val]; omega
  have hc6_ph_ge : (c6.work pIdx).head ≥ 1 := by rw [hc6_ph_val]; omega
  have hc6_ic : c6.input.cells = c5.input.cells := by rw [hc6_inp]
  have hc6_ic0 : c6.input.cells 0 = Γ.start := by rw [hc6_ic]; exact hc5_ic0
  have hc6_ins : ∀ j, j ≥ 1 → c6.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc6_ic]; exact hc5_ins j hj
  have hc6_yc_eq : (c6.work yIdx).cells = (c5.work yIdx).cells := hc6_yc
  have hc6_yns : ∀ j, j ≥ 1 → (c6.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc6_yc_eq]; exact hc5_yns j hj
  have hc6_yread : (c6.work yIdx).read = Γ.blank := by
    show (c6.work yIdx).cells (c6.work yIdx).head = Γ.blank
    rw [hc6_yc_eq, hc5_yw_cells_eq, hc6_yh_val]
    rw [show 1 + y.length = y.length + 1 from by omega]
    exact Tape.init_ofBool_cells_ge y y.length (le_refl _)
  obtain ⟨c7, hstep7, hc7_state, hc7_inp, hc7_yw, hc7_pw⟩ :=
    pairBuild_copyY_halt_step yIdx pIdx c6 hc6_state hc6_yread
      hc6_ih_ge hc6_yh_ge hc6_ph_ge hc6_ins hc6_yns hc6_pns
  have hc7_ih_val : c7.input.head = 1 + x.length := by rw [hc7_inp]; exact hc6_ih_val
  have hc7_ih_ge : c7.input.head ≥ 1 := by rw [hc7_ih_val]; omega
  have hc7_ic : c7.input.cells = c6.input.cells := by rw [hc7_inp]
  have hc7_ic0 : c7.input.cells 0 = Γ.start := by rw [hc7_ic]; exact hc6_ic0
  have hc7_ins : ∀ j, j ≥ 1 → c7.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc7_ic]; exact hc6_ins j hj
  have hc7_yh_ge : (c7.work yIdx).head ≥ 1 := by rw [hc7_yw]; exact hc6_yh_ge
  have hc7_yc : (c7.work yIdx).cells = (c6.work yIdx).cells := by rw [hc7_yw]
  have hc7_yns : ∀ j, j ≥ 1 → (c7.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc7_yw]; exact hc6_yns j hj
  have hc7_ph_val : (c7.work pIdx).head = 3 + 2 * x.length + y.length := by
    rw [hc7_pw]; exact hc6_ph_val
  have hc7_pc : (c7.work pIdx).cells = (c6.work pIdx).cells := by rw [hc7_pw]
  have hc7_ph_ge : (c7.work pIdx).head ≥ 1 := by rw [hc7_ph_val]; omega
  have hc7_pc0 : (c7.work pIdx).cells 0 = Γ.start := by rw [hc7_pc]; exact hc6_pc0
  have hc7_pns : ∀ j, j ≥ 1 → (c7.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc7_pw]; exact hc6_pns j hj
  obtain ⟨c8, hreach_rewind, hc8_state, hc8_inp, hc8_yw, hc8_ph, hc8_pc⟩ :=
    pairBuild_rewindP1_loop yIdx pIdx hne (3 + 2 * x.length + y.length) c7
      hc7_state hc7_ph_val hc7_pc0 hc7_pns hc7_ih_ge hc7_ins hc7_yh_ge hc7_yns
  have hc8_ih_val : c8.input.head = 1 + x.length := by rw [hc8_inp]; exact hc7_ih_val
  have hc8_ih_ge : c8.input.head ≥ 1 := by rw [hc8_ih_val]; omega
  have hc8_ic : c8.input.cells = c7.input.cells := by rw [hc8_inp]
  have hc8_ic0 : c8.input.cells 0 = Γ.start := by rw [hc8_ic]; exact hc7_ic0
  have hc8_ins : ∀ j, j ≥ 1 → c8.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc8_ic]; exact hc7_ins j hj
  have hc8_yh_ge : (c8.work yIdx).head ≥ 1 := by rw [hc8_yw]; exact hc7_yh_ge
  have hc8_yc : (c8.work yIdx).cells = (c7.work yIdx).cells := by rw [hc8_yw]
  have hc8_yns : ∀ j, j ≥ 1 → (c8.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc8_yw]; exact hc7_yns j hj
  have hc8_ph_ge : (c8.work pIdx).head ≥ 1 := by rw [hc8_ph]
  have hc8_pc_eq : (c8.work pIdx).cells = (c7.work pIdx).cells := hc8_pc
  have hc8_pc0 : (c8.work pIdx).cells 0 = Γ.start := by rw [hc8_pc_eq]; exact hc7_pc0
  have hc8_pns : ∀ j, j ≥ 1 → (c8.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc8_pc_eq]; exact hc7_pns j hj
  obtain ⟨c9, hstep9, hc9_state, _hc9_inp, _hc9_yw, hc9_pw⟩ :=
    pairBuild_rewindP2_step yIdx pIdx c8 hc8_state hc8_ih_ge hc8_yh_ge hc8_ph_ge
      hc8_ins hc8_yns hc8_pns
  have hc9_ph_val : (c9.work pIdx).head = 1 := by rw [hc9_pw]; exact hc8_ph
  have hc9_pc_via_c6 : (c9.work pIdx).cells = (c6.work pIdx).cells := by
    rw [hc9_pw, hc8_pc_eq, hc7_pc]
  have hreach_13 : (pairBuildTM yIdx pIdx).reachesIn (2 * x.length + 1) c1 c3 :=
    reachesIn_trans _ hreach_copyX (.step hstep3 .zero)
  have hreach_14 : (pairBuildTM yIdx pIdx).reachesIn (2 * x.length + 1 + 1) c1 c4 :=
    reachesIn_trans _ hreach_13 (.step hstep4 .zero)
  have hreach_15 : (pairBuildTM yIdx pIdx).reachesIn (2 * x.length + 1 + 1 + 1) c1 c5 :=
    reachesIn_trans _ hreach_14 (.step hstep5 .zero)
  have hreach_16 : (pairBuildTM yIdx pIdx).reachesIn
      (2 * x.length + 1 + 1 + 1 + y.length) c1 c6 :=
    reachesIn_trans _ hreach_15 hreach_copyY
  have hreach_17 : (pairBuildTM yIdx pIdx).reachesIn
      (2 * x.length + 1 + 1 + 1 + y.length + 1) c1 c7 :=
    reachesIn_trans _ hreach_16 (.step hstep7 .zero)
  have hreach_18 : (pairBuildTM yIdx pIdx).reachesIn
      (2 * x.length + 1 + 1 + 1 + y.length + 1 + (3 + 2 * x.length + y.length + 1))
      c1 c8 := reachesIn_trans _ hreach_17 hreach_rewind
  have hreach_19 : (pairBuildTM yIdx pIdx).reachesIn
      (2 * x.length + 1 + 1 + 1 + y.length + 1 + (3 + 2 * x.length + y.length + 1) + 1)
      c1 c9 := reachesIn_trans _ hreach_18 (.step hstep9 .zero)
  have hbound :
      2 * x.length + 1 + 1 + 1 + y.length + 1 + (3 + 2 * x.length + y.length + 1) + 1
        ≤ 4 * x.length + 2 * y.length + 9 := by
    omega
  refine ⟨c9, _, hbound, hreach_19, hc9_state, hc9_ph_val, ?_, ?_, ?_⟩
  · rw [hc9_pc_via_c6]; exact hc6_pc0
  · intro i hi
    rw [pair_length] at hi
    by_cases hx : i < 2 * x.length
    · have hdecomp : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
      have hidiv : i / 2 < x.length := by omega
      have hpair : (pair x y)[i]'(by rw [pair_length]; omega) = x[i / 2]'hidiv := by
        rcases hdecomp with hi_even | hi_odd
        · exact (getElem_congr_idx hi_even).trans
            (pair_getElem_doubled_even x y (i / 2) hidiv)
        · exact (getElem_congr_idx hi_odd).trans
            (pair_getElem_doubled_odd x y (i / 2) hidiv)
      have hi_c5 : i + 1 < 3 + 2 * x.length := by omega
      have hc6_at : (c6.work pIdx).cells (i + 1) = (c5.work pIdx).cells (i + 1) := by
        have := hc6_below (i + 1) (by rw [hc5_ph_val]; exact hi_c5)
        exact this
      have hc5_at : (c5.work pIdx).cells (i + 1) = (c4.work pIdx).cells (i + 1) :=
        hc5_pc_other (i + 1) (by omega)
      have hi_ne_ws1 : i + 1 ≠ 1 + 2 * x.length := by omega
      have hc4_at : (c4.work pIdx).cells (i + 1) = (c3.work pIdx).cells (i + 1) :=
        hc4_pc_other (i + 1) hi_ne_ws1
      rw [hc9_pc_via_c6, hc6_at, hc5_at, hc4_at, hc3_pw_cells]
      rw [hpair]
      obtain ⟨heven, hodd⟩ := hc2_data (i / 2) hidiv
      rcases hdecomp with hi_even | hi_odd
      · have hheq : (c1.work pIdx).head + 2 * (i / 2) = i + 1 := by rw [hc1_ph]; omega
        rw [← hheq, heven]
        rw [hc1_ic, hc1_ih]
        rw [show 1 + (i / 2) = (i / 2) + 1 from by omega]
        exact Tape.init_ofBool_cells_lt x (i / 2) hidiv
      · have hheq : (c1.work pIdx).head + 2 * (i / 2) + 1 = i + 1 := by
          rw [hc1_ph]; omega
        rw [← hheq, hodd]
        rw [hc1_ic, hc1_ih]
        rw [show 1 + (i / 2) = (i / 2) + 1 from by omega]
        exact Tape.init_ofBool_cells_lt x (i / 2) hidiv
    · push Not at hx
      by_cases hx2 : i = 2 * x.length
      · subst hx2
        have hpair : (pair x y)[2 * x.length]'(by rw [pair_length]; omega) = false :=
          pair_getElem_sep0 x y
        rw [hpair]
        rw [hc9_pc_via_c6]
        have hi_c5 : 2 * x.length + 1 < 3 + 2 * x.length := by omega
        rw [hc6_below (2 * x.length + 1) (by rw [hc5_ph_val]; exact hi_c5)]
        rw [hc5_pc_other (2 * x.length + 1) (by omega)]
        have : 2 * x.length + 1 = 1 + 2 * x.length := by omega
        rw [this, hc4_pc_zero]
        rfl
      · by_cases hx3 : i = 2 * x.length + 1
        · subst hx3
          have hpair : (pair x y)[2 * x.length + 1]'(by rw [pair_length]; omega) = true :=
            pair_getElem_sep1 x y
          rw [hpair]
          rw [hc9_pc_via_c6]
          have hi_c5 : 2 * x.length + 1 + 1 < 3 + 2 * x.length := by omega
          rw [hc6_below (2 * x.length + 1 + 1) (by rw [hc5_ph_val]; exact hi_c5)]
          have : 2 * x.length + 1 + 1 = 2 + 2 * x.length := by omega
          rw [this, hc5_pc_one]
          rfl
        · have hi_lo : i ≥ 2 * x.length + 2 := by omega
          set j := i - 2 * x.length - 2 with hj_def
          have hi_eq : i = 2 * x.length + 2 + j := by omega
          have hj_lt : j < y.length := by omega
          have hpair : (pair x y)[i]'(by rw [pair_length]; omega) = y[j]'hj_lt := by
            exact (getElem_congr_idx hi_eq).trans (pair_getElem_y x y j hj_lt)
          rw [hpair]
          rw [hc9_pc_via_c6]
          have hheq : (c5.work pIdx).head + j = i + 1 := by rw [hc5_ph_val]; omega
          rw [← hheq]
          rw [hc6_data j hj_lt]
          rw [hc5_yw_cells_eq, hc5_yh_val]
          rw [show 1 + j = j + 1 from by omega]
          exact Tape.init_ofBool_cells_lt y j hj_lt
  · intro i hi_tail
    rw [pair_length] at hi_tail
    rw [hc9_pc_via_c6]
    have hi_above : i + 1 ≥ (c5.work pIdx).head + y.length := by
      rw [hc5_ph_val]; omega
    rw [hc6_above _ hi_above]
    rw [hc5_pc_other _ (by omega)]
    rw [hc4_pc_other _ (by omega)]
    rw [hc3_pw_cells]
    have hi_c2 : i + 1 ≥ (c1.work pIdx).head + 2 * x.length := by
      rw [hc1_ph]; omega
    rw [hc2_above _ hi_c2]
    rw [hc1_pc]
    exact Tape.init_nil_cells_succ i

/-- **`pairBuildTM` correctness.** Given `x` on the input tape and `y` on
    work tape `yIdx` (with `yIdx ≠ pIdx`), `pairBuildTM yIdx pIdx` halts
    leaving work tape `pIdx` carrying `pair x y` (in the cells indexed
    `1..|pair x y|`), blank thereafter, with head at cell `1`, within
    `pairBuildTime` steps. -/
theorem pairBuildTM_hoareTime
    {k : ℕ} (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx)
    (x y : List Bool) :
    (pairBuildTM yIdx pIdx).HoareTime
      (fun inp work _ =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work yIdx = Tape.init (y.map Γ.ofBool) ∧
        work pIdx = Tape.init [])
      (fun _ work _ =>
        (work pIdx).head = 1 ∧
        (work pIdx).cells 0 = Γ.start ∧
        (∀ i : ℕ, (h : i < (pair x y).length) →
          (work pIdx).cells (i + 1) = Γ.ofBool ((pair x y)[i]'h)) ∧
        (∀ i : ℕ, (pair x y).length ≤ i →
          (work pIdx).cells (i + 1) = Γ.blank))
      (pairBuildTime x.length y.length) := by
  intro inp work out ⟨hinp, hyw, hpw⟩
  -- c0 = initial configuration. Unfold using the starting tapes.
  let c0 : Cfg k (pairBuildTM yIdx pIdx).Q :=
    { state := (pairBuildTM yIdx pIdx).qstart, input := inp, work := work, output := out }
  -- Tape facts derived from the preconditions.
  have hc0_input_head : c0.input.head = 0 := by
    show inp.head = 0; rw [hinp]; rfl
  have hc0_input_cell0 : c0.input.cells 0 = Γ.start := by
    show inp.cells 0 = _; rw [hinp]; rfl
  have hc0_input_ns : ∀ j, j ≥ 1 → c0.input.cells j ≠ Γ.start := by
    intro j hj; show inp.cells j ≠ _; rw [hinp]
    exact Tape.init_ofBool_cells_ne_start x j hj
  have hc0_yw_head : (c0.work yIdx).head = 0 := by
    show (work yIdx).head = 0; rw [hyw]; rfl
  have hc0_yw_cell0 : (c0.work yIdx).cells 0 = Γ.start := by
    show (work yIdx).cells 0 = _; rw [hyw]; rfl
  have hc0_yw_ns : ∀ j, j ≥ 1 → (c0.work yIdx).cells j ≠ Γ.start := by
    intro j hj; show (work yIdx).cells j ≠ _; rw [hyw]
    exact Tape.init_ofBool_cells_ne_start y j hj
  have hc0_pw_head : (c0.work pIdx).head = 0 := by
    show (work pIdx).head = 0; rw [hpw]; rfl
  have hc0_pw_cell0 : (c0.work pIdx).cells 0 = Γ.start := by
    show (work pIdx).cells 0 = _; rw [hpw]; rfl
  have hc0_pw_cells : ∀ j, (c0.work pIdx).cells j =
      (if j = 0 then Γ.start else Γ.blank) := by
    intro j
    show (work pIdx).cells j = _
    rw [hpw]
    show (if j = 0 then Γ.start else ([][j - 1]?).getD Γ.blank) = _
    split
    · rfl
    · simp
  have hc0_pw_ns : ∀ j, j ≥ 1 → (c0.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc0_pw_cells]; simp [show j ≠ 0 from by omega]
  have hc0_state : c0.state = .init := rfl
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 1: init step (1 step)
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c1, hstep_init, hc1_state, hc1_ih, hc1_ic, hc1_yh, hc1_yc, hc1_ph, hc1_pc⟩ :=
    pairBuild_init_step yIdx pIdx c0 hc0_state hc0_input_head hc0_input_cell0
      hc0_yw_head hc0_yw_cell0 hc0_pw_head hc0_pw_cell0
  -- Invariants for c1.
  have hc1_ih_ge : c1.input.head ≥ 1 := by rw [hc1_ih]
  have hc1_yh_ge : (c1.work yIdx).head ≥ 1 := by rw [hc1_yh]
  have hc1_ph_ge : (c1.work pIdx).head ≥ 1 := by rw [hc1_ph]
  have hc1_ic0 : c1.input.cells 0 = Γ.start := by rw [hc1_ic]; exact hc0_input_cell0
  have hc1_ins : ∀ j, j ≥ 1 → c1.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc1_ic]; exact hc0_input_ns j hj
  have hc1_yns : ∀ j, j ≥ 1 → (c1.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc1_yc]; exact hc0_yw_ns j hj
  have hc1_pc0 : (c1.work pIdx).cells 0 = Γ.start := by rw [hc1_pc]; exact hc0_pw_cell0
  have hc1_pns : ∀ j, j ≥ 1 → (c1.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc1_pc]; exact hc0_pw_ns j hj
  -- The x-input data bits ahead of c1.input.head.
  have hc1_input_data : ∀ i, i < x.length →
      c1.input.cells (c1.input.head + i) ≠ Γ.blank ∧
      c1.input.cells (c1.input.head + i) ≠ Γ.start := by
    intro i hi
    rw [hc1_ic, hc1_ih]
    show c0.input.cells (1 + i) ≠ Γ.blank ∧ c0.input.cells (1 + i) ≠ Γ.start
    have heq : c0.input.cells (1 + i) = Γ.ofBool (x[i]'hi) := by
      show inp.cells _ = _
      rw [hinp, show 1 + i = i + 1 from by omega]
      exact Tape.init_ofBool_cells_lt x i hi
    refine ⟨?_, ?_⟩
    · rw [heq]; exact Γ.ofBool_ne_blank _
    · rw [heq]; exact Γ.ofBool_ne_start _
  -- The y-data bits ahead of c1.work yIdx head.
  have hc1_yw_data : ∀ i, i < y.length →
      (c1.work yIdx).cells ((c1.work yIdx).head + i) ≠ Γ.blank ∧
      (c1.work yIdx).cells ((c1.work yIdx).head + i) ≠ Γ.start := by
    intro i hi
    rw [hc1_yc, hc1_yh]
    show (c0.work yIdx).cells (1 + i) ≠ Γ.blank ∧ (c0.work yIdx).cells (1 + i) ≠ Γ.start
    have heq : (c0.work yIdx).cells (1 + i) = Γ.ofBool (y[i]'hi) := by
      show (work yIdx).cells _ = _
      rw [hyw, show 1 + i = i + 1 from by omega]
      exact Tape.init_ofBool_cells_lt y i hi
    refine ⟨?_, ?_⟩
    · rw [heq]; exact Γ.ofBool_ne_blank _
    · rw [heq]; exact Γ.ofBool_ne_start _
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 2: copyX loop (2|x| steps)
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c2, hreach_copyX, hc2_state, hc2_ic, hc2_ih, hc2_yw, hc2_ph, hc2_pc0,
          hc2_pns, hc2_below, hc2_above, hc2_data⟩ :=
    pairBuild_copyX_loop yIdx pIdx hne x.length c1 hc1_state hc1_ih_ge hc1_ic0
      hc1_ins hc1_input_data hc1_yh_ge hc1_yns hc1_ph_ge hc1_pc0 hc1_pns
  -- Derived c2 invariants.
  have hc2_ih_val : c2.input.head = 1 + x.length := by rw [hc2_ih, hc1_ih]
  have hc2_ph_val : (c2.work pIdx).head = 1 + 2 * x.length := by
    rw [hc2_ph, hc1_ph]
  have hc2_ih_ge : c2.input.head ≥ 1 := by rw [hc2_ih_val]; omega
  have hc2_yh_ge : (c2.work yIdx).head ≥ 1 := by rw [hc2_yw]; exact hc1_yh_ge
  have hc2_ph_ge : (c2.work pIdx).head ≥ 1 := by rw [hc2_ph_val]; omega
  have hc2_ic0 : c2.input.cells 0 = Γ.start := by rw [hc2_ic]; exact hc1_ic0
  have hc2_ins : ∀ j, j ≥ 1 → c2.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc2_ic]; exact hc1_ins j hj
  have hc2_yns : ∀ j, j ≥ 1 → (c2.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc2_yw]; exact hc1_yns j hj
  -- c2 reads blank on input: cells at (1+|x|) = cells at (x.length + 1).
  have hc2_iread : c2.input.read = Γ.blank := by
    show c2.input.cells c2.input.head = Γ.blank
    rw [hc2_ic, hc1_ic, hc2_ih_val]
    show inp.cells _ = _
    rw [hinp, show 1 + x.length = x.length + 1 from by omega]
    exact Tape.init_ofBool_cells_ge x x.length (le_refl _)
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 3: copyX1 halt (1 step) -- all tapes stable
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c3, hstep3, hc3_state, hc3_inp, hc3_yw, hc3_pw⟩ :=
    pairBuild_copyX1_halt_step yIdx pIdx c2 hc2_state hc2_iread
      hc2_ih_ge hc2_yh_ge hc2_ph_ge hc2_ins hc2_yns hc2_pns
  have hc3_ih : c3.input.head = 1 + x.length := by rw [hc3_inp]; exact hc2_ih_val
  have hc3_ic : c3.input.cells = c2.input.cells := by rw [hc3_inp]
  have hc3_ih_ge : c3.input.head ≥ 1 := by rw [hc3_ih]; omega
  have hc3_ic0 : c3.input.cells 0 = Γ.start := by rw [hc3_ic]; exact hc2_ic0
  have hc3_ins : ∀ j, j ≥ 1 → c3.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc3_ic]; exact hc2_ins j hj
  have hc3_yw_head : (c3.work yIdx).head ≥ 1 := by rw [hc3_yw]; exact hc2_yh_ge
  have hc3_yw_cells : (c3.work yIdx).cells = (c2.work yIdx).cells := by rw [hc3_yw]
  have hc3_yns : ∀ j, j ≥ 1 → (c3.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc3_yw]; exact hc2_yns j hj
  have hc3_pw_head : (c3.work pIdx).head = 1 + 2 * x.length := by
    rw [hc3_pw]; exact hc2_ph_val
  have hc3_pw_cells : (c3.work pIdx).cells = (c2.work pIdx).cells := by rw [hc3_pw]
  have hc3_ph_ge : (c3.work pIdx).head ≥ 1 := by rw [hc3_pw_head]; omega
  have hc3_pc0 : (c3.work pIdx).cells 0 = Γ.start := by rw [hc3_pw_cells]; exact hc2_pc0
  have hc3_pns : ∀ j, j ≥ 1 → (c3.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc3_pw]; exact hc2_pns j hj
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 4: writeSep1 → writeSep2 (1 step)
  -- Writes Γ.zero at pIdx head (= 1 + 2|x|).
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c4, hstep4, hc4_state, hc4_inp, hc4_yw, hc4_ph, hc4_pc⟩ :=
    pairBuild_writeSep1_step yIdx pIdx hne c3 hc3_state
      hc3_ih_ge hc3_yw_head hc3_ph_ge hc3_ins hc3_yns
  have hc4_ih_val : c4.input.head = 1 + x.length := by rw [hc4_inp]; exact hc3_ih
  have hc4_ic : c4.input.cells = c3.input.cells := by rw [hc4_inp]
  have hc4_ih_ge : c4.input.head ≥ 1 := by rw [hc4_ih_val]; omega
  have hc4_ic0 : c4.input.cells 0 = Γ.start := by rw [hc4_ic]; exact hc3_ic0
  have hc4_ins : ∀ j, j ≥ 1 → c4.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc4_ic]; exact hc3_ins j hj
  have hc4_yh_ge : (c4.work yIdx).head ≥ 1 := by rw [hc4_yw]; exact hc3_yw_head
  have hc4_yw_cells : (c4.work yIdx).cells = (c3.work yIdx).cells := by rw [hc4_yw]
  have hc4_yns : ∀ j, j ≥ 1 → (c4.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc4_yw]; exact hc3_yns j hj
  have hc4_ph_val : (c4.work pIdx).head = 2 + 2 * x.length := by
    rw [hc4_ph, hc3_pw_head]; omega
  have hc4_ph_ge : (c4.work pIdx).head ≥ 1 := by rw [hc4_ph_val]; omega
  -- c4.pIdx.cells at position (1 + 2|x|) has Γ.zero; other positions from c3.
  have hc4_pc_zero : (c4.work pIdx).cells (1 + 2 * x.length) = Γ.zero := by
    rw [hc4_pc, ← hc3_pw_head, Function.update_self]
  have hc4_pc_other : ∀ j, j ≠ 1 + 2 * x.length →
      (c4.work pIdx).cells j = (c3.work pIdx).cells j := by
    intro j hj
    rw [hc4_pc, Function.update_of_ne (by rw [hc3_pw_head]; exact hj)]
  have hc4_pc0 : (c4.work pIdx).cells 0 = Γ.start := by
    rw [hc4_pc_other 0 (by omega)]; exact hc3_pc0
  have hc4_pns : ∀ j, j ≥ 1 → (c4.work pIdx).cells j ≠ Γ.start := by
    intro j hj
    by_cases heq : j = 1 + 2 * x.length
    · rw [heq, hc4_pc_zero]; decide
    · rw [hc4_pc_other j heq]; exact hc3_pns j hj
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 5: writeSep2 → copyY (1 step)
  -- Writes Γ.one at pIdx head (= 2 + 2|x|).
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c5, hstep5, hc5_state, hc5_inp, hc5_yw, hc5_ph, hc5_pc⟩ :=
    pairBuild_writeSep2_step yIdx pIdx hne c4 hc4_state
      hc4_ih_ge hc4_yh_ge hc4_ph_ge hc4_ins hc4_yns
  have hc5_ih_val : c5.input.head = 1 + x.length := by rw [hc5_inp]; exact hc4_ih_val
  have hc5_ic : c5.input.cells = c4.input.cells := by rw [hc5_inp]
  have hc5_ih_ge : c5.input.head ≥ 1 := by rw [hc5_ih_val]; omega
  have hc5_ic0 : c5.input.cells 0 = Γ.start := by rw [hc5_ic]; exact hc4_ic0
  have hc5_ins : ∀ j, j ≥ 1 → c5.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc5_ic]; exact hc4_ins j hj
  have hc5_yh_ge : (c5.work yIdx).head ≥ 1 := by rw [hc5_yw]; exact hc4_yh_ge
  have hc5_yw_cells : (c5.work yIdx).cells = (c4.work yIdx).cells := by rw [hc5_yw]
  have hc5_yns : ∀ j, j ≥ 1 → (c5.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc5_yw]; exact hc4_yns j hj
  have hc5_ph_val : (c5.work pIdx).head = 3 + 2 * x.length := by
    rw [hc5_ph, hc4_ph_val]; omega
  have hc5_ph_ge : (c5.work pIdx).head ≥ 1 := by rw [hc5_ph_val]; omega
  have hc5_pc_one : (c5.work pIdx).cells (2 + 2 * x.length) = Γ.one := by
    rw [hc5_pc, ← hc4_ph_val, Function.update_self]
  have hc5_pc_other : ∀ j, j ≠ 2 + 2 * x.length →
      (c5.work pIdx).cells j = (c4.work pIdx).cells j := by
    intro j hj
    rw [hc5_pc, Function.update_of_ne (by rw [hc4_ph_val]; exact hj)]
  have hc5_pc0 : (c5.work pIdx).cells 0 = Γ.start := by
    rw [hc5_pc_other 0 (by omega)]; exact hc4_pc0
  have hc5_pns : ∀ j, j ≥ 1 → (c5.work pIdx).cells j ≠ Γ.start := by
    intro j hj
    by_cases heq : j = 2 + 2 * x.length
    · rw [heq, hc5_pc_one]; decide
    · rw [hc5_pc_other j heq]; exact hc4_pns j hj
  -- c5.work yIdx reads y[0] at head = 1; or blank if y is empty.
  -- We need hc5_yw_data: the y-data bits ahead of c5.work yIdx head = 1.
  have hc5_yh_val : (c5.work yIdx).head = 1 := by
    rw [hc5_yw, hc4_yw, hc3_yw, hc2_yw, hc1_yh]
  have hc5_yw_cells_eq : (c5.work yIdx).cells = (c0.work yIdx).cells := by
    rw [hc5_yw_cells, hc4_yw_cells, hc3_yw_cells, hc2_yw, hc1_yc]
  have hc5_yw_data : ∀ i, i < y.length →
      (c5.work yIdx).cells ((c5.work yIdx).head + i) ≠ Γ.blank ∧
      (c5.work yIdx).cells ((c5.work yIdx).head + i) ≠ Γ.start := by
    intro i hi
    rw [hc5_yw_cells_eq, hc5_yh_val]
    show (work yIdx).cells (1 + i) ≠ Γ.blank ∧ (work yIdx).cells (1 + i) ≠ Γ.start
    have heq : (work yIdx).cells (1 + i) = Γ.ofBool (y[i]'hi) := by
      rw [hyw, show 1 + i = i + 1 from by omega]
      exact Tape.init_ofBool_cells_lt y i hi
    exact ⟨by rw [heq]; exact Γ.ofBool_ne_blank _,
           by rw [heq]; exact Γ.ofBool_ne_start _⟩
  have hc5_yw_cell0 : (c5.work yIdx).cells 0 = Γ.start := by
    rw [hc5_yw_cells_eq]; exact hc0_yw_cell0
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 6: copyY loop (|y| steps)
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c6, hreach_copyY, hc6_state, hc6_inp, hc6_yh, hc6_yc, hc6_ph, hc6_pc0,
          hc6_pns, hc6_below, hc6_above, hc6_data⟩ :=
    pairBuild_copyY_loop yIdx pIdx hne y.length c5 hc5_state hc5_ih_ge
      hc5_ins hc5_yh_ge hc5_yw_cell0 hc5_yns hc5_yw_data hc5_ph_ge hc5_pc0 hc5_pns
  -- Derived c6 invariants.
  have hc6_yh_val : (c6.work yIdx).head = 1 + y.length := by
    rw [hc6_yh, hc5_yh_val]
  have hc6_ph_val : (c6.work pIdx).head = 3 + 2 * x.length + y.length := by
    rw [hc6_ph, hc5_ph_val]
  have hc6_ih_val : c6.input.head = 1 + x.length := by rw [hc6_inp]; exact hc5_ih_val
  have hc6_ih_ge : c6.input.head ≥ 1 := by rw [hc6_ih_val]; omega
  have hc6_yh_ge : (c6.work yIdx).head ≥ 1 := by rw [hc6_yh_val]; omega
  have hc6_ph_ge : (c6.work pIdx).head ≥ 1 := by rw [hc6_ph_val]; omega
  have hc6_ic : c6.input.cells = c5.input.cells := by rw [hc6_inp]
  have hc6_ic0 : c6.input.cells 0 = Γ.start := by rw [hc6_ic]; exact hc5_ic0
  have hc6_ins : ∀ j, j ≥ 1 → c6.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc6_ic]; exact hc5_ins j hj
  have hc6_yc_eq : (c6.work yIdx).cells = (c5.work yIdx).cells := hc6_yc
  have hc6_yns : ∀ j, j ≥ 1 → (c6.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc6_yc_eq]; exact hc5_yns j hj
  -- c6 reads blank on work yIdx: cells at (1 + y.length).
  have hc6_yread : (c6.work yIdx).read = Γ.blank := by
    show (c6.work yIdx).cells (c6.work yIdx).head = Γ.blank
    rw [hc6_yc_eq, hc5_yw_cells_eq, hc6_yh_val]
    show (work yIdx).cells _ = _
    rw [hyw, show 1 + y.length = y.length + 1 from by omega]
    exact Tape.init_ofBool_cells_ge y y.length (le_refl _)
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 7: copyY halt (1 step) — all tapes stable.
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c7, hstep7, hc7_state, hc7_inp, hc7_yw, hc7_pw⟩ :=
    pairBuild_copyY_halt_step yIdx pIdx c6 hc6_state hc6_yread
      hc6_ih_ge hc6_yh_ge hc6_ph_ge hc6_ins hc6_yns hc6_pns
  have hc7_ih_val : c7.input.head = 1 + x.length := by rw [hc7_inp]; exact hc6_ih_val
  have hc7_ih_ge : c7.input.head ≥ 1 := by rw [hc7_ih_val]; omega
  have hc7_ic : c7.input.cells = c6.input.cells := by rw [hc7_inp]
  have hc7_ic0 : c7.input.cells 0 = Γ.start := by rw [hc7_ic]; exact hc6_ic0
  have hc7_ins : ∀ j, j ≥ 1 → c7.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc7_ic]; exact hc6_ins j hj
  have hc7_yh_ge : (c7.work yIdx).head ≥ 1 := by rw [hc7_yw]; exact hc6_yh_ge
  have hc7_yc : (c7.work yIdx).cells = (c6.work yIdx).cells := by rw [hc7_yw]
  have hc7_yns : ∀ j, j ≥ 1 → (c7.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc7_yw]; exact hc6_yns j hj
  have hc7_ph_val : (c7.work pIdx).head = 3 + 2 * x.length + y.length := by
    rw [hc7_pw]; exact hc6_ph_val
  have hc7_pc : (c7.work pIdx).cells = (c6.work pIdx).cells := by rw [hc7_pw]
  have hc7_ph_ge : (c7.work pIdx).head ≥ 1 := by rw [hc7_ph_val]; omega
  have hc7_pc0 : (c7.work pIdx).cells 0 = Γ.start := by rw [hc7_pc]; exact hc6_pc0
  have hc7_pns : ∀ j, j ≥ 1 → (c7.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc7_pw]; exact hc6_pns j hj
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 8: rewindP1 loop (p + 1 = 4 + 2|x| + |y| steps)
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c8, hreach_rewind, hc8_state, hc8_inp, hc8_yw, hc8_ph, hc8_pc⟩ :=
    pairBuild_rewindP1_loop yIdx pIdx hne (3 + 2 * x.length + y.length) c7
      hc7_state hc7_ph_val hc7_pc0 hc7_pns hc7_ih_ge hc7_ins hc7_yh_ge hc7_yns
  have hc8_ih_val : c8.input.head = 1 + x.length := by rw [hc8_inp]; exact hc7_ih_val
  have hc8_ih_ge : c8.input.head ≥ 1 := by rw [hc8_ih_val]; omega
  have hc8_ic : c8.input.cells = c7.input.cells := by rw [hc8_inp]
  have hc8_ic0 : c8.input.cells 0 = Γ.start := by rw [hc8_ic]; exact hc7_ic0
  have hc8_ins : ∀ j, j ≥ 1 → c8.input.cells j ≠ Γ.start := by
    intro j hj; rw [hc8_ic]; exact hc7_ins j hj
  have hc8_yh_ge : (c8.work yIdx).head ≥ 1 := by rw [hc8_yw]; exact hc7_yh_ge
  have hc8_yc : (c8.work yIdx).cells = (c7.work yIdx).cells := by rw [hc8_yw]
  have hc8_yns : ∀ j, j ≥ 1 → (c8.work yIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc8_yw]; exact hc7_yns j hj
  have hc8_ph_ge : (c8.work pIdx).head ≥ 1 := by rw [hc8_ph]
  have hc8_pc_eq : (c8.work pIdx).cells = (c7.work pIdx).cells := hc8_pc
  have hc8_pc0 : (c8.work pIdx).cells 0 = Γ.start := by rw [hc8_pc_eq]; exact hc7_pc0
  have hc8_pns : ∀ j, j ≥ 1 → (c8.work pIdx).cells j ≠ Γ.start := by
    intro j hj; rw [hc8_pc_eq]; exact hc7_pns j hj
  -- ═══════════════════════════════════════════════════════════════════
  -- Phase 9: rewindP2 → done (1 step).
  -- ═══════════════════════════════════════════════════════════════════
  obtain ⟨c9, hstep9, hc9_state, hc9_inp, hc9_yw, hc9_pw⟩ :=
    pairBuild_rewindP2_step yIdx pIdx c8 hc8_state hc8_ih_ge hc8_yh_ge hc8_ph_ge
      hc8_ins hc8_yns hc8_pns
  -- c9 invariants: head = 1 on pIdx, state = .done, tapes same as c8.
  have hc9_ph_val : (c9.work pIdx).head = 1 := by rw [hc9_pw]; exact hc8_ph
  have hc9_pc_via_c6 : (c9.work pIdx).cells = (c6.work pIdx).cells := by
    rw [hc9_pw, hc8_pc_eq, hc7_pc]
  -- ═══════════════════════════════════════════════════════════════════
  -- Assemble the reachesIn chain.
  -- ═══════════════════════════════════════════════════════════════════
  have hreach_01 : (pairBuildTM yIdx pIdx).reachesIn 1 c0 c1 := .step hstep_init .zero
  have hreach_02 : (pairBuildTM yIdx pIdx).reachesIn (1 + 2 * x.length) c0 c2 :=
    reachesIn_trans _ hreach_01 hreach_copyX
  have hreach_03 : (pairBuildTM yIdx pIdx).reachesIn (1 + 2 * x.length + 1) c0 c3 :=
    reachesIn_trans _ hreach_02 (.step hstep3 .zero)
  have hreach_04 : (pairBuildTM yIdx pIdx).reachesIn (1 + 2 * x.length + 1 + 1) c0 c4 :=
    reachesIn_trans _ hreach_03 (.step hstep4 .zero)
  have hreach_05 : (pairBuildTM yIdx pIdx).reachesIn (1 + 2 * x.length + 1 + 1 + 1) c0 c5 :=
    reachesIn_trans _ hreach_04 (.step hstep5 .zero)
  have hreach_06 : (pairBuildTM yIdx pIdx).reachesIn
      (1 + 2 * x.length + 1 + 1 + 1 + y.length) c0 c6 :=
    reachesIn_trans _ hreach_05 hreach_copyY
  have hreach_07 : (pairBuildTM yIdx pIdx).reachesIn
      (1 + 2 * x.length + 1 + 1 + 1 + y.length + 1) c0 c7 :=
    reachesIn_trans _ hreach_06 (.step hstep7 .zero)
  have hreach_08 : (pairBuildTM yIdx pIdx).reachesIn
      (1 + 2 * x.length + 1 + 1 + 1 + y.length + 1 + (3 + 2 * x.length + y.length + 1))
      c0 c8 := reachesIn_trans _ hreach_07 hreach_rewind
  have hreach_09 : (pairBuildTM yIdx pIdx).reachesIn
      (1 + 2 * x.length + 1 + 1 + 1 + y.length + 1 + (3 + 2 * x.length + y.length + 1) + 1)
      c0 c9 := reachesIn_trans _ hreach_08 (.step hstep9 .zero)
  have hbound :
      1 + 2 * x.length + 1 + 1 + 1 + y.length + 1 + (3 + 2 * x.length + y.length + 1) + 1
        ≤ pairBuildTime x.length y.length := by
    show _ ≤ 4 * x.length + 2 * y.length + 10; omega
  have hhalted : (pairBuildTM yIdx pIdx).halted c9 := hc9_state
  refine ⟨c9, _, hbound, hreach_09, hhalted, hc9_ph_val, ?_, ?_, ?_⟩
  · -- (work pIdx).cells 0 = Γ.start
    rw [hc9_pc_via_c6]; exact hc6_pc0
  · -- (work pIdx).cells (i + 1) = Γ.ofBool (pair x y)[i] for i < |pair x y|
    intro i hi
    rw [pair_length] at hi
    -- Three case ranges: [0, 2|x|), {2|x|}, {2|x|+1}, [2|x|+2, 2|x|+2+|y|).
    by_cases hx : i < 2 * x.length
    · -- Case 1: i < 2|x|. Use hc2_data via hc6_below chain.
      have hdecomp : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
      have hidiv : i / 2 < x.length := by omega
      have hpair : (pair x y)[i]'(by rw [pair_length]; omega) = x[i / 2]'hidiv := by
        rcases hdecomp with hi_even | hi_odd
        · exact (getElem_congr_idx hi_even).trans
            (pair_getElem_doubled_even x y (i / 2) hidiv)
        · exact (getElem_congr_idx hi_odd).trans
            (pair_getElem_doubled_odd x y (i / 2) hidiv)
      -- i + 1 < c5.pIdx.head = 3 + 2|x|, so hc6_below applies.
      have hi_c5 : i + 1 < 3 + 2 * x.length := by omega
      have hc6_at : (c6.work pIdx).cells (i + 1) = (c5.work pIdx).cells (i + 1) := by
        have := hc6_below (i + 1) (by rw [hc5_ph_val]; exact hi_c5)
        exact this
      -- i + 1 ≠ 2 + 2|x| and ≠ 1 + 2|x|, so c5 → c4 → c3 chain stable.
      have hc5_at : (c5.work pIdx).cells (i + 1) = (c4.work pIdx).cells (i + 1) :=
        hc5_pc_other (i + 1) (by omega)
      -- Further decompose: i+1 = 1+2|x| iff i = 2|x|. But we have i < 2|x|, so ≠.
      have hi_ne_ws1 : i + 1 ≠ 1 + 2 * x.length := by omega
      have hc4_at : (c4.work pIdx).cells (i + 1) = (c3.work pIdx).cells (i + 1) :=
        hc4_pc_other (i + 1) hi_ne_ws1
      -- c3.pc = c2.pc, and use hc2_data.
      rw [hc9_pc_via_c6, hc6_at, hc5_at, hc4_at, hc3_pw_cells]
      -- Now goal: c2.cells[i+1] = Γ.ofBool (pair x y)[i]
      rw [hpair]
      -- Use hc2_data on i/2.
      obtain ⟨heven, hodd⟩ := hc2_data (i / 2) hidiv
      rcases hdecomp with hi_even | hi_odd
      · -- i = 2 * (i/2): cell at i+1 = c1.pIdx.head + 2*(i/2) + 1? No wait.
        -- c1.pIdx.head + 2*(i/2) = 1 + 2*(i/2) = i + 1 (since i = 2*(i/2)).
        have hheq : (c1.work pIdx).head + 2 * (i / 2) = i + 1 := by rw [hc1_ph]; omega
        rw [← hheq, heven]
        -- Now: c1.input.cells (c1.input.head + i/2) = Γ.ofBool x[i/2]
        rw [hc1_ic, hc1_ih]
        show c0.input.cells (1 + (i / 2)) = Γ.ofBool (x[i / 2]'hidiv)
        show inp.cells _ = _
        rw [hinp, show 1 + (i / 2) = (i / 2) + 1 from by omega]
        exact Tape.init_ofBool_cells_lt x (i / 2) hidiv
      · -- i = 2*(i/2) + 1: cell at i+1 = c1.pIdx.head + 2*(i/2) + 1 + 1.
        -- c1.pIdx.head + 2*(i/2) + 1 = 1 + 2*(i/2) + 1 = i + 1.
        have hheq : (c1.work pIdx).head + 2 * (i / 2) + 1 = i + 1 := by rw [hc1_ph]; omega
        rw [← hheq, hodd]
        rw [hc1_ic, hc1_ih]
        show c0.input.cells (1 + (i / 2)) = Γ.ofBool (x[i / 2]'hidiv)
        show inp.cells _ = _
        rw [hinp, show 1 + (i / 2) = (i / 2) + 1 from by omega]
        exact Tape.init_ofBool_cells_lt x (i / 2) hidiv
    · -- i ≥ 2|x|. Two subcases: i = 2|x|, i = 2|x|+1, or i ≥ 2|x|+2.
      push Not at hx
      by_cases hx2 : i = 2 * x.length
      · -- Case 2: i = 2|x|. pair[2|x|] = false = Γ.ofBool false.
        subst hx2
        have hpair : (pair x y)[2 * x.length]'(by rw [pair_length]; omega) = false :=
          pair_getElem_sep0 x y
        rw [hpair]
        -- cells at 2|x|+1 via c5 → c4 at position 1+2|x|.
        rw [hc9_pc_via_c6]
        have hi_c5 : 2 * x.length + 1 < 3 + 2 * x.length := by omega
        rw [hc6_below (2 * x.length + 1) (by rw [hc5_ph_val]; exact hi_c5)]
        rw [hc5_pc_other (2 * x.length + 1) (by omega)]
        -- c4.cells[2|x|+1] = c4.cells[1+2|x|] = Γ.zero
        have : 2 * x.length + 1 = 1 + 2 * x.length := by omega
        rw [this, hc4_pc_zero]
        rfl
      · by_cases hx3 : i = 2 * x.length + 1
        · -- Case 3: i = 2|x| + 1. pair[2|x|+1] = true.
          subst hx3
          have hpair : (pair x y)[2 * x.length + 1]'(by rw [pair_length]; omega) = true :=
            pair_getElem_sep1 x y
          rw [hpair]
          rw [hc9_pc_via_c6]
          have hi_c5 : 2 * x.length + 1 + 1 < 3 + 2 * x.length := by omega
          rw [hc6_below (2 * x.length + 1 + 1) (by rw [hc5_ph_val]; exact hi_c5)]
          -- c5.cells[2|x|+2] = Γ.one
          have : 2 * x.length + 1 + 1 = 2 + 2 * x.length := by omega
          rw [this, hc5_pc_one]
          rfl
        · -- Case 4: i ≥ 2|x| + 2. Use hc6_data for y-region.
          have hi_lo : i ≥ 2 * x.length + 2 := by omega
          -- Let j := i - 2|x| - 2, so i = 2|x| + 2 + j, with j < |y|.
          set j := i - 2 * x.length - 2 with hj_def
          have hi_eq : i = 2 * x.length + 2 + j := by omega
          have hj_lt : j < y.length := by omega
          have hpair : (pair x y)[i]'(by rw [pair_length]; omega) = y[j]'hj_lt := by
            exact (getElem_congr_idx hi_eq).trans (pair_getElem_y x y j hj_lt)
          rw [hpair]
          -- cells at i+1 = c5.pIdx.head + j = 3+2|x|+j. Use hc6_data.
          rw [hc9_pc_via_c6]
          have hheq : (c5.work pIdx).head + j = i + 1 := by rw [hc5_ph_val]; omega
          rw [← hheq]
          rw [hc6_data j hj_lt]
          -- Now: c5.yIdx.cells[c5.yIdx.head + j] = Γ.ofBool y[j]
          rw [hc5_yw_cells_eq, hc5_yh_val]
          show (work yIdx).cells (1 + j) = Γ.ofBool (y[j]'hj_lt)
          rw [hyw, show 1 + j = j + 1 from by omega]
          exact Tape.init_ofBool_cells_lt y j hj_lt
  · -- (work pIdx).cells are blank after the encoded pair.
    intro i hi_tail
    rw [pair_length] at hi_tail
    rw [hc9_pc_via_c6]
    -- Position: i + 1, with i beyond 2|x| + 2 + |y|.
    -- ≥ c5.pIdx.head + |y| = 3+2|x|+|y|: use hc6_above.
    have hi_above : i + 1 ≥ (c5.work pIdx).head + y.length := by
      rw [hc5_ph_val]; omega
    rw [hc6_above _ hi_above]
    -- c5/c4/c3 chain is stable at this tail position.
    rw [hc5_pc_other _ (by omega)]
    rw [hc4_pc_other _ (by omega)]
    rw [hc3_pw_cells]
    -- Position ≥ 1+2|x| = c1.pIdx.head + 2|x|. Use hc2_above.
    have hi_c2 : i + 1 ≥ (c1.work pIdx).head + 2 * x.length := by
      rw [hc1_ph]; omega
    rw [hc2_above _ hi_c2]
    -- c1.cells = c0.cells. Initial tape is Tape.init [], cells at j ≥ 1 = blank.
    rw [hc1_pc, hc0_pw_cells]
    rw [ite_eq_right (by omega : i + 1 ≠ 0)]

/-- A compact corollary of `pairBuildTM_hoareTime`: the pair tape satisfies
    exact equality with the standard initialized pair tape, moved to cell 1. -/
theorem pairBuildTM_hoareTime_initTape_move_right
    {k : ℕ} (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx)
    (x y : List Bool) :
    (pairBuildTM yIdx pIdx).HoareTime
      (fun inp work _ =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work yIdx = Tape.init (y.map Γ.ofBool) ∧
        work pIdx = Tape.init [])
      (fun _ work _ =>
        work pIdx = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
      (pairBuildTime x.length y.length) := by
  exact (pairBuildTM_hoareTime yIdx pIdx hne x y).strengthen_post
    (fun _ work _ hpost => by
      exact Tape.eq_init_move_right_of_binary hpost.1 hpost.2.1
        hpost.2.2.1 hpost.2.2.2)

/-- `pairBuildTM` correctness for phase composition where input, witness,
    and pair tapes have already passed the start marker. This is the layout
    produced by earlier setup phases that idle untouched tapes once from `▷`
    to cell `1`. -/
theorem pairBuildTM_hoareTime_all_started_initTape_move_right
    {k : ℕ} (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx)
    (x y : List Bool) :
    (pairBuildTM yIdx pIdx).HoareTime
      (fun inp work _ =>
        inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work yIdx = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
        work pIdx = (Tape.init []).move Dir3.right)
      (fun _ work _ =>
        work pIdx = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
      (pairBuildTime x.length y.length) := by
  intro inp work out ⟨hinp, hyw, hpw⟩
  let c0 : Cfg k (pairBuildTM yIdx pIdx).Q :=
    { state := (pairBuildTM yIdx pIdx).qstart, input := inp, work := work, output := out }
  have hc0_state : c0.state = .init := rfl
  have hinp_read : c0.input.read ≠ Γ.start := by
    show inp.read ≠ Γ.start
    rw [hinp]
    show ((Tape.init (x.map Γ.ofBool)).move Dir3.right).read ≠ Γ.start
    simp only [Tape.read, Tape.move]
    exact Tape.init_ofBool_cells_ne_start x 1 (by omega)
  have hy_read : (c0.work yIdx).read ≠ Γ.start := by
    show (work yIdx).read ≠ Γ.start
    rw [hyw]
    show ((Tape.init (y.map Γ.ofBool)).move Dir3.right).read ≠ Γ.start
    simp only [Tape.read, Tape.move]
    exact Tape.init_ofBool_cells_ne_start y 1 (by omega)
  have hp_read : (c0.work pIdx).read ≠ Γ.start := by
    show (work pIdx).read ≠ Γ.start
    rw [hpw]
    show ((Tape.init []).move Dir3.right).read ≠ Γ.start
    simp only [Tape.read, Tape.move]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  obtain ⟨c1, hstep_init, hc1_state, hc1_inp, hc1_yw, hc1_pw⟩ :=
    pairBuild_init_step_all_started yIdx pIdx c0 hc0_state hinp_read hy_read hp_read
  have hc1_input : c1.input =
      (Tape.init (x.map Γ.ofBool)).move Dir3.right := by
    rw [hc1_inp]
    exact hinp
  have hc1_y : c1.work yIdx =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    rw [hc1_yw]
    exact hyw
  have hc1_p : c1.work pIdx = (Tape.init []).move Dir3.right := by
    rw [hc1_pw]
    exact hpw
  obtain ⟨c9, t, ht, hreach_core, hhalt, hpost⟩ :=
    pairBuildTM_from_copyX1_initTape_move_right yIdx pIdx hne x y c1
      hc1_state hc1_input hc1_y hc1_p
  refine ⟨c9, 1 + t, ?_, ?_, hhalt, ?_⟩
  · dsimp [pairBuildTime]
    omega
  · exact reachesIn_trans _ (.step hstep_init .zero) hreach_core
  · exact Tape.eq_init_move_right_of_binary hpost.1 hpost.2.1
      hpost.2.2.1 hpost.2.2.2

/-- Nondeterministic lift of
    `pairBuildTM_hoareTime_all_started_initTape_move_right`. -/
theorem pairBuildTM_toNTM_hoareTime_all_started_initTape_move_right
    {k : ℕ} (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx)
    (x y : List Bool) :
    ((pairBuildTM yIdx pIdx).toNTM).HoareTime
      (fun inp work _ =>
        inp = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        work yIdx = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
        work pIdx = (Tape.init []).move Dir3.right)
      (fun _ work _ =>
        work pIdx = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
      (pairBuildTime x.length y.length) :=
  (pairBuildTM_hoareTime_all_started_initTape_move_right yIdx pIdx hne x y).toNTM

/-- Local tape fact for pair-builder preservation proofs. -/
private theorem pairBuild_writeAndMove_readBack_idle_of_ne_start (t : Tape)
    (hread : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  have hback : (readBackWrite t.read).toΓ = t.read := by
    cases h : t.read with
    | zero => rfl
    | one => rfl
    | blank => rfl
    | start => exact (hread h).elim
  have hdir : idleDir t.read = Dir3.stay := by
    simp [idleDir, hread]
  rw [hback]
  simp only [Tape.writeAndMove, hdir, Tape.move]
  by_cases h0 : t.head = 0
  · simp [Tape.write, h0]
  · simp [Tape.write, h0, Tape.read, Function.update_eq_self]

/-- One pair-builder step preserves the output tape once the output head is
    past the start marker. -/
theorem pairBuildTM_trace_one_preserves_output
    {k : ℕ} (yIdx pIdx : Fin k) (choice : Bool)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hread : c.output.read ≠ Γ.start) :
    ((((pairBuildTM yIdx pIdx).toNTM).trace 1 (fun _ => choice) c).output) =
      c.output := by
  have hpres := pairBuild_writeAndMove_readBack_idle_of_ne_start c.output hread
  by_cases hhalt : c.state = PairBuildPhase.done
  · simp [NTM.trace, TM.toNTM, pairBuildTM, hhalt]
  · cases hstate : c.state
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt] using hpres
    · by_cases hi : c.input.read = Γ.blank <;>
        simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hi] using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt] using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt] using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt] using hpres
    · by_cases hy : (c.work yIdx).read = Γ.blank <;>
        simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hy] using hpres
    · by_cases hp : (c.work pIdx).read = Γ.start <;>
        simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hp] using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt] using hpres
    · exact (hhalt hstate).elim

/-- Pair-builder traces preserve the output tape once the output head is
    past the start marker. -/
theorem pairBuildTM_trace_preserves_output
    {k : ℕ} (yIdx pIdx : Fin k) (T : ℕ)
    (choices : Fin T → Bool)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hread : c.output.read ≠ Γ.start) :
    ((((pairBuildTM yIdx pIdx).toNTM).trace T choices c).output) =
      c.output := by
  apply ((pairBuildTM yIdx pIdx).toNTM).trace_invariant T choices c
    (fun _ current => current.output = c.output) rfl
  intro time htime current hcurrent
  have hreadCurrent : current.output.read ≠ Γ.start := by
    rw [hcurrent]
    exact hread
  exact (pairBuildTM_trace_one_preserves_output yIdx pIdx
    (choices ⟨time, htime⟩) current hreadCurrent).trans hcurrent

/-- One pair-builder step preserves a non-active work tape once that tape's
    head is past the start marker. -/
theorem pairBuildTM_trace_one_preserves_other_work
    {k : ℕ} (yIdx pIdx otherIdx : Fin k) (choice : Bool)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hy : otherIdx ≠ yIdx) (hp : otherIdx ≠ pIdx)
    (hread : (c.work otherIdx).read ≠ Γ.start) :
    (((((pairBuildTM yIdx pIdx).toNTM).trace 1 (fun _ => choice) c).work
      otherIdx)) = c.work otherIdx := by
  have hpres := pairBuild_writeAndMove_readBack_idle_of_ne_start
    (c.work otherIdx) hread
  by_cases hhalt : c.state = PairBuildPhase.done
  · simp [NTM.trace, TM.toNTM, pairBuildTM, hhalt]
  · cases hstate : c.state
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hy, hp] using hpres
    · by_cases hi : c.input.read = Γ.blank <;>
        simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hi, hy, hp]
          using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hy, hp] using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hy, hp] using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hy, hp] using hpres
    · by_cases hyb : (c.work yIdx).read = Γ.blank <;>
        simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hyb, hy, hp]
          using hpres
    · by_cases hps : (c.work pIdx).read = Γ.start <;>
        simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hps, hy, hp]
          using hpres
    · simpa [NTM.trace, TM.toNTM, pairBuildTM, hstate, hhalt, hy, hp] using hpres
    · exact (hhalt hstate).elim

/-- Pair-builder traces preserve a non-active work tape once that tape's head
    is past the start marker. -/
theorem pairBuildTM_trace_preserves_other_work
    {k : ℕ} (yIdx pIdx otherIdx : Fin k) (T : ℕ)
    (choices : Fin T → Bool)
    (c : Cfg k (pairBuildTM yIdx pIdx).Q)
    (hy : otherIdx ≠ yIdx) (hp : otherIdx ≠ pIdx)
    (hread : (c.work otherIdx).read ≠ Γ.start) :
    ((((pairBuildTM yIdx pIdx).toNTM).trace T choices c).work otherIdx) =
      c.work otherIdx := by
  apply ((pairBuildTM yIdx pIdx).toNTM).trace_invariant T choices c
    (fun _ current => current.work otherIdx = c.work otherIdx) rfl
  intro time htime current hcurrent
  have hreadCurrent : (current.work otherIdx).read ≠ Γ.start := by
    rw [hcurrent]
    exact hread
  exact (pairBuildTM_trace_one_preserves_other_work yIdx pIdx otherIdx
    (choices ⟨time, htime⟩) current hy hp hreadCurrent).trans hcurrent

/-- A compact corollary of `pairBuildTM_hoareTime`: the pair tape satisfies
    the standard `Tape.HasOutput` predicate for `pair x y`. -/
theorem pairBuildTM_hoareTime_hasOutput
    {k : ℕ} (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx)
    (x y : List Bool) :
    (pairBuildTM yIdx pIdx).HoareTime
      (fun inp work _ =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work yIdx = Tape.init (y.map Γ.ofBool) ∧
        work pIdx = Tape.init [])
      (fun _ work _ =>
        (work pIdx).head = 1 ∧ (work pIdx).HasOutput (pair x y))
      (pairBuildTime x.length y.length) := by
  exact (pairBuildTM_hoareTime yIdx pIdx hne x y).strengthen_post
    (fun _ work _ hpost => by
      exact ⟨hpost.1, hpost.2.2.1, hpost.2.2.2 (pair x y).length le_rfl⟩)

end TM

end Complexity
