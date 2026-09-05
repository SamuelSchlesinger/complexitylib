/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Sim
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.SingleTape.Internal

/-!
# Single-tape simulation — transition function

The phase transition functions assembled into the single-tape simulator's `δ`.
Each phase function has the full `δ`-output signature
`SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3`
(next state, single work write, output write, input dir, single work dir, output
dir — there is no input write, the input tape being read-only).

All six phases are implemented — `runStep`, `gatherStep`, `rewindStep`,
`scatter1Step`, `scatter2Step`, `commitStep` — and dispatched by `simDelta`,
which drives the macro-step cycle `run → gather → rewind → scatter1 → scatter2
→ commit → run`. Each phase comes with its `▷`-safety lemma
(`*_right_of_start`), and `NTM.singleTapeSim` packages `simDelta` into the
1-work-tape machine simulating a `k`-work-tape NTM. The file also proves the
structural lemmas used by the simulation proof: choice irrelevance off the `□`
sentinel, phase-membership of each step's successor state, and the
backward-chaining characterizations of `gather` and `run` predecessors.
See `docs/A4-SingleTapeSimulation.md`.
-/


@[expose] public section

namespace Complexity

namespace NTM.SingleTape

/-- The **run** step starts a macro-step: read the input/output head symbols,
    initialise GATHER (accumulator all `▷` = the heads-at-0 default that the
    sweep overwrites for heads it finds; sweep at tape 0, slot 0), and reposition
    the work head to cell 1. `idleDir wH` moves the work head right off `▷` on
    the very first step (initial config) and stays on cell 1 afterwards;
    `idleDir` on input/output performs the `▷`-dodge. -/
def runStep {k : ℕ} {Q : Type} (q : Q) (iHead wH oHead : Γ) :
    SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  ( SimQ.gather (q, (fun _ => Γ.start), iHead, oHead, (0, 0), false, Γ.blank),
    (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
    TM.idleDir iHead, (fun _ => TM.idleDir wH), TM.idleDir oHead )

/-- `run`'s directions are `▷`-safe (everything is `idleDir`). -/
theorem runStep_right_of_start {k : ℕ} {Q : Type} (q : Q) (iHead wH oHead : Γ) :
    (iHead = Γ.start → (runStep (k := k) q iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (runStep (k := k) q iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (runStep (k := k) q iHead wH oHead).2.2.2.2.2 = Dir3.right) :=
  ⟨fun h => TM.idleDir_right_of_start h, fun _ h => TM.idleDir_right_of_start h,
    fun h => TM.idleDir_right_of_start h⟩

/-- The **rewind** step sweeps the work head leftward, carrying the `δ` results
    untouched, until it reads `▷` (cell 0); then it steps right to cell 1 and
    enters SCATTER sweep 1 (empty carries). Moves left otherwise. -/
def rewindStep {k : ℕ} {Q : Type} (d : RewindData k Q) (iHead wH oHead : Γ) :
    SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q', wact, oWoD, iD, iSym, oSym, initRC) := d
  if wH = Γ.start then
    ( SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (0, 0),
        initRC, (fun _ => false), false, false),
      (fun _ => Γw.blank), TM.readBackWrite oHead,
      TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )
  else
    ( SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC),
      (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
      TM.idleDir iHead, (fun _ => Dir3.left), TM.idleDir oHead )

/-- `rewind`'s directions are `▷`-safe: the work head moves left only off `▷`
    (it moves right on `▷`); input/output use `idleDir`. -/
theorem rewindStep_right_of_start {k : ℕ} {Q : Type} (d : RewindData k Q)
    (iHead wH oHead : Γ) :
    (iHead = Γ.start → (rewindStep d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (rewindStep d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (rewindStep d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q', wact, oWoD, iD, iSym, oSym⟩ := d
  refine ⟨fun h => ?_, fun _ h => ?_, fun h => ?_⟩
  · simp only [rewindStep]; split <;> exact TM.idleDir_right_of_start h
  · subst h; simp [rewindStep]
  · simp only [rewindStep]; split <;> exact TM.idleDir_right_of_start h

/-- Clamp a direction to be `▷`-safe: a head reading `▷` is forced right
    (`δ_right_of_start`). On non-`▷` cells (the reachable case) it is the
    identity, so it never changes the simulated behaviour. -/
def safeDir (head : Γ) (d : Dir3) : Dir3 := if head = Γ.start then Dir3.right else d

/-- `safeDir` on a head reading `▷` is `right`, whatever the requested direction. -/
@[simp] theorem safeDir_start (d : Dir3) : safeDir Γ.start d = Dir3.right := rfl

/-- Hypothesis-form of `safeDir_start`: if the head symbol equals `▷` then
    `safeDir` clamps the direction to `right`. -/
theorem safeDir_right_of_start {head : Γ} {d : Dir3} (h : head = Γ.start) :
    safeDir head d = Dir3.right := by subst h; rfl

/-- The **COMMIT** step applies the simulated `N`-step's deferred input/output
    actions — output write+move, input move — then returns to `run q'` (work head
    idling at cell 1). It accounts for the `▷`-dodge performed at `run`: if the
    original input/output symbol was `▷` that head already moved right, so we
    leave it (idle); otherwise we apply the recorded action, `▷`-clamped. -/
def commitStep {k : ℕ} {Q : Type} (d : CommitData Q) (iHead wH oHead : Γ) :
    SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q', oW, oD, iD, iSym, oSym) := d
  let iDir := if iSym = Γ.start then TM.idleDir iHead else safeDir iHead iD
  let oWrite := if oSym = Γ.start then TM.readBackWrite oHead else oW
  let oDir := if oSym = Γ.start then TM.idleDir oHead else safeDir oHead oD
  ( SimQ.run q', (fun _ => TM.readBackWrite wH), oWrite,
    iDir, (fun _ => TM.idleDir wH), oDir )

/-- COMMIT's directions are `▷`-safe (`δ_right_of_start`). -/
theorem commitStep_right_of_start {k : ℕ} {Q : Type} (d : CommitData Q)
    (iHead wH oHead : Γ) :
    (iHead = Γ.start → (commitStep (k := k) d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (commitStep (k := k) d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (commitStep (k := k) d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q', oW, oD, iD, iSym, oSym⟩ := d
  refine ⟨fun h => ?_, fun _ h => ?_, fun h => ?_⟩
  · simp only [commitStep]
    split
    · exact TM.idleDir_right_of_start h
    · exact safeDir_right_of_start h
  · simp only [commitStep]; exact TM.idleDir_right_of_start h
  · simp only [commitStep]
    split
    · exact TM.idleDir_right_of_start h
    · exact safeDir_right_of_start h

/-- Advance the sweep one cell within the block layout: slot `0 → 1 → 2` within
    a tape's triple, then on to the next tape's slot `0` (wrapping past the last
    tape into the next block's tape `0`). -/
def advanceSweep (k : ℕ) (pos : SweepPos k) : SweepPos k :=
  if pos.2 = 2 then
    -- next tape: `t+1` if still a real tape, else wrap to tape `0` (next block)
    (⟨if pos.1.val + 1 < k then pos.1.val + 1 else 0, by split <;> omega⟩, 0)
  else (pos.1, pos.2 + 1)

/-- One **GATHER** step. The work head sweeps rightward over the encoded region,
    reading each tape's `(sym-hi, sym-lo, head-bit)` triple and recording the
    symbol under a head into `acc`. Slots:

    * `0` (sym-hi): stash the high code cell in `pending`.
    * `1` (sym-lo): decode the symbol (`decSymΓ`) into `pending`.
    * `2` (head-bit): if set (`Γ.one`), this tape's head is here — write the
      decoded symbol into `acc` at this tape.

    Reaching the `□` sentinel ends the sweep: apply `N.δ b` (the one meaningful
    use of the choice `b`) and hand the writes/directions to SCATTER. The work
    head moves right while sweeping and never left except on `□` (≠ `▷`), so the
    work direction is `▷`-safe; input/output stay put via `idleDir` and are
    preserved via `readBackWrite`. -/
def gatherStep {k : ℕ} (N : NTM k) (b : Bool) (d : GatherData k N.Q)
    (iHead wH oHead : Γ) :
    SimQ k N.Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q, acc, iSym, oSym, pos, rf, pending) := d
  if wH = Γ.blank then
    -- sentinel reached: compute one N-step and rewind leftward to cell 1
    let (q', wW, oW, iD, wD, oD) := N.δ b q iSym acc oSym
    ( SimQ.rewind (q', (fun i => (wW i, wD i)), (oW, oD), iD, iSym, oSym,
        (fun j => decide (acc j = Γ.start))),
      (fun _ => Γw.blank), TM.readBackWrite oHead,
      TM.idleDir iHead, (fun _ => Dir3.left), TM.idleDir oHead )
  else
    let pos' := advanceSweep k pos
    if pos.2 = 0 then
      -- head-bit: record whether this tape's head is here
      ( SimQ.gather (q, acc, iSym, oSym, pos', decide (wH = Γ.one), pending),
        (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )
    else if pos.2 = 1 then
      -- sym-hi: stash the high code cell
      ( SimQ.gather (q, acc, iSym, oSym, pos', rf, wH),
        (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )
    else
      -- sym-lo: decode the symbol and, if a head is here, record it in `acc`
      let acc' := if rf then
          (if h : pos.1.val < k then Function.update acc ⟨pos.1.val, h⟩ (decSymΓ pending wH)
           else acc)
        else acc
      ( SimQ.gather (q, acc', iSym, oSym, pos', rf, pending),
        (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )

/-- The GATHER step's directions are `▷`-safe (`δ_right_of_start`): input and
    output use `idleDir`, and the work head moves left only on the `□` sentinel
    (never on `▷`), moving right in every `▷`-reachable branch. -/
theorem gatherStep_right_of_start {k : ℕ} (N : NTM k) (b : Bool)
    (d : GatherData k N.Q) (iHead wH oHead : Γ) :
    (iHead = Γ.start → (gatherStep N b d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (gatherStep N b d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (gatherStep N b d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q, acc, iSym, oSym, pos, rf, pending⟩ := d
  refine ⟨fun h => ?_, fun i h => ?_, fun h => ?_⟩
  · simp only [gatherStep]; split_ifs <;> exact TM.idleDir_right_of_start h
  · subst h
    simp only [gatherStep]
    rw [ite_eq_right (by decide : ¬ (Γ.start = Γ.blank))]
    split_ifs <;> rfl
  · simp only [gatherStep]; split_ifs <;> exact TM.idleDir_right_of_start h

/-- Retreat the sweep one cell (leftward): slot `2 → 1 → 0`, then to the previous
    tape's slot `2` (wrapping past tape `0` to tape `k-1` of the previous block). -/
def retreatSweep (k : ℕ) (pos : SweepPos k) : SweepPos k :=
  if pos.2 = 0 then
    (⟨if pos.1.val = 0 then k - 1 else pos.1.val - 1, by have := pos.1.isLt; split <;> omega⟩, 2)
  else (pos.1, pos.2 - 1)

/-- One **SCATTER sweep-1** step (rightward). Writes each head's new symbol,
    places `stay`/`right` markers (carrying `right` ones to the next block via
    `rightCarry`), records `left`-movers (`isLeftMover`) for sweep 2, and — on
    reaching the `□` sentinel — materializes a fresh block (`mat`) before turning
    around (leftward) into sweep 2 once the block is complete. Directions are
    factored out: input/output idle, work head moves right except the single
    `□`-only turn-around, so `δ_right_of_start` is immediate. -/
def scatter1Step {k : ℕ} {Q : Type} (d : Scatter1Data k Q) (iHead wH oHead : Γ) :
    SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat) := d
  let t := pos.1.val
  let stWr : SimQ k Q × Γw :=
    if wH = Γ.blank then
      if mat = true ∧ pos = (0, 0) then
        -- new block complete: turn around into sweep 2, starting at the last cell
        -- of the last materialized block (tape k-1, slot 2), since sweep 2 sweeps left
        (SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2), isLeftMover,
            fun _ => false),
          Γw.blank)
      else
        -- materialize this cell of the new block (head-bit per `rightCarry`, symbol `□`)
        let wv : Γw :=
          if pos.2 = 0 then
            (if h : t < k then (if rightCarry ⟨t, h⟩ then Γw.one else Γw.zero) else Γw.zero)
          else Γw.zero
        let rc' : Fin k → Bool :=
          if pos.2 = 0 then
            (if h : t < k then Function.update rightCarry ⟨t, h⟩ false else rightCarry)
          else rightCarry
        (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos, rc',
          isLeftMover, false, true), wv)
    else if pos.2 = 0 then
      -- real head-bit cell
      if h : t < k then
        if wH = Γ.one then
          match (wact ⟨t, h⟩).2 with
          | Dir3.stay =>
            (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
              rightCarry, isLeftMover, true, mat), Γw.one)
          | Dir3.right =>
            (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
              Function.update rightCarry ⟨t, h⟩ true, isLeftMover, true, mat), Γw.zero)
          | Dir3.left =>
            (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
              rightCarry, Function.update isLeftMover ⟨t, h⟩ true, true, mat), Γw.one)
        else if rightCarry ⟨t, h⟩ then
          (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
            Function.update rightCarry ⟨t, h⟩ false, isLeftMover, false, mat), Γw.one)
        else
          (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
            rightCarry, isLeftMover, false, mat), Γw.zero)
      else
        (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
          rightCarry, isLeftMover, false, mat), TM.readBackWrite wH)
    else
      -- real symbol cell: overwrite with the new symbol if a head was here
      let wv : Γw :=
        if writeFlag then
          (if h : t < k then
            (if pos.2 = 1 then (encSymW (wact ⟨t, h⟩).1).1 else (encSymW (wact ⟨t, h⟩).1).2)
           else TM.readBackWrite wH)
        else TM.readBackWrite wH
      (SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k pos,
        rightCarry, isLeftMover, (if pos.2 = 2 then false else writeFlag), mat), wv)
  ( stWr.1, (fun _ => stWr.2), TM.readBackWrite oHead, TM.idleDir iHead,
    (fun _ => if wH = Γ.blank ∧ mat = true ∧ pos = (0, 0) then Dir3.left else Dir3.right),
    TM.idleDir oHead )

/-- One **SCATTER sweep-2** step (leftward). Deposits the recorded left-movers
    (`isLeftMover`): clears each one's old marker and re-sets it one block left
    (`leftCarry`). On reaching `▷` (cell 0) it steps right to cell 1 and enters
    COMMIT. Directions factored: input/output idle, work head moves left except
    the `▷`-only turn into COMMIT, so `δ_right_of_start` is immediate. -/
def scatter2Step {k : ℕ} {Q : Type} (d : Scatter2Data k Q) (iHead wH oHead : Γ) :
    SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q', oWoD, iD, iSym, oSym, pos, isLeftMover, leftCarry) := d
  let t := pos.1.val
  let stWr : SimQ k Q × Γw :=
    if wH = Γ.start then
      (SimQ.commit (q', oWoD.1, oWoD.2, iD, iSym, oSym), Γw.blank)
    else if pos.2 = 0 then
      if h : t < k then
        if wH = Γ.one ∧ isLeftMover ⟨t, h⟩ = true then
          (SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k pos, isLeftMover,
            Function.update leftCarry ⟨t, h⟩ true), Γw.zero)
        else if leftCarry ⟨t, h⟩ = true then
          (SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k pos,
            Function.update isLeftMover ⟨t, h⟩ false, Function.update leftCarry ⟨t, h⟩ false),
            Γw.one)
        else
          (SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k pos, isLeftMover, leftCarry),
            TM.readBackWrite wH)
      else
        (SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k pos, isLeftMover, leftCarry),
          TM.readBackWrite wH)
    else
      (SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k pos, isLeftMover, leftCarry),
        TM.readBackWrite wH)
  ( stWr.1, (fun _ => stWr.2), TM.readBackWrite oHead, TM.idleDir iHead,
    (fun _ => if wH = Γ.start then Dir3.right else Dir3.left),
    TM.idleDir oHead )

/-- `scatter1`'s directions are `▷`-safe. -/
theorem scatter1Step_right_of_start {k : ℕ} {Q : Type} (d : Scatter1Data k Q)
    (iHead wH oHead : Γ) :
    (iHead = Γ.start → (scatter1Step d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (scatter1Step d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (scatter1Step d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat⟩ := d
  refine ⟨fun h => ?_, fun _ h => ?_, fun h => ?_⟩
  · exact TM.idleDir_right_of_start h
  · subst h; simp only [scatter1Step]
    split
    · rename_i hc; exact absurd hc.1 (by decide)
    · rfl
  · exact TM.idleDir_right_of_start h

/-- `scatter2`'s directions are `▷`-safe (work moves left only off `▷`). -/
theorem scatter2Step_right_of_start {k : ℕ} {Q : Type} (d : Scatter2Data k Q)
    (iHead wH oHead : Γ) :
    (iHead = Γ.start → (scatter2Step d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (scatter2Step d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (scatter2Step d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q', oWoD, iD, iSym, oSym, pos, isLeftMover, leftCarry⟩ := d
  refine ⟨fun h => ?_, fun _ h => ?_, fun h => ?_⟩
  · exact TM.idleDir_right_of_start h
  · simp only [scatter2Step]; rw [ite_eq_left h]
  · exact TM.idleDir_right_of_start h

/-- The assembled single-tape transition function: dispatch on the phase. The
    work head symbol is `wHead 0` (the single work tape). -/
def simDelta {k : ℕ} (N : NTM k) (b : Bool) (state : SimQ k N.Q)
    (iHead : Γ) (wHead : Fin 1 → Γ) (oHead : Γ) :
    SimQ k N.Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  match state with
  | SimQ.run q =>
    if q = N.qhalt then
      -- N has halted: stop, preserving the tapes (the accept bit lives on output)
      (SimQ.halt, (fun _ => TM.readBackWrite (wHead 0)), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => TM.idleDir (wHead 0)), TM.idleDir oHead)
    else runStep q iHead (wHead 0) oHead
  | SimQ.gather d => gatherStep N b d iHead (wHead 0) oHead
  | SimQ.rewind d => rewindStep d iHead (wHead 0) oHead
  | SimQ.scatter1 d => scatter1Step d iHead (wHead 0) oHead
  | SimQ.scatter2 d => scatter2Step d iHead (wHead 0) oHead
  | SimQ.commit d => commitStep d iHead (wHead 0) oHead
  | SimQ.halt =>
    (SimQ.halt, (fun _ => Γw.blank), Γw.blank,
      TM.idleDir iHead, (fun _ => TM.idleDir (wHead 0)), TM.idleDir oHead)

/-- The assembled transition satisfies `δ_right_of_start`: every phase moves a
    head reading `▷` to the right. Each case is the corresponding phase's
    `*_right_of_start`; the work-head condition uses `wHeads i = wHeads 0`
    (`Fin 1` is a subsingleton). -/
theorem simDelta_right_of_start {k : ℕ} (N : NTM k) (b : Bool) (q : SimQ k N.Q)
    (iHead : Γ) (wHeads : Fin 1 → Γ) (oHead : Γ) :
    (iHead = Γ.start → (simDelta N b q iHead wHeads oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → (simDelta N b q iHead wHeads oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (simDelta N b q iHead wHeads oHead).2.2.2.2.2 = Dir3.right) := by
  have hw : ∀ i : Fin 1, wHeads i = wHeads 0 := fun i => by rw [Subsingleton.elim i 0]
  rcases q with q | d | d | d | d | d | ⟨⟩
  · -- run q: the halt-branch and the runStep-branch both use `idleDir` for every head
    refine ⟨fun h => ?_, fun i hi => ?_, fun h => ?_⟩
    · simp only [simDelta]; split <;> exact TM.idleDir_right_of_start h
    · simp only [simDelta]; split <;> exact TM.idleDir_right_of_start (hw i ▸ hi)
    · simp only [simDelta]; split <;> exact TM.idleDir_right_of_start h
  · exact ⟨(gatherStep_right_of_start N b d iHead (wHeads 0) oHead).1,
      fun i hi => (gatherStep_right_of_start N b d iHead (wHeads 0) oHead).2.1 i (hw i ▸ hi),
      (gatherStep_right_of_start N b d iHead (wHeads 0) oHead).2.2⟩
  · exact ⟨(rewindStep_right_of_start d iHead (wHeads 0) oHead).1,
      fun i hi => (rewindStep_right_of_start d iHead (wHeads 0) oHead).2.1 i (hw i ▸ hi),
      (rewindStep_right_of_start d iHead (wHeads 0) oHead).2.2⟩
  · exact ⟨(scatter1Step_right_of_start d iHead (wHeads 0) oHead).1,
      fun i hi => (scatter1Step_right_of_start d iHead (wHeads 0) oHead).2.1 i (hw i ▸ hi),
      (scatter1Step_right_of_start d iHead (wHeads 0) oHead).2.2⟩
  · exact ⟨(scatter2Step_right_of_start d iHead (wHeads 0) oHead).1,
      fun i hi => (scatter2Step_right_of_start d iHead (wHeads 0) oHead).2.1 i (hw i ▸ hi),
      (scatter2Step_right_of_start d iHead (wHeads 0) oHead).2.2⟩
  · exact ⟨(commitStep_right_of_start d iHead (wHeads 0) oHead).1,
      fun i hi => (commitStep_right_of_start d iHead (wHeads 0) oHead).2.1 i (hw i ▸ hi),
      (commitStep_right_of_start d iHead (wHeads 0) oHead).2.2⟩
  · exact ⟨fun h => TM.idleDir_right_of_start h,
      fun i hi => TM.idleDir_right_of_start (hw i ▸ hi),
      fun h => TM.idleDir_right_of_start h⟩

/-- **Choice irrelevance — GATHER step.** Off the `□` sentinel, the GATHER step
    does not consult the nondeterministic bit `b` (only the sentinel step fires
    `N.δ b`), so it produces the same output under any choice. -/
theorem gatherStep_eq_of_ne_blank {k : ℕ} (N : NTM k) (b b' : Bool) (d : GatherData k N.Q)
    (iHead wH oHead : Γ) (h : wH ≠ Γ.blank) :
    gatherStep N b d iHead wH oHead = gatherStep N b' d iHead wH oHead := by
  simp only [gatherStep, ite_eq_right h]

/-- **GATHER stays in GATHER off the sentinel.** As long as the work head is not
    on the `□` sentinel, the GATHER step's next state is again a GATHER state (the
    sweep only leaves GATHER to enter REWIND when it reads `□`). The inductive
    building block for characterizing the sweep's per-step states. -/
theorem gatherStep_fst_eq_gather_of_ne_blank {k : ℕ} (N : NTM k) (b : Bool) (d : GatherData k N.Q)
    (iHead wH oHead : Γ) (h : wH ≠ Γ.blank) :
    ∃ d', (gatherStep N b d iHead wH oHead).1 = SimQ.gather d' := by
  simp only [gatherStep, ite_eq_right h]
  split
  · exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

/-- **GATHER non-state components off the sentinel.** For `wH ≠ □` all three
    sweep sub-branches (head-bit / sym-hi / sym-lo) agree on everything but the
    next state: the work head reads-back-writes `wH` and moves right, input/output
    stay idle. Lets the per-step sweep lemma treat one gather step uniformly. -/
theorem gatherStep_snd_eq_of_ne_blank {k : ℕ} (N : NTM k) (b : Bool) (d : GatherData k N.Q)
    (iHead wH oHead : Γ) (h : wH ≠ Γ.blank) :
    (gatherStep N b d iHead wH oHead).2.1 = (fun _ => TM.readBackWrite wH) ∧
    (gatherStep N b d iHead wH oHead).2.2.1 = TM.readBackWrite oHead ∧
    (gatherStep N b d iHead wH oHead).2.2.2.1 = TM.idleDir iHead ∧
    (gatherStep N b d iHead wH oHead).2.2.2.2.1 = (fun _ => Dir3.right) ∧
    (gatherStep N b d iHead wH oHead).2.2.2.2.2 = TM.idleDir oHead := by
  simp only [gatherStep, ite_eq_right h]
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A GATHER configuration arises only from `run` or `gather`.** The only
    transitions producing a GATHER state are `run → gather` (starting the sweep)
    and `gather → gather` (continuing it); every back-phase step
    (`rewind`/`scatter1`/`scatter2`/`commit`) and `halt` produces a non-GATHER
    state. The backward-chaining tool for locating the sweep within a macro-step. -/
theorem eq_run_or_gather_of_simDelta_eq_gather {k : ℕ} (N : NTM k) (b : Bool) (state : SimQ k N.Q)
    (iHead : Γ) (wHead : Fin 1 → Γ) (oHead : Γ) (d' : GatherData k N.Q)
    (h : (simDelta N b state iHead wHead oHead).1 = SimQ.gather d') :
    (∃ q, state = SimQ.run q) ∨ (∃ d, state = SimQ.gather d) := by
  rcases state with q | d | d | d | d | d | ⟨⟩
  · exact Or.inl ⟨q, rfl⟩
  · exact Or.inr ⟨d, rfl⟩
  · exact absurd h (by
      simp only [simDelta, rewindStep]; split <;>
        simp [SimQ.gather, SimQ.scatter1, SimQ.rewind])
  · exact absurd h (by
      simp only [simDelta, scatter1Step]; (repeat' split) <;>
        simp [SimQ.gather, SimQ.scatter1, SimQ.scatter2])
  · exact absurd h (by
      simp only [simDelta, scatter2Step]; (repeat' split) <;>
        simp [SimQ.gather, SimQ.scatter2, SimQ.commit])
  · exact absurd h (by simp [simDelta, commitStep, SimQ.gather, SimQ.run])
  · exact absurd h (by simp [simDelta, SimQ.gather, SimQ.halt])

/-- **A `run` configuration arises only from `commit`.** The only transition
    producing a `run` state is `commit → run` (closing a macro-step); `run` itself
    steps to `gather`/`halt`, and every other phase step stays within its own
    cluster. Companion to `eq_run_or_gather_of_simDelta_eq_gather`; together they fix the phase
    order `… → scatter2 → commit → run → gather → …` of the simulation. -/
theorem eq_commit_of_simDelta_eq_run {k : ℕ} (N : NTM k) (b : Bool) (state : SimQ k N.Q)
    (iHead : Γ) (wHead : Fin 1 → Γ) (oHead : Γ) (q' : N.Q)
    (h : (simDelta N b state iHead wHead oHead).1 = SimQ.run q') :
    ∃ d, state = SimQ.commit d := by
  rcases state with q | d | d | d | d | d | ⟨⟩
  · exact absurd h (by
      simp only [simDelta]; split <;> simp [SimQ.run, SimQ.gather, SimQ.halt, runStep])
  · exact absurd h (by
      simp only [simDelta, gatherStep]; (repeat' split) <;>
        simp [SimQ.run, SimQ.gather, SimQ.rewind])
  · exact absurd h (by
      simp only [simDelta, rewindStep]; split <;>
        simp [SimQ.run, SimQ.scatter1, SimQ.rewind])
  · exact absurd h (by
      simp only [simDelta, scatter1Step]; (repeat' split) <;>
        simp [SimQ.run, SimQ.scatter1, SimQ.scatter2])
  · exact absurd h (by
      simp only [simDelta, scatter2Step]; (repeat' split) <;>
        simp [SimQ.run, SimQ.scatter2, SimQ.commit])
  · exact ⟨d, rfl⟩
  · exact absurd h (by simp [simDelta, SimQ.run, SimQ.halt])

/-- **SCATTER-1 lands in `scatter1` or `scatter2`.** One sweep-1 step either
    continues the rightward materialization (`scatter1`) or, on completing the new
    block, turns around into sweep-2 (`scatter2`) — never any other phase. -/
theorem scatter1Step_fst_eq_scatter1_or_scatter2 {k : ℕ} {Q : Type} (d : Scatter1Data k Q)
    (iHead wH oHead : Γ) :
    (∃ d', (scatter1Step d iHead wH oHead).1 = SimQ.scatter1 d') ∨
    (∃ d', (scatter1Step d iHead wH oHead).1 = SimQ.scatter2 d') := by
  simp only [scatter1Step]
  (repeat' split) <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩

/-- **SCATTER-2 lands in `scatter2` or `commit`.** One sweep-2 step either
    continues the leftward deposit (`scatter2`) or, on reaching `▷`, enters
    `commit` — never any other phase. -/
theorem scatter2Step_fst_eq_scatter2_or_commit {k : ℕ} {Q : Type} (d : Scatter2Data k Q)
    (iHead wH oHead : Γ) :
    (∃ d', (scatter2Step d iHead wH oHead).1 = SimQ.scatter2 d') ∨
    (∃ d', (scatter2Step d iHead wH oHead).1 = SimQ.commit d') := by
  simp only [scatter2Step]
  (repeat' split) <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩

/-- **Choice irrelevance — one simulator step.** The single-tape simulator's
    transition consults the nondeterministic bit only at a GATHER step reading the
    `□` sentinel (the COMPUTE sub-step firing `N.δ b`); every other configuration
    steps identically under any choice. -/
theorem simDelta_eq_of_forall_ne_blank {k : ℕ} (N : NTM k) (b b' : Bool) (state : SimQ k N.Q)
    (iHead : Γ) (wHead : Fin 1 → Γ) (oHead : Γ)
    (h : ∀ d, state = SimQ.gather d → wHead 0 ≠ Γ.blank) :
    simDelta N b state iHead wHead oHead = simDelta N b' state iHead wHead oHead := by
  rcases state with q | d | d | d | d | d | ⟨⟩
  · rfl
  · show simDelta N b (SimQ.gather d) iHead wHead oHead
      = simDelta N b' (SimQ.gather d) iHead wHead oHead
    simp only [simDelta]
    exact gatherStep_eq_of_ne_blank N b b' d iHead (wHead 0) oHead (h d rfl)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end NTM.SingleTape

namespace NTM

/-- The single-work-tape machine simulating the `k`-work-tape machine `N`. It
    stores the `k` work tapes block-encoded (binary, `□`-sentinel) on its one
    work tape and simulates each `N`-step by the phase machine
    `run → gather → rewind → scatter1 → scatter2 → commit` (see this file and
    `docs/A4-SingleTapeSimulation.md`). The `Fintype`/`DecidableEq` instances on
    the state type `SingleTape.SimQ` are noncomputable. -/
noncomputable def singleTapeSim {k : ℕ} (N : NTM k) : NTM 1 where
  Q := SingleTape.SimQ k N.Q
  qstart := SingleTape.SimQ.run N.qstart
  qhalt := SingleTape.SimQ.halt
  δ := SingleTape.simDelta N
  δ_right_of_start := SingleTape.simDelta_right_of_start N

end NTM

end Complexity
