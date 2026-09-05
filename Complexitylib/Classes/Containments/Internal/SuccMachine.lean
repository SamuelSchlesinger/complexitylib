/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BlockScan
public import Complexitylib.Models.TuringMachine.Subroutines.InputMatch
public import Complexitylib.Models.TuringMachine.Subroutines.WriteOutputBit
public import Complexitylib.Models.TuringMachine.Combinators.Internal.LoopIteration
public import Complexitylib.Classes.Containments.Internal.CountingCert
public import Complexitylib.Models.TuringMachine.GuessAssembly
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
public import Complexitylib.Models.TuringMachine.Placement.Hoare
public import Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import Complexitylib.Models.TuringMachine.Combinators.Internal.LoopIndexed

/-!
# Assembling the successor check

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.BlockScan` proves what the scans decide, in terms of
what the registers hold. `Complexitylib.Models.TuringMachine.GuessAssembly` proves what the guess
machinery puts on a register. This file is where the two meet: a block of guesses written onto a
register is a register the scans can read.

## Main results

- `Complexity.holdsBits_of_guessBlock` — a written block of guesses is a register holding those
  bits
- `Complexity.ofTable_state` — the state a scan reads off a code's state register
- `Complexity.blockEmit_work`, `Complexity.blockEmit_output`, `Complexity.inHeadEmit_code` — what
  each scan says about the code the registers hold
- `Complexity.mem_codeSucc_of_scans` — and together: the scans decide `codeSucc` membership
- `Complexity.HoldsCode.inj` — the registers determine the code, so comparing registers compares
  codes
- `Complexity.codeBlock`, `Complexity.codeWidth`, `Complexity.codeRegsOf` — the block layout a
  code guess uses
- `Complexity.holdsCode_of_guessBlocks`, `Complexity.holdsCode_of_guessStage`,
  `Complexity.holdsCode_of_stage` — a guess stage can lay down any code, the rewind that follows
  it does not disturb one, and a stage of a loop lays down the code its stream names
- `Complexity.codeBlockScan`, `Complexity.HoldsCodeScan`, `Complexity.holdsCodeScan_of_blocks` —
  the padded layout the walk's checks read, and that a guess lays it down
- `Complexity.eqScanner`, `Complexity.eqScanner_decides`, `Complexity.eqScanner_accepts` — one
  comparison per block, in one scan, deciding that two guesses are the same code — and accepting
  when they are
- `Complexity.succScanner`, `Complexity.succScanner_verdicts` — and every successor check in one
  scan, with each component's verdict recovered
- `Complexity.succScanner_decides` — that scan decides a successor step
- `Complexity.succScanner_accepts` — and accepts a genuine one, which is what says the right guess
  exists
- `Complexity.walkCodeScanner`, `Complexity.walkCodeScanner_decides` — both halves together:
  one scan whose verdict is exactly one step of the walk, together with the direction the input
  head is to take
- `Complexity.walkCodeScanner_accepts_stay`, `Complexity.walkCodeScanner_accepts_succ` — and
  accepts either kind of genuine step
- `Complexity.walkStepScanner`, `Complexity.walkStepScanner_decides`,
  `Complexity.walkStepScanner_accepts`, `Complexity.walkStepScanner_accepts_stay`,
  `Complexity.walkStepScanner_accepts_succ` — and with the counter, the whole verdict of a step,
  in both directions
- `Complexity.rulerBlock`, `Complexity.scanTape_of_ruler`, `Complexity.ruler_of_holds` — the
  guessed register that fixes the scan's length
- `Complexity.checkedCells`, `Complexity.checkPhase_hoareTime` — the input check and the scan in
  sequence, with the check's verdict on a register the scan reads
- `Complexity.checkMove_hoareTime` — and with the input head's move, the whole guess-free part of
  a walk step
- `Complexity.verdictCells`, `Complexity.verdictCells_acc_one` — and the register a verdict is
  published on
- `Complexity.loopTestScanner`, `Complexity.loopTestScanner_decides`,
  `Complexity.loopTestScanner_of_fail`, `Complexity.loopTestTM`,
  `Complexity.publishTestTM_hoareTime` — the loop's test: stop when the counter reaches its target
  or a check has failed, with the verdict published where `TM.loopTM` reads it
- `Complexity.counterStepScanner`, `Complexity.counterStepScanner_decides`,
  `Complexity.counterStepScanner_accepts` — the counter check of a step: stay, or advance by one
- `Complexity.mem_reachCodes_of_pairWalk` — a walk of even length reaches whatever a shorter one
  does
- `Complexity.DirCodec`, `Complexity.dirCodec`, `Complexity.move_head_of_dir` — a direction in one
  cell, and that the input head lands where the code says
- `Complexity.adjustedDir`, `Complexity.move_adjusted`, `Complexity.dirCheckScanner`,
  `Complexity.dirCheckScanner_decides`, `Complexity.dirCheckScanner_accepts` — and the direction a
  head pinned away from the marker must actually take, decided and accepted
- `Complexity.move_of_walkStep`, `Complexity.move_of_walkStay`,
  `Complexity.walkStep_transports` — a step carries the input head to where the next code says,
  and its code is one step of the walk
- `Complexity.succ_fields_of_eq` — a genuine successor's fields are what the checks compare
  against
- `Complexity.WalkLayout`, `Complexity.WalkWidths` — which register plays which role in the walk,
  and how wide each is guessed
- `Complexity.stageBits`, `Complexity.walkCert` — what one stage of the walk must guess into each
  of them, and the certificate for a whole walk
- `Complexity.stageCells`, `Complexity.stageCols` — the registers a stage leaves, as the scan
  sees them
- `Complexity.stage_accepts_stay`, `Complexity.stage_accepts_succ` — a stage of a real walk is
  accepted, whichever kind of step it takes
- `Complexity.guessFrom_after_stage` — and the guess tape is left ready for the next stage
- `Complexity.holdsBits_block_of_stage`, `Complexity.cell_of_stage` and their instances for the
  code tuples, the parameter block, the counters, the direction cells and the ruler — after a
  stage, each register holds what the certificate names
- `Complexity.walkReg`, `Complexity.WalkLoopInv`, `Complexity.holdsCounter_of_walkLoopInv`,
  `Complexity.inSym_of_walkLoopInv`, `Complexity.guessFrom_of_walkLoopInv` — the walk loop's
  invariant: the counter names the iteration, the registers hold the code, the input head sits
  where the code says, and the guess tape still holds what the rest of the walk will need
- `Complexity.walkPairTM`, `Complexity.guessProtocol_walkPairTM` — the loop's body: two steps
  with the code's registers swapping roles, so no register need be copied
- `Complexity.walkLoopTM`, `Complexity.guessProtocol_walkLoopTM` — the walk as a machine, driven
  by `TM.binaryForTM`'s own binary counter, and that only its guess stage consumes guesses
- `Complexity.walkCheckTM`, `Complexity.walkStepTM`, `Complexity.walkStepTM_hoareTime`,
  `Complexity.guessProtocol_walkStepTM` — one walk step as a machine: guess, rewind, check the
  input symbol, scan, move the input head, and conjoin the verdict into the accumulator; its
  contract, and that it respects the guess protocol. The step holds `r` further tapes still
  (`TM.liftMany`) — the enclosing loops' counters and the accumulator, none of them guessed, none
  of them scanned
- `Complexity.windowParams_congr`, `Complexity.walkParams_eq`, `Complexity.params_of_holds` — all
  of those checks read the same guessed parameters, through either of the two readers
- `Complexity.walkScanLen` — a scan length that covers every check of a walk step
- `Complexity.mem_reachCodes_of_walk` — what a walk establishes
- `Complexity.roundList_of_inj` — what the counting establishes
- `Complexity.WalkInv`, `Complexity.counterVal_of_walkInv` — the walk loop's invariant, and that
  the counter reads back the loop's index
- `Complexity.walkLoop_hoareTime` — and the loop itself, given a body that carries it forward
- `Complexity.HoldsCounter`, `Complexity.counterLoop_hoareTime` — the general counter-driven loop
  rule the walk and both enumerations share
- `Complexity.windowScanner` — the scanner that checks one tape window against its successor
- `Complexity.outputScanner`, `Complexity.headScanner` — the output-window and input-head
  checkers
- `Complexity.stateScanner` — the state checker
- `Complexity.dirScanner`, `Complexity.dirScanner_decides` — the checker that pins the guessed
  input-head direction, the one cell `TM.inMoveTM` reads
- `Complexity.inSym_cells`, `Complexity.inSym_eq_of_inMatch`,
  `Complexity.inMatchVerdict_of_inSym` — the guessed input symbol opens the parameter register,
  where `TM.inMatchTM` checks it against the machine's own input tape, in both directions
- `Complexity.headZeroScanner`, `Complexity.headNonZeroScanner` and their decision lemmas —
  whether the simulated input head is at the marker, where no tape read is possible
- `Complexity.parStart_iff` — and that the parameter register opens with two ones exactly when the
  guessed symbol is the marker
- `Complexity.windowScanner_run`, `Complexity.outputScanner_run`,
  `Complexity.headScanner_run`, `Complexity.stateScanner_run` — and what each computes
- `Complexity.windowScanner_decides`, `Complexity.outputScanner_decides`,
  `Complexity.headScanner_decides`, `Complexity.stateScanner_decides` — and what each decides
  about the code the registers hold
- `Complexity.combineTM`, `Complexity.combineTM_hoareTime`, `Complexity.combineTM_verdict` — and
  the machine that combines their verdicts

## Main definitions

- `Complexity.CodeRegs` — which register holds which field of a code
- `Complexity.HoldsCode` — and that they hold a given code
-/

@[expose] public section

namespace Complexity

/-- A machine's state type is nonempty: it has a start state. -/
instance instNonemptyNTMQ {kk : ℕ} (tm : NTM kk) : Nonempty tm.Q := ⟨tm.qstart⟩

variable {m : ℕ}

/-- **A block of guesses is a register the scans can read.** Writing `n + 1` guessed bits onto a
register parked at cell one leaves it holding exactly those bits. -/
theorem holdsBits_of_guessBlock (r : Fin (m + 1)) (hr : r ≠ Fin.last m) (n : ℕ)
    (W : Fin (m + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : (W r).head = 1) (b : ℕ → Bool)
    (hg : ∀ p ≤ n, (W (Fin.last m)).cells ((W (Fin.last m)).head + p) = Γ.ofBool (b p)) :
    HoldsBits (fun p i => (TM.guessBlockTapes r n W i).cells p) 0 r
      (List.ofFn (fun q : Fin (n + 1) => b q.val)) := by
  obtain ⟨-, -, -, -, hcells⟩ := TM.guessBlockTapes_spec r hr n W hinv hh
  intro q hq
  have hqlt : q < n + 1 := by simpa using hq
  show (TM.guessBlockTapes r n W r).cells (0 + q + 1) = _
  rw [show 0 + q + 1 = (W r).head + q by rw [hr1]; omega, hcells q (by omega),
    hg q (by omega), List.getElem_ofFn]

/-- **Several blocks of guesses give several registers to read.** Each target register, parked at
cell one, ends up holding the bits guessed for its own block. -/
theorem holdsBits_of_guessBlocks (j : ℕ → Fin (m + 1)) (hj : ∀ p, j p ≠ Fin.last m) (w : ℕ → ℕ)
    (t : ℕ) (W : Fin (m + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (hinj : ∀ p q, p < t → q < t → j p = j q → p = q)
    (hr1 : ∀ p, p < t → (W (j p)).head = 1) (b : ℕ → ℕ → Bool)
    (hg : ∀ p, p < t → ∀ q ≤ w p, (W (Fin.last m)).cells
      ((W (Fin.last m)).head + TM.guessOffset w p + q) = Γ.ofBool (b p q)) :
    ∀ p, p < t → HoldsBits (fun c i => (TM.guessBlocksTapes j w t W i).cells c) 0 (j p)
      (List.ofFn (fun q : Fin (w p + 1) => b p q.val)) := by
  obtain ⟨-, -, -, -, hblk⟩ := TM.guessBlocksTapes_spec j hj w t W hinv hh hinj
  intro p hp q hq
  have hqlt : q < w p + 1 := by simpa using hq
  show (TM.guessBlocksTapes j w t W (j p)).cells (0 + q + 1) = _
  rw [show 0 + q + 1 = (W (j p)).head + q by rw [hr1 p hp]; omega,
    (hblk p hp).2 q (by omega), hg p hp q (by omega), List.getElem_ofFn]

/-! ## Which register holds which field -/

/-- The layout of a configuration code across registers: one for the state, one for the input
head, one per work window, and one for the output window. -/
structure CodeRegs (kk jj : ℕ) where
  /-- The register holding the state. -/
  st : Fin (jj + 1)
  /-- The register holding the input head. -/
  hd : Fin (jj + 1)
  /-- The registers holding the work windows. -/
  wk : Fin kk → Fin (jj + 1)
  /-- The register holding the output window. -/
  ot : Fin (jj + 1)

/-- Those registers hold the code `a`. -/
def HoldsCode {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (cols : ℕ → Fin (jj + 1) → Γ) (off : ℕ) (R : CodeRegs kk jj)
    (a : Code tm.Q kk x.length S) : Prop :=
  HoldsBits (fun q => cols (off + q)) 0 R.st ((qCodec tm.Q).enc a.1) ∧
    HoldsBits (fun q => cols (off + q)) 0 R.hd ((finCodec (x.length + S + 2)).enc a.2.1) ∧
    (∀ i, HoldsWindow (fun q => cols (off + q)) 0 (R.wk i) (a.2.2.1 i).1 (a.2.2.1 i).2) ∧
    HoldsWindow (fun q => cols (off + q)) 0 R.ot a.2.2.2.1 a.2.2.2.2

theorem HoldsCode.state {kk : ℕ} {tm : NTM kk} {x : List Bool} {S jj : ℕ}
    {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ} {R : CodeRegs kk jj}
    {a : Code tm.Q kk x.length S} (h : HoldsCode tm x S cols off R a) :
    HoldsBits (fun q => cols (off + q)) 0 R.st ((qCodec tm.Q).enc a.1) := h.1

theorem HoldsCode.inputHead {kk : ℕ} {tm : NTM kk} {x : List Bool} {S jj : ℕ}
    {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ} {R : CodeRegs kk jj}
    {a : Code tm.Q kk x.length S} (h : HoldsCode tm x S cols off R a) :
    HoldsBits (fun q => cols (off + q)) 0 R.hd
      ((finCodec (x.length + S + 2)).enc a.2.1) := h.2.1

theorem HoldsCode.work {kk : ℕ} {tm : NTM kk} {x : List Bool} {S jj : ℕ}
    {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ} {R : CodeRegs kk jj}
    {a : Code tm.Q kk x.length S} (h : HoldsCode tm x S cols off R a) (i : Fin kk) :
    HoldsWindow (fun q => cols (off + q)) 0 (R.wk i) (a.2.2.1 i).1 (a.2.2.1 i).2 := h.2.2.1 i

theorem HoldsCode.output {kk : ℕ} {tm : NTM kk} {x : List Bool} {S jj : ℕ}
    {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ} {R : CodeRegs kk jj}
    {a : Code tm.Q kk x.length S} (h : HoldsCode tm x S cols off R a) :
    HoldsWindow (fun q => cols (off + q)) 0 R.ot a.2.2.2.1 a.2.2.2.2 := h.2.2.2

/-! ## Guessing a whole code -/

/-- The raw width of block `p` of a code: the state, the input head, the `kk` work windows, then
the output window. -/
noncomputable def codeWidthRaw {kk : ℕ} (tm : NTM kk) (nn S : ℕ) (p : ℕ) : ℕ :=
  if p = 0 then (qCodec tm.Q).width
  else if p = 1 then (finCodec (nn + S + 2)).width
  else if p < kk + 2 then (S + 1) * 3
  else (S + 2) * 3

/-- The block width a code guess passes to `TM.guessBlocksTM`, which writes `n + 1` bits for a
block of `n`. A field of width zero is guessed one bit wide and its (empty) contents read back
off the prefix. -/
noncomputable def codeWidth {kk : ℕ} (tm : NTM kk) (nn S : ℕ) (p : ℕ) : ℕ :=
  codeWidthRaw tm nn S p - 1

/-- The bits block `p` of a code guess should hold. -/
noncomputable def codeBlock {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (p : ℕ) : List Bool :=
  if _ : p = 0 then (qCodec tm.Q).enc a.1
  else if _ : p = 1 then (finCodec (x.length + S + 2)).enc a.2.1
  else if h : p < kk + 2 then (tapeCodec (S + 1)).enc (a.2.2.1 ⟨p - 2, by omega⟩)
  else (tapeCodec (S + 2)).enc a.2.2.2

@[simp] theorem codeBlock_st {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) : codeBlock tm x S a 0 = (qCodec tm.Q).enc a.1 := by
  rw [codeBlock, dite_eq_left rfl]

@[simp] theorem codeBlock_hd {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) :
    codeBlock tm x S a 1 = (finCodec (x.length + S + 2)).enc a.2.1 := by
  rw [codeBlock, dite_eq_right (by omega), dite_eq_left rfl]

@[simp] theorem codeBlock_wk {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (i : Fin kk) :
    codeBlock tm x S a (i.val + 2) = (tapeCodec (S + 1)).enc (a.2.2.1 i) := by
  rw [codeBlock, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega),
    show (⟨i.val + 2 - 2, by omega⟩ : Fin kk) = i from Fin.ext (by simp)]

@[simp] theorem codeBlock_ot {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) :
    codeBlock tm x S a (kk + 2) = (tapeCodec (S + 2)).enc a.2.2.2 := by
  rw [codeBlock, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]

theorem codeBlock_length {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (p : ℕ) :
    (codeBlock tm x S a p).length = codeWidthRaw tm x.length S p := by
  unfold codeBlock codeWidthRaw
  split_ifs with h0 h1 h2
  · exact (qCodec tm.Q).enc_length _
  · exact (finCodec (x.length + S + 2)).enc_length _
  · exact (tapeCodec (S + 1)).enc_length _
  · exact (tapeCodec (S + 2)).enc_length _

/-- The registers a code guess writes to: one block each, in the order of `codeBlock`. -/
def codeRegsOf {kk jj : ℕ} (j : ℕ → Fin (jj + 1)) : CodeRegs kk jj where
  st := j 0
  hd := j 1
  wk i := j (i.val + 2)
  ot := j (kk + 2)

/-! ## The registers determine the code -/

/-- A register holding an encoded window determines the window. -/
theorem HoldsWindow.inj {m : ℕ} [NeZero m] {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ}
    {r : Fin (jj + 1)} {hd hd' : Fin m} {cl cl' : Fin m → Γ}
    (h : HoldsWindow cols off r hd cl) (h' : HoldsWindow cols off r hd' cl') :
    (hd, cl) = (hd', cl') := by
  have hb : HoldsBits cols off r ((tapeCodec m).enc (hd, cl)) := by
    intro q hq
    exact h q (by rw [(tapeCodec m).enc_length] at hq; exact hq)
  have hb' : HoldsBits cols off r ((tapeCodec m).enc (hd', cl')) := by
    intro q hq
    exact h' q (by rw [(tapeCodec m).enc_length] at hq; exact hq)
  refine (tapeCodec m).enc_injective (hb.inj hb' ?_)
  rw [(tapeCodec m).enc_length, (tapeCodec m).enc_length]

/-- **The registers determine the code.** The same registers cannot hold two different codes, so
comparing registers compares codes — which is what the walk's "stay" step and the final
comparison need. -/
theorem HoldsCode.inj {kk : ℕ} {tm : NTM kk} {x : List Bool} {S jj : ℕ}
    {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ} {R : CodeRegs kk jj}
    {a b : Code tm.Q kk x.length S} (ha : HoldsCode tm x S cols off R a)
    (hb : HoldsCode tm x S cols off R b) : a = b := by
  have hst : a.1 = b.1 := by
    refine (qCodec tm.Q).enc_injective (ha.state.inj hb.state ?_)
    rw [(qCodec tm.Q).enc_length, (qCodec tm.Q).enc_length]
  have hhd : a.2.1 = b.2.1 := by
    refine (finCodec (x.length + S + 2)).enc_injective (ha.inputHead.inj hb.inputHead ?_)
    rw [(finCodec (x.length + S + 2)).enc_length, (finCodec (x.length + S + 2)).enc_length]
  have hwk : a.2.2.1 = b.2.2.1 := by
    funext i
    exact HoldsWindow.inj (ha.work i) (hb.work i)
  have hot : a.2.2.2 = b.2.2.2 := HoldsWindow.inj ha.output hb.output
  exact Prod.ext hst (Prod.ext hhd (Prod.ext hwk hot))

/-- A register holding an encoded window holds the corresponding bits. -/
theorem HoldsWindow.bits {m : ℕ} [NeZero m] {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ}
    {r : Fin (jj + 1)} {hd : Fin m} {cl : Fin m → Γ} (h : HoldsWindow cols off r hd cl) :
    HoldsBits cols off r ((tapeCodec m).enc (hd, cl)) := by
  intro q hq
  exact h q (by rw [(tapeCodec m).enc_length] at hq; exact hq)

/-- A register holding an encoded window holds that window. -/
theorem HoldsWindow.of_bits {m : ℕ} [NeZero m] {jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ} {off : ℕ}
    {r : Fin (jj + 1)} {hd : Fin m} {cl : Fin m → Γ}
    (h : HoldsBits cols off r ((tapeCodec m).enc (hd, cl))) : HoldsWindow cols off r hd cl := by
  intro q hq
  exact h q (by rw [(tapeCodec m).enc_length]; exact hq)

/-- **Blocks on the right registers are a code.** -/
theorem holdsCode_of_blocks {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (h : ∀ p, p < kk + 3 →
      HoldsBits (fun q => cols (0 + q)) 0 (j p) (codeBlock tm x S a p)) :
    HoldsCode tm x S cols 0 (codeRegsOf j) a := by
  refine ⟨?_, ?_, fun i => ?_, ?_⟩
  · have := h 0 (by omega)
    rwa [codeBlock, dite_eq_left rfl] at this
  · have := h 1 (by omega)
    rwa [codeBlock, dite_eq_right (by omega), dite_eq_left rfl] at this
  · have hb := h (i.val + 2) (by omega)
    rw [codeBlock, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega),
      show (⟨i.val + 2 - 2, by omega⟩ : Fin kk) = i from Fin.ext (by simp)] at hb
    exact HoldsWindow.of_bits hb
  · have hb := h (kk + 2) (by omega)
    rw [codeBlock, dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega)] at hb
    exact HoldsWindow.of_bits hb

/-- **A guess stage can lay down any code.** Given a guess tape whose bits, block by block, are
the code's own encoding, the `kk + 3` guessed registers hold that code. Together with
`Complexity.NTM.exists_loadTape` this is how a nondeterministic step is taken: guess a code, then
check it. -/
theorem holdsCode_of_guessBlocks {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {m : ℕ}
    (j : ℕ → Fin (m + 1)) (hj : ∀ p, j p ≠ Fin.last m) (W : Fin (m + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (hinj : ∀ p q, p < kk + 3 → q < kk + 3 → j p = j q → p = q)
    (hr1 : ∀ p, p < kk + 3 → (W (j p)).head = 1) (a : Code tm.Q kk x.length S)
    (hg : ∀ p, p < kk + 3 → ∀ q ≤ codeWidth tm x.length S p, (W (Fin.last m)).cells
      ((W (Fin.last m)).head + TM.guessOffset (codeWidth tm x.length S) p + q)
        = Γ.ofBool ((codeBlock tm x S a p).getD q false)) :
    HoldsCode tm x S
      (fun c i => (TM.guessBlocksTapes j (codeWidth tm x.length S) (kk + 3) W i).cells c) 0
      (codeRegsOf j) a := by
  have hbits := holdsBits_of_guessBlocks j hj (codeWidth tm x.length S) (kk + 3) W hinv hh hinj
    hr1 (fun p q => (codeBlock tm x S a p).getD q false) hg
  refine holdsCode_of_blocks tm x S _ j a (fun p hp => ?_)
  simp only [Nat.zero_add]
  refine (hbits p hp).of_isPrefix
    (isPrefix_ofFn (fun q => (codeBlock tm x S a p).getD q false) ?_ ?_)
  · rw [codeBlock_length, codeWidth]
    omega
  · intro q hq
    simp [List.getD, List.getElem?_eq_getElem hq]

/-- **A stage of the loop lays down the code its stream names.** The guess-tape clause of the
walk's invariant feeds exactly this. -/
theorem holdsCode_of_stage {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {m : ℕ}
    (j : ℕ → Fin (m + 1)) (hj : ∀ p, j p ≠ Fin.last m) (W : Fin (m + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (hinj : ∀ p q, p < kk + 3 → q < kk + 3 → j p = j q → p = q)
    (hr1 : ∀ p, p < kk + 3 → (W (j p)).head = 1) (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks (codeWidth tm x.length S) (kk + 3) b g) (s : ℕ)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (codeWidth tm x.length S) (kk + 3) + q))
      (W (Fin.last m)))
    (a : Code tm.Q kk x.length S)
    (hb : ∀ p, p < kk + 3 → ∀ q, q ≤ codeWidth tm x.length S p →
      b s p q = (codeBlock tm x S a p).getD q false) :
    HoldsCode tm x S
      (fun c i => (TM.guessBlocksTapes j (codeWidth tm x.length S) (kk + 3) W i).cells c) 0
      (codeRegsOf j) a := by
  refine holdsCode_of_guessBlocks tm x S j hj W hinv hh hinj hr1 a ?_
  intro p hp q hq
  rw [TM.blocks_of_stageBlocks hs s hgf p hp q hq, hb p hp q hq]


/-- Holding a code depends only on the registers' cells, not on their heads — which is why a
rewind between the guess and the checks is harmless. -/
theorem HoldsCode.of_cells_eq {kk jj : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    {cols cols' : ℕ → Fin (jj + 1) → Γ} {off : ℕ} {R : CodeRegs kk jj}
    {a : Code tm.Q kk x.length S} (h : HoldsCode tm x S cols off R a)
    (hc : ∀ q i, cols' q i = cols q i) : HoldsCode tm x S cols' off R a := by
  have heq : cols' = cols := by
    funext q i
    exact hc q i
  rw [heq]
  exact h

/-- **After a code-guessing stage the registers hold the code.** The stage rewinds the guessed
registers so the scans can read them; the rewind moves heads, and a code is held in cells. -/
theorem holdsCode_of_guessStage {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {m : ℕ}
    (j : ℕ → Fin (m + 1)) (hj : ∀ p, j p ≠ Fin.last m) (W : Fin (m + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (hinj : ∀ p q, p < kk + 3 → q < kk + 3 → j p = j q → p = q)
    (hr1 : ∀ p, p < kk + 3 → (W (j p)).head = 1) (a : Code tm.Q kk x.length S)
    (hg : ∀ p, p < kk + 3 → ∀ q ≤ codeWidth tm x.length S p, (W (Fin.last m)).cells
      ((W (Fin.last m)).head + TM.guessOffset (codeWidth tm x.length S) p + q)
        = Γ.ofBool ((codeBlock tm x S a p).getD q false))
    (work : Fin (m + 1) → Tape)
    (hcells : ∀ i, (work i).cells
      = (TM.guessBlocksTapes j (codeWidth tm x.length S) (kk + 3) W i).cells) :
    HoldsCode tm x S (fun c i => (work i).cells c) 0 (codeRegsOf j) a :=
  (holdsCode_of_guessBlocks tm x S j hj W hinv hh hinj hr1 a hg).of_cells_eq
    (fun q i => by rw [hcells i])

/-! ## The layout the walk's scan reads

A check reads the guessed transition from the first cells of the parameter register, and the
fields it checks from the cells after that. So every register except the state's — whose check
reads it alongside the parameters — carries a block of padding as wide as the parameter block,
and its field begins where the padding ends. -/

/-- The bits block `p` of a code guess holds in the walk's layout. -/
noncomputable def codeBlockScan {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (p : ℕ) : List Bool :=
  if p = 0 then codeBlock tm x S a 0
  else List.replicate (succParamsCodec tm.Q kk).width false ++ (codeBlock tm x S a p ++ [false])

/-- The block widths that layout guesses. -/
noncomputable def codeWidthScan {kk : ℕ} (tm : NTM kk) (nn S : ℕ) (p : ℕ) : ℕ :=
  if p = 0 then codeWidth tm nn S 0
  else (succParamsCodec tm.Q kk).width + codeWidth tm nn S p + 1

/-- The registers hold code `a` where the walk's scan looks for it. -/
def HoldsCodeScan {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (cols : ℕ → Fin (jj + 1) → Γ) (R : CodeRegs kk jj) (a : Code tm.Q kk x.length S) : Prop :=
  HoldsBits cols 0 R.st ((qCodec tm.Q).enc a.1) ∧
    HoldsBits cols (succParamsCodec tm.Q kk).width R.hd
      ((finCodec (x.length + S + 2)).enc a.2.1) ∧
    (∀ i, HoldsWindow cols (succParamsCodec tm.Q kk).width (R.wk i)
      (a.2.2.1 i).1 (a.2.2.1 i).2) ∧
    HoldsWindow cols (succParamsCodec tm.Q kk).width R.ot a.2.2.2.1 a.2.2.2.2

/-- **The block ends with a cell carrying no head marker.** The window checks need to know that
the chunk just past the window is unmarked; rather than reason about untouched tape, the guess
writes one more zero and the check reads it. -/
theorem markOf_end {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (p m : ℕ) (hp : p ≠ 0)
    (hlen : (codeBlock tm x S a p).length = 3 * m)
    (cols : ℕ → Fin (jj + 1) → Γ) (r : Fin (jj + 1))
    (h : HoldsBits cols 0 r (codeBlockScan tm x S a p)) :
    markOf cols (succParamsCodec tm.Q kk).width r m = false := by
  set pw := (succParamsCodec tm.Q kk).width with hpw
  have hblk : codeBlockScan tm x S a p
      = List.replicate pw false ++ (codeBlock tm x S a p ++ [false]) := by
    rw [codeBlockScan, ite_eq_right hp]
  have hlast : (codeBlockScan tm x S a p)[pw + 3 * m]?  = some false := by
    rw [hblk, List.getElem?_append_right (by rw [List.length_replicate]; omega),
      List.length_replicate, show pw + 3 * m - pw = 3 * m by omega,
      List.getElem?_append_right (by omega), hlen, show 3 * m - 3 * m = 0 by omega]
    rfl
  have hlt : pw + 3 * m < (codeBlockScan tm x S a p).length := by
    rw [hblk]
    simp only [List.length_append, List.length_replicate, hlen, List.length_cons,
      List.length_nil]
    omega
  have hcell := h (pw + 3 * m) hlt
  rw [Nat.zero_add] at hcell
  have hval : (codeBlockScan tm x S a p)[pw + 3 * m]'hlt = false :=
    Option.some_injective _ (by rw [← List.getElem?_eq_getElem hlt, hlast])
  rw [hval] at hcell
  rw [markOf, hcell]
  rfl

/-- **Blocks in the walk's layout are a code the scan can read.** -/
theorem holdsCodeScan_of_blocks {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (h : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p)) :
    HoldsCodeScan tm x S cols (codeRegsOf j) a := by
  have hpad : ∀ p, p < kk + 3 → p ≠ 0 →
      HoldsBits cols (succParamsCodec tm.Q kk).width (j p) (codeBlock tm x S a p) := by
    intro p hp hp0
    have hb := h p hp
    rw [codeBlockScan, ite_eq_right hp0] at hb
    have hdrop := hb.drop_prefix
    rw [List.length_replicate] at hdrop
    exact hdrop.of_isPrefix ⟨[false], rfl⟩
  refine ⟨?_, ?_, fun i => ?_, ?_⟩
  · have hb := h 0 (by omega)
    rw [codeBlockScan, ite_eq_left rfl, codeBlock, dite_eq_left rfl] at hb
    exact hb
  · have hb := hpad 1 (by omega) (by omega)
    rwa [codeBlock, dite_eq_right (by omega), dite_eq_left rfl] at hb
  · have hb := hpad (i.val + 2) (by omega) (by omega)
    rw [codeBlock, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega),
      show (⟨i.val + 2 - 2, by omega⟩ : Fin kk) = i from Fin.ext (by simp)] at hb
    exact HoldsWindow.of_bits hb
  · have hb := hpad (kk + 2) (by omega) (by omega)
    rw [codeBlock, dite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega)] at hb
    exact HoldsWindow.of_bits hb

/-! ## What each scan says about the code the registers hold -/

variable {kk : ℕ} {tm : NTM kk} {x : List Bool} {S jj : ℕ} {cols : ℕ → Fin (jj + 1) → Γ}
  {off : ℕ}

/-- The state a scan reads off a code's state register. -/
theorem ofTable_state {R : CodeRegs kk jj} {a : Code tm.Q kk x.length S}
    (h : HoldsCode tm x S cols off R a) (s w : ℕ) (regs : Fin s → Fin (jj + 1)) (t : Fin s)
    (ht : regs t = R.st) (hc : (qCodec tm.Q).width ≤ w) (x₀ : Fin s → Fin w → Bool) :
    (qCodec tm.Q).ofTable (tableSlice
        (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs)
          (fun q => cols (off + q)) w).2 t (qCodec tm.Q).width hc) = a.1 :=
  ofTable_of_holds (qCodec tm.Q) a.1 cols off s w regs t hc x₀ (ht ▸ h.state)

/-- **What the work-window scan says.** -/
theorem blockEmit_work {Ra Rb : CodeRegs kk jj} {a b : Code tm.Q kk x.length S}
    (ha : HoldsCode tm x S cols off Ra a) (hb : HoldsCode tm x S cols off Rb b)
    (P : SuccParams tm.Q kk) (i : Fin kk)
    (hend : markOf (fun q => cols (off + q)) 0 (Ra.wk i) (S + 1) = false) :
    blockEmit (succDir tm P i) (Scanner.chunkRun
        (blockStep (Ra.wk i) (Rb.wk i) (gammaBits (P.wSym i)) (gammaBits (succWrite tm P i))
          (succDir tm P i)) (fun q => cols (off + q)) 0 blockStart (S + 1)) = true ↔
      ((a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i ∧
        (∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
          else (a.2.2.1 i).2 p) ∧
        (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val) :=
  blockEmit_holds (fun q => cols (off + q)) 0 (Ra.wk i) (Rb.wk i) _ _ _ _ (ha.work i)
    (hb.work i) (P.wSym i) (succWrite tm P i) (succDir tm P i) (by omega) hend

/-- **What the output-window scan says.** -/
theorem blockEmit_output {Ra Rb : CodeRegs kk jj} {a b : Code tm.Q kk x.length S}
    (ha : HoldsCode tm x S cols off Ra a) (hb : HoldsCode tm x S cols off Rb b)
    (P : SuccParams tm.Q kk)
    (hend : markOf (fun q => cols (off + q)) 0 Ra.ot (S + 2) = false) :
    blockEmit (succTrans tm P).2.2.2.2.2 (Scanner.chunkRun
        (blockStep Ra.ot Rb.ot (gammaBits P.oSym)
          (gammaBits (((succTrans tm P).2.2.1 : Γw) : Γ)) (succTrans tm P).2.2.2.2.2)
        (fun q => cols (off + q)) 0 blockStart (S + 2)) = true ↔
      (a.2.2.2.2 a.2.2.2.1 = P.oSym ∧
        (∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
          then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p) ∧
        b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val) :=
  blockEmit_holds (fun q => cols (off + q)) 0 Ra.ot Rb.ot _ _ _ _ ha.output hb.output
    P.oSym (((succTrans tm P).2.2.1 : Γw) : Γ) (succTrans tm P).2.2.2.2.2 (by omega) hend

/-- **What the input-head scan says.** -/
theorem inHeadEmit_code {Ra Rb : CodeRegs kk jj} {a b : Code tm.Q kk x.length S}
    (ha : HoldsCode tm x S cols off Ra a) (hb : HoldsCode tm x S cols off Rb b)
    (d : Dir3) (hleft : d = Dir3.left → 0 < a.2.1.val) :
    inHeadEmit d (Scanner.cellFold (inHeadStep Ra.hd Rb.hd d) cols off (true, true)
        (bitWidth (x.length + S + 2))) = true ↔
      b.2.1.val = movedIdx d a.2.1.val :=
  inHeadEmit_of_holds cols off Ra.hd Rb.hd d (bitWidth (x.length + S + 2)) a.2.1.val b.2.1.val
    (lt_of_lt_of_le a.2.1.isLt (le_two_pow_bitWidth _))
    (lt_of_lt_of_le b.2.1.isLt (le_two_pow_bitWidth _))
    ha.inputHead hb.inputHead hleft

/-- **The successor check, assembled.** Every scan verdict says what its field must, and together
they say the guessed code is a successor of the held one. -/
theorem mem_codeSucc_of_scans {Ra Rb : CodeRegs kk jj} {a b : Code tm.Q kk x.length S}
    (ha : HoldsCode tm x S cols off Ra a) (hb : HoldsCode tm x S cols off Rb b)
    (P : SuccParams tm.Q kk) (hne : a.1 ≠ tm.qhalt)
    (hq : a.1 = P.q) (hstate : b.1 = succState tm P)
    (hin : P.inSym = inSymOf tm x S a)
    (hclampIn : movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hclampW : ∀ i, movedIdx (succDir tm P i) (a.2.2.1 i).1.val ≤ S)
    (hclampO : movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ≤ S + 1)
    (hleft : (succTrans tm P).2.2.2.1 = Dir3.left → 0 < a.2.1.val)
    (hendW : ∀ i, markOf (fun q => cols (off + q)) 0 (Ra.wk i) (S + 1) = false)
    (hendO : markOf (fun q => cols (off + q)) 0 Ra.ot (S + 2) = false)
    (vhead : inHeadEmit (succTrans tm P).2.2.2.1
      (Scanner.cellFold (inHeadStep Ra.hd Rb.hd (succTrans tm P).2.2.2.1) cols off (true, true)
        (bitWidth (x.length + S + 2))) = true)
    (vwork : ∀ i, blockEmit (succDir tm P i) (Scanner.chunkRun
      (blockStep (Ra.wk i) (Rb.wk i) (gammaBits (P.wSym i)) (gammaBits (succWrite tm P i))
        (succDir tm P i)) (fun q => cols (off + q)) 0 blockStart (S + 1)) = true)
    (vout : blockEmit (succTrans tm P).2.2.2.2.2 (Scanner.chunkRun
      (blockStep Ra.ot Rb.ot (gammaBits P.oSym)
        (gammaBits (((succTrans tm P).2.2.1 : Γw) : Γ)) (succTrans tm P).2.2.2.2.2)
      (fun q => cols (off + q)) 0 blockStart (S + 2)) = true) :
    b ∈ NTM.codeSucc tm x S a := by
  have hw := fun i => (blockEmit_work ha hb P i (hendW i)).mp (vwork i)
  have ho := (blockEmit_output ha hb P hendO).mp vout
  exact mem_codeSucc_of_checks tm x S a b P hne hq hin (fun i => (hw i).1) ho.1
    hclampIn hclampW hclampO hstate ((inHeadEmit_code ha hb _ hleft).mp vhead)
    (fun i => ⟨(hw i).2.2, (hw i).2.1⟩) ⟨ho.2.2, ho.2.1⟩

/-! ## What the loops establish

The walk and the counting are stated here in the form the loops produce them: a walk as a
sequence of codes each either kept or stepped, and a round list as an injective enumeration. -/

/-- **What a walk establishes.** A sequence of codes, each either equal to its predecessor or a
verified successor of it, lands in the round its length names. -/
theorem mem_reachCodes_of_walk (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q kk x.length S) (i : ℕ) (f : ℕ → Code tm.Q kk x.length S)
    (h0 : f 0 = a₀)
    (hstep : ∀ j < i, f (j + 1) = f j ∨ f (j + 1) ∈ NTM.codeSucc tm x S (f j)) :
    f i ∈ NTM.reachCodes tm x S a₀ i :=
  (NTM.mem_reachCodes_iff_walk tm x S a₀ i (f i)).mpr ⟨f, h0, rfl, hstep⟩

/-- **What the counting establishes.** Codes enumerated without repetition, each verified to be in
the round, and at least as many of them as the round holds, form a round list — which is what
licenses concluding that a code not among them is not in the round. -/
theorem roundList_of_inj (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q kk x.length S) (i N : ℕ) (g : Fin N → Code tm.Q kk x.length S)
    (hinj : Function.Injective g) (hmem : ∀ t, g t ∈ NTM.reachCodes tm x S a₀ i)
    (hcard : (NTM.reachCodes tm x S a₀ i).card ≤ N) :
    NTM.RoundList tm x S a₀ i (List.ofFn g) := by
  refine ⟨List.nodup_ofFn.mpr hinj, ?_, ?_⟩
  · intro c hc
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hc
    exact hmem t
  · rw [List.length_ofFn]
    exact hcard

/-! ## The shape of a loop invariant

`TM.loopTM_hoareTime_indexed` asks for a family of tape predicates `E j`, a step from `E j` to
`E (j + 1)`, and a stop at `E N`. For the walk, `E j` says the counter holds `j` and the code
registers hold the `j`-th code of the walk — so the loop's own index is the walk's index. -/

/-- The reading of a counter register as a number. -/
def counterVal {jj : ℕ} (cnt : Fin (jj + 1)) (wc : ℕ) (work : Fin (jj + 1) → Tape) : ℕ :=
  binValLE (List.ofFn fun q : Fin wc => decide ((work cnt).cells (q.val + 1) = Γ.one))

/-- A tape predicate pinning a counter register to a value. The bound `v < 2 ^ wc` is part of it:
past that point a fixed-width counter wraps, and a loop rule needs the counter to *name* its
index. -/
def HoldsCounter {jj : ℕ} (cnt : Fin (jj + 1)) (wc : ℕ) (v : ℕ) : TM.TapePred (jj + 1) :=
  fun _inp work _out => v < 2 ^ wc ∧
    HoldsBits (fun p i => (work i).cells p) 0 cnt (bitsOfLenLE wc v)

/-- The walk loop's invariant. The bound `j < 2 ^ wc` is part of it: past that point the counter
would wrap, and the loop rule needs the counter to *name* the index. -/
def WalkInv (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ} (R : CodeRegs kk jj)
    (cnt : Fin (jj + 1)) (wc : ℕ) (f : ℕ → Code tm.Q kk x.length S) (j : ℕ) :
    TM.TapePred (jj + 1) :=
  fun _inp work _out =>
    j < 2 ^ wc ∧ HoldsCode tm x S (fun p i => (work i).cells p) 0 R (f j) ∧
      HoldsBits (fun p i => (work i).cells p) 0 cnt (bitsOfLenLE wc j)

/-- **The counter reads back the index.** This is the `idx` obligation of the indexed loop rule:
a tape predicate that pins the counter determines the loop's index. -/
theorem counterVal_of_walkInv (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (R : CodeRegs kk jj) (cnt : Fin (jj + 1)) (wc : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (j : ℕ)
    (inp : Tape) (work : Fin (jj + 1) → Tape) (out : Tape)
    (h : WalkInv tm x S R cnt wc f j inp work out) : counterVal cnt wc work = j := by
  obtain ⟨hj, -, hcnt⟩ := h
  have hbits : (List.ofFn fun q : Fin wc => decide ((work cnt).cells (q.val + 1) = Γ.one))
      = bitsOfLenLE wc j := by
    refine List.ext_getElem (by simp [bitsOfLenLE_length]) ?_
    intro q h1 h2
    have hq : q < wc := by simpa using h1
    have hc := hcnt q (by rw [bitsOfLenLE_length]; exact hq)
    simp only [Nat.zero_add] at hc
    simp only [List.getElem_ofFn]
    show decide ((work cnt).cells (q + 1) = Γ.one) = _
    rw [hc]
    cases (bitsOfLenLE wc j)[q]'(by rw [bitsOfLenLE_length]; exact hq) <;> simp [Γ.ofBool]
  rw [counterVal, hbits, binValLE_bitsOfLenLE wc j hj]

/-! ## The scanner that checks one window

Three tapes are scanned: the parameter block, the old window, the new window; the verdict goes to
a fourth. The parameters come first, so by the time the windows are reached the transition is
known. -/

/-- The state of a window check: a chunk position, two buffered columns, and the four running
checks. -/
abbrev WindowState : Type :=
  Fin 3 × (Fin 3 → Γ) × (Fin 3 → Γ) ×
    ((Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool × Bool × Bool))

/-- Equality of window states is decidable; the machine need not be computable. -/
noncomputable instance : DecidableEq WindowState := Classical.decEq _

/-- The state a parameter reader accumulates: how many cells it has read, and the bits. -/
abbrev ParamAcc (tm : NTM kk) : Type :=
  Fin ((succParamsCodec tm.Q kk).width + 1) ×
    (Fin 1 → Fin (succParamsCodec tm.Q kk).width → Bool)

/-- The parameters a window check has read. -/
noncomputable def paramsOfTable (tm : NTM kk) (a : ParamAcc tm) : SuccParams tm.Q kk :=
  (succParamsCodec tm.Q kk).ofTable (a.2 0)

/-- **The window checker.** -/
noncomputable def windowScanner (tm : NTM kk) (i : Fin kk) : Scanner 2 :=
  Scanner.prefixed (succParamsCodec tm.Q kk).width (ParamAcc tm) WindowState
    (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0))
    (fun _ => (0, (fun _ => Γ.blank), (fun _ => Γ.blank), blockStart))
    (fun a t col => Scanner.chunkStepCell
      (blockStep 1 2 (gammaBits ((paramsOfTable tm a).wSym i))
        (gammaBits (succWrite tm (paramsOfTable tm a) i))
        (succDir tm (paramsOfTable tm a) i)) t col)
    (fun a t => blockEmit (succDir tm (paramsOfTable tm a) i) t.2.2.2)

theorem succParamsCodec_width_pos (tm : NTM kk) : 0 < (succParamsCodec tm.Q kk).width := by
  rw [succParamsCodec_width]
  omega

/-- The parameters a window scan reads off the tapes it is given. -/
noncomputable def windowParams (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) : SuccParams tm.Q kk :=
  paramsOfTable tm (Scanner.auxRun (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0)) cols
    (succParamsCodec tm.Q kk).width)

set_option maxHeartbeats 1000000 in
/-- **What the window checker computes**: the block check, with the parameters it read. -/
theorem windowScanner_run (tm : NTM kk) (i : Fin kk) (cols : ℕ → Fin 3 → Γ) (S : ℕ) :
    (windowScanner tm i).emit ((windowScanner tm i).run cols
        ((succParamsCodec tm.Q kk).width + 3 * (S + 1)))
      = blockEmit (succDir tm (windowParams tm cols) i)
        (Scanner.chunkRun (blockStep 1 2 (gammaBits ((windowParams tm cols).wSym i))
          (gammaBits (succWrite tm (windowParams tm cols) i))
          (succDir tm (windowParams tm cols) i)) cols (succParamsCodec tm.Q kk).width
          blockStart (S + 1)) := by
  rw [windowParams, windowScanner,
    Scanner.prefixed_run _ _ _ _ _ _ cols (succParamsCodec_width_pos tm) (3 * (S + 1))]
  rw [Scanner.mainRun_eq_cellFold]
  exact congrArg _ (Scanner.cellFold_chunk _ cols _ blockStart _ _ (S + 1)).2

/-- **The output-window checker.** The same scanner as for a work tape, with the transition's
output write and direction. -/
noncomputable def outputScanner (tm : NTM kk) : Scanner 2 :=
  Scanner.prefixed (succParamsCodec tm.Q kk).width (ParamAcc tm) WindowState
    (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0))
    (fun _ => (0, (fun _ => Γ.blank), (fun _ => Γ.blank), blockStart))
    (fun a t col => Scanner.chunkStepCell
      (blockStep 1 2 (gammaBits (paramsOfTable tm a).oSym)
        (gammaBits (((succTrans tm (paramsOfTable tm a)).2.2.1 : Γw) : Γ))
        (succTrans tm (paramsOfTable tm a)).2.2.2.2.2) t col)
    (fun a t => blockEmit (succTrans tm (paramsOfTable tm a)).2.2.2.2.2 t.2.2.2)

set_option maxHeartbeats 1000000 in
/-- **What the output checker computes.** -/
theorem outputScanner_run (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) (S : ℕ) :
    (outputScanner tm).emit ((outputScanner tm).run cols
        ((succParamsCodec tm.Q kk).width + 3 * (S + 2)))
      = blockEmit (succTrans tm (windowParams tm cols)).2.2.2.2.2
        (Scanner.chunkRun (blockStep 1 2 (gammaBits (windowParams tm cols).oSym)
          (gammaBits (((succTrans tm (windowParams tm cols)).2.2.1 : Γw) : Γ))
          (succTrans tm (windowParams tm cols)).2.2.2.2.2) cols
          (succParamsCodec tm.Q kk).width blockStart (S + 2)) := by
  rw [windowParams, outputScanner,
    Scanner.prefixed_run _ _ _ _ _ _ cols (succParamsCodec_width_pos tm) (3 * (S + 2))]
  rw [Scanner.mainRun_eq_cellFold]
  exact congrArg _ (Scanner.cellFold_chunk _ cols _ blockStart _ _ (S + 2)).2

/-- **The input-head checker.** Two tapes are scanned: the parameter block and, after it, the two
input-head registers — the direction is known by the time they are reached. -/
noncomputable def headScanner (tm : NTM kk) : Scanner 2 :=
  Scanner.prefixed (succParamsCodec tm.Q kk).width (ParamAcc tm) (Bool × Bool)
    (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0))
    (fun _ => (true, true))
    (fun a t col => inHeadStep 1 2 (succTrans tm (paramsOfTable tm a)).2.2.2.1 t col)
    (fun a t => inHeadEmit (succTrans tm (paramsOfTable tm a)).2.2.2.1 t)

set_option maxHeartbeats 1000000 in
/-- **What the input-head checker computes.** -/
theorem headScanner_run (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) (w : ℕ) :
    (headScanner tm).emit ((headScanner tm).run cols
        ((succParamsCodec tm.Q kk).width + w))
      = inHeadEmit (succTrans tm (windowParams tm cols)).2.2.2.1
        (Scanner.cellFold (inHeadStep 1 2 (succTrans tm (windowParams tm cols)).2.2.2.1) cols
          (succParamsCodec tm.Q kk).width (true, true) w) := by
  rw [windowParams, headScanner,
    Scanner.prefixed_run _ _ _ _ _ _ cols (succParamsCodec_width_pos tm) w,
    Scanner.mainRun_eq_cellFold]

/-! ## The state checks

Unlike the window and head checks, these read both registers during the parameter phase — a state
field is a constant number of cells — so the check lives entirely in the accumulated table and the
per-cell state is trivial. -/

/-- The width a state check scans: enough for the parameter block and for a state field. -/
noncomputable def stateWidth (tm : NTM kk) : ℕ :=
  max (succParamsCodec tm.Q kk).width (qCodec tm.Q).width

/-- What a state check has accumulated. -/
abbrev StateAcc (tm : NTM kk) : Type :=
  Fin (stateWidth tm + 1) × (Fin 2 → Fin (stateWidth tm) → Bool)

/-- The state a state check has read off the code's register. -/
noncomputable def stateOfTable (tm : NTM kk) (a : StateAcc tm) : tm.Q :=
  (qCodec tm.Q).ofTable (tableSlice a.2 1 (qCodec tm.Q).width (le_max_right _ _))

/-- The parameters a state check has read. -/
noncomputable def paramsOfStateTable (tm : NTM kk) (a : StateAcc tm) : SuccParams tm.Q kk :=
  (succParamsCodec tm.Q kk).ofTable
    (tableSlice a.2 0 (succParamsCodec tm.Q kk).width (le_max_left _ _))

/-- **The state checker.** With `isNew = false` it checks the old code's state against the guessed
one; with `isNew = true`, the new code's state against the one the transition produces. -/
noncomputable def stateScanner (tm : NTM kk) (isNew : Bool) : Scanner 1 :=
  Scanner.prefixed (stateWidth tm) (StateAcc tm) Unit
    (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 2 (stateWidth tm) (fun t => t))
    (fun _ => ())
    (fun _ t _ => t)
    (fun a _ => decide (stateOfTable tm a =
      if isNew then succState tm (paramsOfStateTable tm a) else (paramsOfStateTable tm a).q))

/-- The table a state check accumulates from given tapes. -/
noncomputable def stateTable (tm : NTM kk) (cols : ℕ → Fin 2 → Γ) : StateAcc tm :=
  Scanner.auxRun (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 2 (stateWidth tm) (fun t => t)) cols (stateWidth tm)

theorem stateWidth_pos (tm : NTM kk) : 0 < stateWidth tm :=
  lt_of_lt_of_le (succParamsCodec_width_pos tm) (le_max_left _ _)

set_option maxHeartbeats 1000000 in
/-- **What a state checker computes.** -/
theorem stateScanner_run (tm : NTM kk) (isNew : Bool) (cols : ℕ → Fin 2 → Γ) :
    (stateScanner tm isNew).emit ((stateScanner tm isNew).run cols (stateWidth tm))
      = decide (stateOfTable tm (stateTable tm cols) =
        if isNew then succState tm (paramsOfStateTable tm (stateTable tm cols))
        else (paramsOfStateTable tm (stateTable tm cols)).q) := by
  have h := Scanner.prefixed_run (α := StateAcc tm) (τ := Unit) (stateWidth tm)
    (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 2 (stateWidth tm) (fun t => t)) (fun _ => ()) (fun _ t _ => t)
    (fun a _ => decide (stateOfTable tm a =
      if isNew then succState tm (paramsOfStateTable tm a) else (paramsOfStateTable tm a).q))
    cols (stateWidth_pos tm) 0
  rw [stateTable, stateScanner]
  exact h

/-! ## When the simulated input head is at the marker

A machine cannot keep its own input head on cell zero: reading `▷` forces that head right on every
step. But it need not — a simulated head at cell zero reads `▷`, which the code's own head field
already says. So the input symbol is checked against the tape only when the head field is nonzero;
when it is zero the check is on the parameter register alone. -/

/-- The scan that decides whether a code's input-head field is zero: every bit of the field is a
zero. -/
noncomputable def headZeroScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (hd : Fin (jj + 1)) :
    Scanner jj :=
  ((Scanner.isConst jj hd Γ.zero).after (succParamsCodec tm.Q kk).width).upTo
    ((succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width)

/-- A string of zeros has value zero. -/
theorem binValLE_replicate_false : ∀ ℓ : ℕ, binValLE (List.replicate ℓ false) = 0 := by
  intro ℓ
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
      rw [List.replicate_succ, binValLE, ih]
      rfl

/-- A fixed-width encoding is all zeros exactly when it encodes zero. -/
theorem bitsOfLenLE_all_false_iff (ℓ v : ℕ) (hv : v < 2 ^ ℓ) :
    (∀ q, (hq : q < ℓ) →
      (bitsOfLenLE ℓ v)[q]'(by rw [bitsOfLenLE_length]; exact hq) = false) ↔ v = 0 := by
  constructor
  · intro h
    have hrep : bitsOfLenLE ℓ v = List.replicate ℓ false := by
      refine List.ext_getElem (by rw [bitsOfLenLE_length, List.length_replicate]) ?_
      intro q h1 h2
      rw [List.getElem_replicate]
      exact h q (by rw [bitsOfLenLE_length] at h1; exact h1)
    have hval := binValLE_bitsOfLenLE ℓ v hv
    rw [hrep, binValLE_replicate_false] at hval
    exact hval.symm
  · intro h q hq
    subst h
    have hrep : ∀ m : ℕ, bitsOfLenLE m 0 = List.replicate m false := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
          rw [bitsOfLenLE, List.replicate_succ, ih]
          rfl
    have : (bitsOfLenLE ℓ 0)[q]? = some false := by
      rw [hrep ℓ, List.getElem?_replicate]
      rw [ite_eq_left hq]
    exact Option.some_injective _
      (by rw [← List.getElem?_eq_getElem (by rw [bitsOfLenLE_length]; exact hq), this])

/-- **The zero-head scan decides that the code's input head is at the marker.** -/
theorem headZeroScanner_decides {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (hd : Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ)
    (hlen : (succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width ≤ len)
    (u : Fin (nn + S + 2))
    (hu : HoldsBits cols (succParamsCodec tm.Q kk).width hd ((finCodec (nn + S + 2)).enc u)) :
    (headZeroScanner tm nn S hd).emit ((headZeroScanner tm nn S hd).run cols len) = true ↔
      u.val = 0 := by
  rw [headZeroScanner, Scanner.isConst_range_run _ _ _ _ _ _ len hlen]
  have hwidth : (finCodec (nn + S + 2)).width = bitWidth (nn + S + 2) := rfl
  have hbound : u.val < 2 ^ bitWidth (nn + S + 2) :=
    lt_of_lt_of_le u.isLt (le_two_pow_bitWidth _)
  rw [← bitsOfLenLE_all_false_iff (bitWidth (nn + S + 2)) u.val hbound]
  constructor
  · intro h q hq
    have hcell := hu q (by rw [(finCodec (nn + S + 2)).enc_length]; exact hq)
    have hz := h ((succParamsCodec tm.Q kk).width + q + 1) (by omega) (by rw [hwidth]; omega)
    rw [hz] at hcell
    cases hb : ((finCodec (nn + S + 2)).enc u)[q]'(by
      rw [(finCodec (nn + S + 2)).enc_length]; exact hq) with
    | false => exact hb
    | true =>
        rw [hb] at hcell
        exact absurd hcell.symm (fun hc => Γ.noConfusion hc)
  · intro h q h1 h2
    have hq : q - (succParamsCodec tm.Q kk).width - 1 < bitWidth (nn + S + 2) := by
      rw [hwidth] at h2
      omega
    have hcell := hu (q - (succParamsCodec tm.Q kk).width - 1)
      (by rw [(finCodec (nn + S + 2)).enc_length]; exact hq)
    rw [show (succParamsCodec tm.Q kk).width + (q - (succParamsCodec tm.Q kk).width - 1) + 1 = q
      by omega] at hcell
    rw [hcell]
    show Γ.ofBool ((bitsOfLenLE (bitWidth (nn + S + 2)) u.val)[q -
      (succParamsCodec tm.Q kk).width - 1]'(by rw [bitsOfLenLE_length]; exact hq)) = Γ.zero
    rw [h _ hq]
    rfl

/-- The scan that decides a code's input-head field is **not** zero. -/
noncomputable def headNonZeroScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (hd : Fin (jj + 1)) :
    Scanner jj :=
  ((Scanner.isNotConst jj hd Γ.zero).after (succParamsCodec tm.Q kk).width).upTo
    ((succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width)

/-- **The nonzero-head scan decides that the code's input head is off the marker.** -/
theorem headNonZeroScanner_decides {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (hd : Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ)
    (hlen : (succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width ≤ len)
    (u : Fin (nn + S + 2))
    (hu : HoldsBits cols (succParamsCodec tm.Q kk).width hd ((finCodec (nn + S + 2)).enc u)) :
    (headNonZeroScanner tm nn S hd).emit ((headNonZeroScanner tm nn S hd).run cols len) = true ↔
      u.val ≠ 0 := by
  rw [headNonZeroScanner, Scanner.isNotConst_range_run _ _ _ _ _ _ len hlen]
  have hwidth : (finCodec (nn + S + 2)).width = bitWidth (nn + S + 2) := rfl
  have hbound : u.val < 2 ^ bitWidth (nn + S + 2) :=
    lt_of_lt_of_le u.isLt (le_two_pow_bitWidth _)
  rw [← not_iff_not, not_not, ← bitsOfLenLE_all_false_iff (bitWidth (nn + S + 2)) u.val hbound]
  constructor
  · intro h q hq
    by_contra hne
    refine h ⟨(succParamsCodec tm.Q kk).width + q + 1, by omega, by rw [hwidth]; omega, ?_⟩
    have hcell := hu q (by rw [(finCodec (nn + S + 2)).enc_length]; exact hq)
    rw [hcell]
    show Γ.ofBool ((bitsOfLenLE (bitWidth (nn + S + 2)) u.val)[q]'(by
      rw [bitsOfLenLE_length]; exact hq)) ≠ Γ.zero
    cases hb : (bitsOfLenLE (bitWidth (nn + S + 2)) u.val)[q]'(by
      rw [bitsOfLenLE_length]; exact hq) with
    | false => exact absurd hb hne
    | true => exact fun hc => Γ.noConfusion hc
  · rintro h ⟨q, h1, h2, h3⟩
    have hq : q - (succParamsCodec tm.Q kk).width - 1 < bitWidth (nn + S + 2) := by
      rw [hwidth] at h2
      omega
    have hcell := hu (q - (succParamsCodec tm.Q kk).width - 1)
      (by rw [(finCodec (nn + S + 2)).enc_length]; exact hq)
    rw [show (succParamsCodec tm.Q kk).width + (q - (succParamsCodec tm.Q kk).width - 1) + 1 = q
      by omega] at hcell
    refine h3 ?_
    rw [hcell]
    show Γ.ofBool ((bitsOfLenLE (bitWidth (nn + S + 2)) u.val)[q -
      (succParamsCodec tm.Q kk).width - 1]'(by rw [bitsOfLenLE_length]; exact hq)) = Γ.zero
    rw [h _ hq]
    rfl

/-! ## The direction the input head takes

`TM.inMoveTM` reads the direction to move the input head from a single cell, because a direction
fits in one writable symbol. That cell is guessed, so a check has to pin it against the guessed
transition — and unlike every other check this one reads a raw symbol rather than a bit. -/

/-- What a direction check accumulates: the parameters, and the symbol it saw on the direction
register's first cell. -/
abbrev DirAcc (tm : NTM kk) : Type := ParamAcc tm × Γ

/-- The direction check's reader: read the parameter block, and capture the direction register's
first cell as it goes past. -/
noncomputable def dirRead (tm : NTM kk) (a : DirAcc tm) (col : Fin 2 → Γ) : DirAcc tm :=
  (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0) a.1 col,
    if a.1.1.val = 0 then col 1 else a.2)

/-- **The direction checker.** It accepts when the direction register's first cell names the way
the guessed transition moves the input head. -/
noncomputable def dirScanner (tm : NTM kk) (enc : Dir3 → Γ) : Scanner 1 :=
  Scanner.prefixed (succParamsCodec tm.Q kk).width (DirAcc tm) Unit
    ((⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false), Γ.blank)
    (dirRead tm)
    (fun _ => ())
    (fun _ t _ => t)
    (fun a _ => decide (a.2 = enc (succTrans tm (paramsOfTable tm a.1)).2.2.2.1))

/-- The reader's parameter half is the ordinary parameter reader. -/
theorem dirRead_fst (tm : NTM kk) (cols : ℕ → Fin 2 → Γ) (g₀ : Γ) (x₀ : Fin 1 → Fin _ → Bool) :
    ∀ p : ℕ, (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (dirRead tm) cols p).1
      = Scanner.auxRun (⟨0, Nat.zero_lt_succ _⟩, x₀)
        (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0)) cols p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih => rw [Scanner.auxRun, Scanner.auxRun, dirRead, ih]

/-- The reader's captured half is the direction register's first cell, and its counter has left
zero behind — so nothing later overwrites the capture. -/
theorem dirRead_snd (tm : NTM kk) (cols : ℕ → Fin 2 → Γ) (g₀ : Γ)
    (x₀ : Fin 1 → Fin (succParamsCodec tm.Q kk).width → Bool) :
    ∀ p : ℕ, 1 ≤ p →
      (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (dirRead tm) cols p).2 = cols 1 1 ∧
        (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (dirRead tm) cols p).1.1.val ≠ 0 := by
  have hw := succParamsCodec_width_pos tm
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ih =>
      intro _
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        constructor
        · show (dirRead tm ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (cols (0 + 1))).2 = cols 1 1
          rw [dirRead]
          show (if (0 : ℕ) = 0 then cols (0 + 1) 1 else g₀) = cols 1 1
          rw [ite_eq_left rfl]
        · show (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0)
            (⟨0, Nat.zero_lt_succ _⟩, x₀) (cols (0 + 1))).1.val ≠ 0
          rw [Scanner.bitsStep,
            dite_eq_left (show (0 : ℕ) < (succParamsCodec tm.Q kk).width by omega)]
          exact Nat.succ_ne_zero _
      · obtain ⟨ihcap, ihcnt⟩ := ih hp
        constructor
        · show (dirRead tm (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (dirRead tm)
            cols p) (cols (p + 1))).2 = cols 1 1
          rw [dirRead]
          show (if (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (dirRead tm)
            cols p).1.1.val = 0 then _ else _) = cols 1 1
          rw [ite_eq_right ihcnt]
          exact ihcap
        · show (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0)
            (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, x₀), g₀) (dirRead tm) cols p).1
            (cols (p + 1))).1.val ≠ 0
          rw [Scanner.bitsStep]
          split
          · exact Nat.succ_ne_zero _
          · exact ihcnt

/-- The parameters a direction check reads. -/
noncomputable def dirParams (tm : NTM kk) (cols : ℕ → Fin 2 → Γ) : SuccParams tm.Q kk :=
  paramsOfTable tm (Scanner.auxRun (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 1 (succParamsCodec tm.Q kk).width (fun _ => 0)) cols
    (succParamsCodec tm.Q kk).width)

/-- **What the direction checker computes.** -/
theorem dirScanner_run (tm : NTM kk) (enc : Dir3 → Γ) (cols : ℕ → Fin 2 → Γ) :
    (dirScanner tm enc).emit
        ((dirScanner tm enc).run cols (succParamsCodec tm.Q kk).width)
      = decide (cols 1 1 = enc (succTrans tm (dirParams tm cols)).2.2.2.1) := by
  have h := Scanner.prefixed_run (α := DirAcc tm) (τ := Unit) (succParamsCodec tm.Q kk).width
    ((⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false), Γ.blank) (dirRead tm) (fun _ => ())
    (fun _ t _ => t)
    (fun a _ => decide (a.2 = enc (succTrans tm (paramsOfTable tm a.1)).2.2.2.1))
    cols (succParamsCodec_width_pos tm) 0
  have h2 : (dirScanner tm enc).emit
      ((dirScanner tm enc).run cols (succParamsCodec tm.Q kk).width)
      = decide ((Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false), Γ.blank)
          (dirRead tm) cols (succParamsCodec tm.Q kk).width).2
        = enc (succTrans tm (paramsOfTable tm
          (Scanner.auxRun ((⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false), Γ.blank)
            (dirRead tm) cols (succParamsCodec tm.Q kk).width).1)).2.2.2.1) := h
  rw [h2, dirParams,
    dirRead_fst tm cols Γ.blank (fun _ _ => false) (succParamsCodec tm.Q kk).width,
    (dirRead_snd tm cols Γ.blank (fun _ _ => false) (succParamsCodec tm.Q kk).width
      (succParamsCodec_width_pos tm)).1]

/-- **The direction checker decides that the guessed direction is the one the transition
takes.** -/
theorem dirScanner_decides (tm : NTM kk) (enc : Dir3 → Γ) (cols : ℕ → Fin 2 → Γ)
    (P : SuccParams tm.Q kk) (hpar : HoldsBits cols 0 0 ((succParamsCodec tm.Q kk).enc P)) :
    (dirScanner tm enc).emit
        ((dirScanner tm enc).run cols (succParamsCodec tm.Q kk).width) = true ↔
      cols 1 1 = enc (succTrans tm P).2.2.2.1 := by
  have hP : dirParams tm cols = P := by
    have h := ofTable_of_holds_zero (succParamsCodec tm.Q kk) P cols 1
      (succParamsCodec tm.Q kk).width (fun _ => 0) 0 le_rfl (fun _ _ => false) hpar
    rw [dirParams, paramsOfTable]
    exact h
  rw [dirScanner_run, hP, decide_eq_true_eq]

/-! ## The symbol under the input head

Of every field of a guessed transition, this is the one no scan can check: it has to agree with
the machine's own input tape. So it is laid out first in the parameter block, where
`TM.inMatchTM` reads it. -/

/-- **The parameter register opens with the guessed input symbol.** -/
theorem inSym_cells (tm : NTM kk) {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1))
    (P : SuccParams tm.Q kk)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P)) :
    cols 1 par = Γ.ofBool (gammaBits P.inSym).1 ∧
      cols 2 par = Γ.ofBool (gammaBits P.inSym).2 := by
  obtain ⟨L, hcat⟩ : ∃ L, (succParamsCodec tm.Q kk).enc P = BitCodec.gamma.enc P.inSym ++ L :=
    ⟨_, rfl⟩
  have hlen : ((succParamsCodec tm.Q kk).enc P).length = (succParamsCodec tm.Q kk).width :=
    (succParamsCodec tm.Q kk).enc_length P
  have hw : (succParamsCodec tm.Q kk).width = 2 + (1 + (bitWidth (Fintype.card tm.Q)
      + (kk * 2 + 2))) := succParamsCodec_width tm.Q kk
  have hopt : ∀ q, q < 2 → ((succParamsCodec tm.Q kk).enc P)[q]?
      = (BitCodec.gamma.enc P.inSym)[q]? := by
    intro q hq
    rw [hcat, List.getElem?_append_left (by rw [BitCodec.gamma.enc_length]; exact hq)]
  have hbit : ∀ q, (hq : q < 2) → ((succParamsCodec tm.Q kk).enc P)[q]?
      = some ([(gammaBits P.inSym).1, (gammaBits P.inSym).2][q]'(by simpa using hq)) := by
    intro q hq
    rw [hopt q hq, gamma_enc_eq, List.getElem?_eq_getElem (by simpa using hq)]
  constructor
  · have hlt : 0 < ((succParamsCodec tm.Q kk).enc P).length := by rw [hlen, hw]; omega
    have h := hpar 0 hlt
    rw [Nat.zero_add] at h
    rw [h]
    refine congrArg Γ.ofBool (Option.some_injective _ ?_)
    rw [← List.getElem?_eq_getElem hlt, hbit 0 (by omega)]
    rfl
  · have hlt : 1 < ((succParamsCodec tm.Q kk).enc P).length := by rw [hlen, hw]; omega
    have h := hpar 1 hlt
    rw [show (0 : ℕ) + 1 + 1 = 2 from rfl] at h
    rw [h]
    refine congrArg Γ.ofBool (Option.some_injective _ ?_)
    rw [← List.getElem?_eq_getElem hlt, hbit 1 (by omega)]
    rfl

/-- **The input check passes when the guess is right.** The converse of
`Complexity.inSym_eq_of_inMatch`: this is what the completeness direction needs, since the
certificate names the symbol the simulated head is really over. -/
theorem inMatchVerdict_of_inSym (tm : NTM kk) {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ)
    (par : Fin (jj + 1)) (P : SuccParams tm.Q kk) (g : Γ)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P)) (hin : P.inSym = g) :
    TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) = true := by
  obtain ⟨h1, h2⟩ := inSym_cells tm cols par P hpar
  rw [TM.inMatchVerdict, h1, h2, hin, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨rfl, rfl⟩

/-- **The input check pins the guessed input symbol.** When the machine's own input head sits
where the simulated one does, the verdict of `TM.inMatchTM` on the parameter register says exactly
that the guess was right. -/
theorem inSym_eq_of_inMatch (tm : NTM kk) {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ)
    (par : Fin (jj + 1)) (P : SuccParams tm.Q kk) (g : Γ)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (hv : TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) = true) : P.inSym = g := by
  obtain ⟨h1, h2⟩ := inSym_cells tm cols par P hpar
  rw [TM.inMatchVerdict, h1, h2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hv
  exact gammaBits_injective (Prod.ext (ofBool_injective hv.1) (ofBool_injective hv.2))

/-- **The parameter register opens with two ones exactly when the guessed symbol is the
marker.** -/
theorem parStart_iff {kk jj : ℕ} (tm : NTM kk) (cols : ℕ → Fin (jj + 1) → Γ)
    (par : Fin (jj + 1)) (P : SuccParams tm.Q kk)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P)) :
    (∀ q, 1 ≤ q → q ≤ 2 → cols q par = Γ.one) ↔ P.inSym = Γ.start := by
  obtain ⟨h1, h2⟩ := inSym_cells tm cols par P hpar
  constructor
  · intro h
    have e1 : Γ.ofBool (gammaBits P.inSym).1 = Γ.one := by rw [← h1]; exact h 1 le_rfl (by omega)
    have e2 : Γ.ofBool (gammaBits P.inSym).2 = Γ.one := by rw [← h2]; exact h 2 (by omega) le_rfl
    refine gammaBits_injective ?_
    refine Prod.ext ?_ ?_
    · cases hb : (gammaBits P.inSym).1 with
      | true => rfl
      | false => rw [hb] at e1; exact absurd e1 (fun hc => Γ.noConfusion hc)
    · cases hb : (gammaBits P.inSym).2 with
      | true => rfl
      | false => rw [hb] at e2; exact absurd e2 (fun hc => Γ.noConfusion hc)
  · intro h q hq1 hq2
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · rw [show q = 1 by omega, h1, h]
      rfl
    · rw [show q = 2 by omega, h2, h]
      rfl

/-! ## What each scanner decides -/

set_option maxHeartbeats 1000000 in
/-- **The window checker decides the window condition.** -/
theorem windowScanner_decides (tm : NTM kk) (i : Fin kk) (cols : ℕ → Fin 3 → Γ) (S : ℕ)
    (hd hd' : Fin (S + 1)) (cl cl' : Fin (S + 1) → Γ)
    (ha : HoldsWindow cols (succParamsCodec tm.Q kk).width 1 hd cl)
    (hb : HoldsWindow cols (succParamsCodec tm.Q kk).width 2 hd' cl')
    (hend : markOf cols (succParamsCodec tm.Q kk).width 1 (S + 1) = false) :
    (windowScanner tm i).emit ((windowScanner tm i).run cols
        ((succParamsCodec tm.Q kk).width + 3 * (S + 1))) = true ↔
      (cl hd = (windowParams tm cols).wSym i ∧
        (∀ p, cl' p = if p = hd ∧ 0 < p.val then succWrite tm (windowParams tm cols) i
          else cl p) ∧
        hd'.val = movedIdx (succDir tm (windowParams tm cols) i) hd.val) := by
  rw [windowScanner_run]
  exact blockEmit_holds cols (succParamsCodec tm.Q kk).width 1 2 hd hd' cl cl' ha hb
    ((windowParams tm cols).wSym i) (succWrite tm (windowParams tm cols) i)
    (succDir tm (windowParams tm cols) i) (by omega) hend

set_option maxHeartbeats 1000000 in
/-- **The output checker decides the output-window condition.** -/
theorem outputScanner_decides (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) (S : ℕ)
    (hd hd' : Fin (S + 2)) (cl cl' : Fin (S + 2) → Γ)
    (ha : HoldsWindow cols (succParamsCodec tm.Q kk).width 1 hd cl)
    (hb : HoldsWindow cols (succParamsCodec tm.Q kk).width 2 hd' cl')
    (hend : markOf cols (succParamsCodec tm.Q kk).width 1 (S + 2) = false) :
    (outputScanner tm).emit ((outputScanner tm).run cols
        ((succParamsCodec tm.Q kk).width + 3 * (S + 2))) = true ↔
      (cl hd = (windowParams tm cols).oSym ∧
        (∀ p, cl' p = if p = hd ∧ 0 < p.val
          then (((succTrans tm (windowParams tm cols)).2.2.1 : Γw) : Γ) else cl p) ∧
        hd'.val = movedIdx (succTrans tm (windowParams tm cols)).2.2.2.2.2 hd.val) := by
  rw [outputScanner_run]
  exact blockEmit_holds cols (succParamsCodec tm.Q kk).width 1 2 hd hd' cl cl' ha hb
    (windowParams tm cols).oSym (((succTrans tm (windowParams tm cols)).2.2.1 : Γw) : Γ)
    (succTrans tm (windowParams tm cols)).2.2.2.2.2 (by omega) hend

set_option maxHeartbeats 1000000 in
/-- **The input-head checker decides the input-head condition.** -/
theorem headScanner_decides (tm : NTM kk) (cols : ℕ → Fin 3 → Γ) (w u v : ℕ)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (ha : HoldsBits (fun t => cols ((succParamsCodec tm.Q kk).width + t)) 0 1
      (bitsOfLenLE w u))
    (hb : HoldsBits (fun t => cols ((succParamsCodec tm.Q kk).width + t)) 0 2
      (bitsOfLenLE w v))
    (hleft : (succTrans tm (windowParams tm cols)).2.2.2.1 = Dir3.left → 0 < u) :
    (headScanner tm).emit ((headScanner tm).run cols
        ((succParamsCodec tm.Q kk).width + w)) = true ↔
      v = movedIdx (succTrans tm (windowParams tm cols)).2.2.2.1 u := by
  rw [headScanner_run]
  exact inHeadEmit_of_holds cols (succParamsCodec tm.Q kk).width 1 2 _ w u v hu hv ha hb hleft

set_option maxHeartbeats 1000000 in
/-- **The state checker decides the state condition.** -/
theorem stateScanner_decides (tm : NTM kk) (isNew : Bool) (cols : ℕ → Fin 2 → Γ) (q : tm.Q)
    (h : HoldsBits cols 0 1 ((qCodec tm.Q).enc q)) :
    (stateScanner tm isNew).emit ((stateScanner tm isNew).run cols (stateWidth tm)) = true ↔
      q = (if isNew then succState tm (paramsOfStateTable tm (stateTable tm cols))
        else (paramsOfStateTable tm (stateTable tm cols)).q) := by
  rw [stateScanner_run, decide_eq_true_eq]
  have hq : stateOfTable tm (stateTable tm cols) = q :=
    ofTable_of_holds_zero (qCodec tm.Q) q cols 2 (stateWidth tm) (fun t => t) 1
      (le_max_right _ _) _ h
  rw [hq]

/-! ## The checks as machines

Each check is `TM.checkTM` of its scanner: the scanner names the columns it reads, so the checked
registers need not be adjacent and no check needs a private copy of them. The checks never consult
the guess tape — they are built on the register tapes alone, and the guess tape is added once, at
the very end, by `TM.liftLast`, which is where their `TM.GuessProtocol` comes from. Only the
stages that *write* guesses carry advancing states.

`Complexity.windowScanner_decides` and its siblings are stated about the three columns a check
reads, which is exactly the restriction `TM.checkTM_hoareTime` leaves in its postcondition, so
they apply to a full-width check unchanged. -/

/-! ## Combining the verdicts

One scan over every tape, looking only at the result registers' first cells. No placement, so the
registers need not be adjacent. -/

/-- The machine that combines the verdicts. -/
noncomputable def combineTM (N : ℕ) (P : Fin (N + 1) → Bool) : TM (N + 2) :=
  TM.twoPassTM (Scanner.andFirst N P)

/-- **The combining machine's contract.** -/
theorem combineTM_hoareTime (N : ℕ) (P : Fin (N + 1) → Bool) (cells : Fin (N + 1) → ℕ → Γ)
    (len : ℕ) (inp₀ out₀ res₀ : Tape) (hok : TM.ScanOk inp₀ res₀ out₀)
    (ht : TM.ScanTape cells len) :
    (combineTM N P).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) res₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape))
          (res₀.write (Γ.ofBool ((Scanner.andFirst N P).emit
            ((Scanner.andFirst N P).run (TM.scanCol cells) len)))))
      (2 * len + 3) :=
  TM.twoPassTM_hoareTime (Scanner.andFirst N P) cells len inp₀ out₀ res₀ hok ht

/-- **The bit the combining machine writes**: whether every designated register said yes. -/
theorem combineTM_verdict (N : ℕ) (P : Fin (N + 1) → Bool) (cells : Fin (N + 1) → ℕ → Γ)
    (len : ℕ) (hlen : 0 < len) :
    (Scanner.andFirst N P).emit ((Scanner.andFirst N P).run (TM.scanCol cells) len) = true ↔
      ∀ i, P i = true → cells i 1 = Γ.one :=
  Scanner.andFirst_run N P (TM.scanCol cells) len hlen

/-! ## The equality and increment checks

The walk may keep a configuration as well as step it, and keeping is register equality — decided
by the comparison scanner, one register pair at a time. A counter advances the same way: the next
value is guessed into a second register and `Complexity.Scanner.plusOne` checks it. Both scanners
already take arbitrary register indices at any width, so neither needs `TM.checkTM`. -/

/-! ## One walk step, as a single scan

A machine has one result tape, so the checks of a walk step run together: one automaton whose
state is the tuple of theirs, each component frozen at its own length by
`Complexity.Scanner.upTo` and reading its own registers through
`Complexity.Scanner.comap`. -/

/-- The columns a window check reads: the parameter block, then the old and new windows. -/
def windowCols {kk jj : ℕ} (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj) (i : Fin kk) :
    Fin 3 → Fin (jj + 1) :=
  fun c => if c.val = 0 then par else if c.val = 1 then Ra.wk i else Rb.wk i

/-- The columns the output-window check reads. -/
def outputCols {kk jj : ℕ} (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj) :
    Fin 3 → Fin (jj + 1) :=
  fun c => if c.val = 0 then par else if c.val = 1 then Ra.ot else Rb.ot

/-- The columns the input-head check reads. -/
def headCols {kk jj : ℕ} (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj) :
    Fin 3 → Fin (jj + 1) :=
  fun c => if c.val = 0 then par else if c.val = 1 then Ra.hd else Rb.hd

/-- The columns a state check reads. -/
def stateCols {kk jj : ℕ} (par : Fin (jj + 1)) (R : CodeRegs kk jj) : Fin 2 → Fin (jj + 1) :=
  fun c => if c.val = 0 then par else R.st

/-- The width of block `p` in the walk's layout: the field's own width, and for every register
but the state's the parameter-block padding in front of it. -/
noncomputable def blockLen {kk : ℕ} (tm : NTM kk) (nn S : ℕ) (p : ℕ) : ℕ :=
  if p = 0 then codeWidthRaw tm nn S 0
  else (succParamsCodec tm.Q kk).width + (codeWidthRaw tm nn S p + 1)

theorem codeBlockScan_length {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (p : ℕ) :
    (codeBlockScan tm x S a p).length = blockLen tm x.length S p := by
  rw [codeBlockScan, blockLen]
  split_ifs with h
  · exact codeBlock_length tm x S a 0
  · rw [List.length_append, List.length_replicate, List.length_append, codeBlock_length]
    rfl

/-- The scan that decides that two register tuples hold the same code: one comparison per block,
each frozen at that block's width. -/
noncomputable def eqScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (j j' : ℕ → Fin (jj + 1)) :
    Scanner jj :=
  Scanner.all (kk + 3) (fun p =>
    (Scanner.eq jj (j p.val) (j' p.val)).upTo (blockLen tm nn S p.val))

/-- A length that covers every check of a walk step. -/
noncomputable def walkScanLen {kk : ℕ} (tm : NTM kk) (nn S : ℕ) : ℕ :=
  (succParamsCodec tm.Q kk).width + (qCodec tm.Q).width + (finCodec (nn + S + 2)).width
    + stateWidth tm + 3 * (S + 2) + (S + 1) * 3 + (S + 2) * 3

theorem blockLen_le {kk : ℕ} (tm : NTM kk) (nn S p : ℕ) :
    blockLen tm nn S p ≤ walkScanLen tm nn S := by
  simp only [blockLen, walkScanLen, codeWidthRaw]
  split_ifs <;> omega

theorem succParamsCodec_width_le_walkScanLen {kk : ℕ} (tm : NTM kk) (nn S : ℕ) :
    (succParamsCodec tm.Q kk).width ≤ walkScanLen tm nn S := by
  rw [walkScanLen]
  omega

theorem one_le_walkScanLen {kk : ℕ} (tm : NTM kk) (nn S : ℕ) : 1 ≤ walkScanLen tm nn S := by
  have := succParamsCodec_width_pos tm
  have := succParamsCodec_width_le_walkScanLen tm nn S
  omega

theorem headField_le_walkScanLen {kk : ℕ} (tm : NTM kk) (nn S : ℕ) :
    (succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width ≤ walkScanLen tm nn S := by
  rw [walkScanLen]
  omega

theorem two_le_walkScanLen {kk : ℕ} (tm : NTM kk) (nn S : ℕ) : 2 ≤ walkScanLen tm nn S := by
  have h1 := succParamsCodec_width_pos tm
  have h2 := headField_le_walkScanLen tm nn S
  have h3 : 0 < (finCodec (nn + S + 2)).width := by
    show 0 < bitWidth (nn + S + 2)
    have := le_two_pow_bitWidth (nn + S + 2)
    by_contra hc
    have hz : bitWidth (nn + S + 2) = 0 := by omega
    rw [hz] at this
    simp at this
  omega

/-- The scan that checks the guessed input symbol, conditional on where the simulated head is:
against the parameter register alone when the head is at the marker, and against the machine's own
input tape — through `TM.inMatchTM`'s verdict — when it is not. -/
noncomputable def inSymScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par hd res : Fin (jj + 1)) : Scanner jj :=
  Scanner.or
    (Scanner.all 2 (fun p => if p.val = 0 then headZeroScanner tm nn S hd
      else (Scanner.isConst jj par Γ.one).upTo 2))
    (Scanner.all 2 (fun p => if p.val = 0 then headNonZeroScanner tm nn S hd
      else (Scanner.isConst jj res Γ.one).upTo 1))

/-- **The equality scan decides that two guesses are the same code.** -/
theorem eqScanner_decides {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j j' : ℕ → Fin (jj + 1)) (a b : Code tm.Q kk x.length S)
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S b p))
    (hv : (eqScanner tm x.length S j j').emit
      ((eqScanner tm x.length S j j').run cols (walkScanLen tm x.length S)) = true) :
    a = b := by
  rw [eqScanner, Scanner.all_emit_run] at hv
  have hblk : ∀ p, p < kk + 3 → codeBlockScan tm x S a p = codeBlockScan tm x S b p := by
    intro p hp
    have h := hv ⟨p, hp⟩
    rw [Scanner.upTo_emit_run _ (Scanner.rightOnly_eq jj (j p) (j' p)) _ _
      (blockLen_le tm x.length S p)] at h
    refine (eq_run_of_holds cols (j p) (j' p) _ _ ?_ (ha p hp) (hb p hp)).mp ?_
    · rw [codeBlockScan_length, codeBlockScan_length]
    · rwa [codeBlockScan_length]
  have hfield : ∀ p, p < kk + 3 → codeBlock tm x S a p = codeBlock tm x S b p := by
    intro p hp
    have h := hblk p hp
    rw [codeBlockScan, codeBlockScan] at h
    by_cases h0 : p = 0
    · subst h0
      rwa [ite_eq_left rfl, ite_eq_left rfl] at h
    · rw [ite_eq_right h0, ite_eq_right h0] at h
      exact List.append_cancel_right (List.append_cancel_left h)
  have hst : a.1 = b.1 := by
    have h := hfield 0 (by omega)
    rw [codeBlock_st, codeBlock_st] at h
    exact (qCodec tm.Q).enc_injective h
  have hhd : a.2.1 = b.2.1 := by
    have h := hfield 1 (by omega)
    rw [codeBlock_hd, codeBlock_hd] at h
    exact (finCodec (x.length + S + 2)).enc_injective h
  have hwk : a.2.2.1 = b.2.2.1 := by
    funext i
    have h := hfield (i.val + 2) (by omega)
    rw [codeBlock_wk, codeBlock_wk] at h
    exact (tapeCodec (S + 1)).enc_injective h
  have hot : a.2.2.2 = b.2.2.2 := by
    have h := hfield (kk + 2) (by omega)
    rw [codeBlock_ot, codeBlock_ot] at h
    exact (tapeCodec (S + 2)).enc_injective h
  exact Prod.ext hst (Prod.ext hhd (Prod.ext hwk hot))

/-- **The equality scan accepts two guesses of the same code.** -/
theorem eqScanner_accepts {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (j j' : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S a p)) :
    (eqScanner tm x.length S j j').emit
      ((eqScanner tm x.length S j j').run cols (walkScanLen tm x.length S)) = true := by
  rw [eqScanner, Scanner.all_emit_run]
  intro p
  rw [Scanner.upTo_emit_run _ (Scanner.rightOnly_eq jj (j p.val) (j' p.val)) _ _
    (blockLen_le tm x.length S p.val)]
  have h := (eq_run_of_holds cols (j p.val) (j' p.val) (codeBlockScan tm x S a p.val)
    (codeBlockScan tm x S a p.val) rfl (ha p.val p.isLt) (hb p.val p.isLt)).mpr rfl
  rwa [codeBlockScan_length] at h

/-- **The input-symbol scan decides the guessed symbol.** -/
theorem inSymScanner_decides {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par hd res : Fin (jj + 1)) (P : SuccParams tm.Q kk)
    (a : Code tm.Q kk x.length S) (g : Γ)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (hhd : HoldsBits cols (succParamsCodec tm.Q kk).width hd
      ((finCodec (x.length + S + 2)).enc a.2.1))
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (hv : (inSymScanner tm x.length S par hd res).emit
      ((inSymScanner tm x.length S par hd res).run cols (walkScanLen tm x.length S)) = true) :
    P.inSym = inSymOf tm x S a := by
  rw [inSymScanner, Scanner.or_emit_run] at hv
  rcases hv with h | h
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at h0
    rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
    have hzero : a.2.1.val = 0 :=
      (headZeroScanner_decides tm x.length S hd cols (walkScanLen tm x.length S)
        (headField_le_walkScanLen tm x.length S) a.2.1 hhd).mp h0
    have hstart : P.inSym = Γ.start :=
      (parStart_iff tm cols par P hpar).mp
        ((Scanner.isConst_upTo_run jj par Γ.one cols 2 (walkScanLen tm x.length S)
          (two_le_walkScanLen tm x.length S)).mp h1)
    rw [hstart, inSymOf, hzero]
    exact (Tape.init_cells_zero _).symm
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at h0
    rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
    have hne : a.2.1.val ≠ 0 :=
      (headNonZeroScanner_decides tm x.length S hd cols (walkScanLen tm x.length S)
        (headField_le_walkScanLen tm x.length S) a.2.1 hhd).mp h0
    have hone : cols 1 res = Γ.one :=
      (Scanner.isConst_cell jj res Γ.one cols (walkScanLen tm x.length S)
        (by have := two_le_walkScanLen tm x.length S; omega)).mp h1
    have hverdict : TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) = true := by
      rw [hres] at hone
      cases hc : TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par) with
      | false => rw [hc] at hone; exact absurd hone (fun hz => Γ.noConfusion hz)
      | true => rfl
    rw [inSym_eq_of_inMatch tm cols par P g hpar hverdict]
    exact hg hne

/-- **The input-symbol scan accepts a correct guess.** -/
theorem inSymScanner_accepts {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par hd res : Fin (jj + 1)) (P : SuccParams tm.Q kk)
    (a : Code tm.Q kk x.length S)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (hhd : HoldsBits cols (succParamsCodec tm.Q kk).width hd
      ((finCodec (x.length + S + 2)).enc a.2.1))
    (hin : P.inSym = inSymOf tm x S a)
    (hres : a.2.1.val ≠ 0 → cols 1 res = Γ.one) :
    (inSymScanner tm x.length S par hd res).emit
      ((inSymScanner tm x.length S par hd res).run cols (walkScanLen tm x.length S)) = true := by
  rw [inSymScanner, Scanner.or_emit_run]
  by_cases hz : a.2.1.val = 0
  · refine Or.inl ?_
    rw [Scanner.all_emit_run]
    intro p
    by_cases hp : p.val = 0
    · rw [ite_eq_left hp]
      exact (headZeroScanner_decides tm x.length S hd cols (walkScanLen tm x.length S)
        (headField_le_walkScanLen tm x.length S) a.2.1 hhd).mpr hz
    · rw [ite_eq_right hp]
      refine (Scanner.isConst_upTo_run jj par Γ.one cols 2 (walkScanLen tm x.length S)
        (two_le_walkScanLen tm x.length S)).mpr ?_
      refine (parStart_iff tm cols par P hpar).mpr ?_
      rw [hin, inSymOf, hz]
      exact Tape.init_cells_zero _
  · refine Or.inr ?_
    rw [Scanner.all_emit_run]
    intro p
    by_cases hp : p.val = 0
    · rw [ite_eq_left hp]
      exact (headNonZeroScanner_decides tm x.length S hd cols (walkScanLen tm x.length S)
        (headField_le_walkScanLen tm x.length S) a.2.1 hhd).mpr hz
    · rw [ite_eq_right hp]
      exact (Scanner.isConst_cell jj res Γ.one cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mpr (hres hz)

/-- The scan that decides a successor step: one check per work window, the output window, the
input head, and the two state fields — all against the parameters in the same register. -/
noncomputable def succScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (par : Fin (jj + 1))
    (Ra Rb : CodeRegs kk jj) : Scanner jj :=
  Scanner.all (kk + 4) (fun p =>
    if h : p.val < kk then
      ((windowScanner tm ⟨p.val, h⟩).comap (windowCols par Ra Rb ⟨p.val, h⟩)).upTo
        ((succParamsCodec tm.Q kk).width + 3 * (S + 1))
    else if p.val = kk then
      ((outputScanner tm).comap (outputCols par Ra Rb)).upTo
        ((succParamsCodec tm.Q kk).width + 3 * (S + 2))
    else if p.val = kk + 1 then
      ((headScanner tm).comap (headCols par Ra Rb)).upTo
        ((succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width)
    else if p.val = kk + 2 then
      ((stateScanner tm false).comap (stateCols par Ra)).upTo (stateWidth tm)
    else ((stateScanner tm true).comap (stateCols par Rb)).upTo (stateWidth tm))

/-- **The parameters a check reads depend only on the register it reads them from.** Every check
of a walk step reads the same parameter register, so they all work against the same guessed
transition — which is what lets one guess serve five checks. -/
theorem windowParams_congr {kk : ℕ} (tm : NTM kk) (cols cols' : ℕ → Fin 3 → Γ)
    (h : ∀ q, cols q 0 = cols' q 0) : windowParams tm cols = windowParams tm cols' := by
  rw [windowParams, windowParams,
    Scanner.auxRun_bitsStep_congr (fun _ => 0) cols cols' (fun q _ => h q) _
      (succParamsCodec tm.Q kk).width]

/-- **Both readers of the parameter register read the same parameters.** The window, output and
input-head checks read the guessed transition with one reader; the state checks read it with
another, over a wider block. When the register holds an encoding, the two agree — which is what
lets the state checks be checks against the same guess as the rest. -/
theorem params_of_holds {kk : ℕ} (tm : NTM kk) (P : SuccParams tm.Q kk)
    (colsW : ℕ → Fin 3 → Γ) (colsS : ℕ → Fin 2 → Γ)
    (hW : HoldsBits colsW 0 0 ((succParamsCodec tm.Q kk).enc P))
    (hS : HoldsBits colsS 0 0 ((succParamsCodec tm.Q kk).enc P)) :
    windowParams tm colsW = P ∧ paramsOfStateTable tm (stateTable tm colsS) = P := by
  constructor
  · have h := ofTable_of_holds_zero (succParamsCodec tm.Q kk) P colsW 1
      (succParamsCodec tm.Q kk).width (fun _ => 0) 0 le_rfl (fun _ _ => false) hW
    rw [windowParams, paramsOfTable]
    exact h
  · have h := ofTable_of_holds_zero (succParamsCodec tm.Q kk) P colsS 2 (stateWidth tm)
      (fun t => t) 0 (le_max_left _ _) (fun _ _ => false) hS
    rw [paramsOfStateTable, stateTable]
    exact h

/-- **Every check of a walk step reads the same parameters.** -/
theorem walkParams_eq {kk jj : ℕ} (tm : NTM kk) (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj)
    (cols : ℕ → Fin (jj + 1) → Γ) (i : Fin kk) :
    windowParams tm (fun q c => cols q (windowCols par Ra Rb i c))
        = windowParams tm (fun q c => cols q (outputCols par Ra Rb c)) ∧
      windowParams tm (fun q c => cols q (windowCols par Ra Rb i c))
        = windowParams tm (fun q c => cols q (headCols par Ra Rb c)) :=
  ⟨windowParams_congr tm _ _ (fun _ => rfl), windowParams_congr tm _ _ (fun _ => rfl)⟩

/-- **A successor scan's verdict is the verdict of each of its checks.** Each component reads its
own registers, over its own cells, exactly as it would have alone. -/
theorem succScanner_verdicts {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ) (par : Fin (jj + 1))
    (Ra Rb : CodeRegs kk jj) (cols : ℕ → Fin (jj + 1) → Γ)
    (hv : (succScanner tm nn S par Ra Rb).emit
      ((succScanner tm nn S par Ra Rb).run cols (walkScanLen tm nn S)) = true) :
    (∀ i, (windowScanner tm i).emit ((windowScanner tm i).run
        (fun q c => cols q (windowCols par Ra Rb i c))
        ((succParamsCodec tm.Q kk).width + 3 * (S + 1))) = true) ∧
      (outputScanner tm).emit ((outputScanner tm).run
        (fun q c => cols q (outputCols par Ra Rb c))
        ((succParamsCodec tm.Q kk).width + 3 * (S + 2))) = true ∧
      (headScanner tm).emit ((headScanner tm).run
        (fun q c => cols q (headCols par Ra Rb c))
        ((succParamsCodec tm.Q kk).width + (finCodec (nn + S + 2)).width)) = true ∧
      (stateScanner tm false).emit ((stateScanner tm false).run
        (fun q c => cols q (stateCols par Ra c)) (stateWidth tm)) = true ∧
      (stateScanner tm true).emit ((stateScanner tm true).run
        (fun q c => cols q (stateCols par Rb c)) (stateWidth tm)) = true := by
  rw [succScanner, Scanner.all_emit_run] at hv
  have hcomp : ∀ {jd : ℕ} (T : Scanner jd) (f : Fin (jd + 1) → Fin (jj + 1)) (w : ℕ),
      (∀ s c, T.stepL s c = s) → w ≤ walkScanLen tm nn S →
      ((T.comap f).upTo w).emit (((T.comap f).upTo w).run cols (walkScanLen tm nn S)) = true →
      T.emit (T.run (fun q c => cols q (f c)) w) = true := by
    intro jd T f w hT hw h
    rw [Scanner.upTo_emit_run _ (Scanner.rightOnly_comap hT f) w _ hw,
      Scanner.comap_emit, Scanner.comap_run] at h
    exact h
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · have h := hv ⟨i.val, by omega⟩
    rw [dite_eq_left i.isLt, show (⟨i.val, i.isLt⟩ : Fin kk) = i from Fin.ext rfl] at h
    exact hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) h
  · have h := hv ⟨kk, by omega⟩
    rw [dite_eq_right (by exact Nat.lt_irrefl kk), ite_eq_left (rfl : kk = kk)] at h
    exact hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) h
  · have h := hv ⟨kk + 1, by omega⟩
    rw [dite_eq_right (by exact Nat.not_lt.mpr (Nat.le_succ kk)),
      ite_eq_right (by exact Nat.succ_ne_self kk), ite_eq_left (rfl : kk + 1 = kk + 1)] at h
    exact hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) h
  · have h := hv ⟨kk + 2, by omega⟩
    rw [dite_eq_right (by exact Nat.not_lt.mpr (Nat.le_add_right kk 2)),
      ite_eq_right (by exact (by omega : kk + 2 ≠ kk)),
      ite_eq_right (by exact (by omega : kk + 2 ≠ kk + 1)),
      ite_eq_left (rfl : kk + 2 = kk + 2)] at h
    exact hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) h
  · have h := hv ⟨kk + 3, by omega⟩
    rw [dite_eq_right (by exact Nat.not_lt.mpr (Nat.le_add_right kk 3)),
      ite_eq_right (by exact (by omega : kk + 3 ≠ kk)),
      ite_eq_right (by exact (by omega : kk + 3 ≠ kk + 1)),
      ite_eq_right (by exact (by omega : kk + 3 ≠ kk + 2))] at h
    exact hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) h

/-- **The successor scan accepts a genuine successor.** The converse of
`Complexity.succScanner_decides`: when the registers really do hold a code and the code the
transition makes of it, every check passes. This is the direction a completeness proof needs — it
says the right guess exists. -/
theorem succScanner_accepts {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj)
    (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (ha : HoldsCodeScan tm x S cols Ra a) (hb : HoldsCodeScan tm x S cols Rb b)
    (hendW : ∀ i, markOf (fun q c => cols q (windowCols par Ra Rb i c))
      (succParamsCodec tm.Q kk).width 1 (S + 1) = false)
    (hendO : markOf (fun q c => cols q (outputCols par Ra Rb c))
      (succParamsCodec tm.Q kk).width 1 (S + 2) = false)
    (hq : a.1 = P.q) (hstate : b.1 = succState tm P)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym)
    (hhead : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val)
    (hwork : ∀ i, (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val ∧
      ∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
        else (a.2.2.1 i).2 p)
    (hout : b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ∧
      ∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
        then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p)
    (hleft : (succTrans tm P).2.2.2.1 = Dir3.left → 0 < a.2.1.val) :
    (succScanner tm x.length S par Ra Rb).emit
      ((succScanner tm x.length S par Ra Rb).run cols (walkScanLen tm x.length S)) = true := by
  obtain ⟨hast, hahd, hawk, haot⟩ := ha
  obtain ⟨hbst, hbhd, hbwk, hbot⟩ := hb
  have hPo : windowParams tm (fun q c => cols q (outputCols par Ra Rb c)) = P :=
    (params_of_holds tm P (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Ra c)) hpar hpar).1
  have hPsa : paramsOfStateTable tm
      (stateTable tm (fun q c => cols q (stateCols par Ra c))) = P :=
    (params_of_holds tm P (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Ra c)) hpar hpar).2
  have hPsb : paramsOfStateTable tm
      (stateTable tm (fun q c => cols q (stateCols par Rb c))) = P :=
    (params_of_holds tm P (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Rb c)) hpar hpar).2
  have hPw : ∀ i : Fin kk,
      windowParams tm (fun q c => cols q (windowCols par Ra Rb i c)) = P := by
    intro i
    rw [windowParams_congr tm (fun q c => cols q (windowCols par Ra Rb i c))
      (fun q c => cols q (outputCols par Ra Rb c)) (fun _ => rfl)]
    exact hPo
  have hPh : windowParams tm (fun q c => cols q (headCols par Ra Rb c)) = P := by
    rw [windowParams_congr tm (fun q c => cols q (headCols par Ra Rb c))
      (fun q c => cols q (outputCols par Ra Rb c)) (fun _ => rfl)]
    exact hPo
  rw [succScanner, Scanner.all_emit_run]
  intro p
  have hcomp : ∀ {jd : ℕ} (T : Scanner jd) (f : Fin (jd + 1) → Fin (jj + 1)) (wid : ℕ),
      (∀ s c, T.stepL s c = s) → wid ≤ walkScanLen tm x.length S →
      T.emit (T.run (fun q c => cols q (f c)) wid) = true →
      ((T.comap f).upTo wid).emit (((T.comap f).upTo wid).run cols
        (walkScanLen tm x.length S)) = true := by
    intro jd T f wid hT hwid h
    rw [Scanner.upTo_emit_run _ (Scanner.rightOnly_comap hT f) wid _ hwid,
      Scanner.comap_emit, Scanner.comap_run]
    exact h
  by_cases hpk : p.val < kk
  · rw [dite_eq_left hpk]
    refine hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) ?_
    refine (windowScanner_decides tm ⟨p.val, hpk⟩ _ S (a.2.2.1 ⟨p.val, hpk⟩).1
      (b.2.2.1 ⟨p.val, hpk⟩).1 (a.2.2.1 ⟨p.val, hpk⟩).2 (b.2.2.1 ⟨p.val, hpk⟩).2
      (hawk ⟨p.val, hpk⟩) (hbwk ⟨p.val, hpk⟩) (hendW ⟨p.val, hpk⟩)).mpr ?_
    rw [hPw ⟨p.val, hpk⟩]
    exact ⟨hwsym _, (hwork _).2, (hwork _).1⟩
  · rw [dite_eq_right hpk]
    by_cases hpo : p.val = kk
    · rw [ite_eq_left hpo]
      refine hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) ?_
      refine (outputScanner_decides tm _ S a.2.2.2.1 b.2.2.2.1 a.2.2.2.2 b.2.2.2.2
        haot hbot hendO).mpr ?_
      rw [hPo]
      exact ⟨hosym, hout.2, hout.1⟩
    · rw [ite_eq_right hpo]
      by_cases hph : p.val = kk + 1
      · rw [ite_eq_left hph]
        refine hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) ?_
        refine (headScanner_decides tm _ (bitWidth (x.length + S + 2)) a.2.1.val b.2.1.val
          (lt_of_lt_of_le a.2.1.isLt (le_two_pow_bitWidth _))
          (lt_of_lt_of_le b.2.1.isLt (le_two_pow_bitWidth _))
          hahd.shift hbhd.shift (by rw [hPh]; exact hleft)).mpr ?_
        rw [hPh]
        exact hhead
      · rw [ite_eq_right hph]
        by_cases hps : p.val = kk + 2
        · rw [ite_eq_left hps]
          refine hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) ?_
          refine (stateScanner_decides tm false _ a.1 hast).mpr ?_
          rw [hPsa, ite_eq_right (by simp)]
          exact hq
        · rw [ite_eq_right hps]
          refine hcomp _ _ _ (fun _ _ => rfl) (by rw [walkScanLen]; omega) ?_
          refine (stateScanner_decides tm true _ b.1 hbst).mpr ?_
          rw [hPsb, ite_eq_left rfl]
          exact hstate

/-- **The successor scan decides a successor step.** Given that the parameter register holds a
guessed transition, the scan's verdict says exactly that the second code is what that transition
makes of the first. What the scan cannot see is left to the caller: the symbol under the
simulated input head, which the machine reads from its own input tape, and that the step stays
inside the space window. -/
theorem succScanner_decides {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1)) (Ra Rb : CodeRegs kk jj)
    (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (ha : HoldsCodeScan tm x S cols Ra a) (hb : HoldsCodeScan tm x S cols Rb b)
    (hne : a.1 ≠ tm.qhalt)
    (hendW : ∀ i, markOf (fun q c => cols q (windowCols par Ra Rb i c))
      (succParamsCodec tm.Q kk).width 1 (S + 1) = false)
    (hendO : markOf (fun q c => cols q (outputCols par Ra Rb c))
      (succParamsCodec tm.Q kk).width 1 (S + 2) = false)
    (hin : P.inSym = inSymOf tm x S a)
    (hv : (succScanner tm x.length S par Ra Rb).emit
      ((succScanner tm x.length S par Ra Rb).run cols (walkScanLen tm x.length S)) = true) :
    b ∈ NTM.codeSucc tm x S a ∧
      b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val := by
  obtain ⟨vwork, vout, vhead, vsta, vstb⟩ :=
    succScanner_verdicts tm x.length S par Ra Rb cols hv
  -- Reading `▷` forces the input head right, so a left move means it was not at the marker.
  have hleft : (succTrans tm P).2.2.2.1 = Dir3.left → 0 < a.2.1.val := by
    intro hd
    by_contra hzero
    have h0 : a.2.1.val = 0 := by omega
    have hstart : P.inSym = Γ.start := by
      rw [hin, inSymOf, h0]
      exact Tape.init_cells_zero _
    have hright := (tm.δ_right_of_start P.beta P.q P.inSym P.wSym P.oSym).1 hstart
    rw [succTrans] at hd
    rw [hd] at hright
    exact Dir3.noConfusion hright
  obtain ⟨hast, hahd, hawk, haot⟩ := ha
  obtain ⟨hbst, hbhd, hbwk, hbot⟩ := hb
  have hPo : windowParams tm (fun q c => cols q (outputCols par Ra Rb c)) = P :=
    (params_of_holds tm P (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Ra c)) hpar hpar).1
  have hPsa : paramsOfStateTable tm
      (stateTable tm (fun q c => cols q (stateCols par Ra c))) = P :=
    (params_of_holds tm P (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Ra c)) hpar hpar).2
  have hPsb : paramsOfStateTable tm
      (stateTable tm (fun q c => cols q (stateCols par Rb c))) = P :=
    (params_of_holds tm P (fun q c => cols q (outputCols par Ra Rb c))
      (fun q c => cols q (stateCols par Rb c)) hpar hpar).2
  have hq : a.1 = P.q := by
    have h := (stateScanner_decides tm false (fun q c => cols q (stateCols par Ra c)) a.1
      hast).mp vsta
    rwa [hPsa, ite_eq_right (by simp)] at h
  have hstate : b.1 = succState tm P := by
    have h := (stateScanner_decides tm true (fun q c => cols q (stateCols par Rb c)) b.1
      hbst).mp vstb
    rwa [hPsb, ite_eq_left rfl] at h
  have hwork : ∀ i, ((a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) ∧
      (∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
        else (a.2.2.1 i).2 p) ∧
      (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val := by
    intro i
    have h := (windowScanner_decides tm i (fun q c => cols q (windowCols par Ra Rb i c)) S
      (a.2.2.1 i).1 (b.2.2.1 i).1 (a.2.2.1 i).2 (b.2.2.1 i).2 (hawk i) (hbwk i)
      (hendW i)).mp (vwork i)
    rwa [windowParams_congr tm (fun q c => cols q (windowCols par Ra Rb i c))
      (fun q c => cols q (outputCols par Ra Rb c)) (fun _ => rfl), hPo] at h
  have hout : (a.2.2.2.2 a.2.2.2.1 = P.oSym) ∧
      (∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
        then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p) ∧
      b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val := by
    have h := (outputScanner_decides tm (fun q c => cols q (outputCols par Ra Rb c)) S
      a.2.2.2.1 b.2.2.2.1 a.2.2.2.2 b.2.2.2.2 haot hbot hendO).mp vout
    rwa [hPo] at h
  have hpar' : windowParams tm (fun q c => cols q (headCols par Ra Rb c)) = P := by
    rw [windowParams_congr tm (fun q c => cols q (headCols par Ra Rb c))
      (fun q c => cols q (outputCols par Ra Rb c)) (fun _ => rfl)]
    exact hPo
  have hhead : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val := by
    have h := (headScanner_decides tm (fun q c => cols q (headCols par Ra Rb c))
      (bitWidth (x.length + S + 2)) a.2.1.val b.2.1.val
      (lt_of_lt_of_le a.2.1.isLt (le_two_pow_bitWidth _))
      (lt_of_lt_of_le b.2.1.isLt (le_two_pow_bitWidth _))
      hahd.shift hbhd.shift (by rw [hpar']; exact hleft)).mp vhead
    rwa [hpar'] at h
  -- The new code's fields are bounded by their own types, so the step stays in the window.
  have hclampIn : movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1 := by
    rw [← hhead]
    exact Nat.lt_succ_iff.mp b.2.1.isLt
  have hclampW : ∀ i, movedIdx (succDir tm P i) (a.2.2.1 i).1.val ≤ S := by
    intro i
    rw [← (hwork i).2.2]
    exact Nat.lt_succ_iff.mp (b.2.2.1 i).1.isLt
  have hclampO : movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ≤ S + 1 := by
    rw [← hout.2.2]
    exact Nat.lt_succ_iff.mp b.2.2.2.1.isLt
  exact ⟨mem_codeSucc_of_checks tm x S a b P hne hq hin (fun i => (hwork i).1) hout.1
    hclampIn hclampW hclampO hstate hhead
    (fun i => ⟨(hwork i).2.2, (hwork i).2.1⟩) ⟨hout.2.2, hout.2.1⟩, hhead⟩

/-- The columns the direction check reads: the parameter block, then the direction register. -/
def dirCols {jj : ℕ} (par dr : Fin (jj + 1)) : Fin 2 → Fin (jj + 1) :=
  fun c => if c.val = 0 then par else dr

/-- The counter check of a walk step: the counter either stays as it was or advances by one.
Only the second step of a pair advances it, so that the counter names the loop's iteration. -/
noncomputable def counterStepScanner {jj : ℕ} (cntOld cntNew : Fin (jj + 1)) (wc : ℕ)
    (advance : Bool) : Scanner jj :=
  if advance then (Scanner.plusOne jj cntOld cntNew).upTo wc
  else (Scanner.eq jj cntOld cntNew).upTo wc

theorem rightOnly_plusOne (jj : ℕ) (a b : Fin (jj + 1)) :
    Scanner.RightOnly (Scanner.plusOne jj a b) := fun _ _ => rfl

/-- **The counter check decides what it should.** -/
theorem counterStepScanner_decides {jj : ℕ} (cntOld cntNew : Fin (jj + 1)) (wc len : ℕ)
    (advance : Bool) (hw : wc ≤ len) (cols : ℕ → Fin (jj + 1) → Γ) (u v : ℕ)
    (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hold : HoldsBits cols 0 cntOld (bitsOfLenLE wc u))
    (hnew : HoldsBits cols 0 cntNew (bitsOfLenLE wc v))
    (hverdict : (counterStepScanner cntOld cntNew wc advance).emit
      ((counterStepScanner cntOld cntNew wc advance).run cols len) = true) :
    if advance then v = u + 1 else u = v := by
  rw [counterStepScanner] at hverdict
  cases advance with
  | true =>
      rw [ite_eq_left rfl, Scanner.upTo_emit_run _ (rightOnly_plusOne jj cntOld cntNew) wc len hw]
        at hverdict
      exact (plusOne_of_holds cols cntOld cntNew wc u v hu hv hold hnew).mp hverdict
  | false =>
      rw [ite_eq_right (by simp),
        Scanner.upTo_emit_run _ (Scanner.rightOnly_eq jj cntOld cntNew) wc len
        hw] at hverdict
      show u = v
      have hbits := (eq_run_of_holds cols cntOld cntNew (bitsOfLenLE wc u) (bitsOfLenLE wc v)
        (by rw [bitsOfLenLE_length, bitsOfLenLE_length]) hold hnew).mp
        (by rw [bitsOfLenLE_length]; exact hverdict)
      have := congrArg binValLE hbits
      rwa [binValLE_bitsOfLenLE wc u hu, binValLE_bitsOfLenLE wc v hv] at this

/-- An encoding of directions in two guessed cells that `TM.inMoveTM` can read back. A guessed
cell holds a bit, so one cell cannot name one of three directions; the first cell says whether to
move at all and the second which way. -/
structure DirCodec where
  /-- Whether the direction moves the head. -/
  encMove : Dir3 → Γ
  /-- Which way it moves, when it does. -/
  enc : Dir3 → Γ
  /-- And how to read the pair back. -/
  dec : Γ → Γ → Dir3
  /-- Reading back what was written gives the direction again. -/
  dec_enc : ∀ d, dec (encMove d) (enc d) = d
  /-- Both cells hold bits, so a guess can write them. -/
  encMove_bit : ∀ d, encMove d = Γ.zero ∨ encMove d = Γ.one
  /-- And likewise the direction cell. -/
  enc_bit : ∀ d, enc d = Γ.zero ∨ enc d = Γ.one

/-- The direction codec: the first cell is `1` exactly when the head moves, the second `1` for
right and `0` for left. -/
def dirCodec : DirCodec where
  encMove d := match d with
    | .stay => Γ.zero
    | _ => Γ.one
  enc d := match d with
    | .left => Γ.zero
    | _ => Γ.one
  dec m g := if m = Γ.one then (if g = Γ.one then .right else .left) else .stay
  dec_enc d := by cases d <;> rfl
  encMove_bit d := by cases d <;> simp
  enc_bit d := by cases d <;> simp

/-- **A bit-valued cell reads back as itself.** -/
theorem ofBool_decide_one {g : Γ} (h : g = Γ.zero ∨ g = Γ.one) :
    Γ.ofBool (decide (g = Γ.one)) = g := by
  rcases h with h | h <;> rw [h] <;> rfl

/-- The direction that takes `max h 1` to `max (movedIdx d h) 1`. -/
def adjustedDir (d : Dir3) (h : ℕ) : Dir3 :=
  if h = 0 then Dir3.stay else if movedIdx d h = 0 then Dir3.stay else d

/-- The scan that pins the direction register, conditional on both head fields being off the
marker. -/
noncomputable def dirCheckScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr hdOld hdNew : Fin (jj + 1)) (dc : DirCodec) : Scanner jj :=
  Scanner.or
    (Scanner.all 3 (fun p => if p.val = 0 then
        Scanner.or (headZeroScanner tm nn S hdOld) (headZeroScanner tm nn S hdNew)
      else if p.val = 1 then (Scanner.isConst jj mv (dc.encMove Dir3.stay)).upTo 1
      else (Scanner.isConst jj dr (dc.enc Dir3.stay)).upTo 1))
    (Scanner.all 4 (fun p => if p.val = 0 then headNonZeroScanner tm nn S hdOld
      else if p.val = 1 then headNonZeroScanner tm nn S hdNew
      else if p.val = 2 then
        ((dirScanner tm dc.encMove).comap (dirCols par mv)).upTo (succParamsCodec tm.Q kk).width
      else ((dirScanner tm dc.enc).comap (dirCols par dr)).upTo (succParamsCodec tm.Q kk).width))

/-- **The direction check pins the register to the direction the machine must actually take.** -/
theorem dirCheckScanner_decides {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr hdOld hdNew : Fin (jj + 1)) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (a b : Code tm.Q kk x.length S)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (hhdOld : HoldsBits cols (succParamsCodec tm.Q kk).width hdOld
      ((finCodec (x.length + S + 2)).enc a.2.1))
    (hhdNew : HoldsBits cols (succParamsCodec tm.Q kk).width hdNew
      ((finCodec (x.length + S + 2)).enc b.2.1))
    (hmove : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val)
    (hv : (dirCheckScanner tm x.length S par mv dr hdOld hdNew dc).emit
      ((dirCheckScanner tm x.length S par mv dr hdOld hdNew dc).run cols
        (walkScanLen tm x.length S)) = true) :
    cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
      cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) := by
  have hzO := headZeroScanner_decides tm x.length S hdOld cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) a.2.1 hhdOld
  have hzN := headZeroScanner_decides tm x.length S hdNew cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) b.2.1 hhdNew
  have hnO := headNonZeroScanner_decides tm x.length S hdOld cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) a.2.1 hhdOld
  have hnN := headNonZeroScanner_decides tm x.length S hdNew cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) b.2.1 hhdNew
  rw [dirCheckScanner, Scanner.or_emit_run] at hv
  have hlen2 : 1 ≤ walkScanLen tm x.length S := by
    have := two_le_walkScanLen tm x.length S
    omega
  rcases hv with h | h
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    rw [ite_eq_left (rfl : (0 : ℕ) = 0), Scanner.or_emit_run] at h0
    rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0)), ite_eq_left (rfl : (1 : ℕ) = 1)] at h1
    rw [ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 0)),
      ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
    have hstay : adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val = Dir3.stay := by
      rw [adjustedDir]
      rcases h0 with hz | hz
      · rw [ite_eq_left (hzO.mp hz)]
      · by_cases ha : a.2.1.val = 0
        · rw [ite_eq_left ha]
        · rw [ite_eq_right ha, ite_eq_left (by rw [← hmove]; exact hzN.mp hz)]
    rw [hstay]
    exact ⟨(Scanner.isConst_cell jj mv (dc.encMove Dir3.stay) cols
        (walkScanLen tm x.length S) hlen2).mp h1,
      (Scanner.isConst_cell jj dr (dc.enc Dir3.stay) cols
        (walkScanLen tm x.length S) hlen2).mp h2⟩
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    have h3 := h ⟨3, by omega⟩
    rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at h0
    rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0)), ite_eq_left (rfl : (1 : ℕ) = 1)] at h1
    rw [ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 0)),
      ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 1)), ite_eq_left (rfl : (2 : ℕ) = 2),
      Scanner.upTo_emit_run _ (Scanner.rightOnly_comap (fun _ _ => rfl) (dirCols par mv))
        _ _ (succParamsCodec_width_le_walkScanLen tm x.length S),
      Scanner.comap_emit, Scanner.comap_run] at h2
    rw [ite_eq_right (by exact (by omega : (3 : ℕ) ≠ 0)),
      ite_eq_right (by exact (by omega : (3 : ℕ) ≠ 1)),
      ite_eq_right (by exact (by omega : (3 : ℕ) ≠ 2)),
      Scanner.upTo_emit_run _ (Scanner.rightOnly_comap (fun _ _ => rfl) (dirCols par dr))
        _ _ (succParamsCodec_width_le_walkScanLen tm x.length S),
      Scanner.comap_emit, Scanner.comap_run] at h3
    have hdir : adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val = (succTrans tm P).2.2.2.1 := by
      rw [adjustedDir, ite_eq_right (hnO.mp h0), ite_eq_right (by rw [← hmove]; exact hnN.mp h1)]
    rw [hdir]
    exact ⟨(dirScanner_decides tm dc.encMove (fun q c => cols q (dirCols par mv c)) P hpar).mp h2,
      (dirScanner_decides tm dc.enc (fun q c => cols q (dirCols par dr c)) P hpar).mp h3⟩

/-- **The direction check accepts the direction the machine must take.** -/
theorem dirCheckScanner_accepts {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr hdOld hdNew : Fin (jj + 1)) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (a b : Code tm.Q kk x.length S)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (hhdOld : HoldsBits cols (succParamsCodec tm.Q kk).width hdOld
      ((finCodec (x.length + S + 2)).enc a.2.1))
    (hhdNew : HoldsBits cols (succParamsCodec tm.Q kk).width hdNew
      ((finCodec (x.length + S + 2)).enc b.2.1))
    (hmove : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val)
    (hmv : cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val))
    (hdr : cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val)) :
    (dirCheckScanner tm x.length S par mv dr hdOld hdNew dc).emit
      ((dirCheckScanner tm x.length S par mv dr hdOld hdNew dc).run cols
        (walkScanLen tm x.length S)) = true := by
  have hlen1 : 1 ≤ walkScanLen tm x.length S := one_le_walkScanLen tm x.length S
  have hzO := headZeroScanner_decides tm x.length S hdOld cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) a.2.1 hhdOld
  have hzN := headZeroScanner_decides tm x.length S hdNew cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) b.2.1 hhdNew
  have hnO := headNonZeroScanner_decides tm x.length S hdOld cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) a.2.1 hhdOld
  have hnN := headNonZeroScanner_decides tm x.length S hdNew cols (walkScanLen tm x.length S)
    (headField_le_walkScanLen tm x.length S) b.2.1 hhdNew
  rw [dirCheckScanner, Scanner.or_emit_run]
  by_cases hz : a.2.1.val = 0 ∨ b.2.1.val = 0
  · have hstay : adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val = Dir3.stay := by
      rw [adjustedDir]
      rcases hz with hz | hz
      · rw [ite_eq_left hz]
      · by_cases ha : a.2.1.val = 0
        · rw [ite_eq_left ha]
        · rw [ite_eq_right ha, ite_eq_left (by rw [← hmove]; exact hz)]
    refine Or.inl ?_
    rw [Scanner.all_emit_run]
    intro p
    by_cases hp0 : p.val = 0
    · rw [ite_eq_left hp0, Scanner.or_emit_run]
      rcases hz with hz | hz
      · exact Or.inl (hzO.mpr hz)
      · exact Or.inr (hzN.mpr hz)
    · rw [ite_eq_right hp0]
      by_cases hp1 : p.val = 1
      · rw [ite_eq_left hp1]
        exact (Scanner.isConst_cell jj mv (dc.encMove Dir3.stay) cols
          (walkScanLen tm x.length S) hlen1).mpr (by rw [hmv, hstay])
      · rw [ite_eq_right hp1]
        exact (Scanner.isConst_cell jj dr (dc.enc Dir3.stay) cols
          (walkScanLen tm x.length S) hlen1).mpr (by rw [hdr, hstay])
  · have hzA : a.2.1.val ≠ 0 := fun hc => hz (Or.inl hc)
    have hzB : b.2.1.val ≠ 0 := fun hc => hz (Or.inr hc)
    have hdir : adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val = (succTrans tm P).2.2.2.1 := by
      rw [adjustedDir, ite_eq_right hzA, ite_eq_right (by rw [← hmove]; exact hzB)]
    refine Or.inr ?_
    rw [Scanner.all_emit_run]
    intro p
    by_cases hp0 : p.val = 0
    · rw [ite_eq_left hp0]
      exact hnO.mpr hzA
    · rw [ite_eq_right hp0]
      by_cases hp1 : p.val = 1
      · rw [ite_eq_left hp1]
        exact hnN.mpr hzB
      · rw [ite_eq_right hp1]
        by_cases hp2 : p.val = 2
        · rw [ite_eq_left hp2, Scanner.upTo_emit_run _
            (Scanner.rightOnly_comap (fun _ _ => rfl) (dirCols par mv))
            _ _ (succParamsCodec_width_le_walkScanLen tm x.length S),
            Scanner.comap_emit, Scanner.comap_run]
          refine (dirScanner_decides tm dc.encMove (fun q c => cols q (dirCols par mv c)) P
            hpar).mpr ?_
          show cols 1 mv = _
          rw [hmv, hdir]
        · rw [ite_eq_right hp2, Scanner.upTo_emit_run _
            (Scanner.rightOnly_comap (fun _ _ => rfl) (dirCols par dr))
            _ _ (succParamsCodec_width_le_walkScanLen tm x.length S),
            Scanner.comap_emit, Scanner.comap_run]
          refine (dirScanner_decides tm dc.enc (fun q c => cols q (dirCols par dr c)) P
            hpar).mpr ?_
          show cols 1 dr = _
          rw [hdr, hdir]

/-- The code half of a walk step's scan. -/
noncomputable def walkCodeScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr res : Fin (jj + 1)) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1)) : Scanner jj :=
  Scanner.or
    (Scanner.all 3 (fun p => if p.val = 0 then eqScanner tm nn S j j'
      else if p.val = 1 then (Scanner.isConst jj mv (dc.encMove Dir3.stay)).upTo 1
      else (Scanner.isConst jj dr (dc.enc Dir3.stay)).upTo 1))
    (Scanner.all 3 (fun p => if p.val = 0 then
        succScanner tm nn S par (codeRegsOf j) (codeRegsOf j')
      else if p.val = 1 then
        dirCheckScanner tm nn S par mv dr (codeRegsOf (kk := kk) j).hd
          (codeRegsOf (kk := kk) j').hd dc
      else inSymScanner tm nn S par (codeRegsOf (kk := kk) j).hd res))


/-- **The counter check accepts the move it is meant to.** -/
theorem counterStepScanner_accepts {jj : ℕ} (cntOld cntNew : Fin (jj + 1)) (wc len : ℕ)
    (advance : Bool) (hw : wc ≤ len) (cols : ℕ → Fin (jj + 1) → Γ) (u v : ℕ)
    (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hold : HoldsBits cols 0 cntOld (bitsOfLenLE wc u))
    (hnew : HoldsBits cols 0 cntNew (bitsOfLenLE wc v))
    (hmove : if advance then v = u + 1 else u = v) :
    (counterStepScanner cntOld cntNew wc advance).emit
      ((counterStepScanner cntOld cntNew wc advance).run cols len) = true := by
  rw [counterStepScanner]
  cases advance with
  | true =>
      rw [ite_eq_left rfl, Scanner.upTo_emit_run _ (rightOnly_plusOne jj cntOld cntNew) wc len hw]
      exact (plusOne_of_holds cols cntOld cntNew wc u v hu hv hold hnew).mpr (by
        simpa using hmove)
  | false =>
      rw [ite_eq_right (by simp),
        Scanner.upTo_emit_run _ (Scanner.rightOnly_eq jj cntOld cntNew) wc len
        hw]
      have huv : u = v := by simpa using hmove
      subst huv
      have h := (eq_run_of_holds cols cntOld cntNew (bitsOfLenLE wc u) (bitsOfLenLE wc u)
        rfl hold hnew).mpr rfl
      rwa [bitsOfLenLE_length] at h

/-- **The code half of a walk step's scan decides a walk step, and says how the input head
moves.** The symbol under the simulated input head is not scanned but read from the machine's own
input tape by `TM.inMatchTM`, whose verdict the scan requires on register `res`; `hg` is the
invariant that the machine's input head sits where the simulated one does. -/
theorem walkCodeScanner_decides {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res : Fin (jj + 1)) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (g : Γ)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S b p))
    (hne : a.1 ≠ tm.qhalt)
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (hv : (walkCodeScanner tm x.length S par mv dr res dc j j').emit
      ((walkCodeScanner tm x.length S par mv dr res dc j j').run cols
        (walkScanLen tm x.length S)) = true) :
    (b = a ∧ cols 1 mv = dc.encMove Dir3.stay ∧ cols 1 dr = dc.enc Dir3.stay) ∨
      (b ∈ NTM.codeSucc tm x S a ∧
        b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
        cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
        cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val)) := by
  have hendW : ∀ i : Fin kk, markOf (fun q c =>
      cols q (windowCols par (codeRegsOf (kk := kk) j) (codeRegsOf (kk := kk) j') i c))
      (succParamsCodec tm.Q kk).width 1 (S + 1) = false := by
    intro i
    exact markOf_end tm x S a (i.val + 2) (S + 1) (by omega)
      (by
        rw [codeBlock_wk, (tapeCodec (S + 1)).enc_length]
        show (S + 1) * 3 = 3 * (S + 1)
        omega)
      cols (j (i.val + 2))
      (ha (i.val + 2) (by omega))
  have hendO : markOf (fun q c => cols q
      (outputCols par (codeRegsOf (kk := kk) j) (codeRegsOf (kk := kk) j') c))
      (succParamsCodec tm.Q kk).width 1 (S + 2) = false :=
    markOf_end tm x S a (kk + 2) (S + 2) (by omega)
      (by
        rw [codeBlock_ot, (tapeCodec (S + 2)).enc_length]
        show (S + 2) * 3 = 3 * (S + 2)
        omega) cols (j (kk + 2))
      (ha (kk + 2) (by omega))
  rw [walkCodeScanner, Scanner.or_emit_run] at hv
  rcases hv with h | h
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at h0
    rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0)), ite_eq_left (rfl : (1 : ℕ) = 1)] at h1
    rw [ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 0)),
      ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
    exact Or.inl ⟨(eqScanner_decides tm x S cols j j' a b ha hb h0).symm,
      (Scanner.isConst_cell jj mv (dc.encMove Dir3.stay) cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mp h1,
      (Scanner.isConst_cell jj dr (dc.enc Dir3.stay) cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mp h2⟩
  · rw [Scanner.all_emit_run] at h
    have h0 := h ⟨0, by omega⟩
    have h1 := h ⟨1, by omega⟩
    have h2 := h ⟨2, by omega⟩
    rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at h0
    rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0)), ite_eq_left (rfl : (1 : ℕ) = 1)] at h1
    rw [ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 0)),
      ite_eq_right (by exact (by omega : (2 : ℕ) ≠ 1))] at h2
    have hin : P.inSym = inSymOf tm x S a :=
      inSymScanner_decides tm x S cols par (codeRegsOf j).hd res P a g hpar
        (holdsCodeScan_of_blocks tm x S cols j a ha).2.1 hres hg h2
    obtain ⟨hsucc, hmove⟩ := succScanner_decides tm x S cols par (codeRegsOf j) (codeRegsOf j')
      a b P hpar (holdsCodeScan_of_blocks tm x S cols j a ha)
      (holdsCodeScan_of_blocks tm x S cols j' b hb) hne hendW hendO hin h0
    obtain ⟨hmvc, hdrc⟩ := dirCheckScanner_decides tm x S cols par mv dr (codeRegsOf j).hd
      (codeRegsOf j').hd dc P a b hpar (holdsCodeScan_of_blocks tm x S cols j a ha).2.1
      (holdsCodeScan_of_blocks tm x S cols j' b hb).2.1 hmove h1
    exact Or.inr ⟨hsucc, hmove, hmvc, hdrc⟩

/-- **The walk-step scan accepts a step that stays put.** -/
theorem walkCodeScanner_accepts_stay {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res : Fin (jj + 1)) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S)
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S a p))
    (hmv : cols 1 mv = dc.encMove Dir3.stay) (hdr : cols 1 dr = dc.enc Dir3.stay) :
    (walkCodeScanner tm x.length S par mv dr res dc j j').emit
      ((walkCodeScanner tm x.length S par mv dr res dc j j').run cols
        (walkScanLen tm x.length S)) = true := by
  rw [walkCodeScanner, Scanner.or_emit_run]
  refine Or.inl ?_
  rw [Scanner.all_emit_run]
  intro p
  by_cases hp : p.val = 0
  · rw [ite_eq_left hp]
    exact eqScanner_accepts tm x S cols j j' a ha hb
  · rw [ite_eq_right hp]
    by_cases hp1 : p.val = 1
    · rw [ite_eq_left hp1]
      exact (Scanner.isConst_cell jj mv (dc.encMove Dir3.stay) cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mpr hmv
    · rw [ite_eq_right hp1]
      exact (Scanner.isConst_cell jj dr (dc.enc Dir3.stay) cols (walkScanLen tm x.length S)
        (one_le_walkScanLen tm x.length S)).mpr hdr

/-- **The walk-step scan accepts a step that advances.** -/
theorem walkCodeScanner_accepts_succ {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res : Fin (jj + 1)) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S b p))
    (hq : a.1 = P.q) (hstate : b.1 = succState tm P)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym)
    (hhead : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val)
    (hwork : ∀ i, (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val ∧
      ∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
        else (a.2.2.1 i).2 p)
    (hout : b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ∧
      ∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
        then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p)
    (hleft : (succTrans tm P).2.2.2.1 = Dir3.left → 0 < a.2.1.val)
    (hdr : (dirCheckScanner tm x.length S par mv dr (codeRegsOf (kk := kk) j).hd
      (codeRegsOf (kk := kk) j').hd dc).emit
      ((dirCheckScanner tm x.length S par mv dr (codeRegsOf (kk := kk) j).hd
        (codeRegsOf (kk := kk) j').hd dc).run cols (walkScanLen tm x.length S)) = true)
    (hres : (inSymScanner tm x.length S par (codeRegsOf (kk := kk) j).hd res).emit
      ((inSymScanner tm x.length S par (codeRegsOf (kk := kk) j).hd res).run cols
        (walkScanLen tm x.length S)) = true) :
    (walkCodeScanner tm x.length S par mv dr res dc j j').emit
      ((walkCodeScanner tm x.length S par mv dr res dc j j').run cols
        (walkScanLen tm x.length S)) = true := by
  have hendW : ∀ i : Fin kk, markOf (fun q c =>
      cols q (windowCols par (codeRegsOf (kk := kk) j) (codeRegsOf (kk := kk) j') i c))
      (succParamsCodec tm.Q kk).width 1 (S + 1) = false := by
    intro i
    exact markOf_end tm x S a (i.val + 2) (S + 1) (by omega)
      (by
        rw [codeBlock_wk, (tapeCodec (S + 1)).enc_length]
        show (S + 1) * 3 = 3 * (S + 1)
        omega)
      cols (j (i.val + 2)) (ha (i.val + 2) (by omega))
  have hendO : markOf (fun q c => cols q
      (outputCols par (codeRegsOf (kk := kk) j) (codeRegsOf (kk := kk) j') c))
      (succParamsCodec tm.Q kk).width 1 (S + 2) = false :=
    markOf_end tm x S a (kk + 2) (S + 2) (by omega)
      (by
        rw [codeBlock_ot, (tapeCodec (S + 2)).enc_length]
        show (S + 2) * 3 = 3 * (S + 2)
        omega) cols (j (kk + 2)) (ha (kk + 2) (by omega))
  rw [walkCodeScanner, Scanner.or_emit_run]
  refine Or.inr ?_
  rw [Scanner.all_emit_run]
  intro p
  by_cases hp0 : p.val = 0
  · rw [ite_eq_left hp0]
    exact succScanner_accepts tm x S cols par (codeRegsOf j) (codeRegsOf j') a b P hpar
      (holdsCodeScan_of_blocks tm x S cols j a ha) (holdsCodeScan_of_blocks tm x S cols j' b hb)
      hendW hendO hq hstate hwsym hosym hhead hwork hout hleft
  · rw [ite_eq_right hp0]
    by_cases hp1 : p.val = 1
    · rw [ite_eq_left hp1]
      exact hdr
    · rw [ite_eq_right hp1]
      exact hres

/-- **One walk step, as a single scan.** Either the guessed code repeats the old one and the
input head is told to stay, or it is a successor and the input head is told to move the way the
transition does. The direction is part of the step because the machine's own input head tracks the
simulated one — `TM.inMoveTM` reads exactly the cell this check pins. -/
noncomputable def walkStepScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) : Scanner jj :=
  Scanner.all 2 (fun p => if p.val = 0 then walkCodeScanner tm nn S par mv dr res dc j j'
    else counterStepScanner cntOld cntNew wc advance)

/-- **The walk-step scan decides a step of the walk, how the input head moves, and what the
counter does.** -/
theorem walkStepScanner_decides {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ)
    (advance : Bool) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1))
    (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (g : Γ) (u v : ℕ)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S b p))
    (hne : a.1 ≠ tm.qhalt)
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a)
    (hwc : wc ≤ walkScanLen tm x.length S) (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hcntOld : HoldsBits cols 0 cntOld (bitsOfLenLE wc u))
    (hcntNew : HoldsBits cols 0 cntNew (bitsOfLenLE wc v))
    (hverdict : (walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').emit
      ((walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').run cols
        (walkScanLen tm x.length S)) = true) :
    ((b = a ∧ cols 1 mv = dc.encMove Dir3.stay ∧ cols 1 dr = dc.enc Dir3.stay) ∨
        (b ∈ NTM.codeSucc tm x S a ∧
          b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
          cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
          cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val))) ∧
      (if advance then v = u + 1 else u = v) := by
  rw [walkStepScanner, Scanner.all_emit_run] at hverdict
  have h0 := hverdict ⟨0, by omega⟩
  have h1 := hverdict ⟨1, by omega⟩
  rw [ite_eq_left (rfl : (0 : ℕ) = 0)] at h0
  rw [ite_eq_right (by exact (by omega : (1 : ℕ) ≠ 0))] at h1
  exact ⟨walkCodeScanner_decides tm x S cols par mv dr res dc j j' a b P g hpar ha hb hne hres hg
      h0,
    counterStepScanner_decides cntOld cntNew wc (walkScanLen tm x.length S) advance hwc cols u v
      hu hv hcntOld hcntNew h1⟩

/-- **The walk-step scan accepts a genuine step.** -/
theorem walkStepScanner_accepts {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ)
    (advance : Bool) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1))
    (hwc : wc ≤ walkScanLen tm x.length S) (u v : ℕ) (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hold : HoldsBits cols 0 cntOld (bitsOfLenLE wc u))
    (hnew : HoldsBits cols 0 cntNew (bitsOfLenLE wc v))
    (hmove : if advance then v = u + 1 else u = v)
    (hcode : (walkCodeScanner tm x.length S par mv dr res dc j j').emit
      ((walkCodeScanner tm x.length S par mv dr res dc j j').run cols
        (walkScanLen tm x.length S)) = true) :
    (walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').emit
      ((walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').run cols
        (walkScanLen tm x.length S)) = true := by
  rw [walkStepScanner, Scanner.all_emit_run]
  intro p
  by_cases hp : p.val = 0
  · rw [ite_eq_left hp]
    exact hcode
  · rw [ite_eq_right hp]
    exact counterStepScanner_accepts cntOld cntNew wc (walkScanLen tm x.length S) advance hwc
      cols u v hu hv hold hnew hmove

/-! ## The check phase

The input check and the scan, in sequence: the check leaves its verdict on a register, and the
scan — which reads every register — takes that verdict into account along with everything else. -/

/-- The registers after the input check: only the verdict register changes. -/
noncomputable def checkedCells {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ) (par res : Fin (jj + 1))
    (g : Γ) : Fin (jj + 1) → ℕ → Γ :=
  Function.update cells res
    (Function.update (cells res) 1
      (Γ.ofBool (TM.inMatchVerdict gammaBits g (cells par 1) (cells par 2))))

@[simp] theorem checkedCells_ne {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ)
    (par res : Fin (jj + 1)) (g : Γ) (i : Fin (jj + 1)) (hi : i ≠ res) :
    checkedCells cells par res g i = cells i := by
  rw [checkedCells, Function.update_of_ne hi]

@[simp] theorem checkedCells_res {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ)
    (par res : Fin (jj + 1)) (g : Γ) :
    checkedCells cells par res g res 1
      = Γ.ofBool (TM.inMatchVerdict gammaBits g (cells par 1) (cells par 2)) := by
  rw [checkedCells, Function.update_self, Function.update_self]

/-- **The input check leaves the scan well formed.** It writes one bit on the verdict register,
which is never the ruler. -/
theorem scanTape_checked {jj : ℕ} {cells : Fin (jj + 1) → ℕ → Γ} {len : ℕ}
    (h : TM.ScanTape cells len) (par res : Fin (jj + 1)) (hres : res ≠ 0) (g : Γ) :
    TM.ScanTape (checkedCells cells par res g) len where
  start i := by
    by_cases hi : i = res
    · subst hi
      rw [checkedCells, Function.update_self, Function.update_of_ne (by omega)]
      exact h.start i
    · rw [checkedCells_ne cells par res g i hi]
      exact h.start i
  ne_start i q hq := by
    by_cases hi : i = res
    · subst hi
      by_cases hq1 : q = 1
      · subst hq1
        rw [checkedCells_res]
        cases TM.inMatchVerdict gammaBits g (cells par 1) (cells par 2) <;>
          exact fun hc => Γ.noConfusion hc
      · rw [checkedCells, Function.update_self, Function.update_of_ne hq1]
        exact h.ne_start i q hq
    · rw [checkedCells_ne cells par res g i hi]
      exact h.ne_start i q hq
  ne_blank q h1 h2 := by
    rw [checkedCells_ne cells par res g 0 (fun hc => hres hc.symm)]
    exact h.ne_blank q h1 h2
  blank := by
    rw [checkedCells_ne cells par res g 0 (fun hc => hres hc.symm)]
    exact h.blank

/-- **A register other than the verdict's survives the input check.** -/
theorem checked_cell {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ) (par res : Fin (jj + 1)) (g : Γ)
    (r : Fin (jj + 1)) (hr : r ≠ res) (q : ℕ) : checkedCells cells par res g r q = cells r q := by
  rw [checkedCells_ne cells par res g r hr]

/-- **And so does what it holds.** -/
theorem holdsBits_checked {jj : ℕ} {cells : Fin (jj + 1) → ℕ → Γ} {par res : Fin (jj + 1)}
    {g : Γ} {r : Fin (jj + 1)} (hr : r ≠ res) {off : ℕ} {bits : List Bool}
    (h : HoldsBits (fun q i => cells i q) off r bits) :
    HoldsBits (fun q i => checkedCells cells par res g i q) off r bits := by
  intro q hq
  show checkedCells cells par res g r _ = _
  rw [checked_cell cells par res g r hr]
  exact h q hq

/-- **The check phase's contract.** -/
theorem checkPhase_hoareTime {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1))
    (cells : Fin (jj + 1) → ℕ → Γ) (len : ℕ) (inp₀ out₀ resT : Tape)
    (hok : TM.ScanOk inp₀ resT out₀) (ht : TM.ScanTape cells len)
    (hresSI : resT.StartInvariant) (hresH : 1 ≤ resT.head)
    (hpr : par ≠ res)
    (ht' : TM.ScanTape (checkedCells cells par res inp₀.read) len) :
    (TM.seqTM (TM.inMatchTM gammaBits par.castSucc res.castSucc)
        (TM.twoPassTM (walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew))).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) resT)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, checkedCells cells par res inp₀.read i⟩ : Tape))
          (resT.write (Γ.ofBool ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew).emit
            ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew).run
              (TM.scanCol (checkedCells cells par res inp₀.read)) len)))))
      (2 + 1 + (2 * len + 3)) := by
  classical
  set W₀ : Fin (jj + 2) → Tape := Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) resT with hW₀
  have hWcast : ∀ i : Fin (jj + 1), W₀ i.castSucc = (⟨1, cells i⟩ : Tape) := by
    intro i
    rw [hW₀, Fin.snoc_castSucc]
  have hWlast : W₀ (Fin.last (jj + 1)) = resT := by rw [hW₀, Fin.snoc_last]
  have hinv : ∀ i, (W₀ i).StartInvariant := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hWlast]; exact hresSI
    · intro q
      rw [hWcast q]
      exact ⟨ht.start q, fun p hp => ht.ne_start q p hp⟩
  have hh : ∀ i, 1 ≤ (W₀ i).head := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hWlast]; exact hresH
    · intro q
      rw [hWcast q]
  have hmatch := TM.inMatchTM_hoareTime gammaBits par.castSucc res.castSucc
    (by
      intro hc
      exact hpr (Fin.castSucc_injective _ hc))
    inp₀ out₀ W₀ hinv hh hok.inp hok.out (by rw [hWcast par]) (by rw [hWcast res])
  have hmatch' : (TM.inMatchTM gammaBits par.castSucc res.castSucc).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ i, i ≠ res.castSucc → work i = W₀ i) ∧
        work res.castSucc = TM.inMatchRes gammaBits inp₀.read ((W₀ par.castSucc).cells 1)
          ((W₀ par.castSucc).cells 2) (W₀ res.castSucc)) 2 :=
    hmatch.consequence (fun _ _ _ h => ⟨h.1, h.2.2, h.2.1⟩) (fun _ _ _ h => h) le_rfl
  have hmid : ∀ (inp : Tape) (work : Fin (jj + 2) → Tape) (out : Tape),
      (inp = inp₀ ∧ out = out₀ ∧
        (∀ i, i ≠ res.castSucc → work i = W₀ i) ∧
        work res.castSucc = TM.inMatchRes gammaBits inp₀.read ((W₀ par.castSucc).cells 1)
          ((W₀ par.castSucc).cells 2) (W₀ res.castSucc)) →
      (TM.transitionInput inp = inp₀ ∧ TM.transitionTape out = out₀ ∧
        (fun i => TM.transitionTape (work i))
          = Fin.snoc (fun i => (⟨1, checkedCells cells par res inp₀.read i⟩ : Tape)) resT) := by
    rintro inp work out ⟨rfl, rfl, hother, hres⟩
    have hnew : ∀ i, work i = (Fin.snoc
        (fun i => (⟨1, checkedCells cells par res inp.read i⟩ : Tape)) resT
        : Fin (jj + 2) → Tape) i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · have hne : (Fin.last (jj + 1) : Fin (jj + 2)) ≠ res.castSucc := by
          intro hc
          have hv := congrArg Fin.val hc
          have h1 : (Fin.last (jj + 1) : Fin (jj + 2)).val = jj + 1 := rfl
          have h2 : (res.castSucc : Fin (jj + 2)).val = res.val := rfl
          have := res.isLt
          omega
        rw [hother _ hne, hWlast, Fin.snoc_last]
      · intro q
        by_cases hq : q = res
        · subst hq
          rw [hres, hWcast q, hWcast par, Fin.snoc_castSucc, TM.inMatchRes, checkedCells,
            Function.update_self]
        · rw [hother _ (fun hc => hq (Fin.castSucc_injective _ hc)), hWcast q,
            Fin.snoc_castSucc, checkedCells, Function.update_of_ne hq]
    refine ⟨TM.transitionInput_eq_self hok.inp, TM.transitionTape_eq_self hok.out, ?_⟩
    funext i
    rw [hnew i]
    refine TM.transitionTape_eq_self ?_
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]
      exact hresSI.read_ne_start hresH
    · intro q
      rw [Fin.snoc_castSucc]
      exact fun hc => ht'.ne_start q 1 le_rfl hc
  exact TM.seqTM_hoareTime _ _ hmatch' hmid
    (TM.twoPassTM_hoareTime (walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew)
      (checkedCells cells par res inp₀.read) len inp₀ out₀ resT hok ht')

/-- The guess-free half of a walk step: check the guessed input symbol against the machine's own
input tape, run the walk-step scan, and move the input head by the direction the scan pinned. The
verdict is left on the result register, where the step's last stage conjoins it into the
accumulator. -/
noncomputable def walkCheckTM {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) : TM (jj + 2) :=
  TM.seqTM
    (TM.seqTM (TM.inMatchTM gammaBits par.castSucc res.castSucc)
      (TM.twoPassTM (walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew)))
    (TM.inMoveTM dc.dec mv.castSucc dr.castSucc)

/-- **The guess-free part of a walk step.** The input check, the scan, and the move of the input
head. -/
theorem checkMove_hoareTime {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (cells : Fin (jj + 1) → ℕ → Γ) (len : ℕ)
    (inp₀ out₀ resT : Tape) (hok : TM.ScanOk inp₀ resT out₀) (ht : TM.ScanTape cells len)
    (hresSI : resT.StartInvariant) (hresH : 1 ≤ resT.head) (hpr : par ≠ res)
    (ht' : TM.ScanTape (checkedCells cells par res inp₀.read) len) :
    (walkCheckTM tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) resT)
      (fun inp work out =>
        inp = inp₀.move (dc.dec (checkedCells cells par res inp₀.read mv 1)
          (checkedCells cells par res inp₀.read dr 1)) ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, checkedCells cells par res inp₀.read i⟩ : Tape))
          (resT.write (Γ.ofBool ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew).emit
            ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew).run
              (TM.scanCol (checkedCells cells par res inp₀.read)) len)))))
      (2 + 1 + (2 * len + 3) + 1 + 1) := by
  classical
  set v : Bool := (walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew).emit
    ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
        jold jnew).run
      (TM.scanCol (checkedCells cells par res inp₀.read)) len) with hvdef
  set W₁ : Fin (jj + 2) → Tape :=
    Fin.snoc (fun i => (⟨1, checkedCells cells par res inp₀.read i⟩ : Tape))
      (resT.write (Γ.ofBool v)) with hW₁
  have hW₁cast : ∀ i : Fin (jj + 1),
      W₁ i.castSucc = (⟨1, checkedCells cells par res inp₀.read i⟩ : Tape) := by
    intro i
    rw [hW₁, Fin.snoc_castSucc]
  have hW₁last : W₁ (Fin.last (jj + 1)) = resT.write (Γ.ofBool v) := by rw [hW₁, Fin.snoc_last]
  have hresW : (resT.write (Γ.ofBool v)).StartInvariant := by
    have := hresSI.write (Γw.ofBool v)
    rwa [Γw.ofBool_toΓ] at this
  have hresWh : 1 ≤ (resT.write (Γ.ofBool v)).head := by rw [Tape.write_head]; exact hresH
  have hinv₁ : ∀ i, (W₁ i).StartInvariant := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁last]; exact hresW
    · intro q
      rw [hW₁cast q]
      exact ⟨ht'.start q, fun p hp => ht'.ne_start q p hp⟩
  have hh₁ : ∀ i, 1 ≤ (W₁ i).head := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁last]; exact hresWh
    · intro q
      rw [hW₁cast q]
  have hns : ∀ i, (W₁ i).read ≠ Γ.start := fun i => (hinv₁ i).read_ne_start (hh₁ i)
  have hmove := TM.inMoveTM_hoareTime dc.dec mv.castSucc dr.castSucc inp₀ out₀ W₁ hinv₁ hh₁
    hok.inp hok.out
  have hmove' : (TM.inMoveTM dc.dec mv.castSucc dr.castSucc).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₁)
      (fun inp work out =>
        inp = inp₀.move (dc.dec (checkedCells cells par res inp₀.read mv 1)
          (checkedCells cells par res inp₀.read dr 1)) ∧ out = out₀ ∧
        work = W₁) 1 := by
    exact hmove.consequence (fun _ _ _ h => ⟨h.1, h.2.2, h.2.1⟩)
      (fun _ _ _ h => ⟨by rw [h.1, hW₁cast dr, hW₁cast mv]; rfl, h.2.2, h.2.1⟩) le_rfl
  refine TM.seqTM_hoareTime _ _
    (checkPhase_hoareTime tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew cells len
      inp₀ out₀ resT hok ht hresSI hresH hpr ht') ?_ hmove'
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨TM.transitionInput_eq_self hok.inp, TM.transitionTape_eq_self hok.out, ?_⟩
  funext i
  exact TM.transitionTape_eq_self (hns i)

/-- The registers after the scan's verdict is copied onto the accumulator. -/
noncomputable def verdictCells {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ) (acc : Fin (jj + 1))
    (v : Bool) : Fin (jj + 1) → ℕ → Γ :=
  Function.update cells acc (Function.update (cells acc) 1 (Γ.ofBool v))

@[simp] theorem verdictCells_self {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ)
    (acc : Fin (jj + 1)) (v : Bool) : verdictCells cells acc v acc 1 = Γ.ofBool v := by
  rw [verdictCells, Function.update_self, Function.update_self]

@[simp] theorem verdictCells_ne {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ)
    (acc : Fin (jj + 1)) (v : Bool) (i : Fin (jj + 1)) (hi : i ≠ acc) :
    verdictCells cells acc v i = cells i := by
  rw [verdictCells, Function.update_of_ne hi]

/-- **The accumulator reads one exactly when the scan accepted.** This is the cell the loop's
test looks at. -/
theorem verdictCells_acc_one {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ)
    (acc : Fin (jj + 1)) (v : Bool) :
    verdictCells cells acc v acc 1 = Γ.one ↔ v = true := by
  rw [verdictCells_self]
  cases v
  · exact ⟨fun h => absurd h (fun hc => Γ.noConfusion hc), fun h => absurd h (by simp)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## One walk step, as a machine

Guess the next code (and the transition, and the direction), rewind the guessed registers, check
the guessed input symbol against the machine's own input tape, run the walk-step scan, and move
the input head. The guess tape is last; everything after the guess stage is guess-free and lifted
past it. -/

/-- One walk step as a machine: guess every register, hold the enclosing loops' `r` tapes still,
check and move, and conjoin the verdict into the accumulator. -/
noncomputable def walkStepTM {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) :
    TM (jj + 2 + r + 1) :=
  TM.seqTM (TM.guessStageTM guessReg w t targets)
    (TM.seqTM
      (TM.liftLast (TM.liftMany
        (walkCheckTM tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew) r))
      (TM.andCellTM (Fin.castAdd r (Fin.last (jj + 1))).castSucc accIdx))

/-- **The contract of a walk step.** Guess every register, then check, move, and record. The
guessed tapes are named by `TM.guessBlocksTapes`; what they contain is the caller's business, and
`Complexity.walkStepScanner_decides` is what turns the resulting verdict into a step of the walk.
The accumulator is not a register — no guess can reach it — and it only ever loses its one, which
is what makes a single failed check final in a loop that cannot stop early. -/
theorem walkStepTM_hoareTime {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) (hnodup : targets.Nodup)
    (hall : ∀ i : Fin (jj + 2), Fin.castAdd r i ∈ targets)
    (haux : ∀ c : Fin r, Fin.natAdd (jj + 2) c ∉ targets)
    (hauxG : ∀ p c, p < t → guessReg p ≠ (Fin.natAdd (jj + 2) c).castSucc)
    (haccReg : ∀ i : Fin (jj + 2), accIdx ≠ (Fin.castAdd r i).castSucc)
    (haccLast : accIdx ≠ Fin.last (jj + 2 + r))
    (hj : ∀ p, guessReg p ≠ Fin.last (jj + 2 + r)) (B : ℕ) (hB : 1 ≤ B)
    (inp₀ out₀ : Tape) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (hinpSI : inp₀.StartInvariant) (houtSI : out₀.StartInvariant)
    (hinp : inp₀.read ≠ Γ.start) (hout : out₀.read ≠ Γ.start)
    (hinvW : ∀ i, (W₀ i).StartInvariant) (hhW : ∀ i, 1 ≤ (W₀ i).head)
    (hinj : ∀ p q, p < t → q < t → guessReg p = guessReg q → p = q)
    (hbound : ∀ i, i ∈ targets →
      (TM.guessBlocksTapes guessReg w t W₀ i.castSucc).head ≤ B)
    (len : ℕ)
    (hok : TM.ScanOk (TM.parkTape inp₀)
      (⟨1, (TM.guessBlocksTapes guessReg w t W₀
        (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape)
      (TM.parkTape out₀))
    (ht : TM.ScanTape (fun i : Fin (jj + 1) =>
      (TM.guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells) len)
    (hpr : par ≠ res)
    (ht' : TM.ScanTape (checkedCells (fun i : Fin (jj + 1) =>
      (TM.guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells) par res
      (TM.parkTape inp₀).read) len)
    (hmoved : ((TM.parkTape inp₀).move (dc.dec (checkedCells (fun i : Fin (jj + 1) =>
      (TM.guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells) par res
      (TM.parkTape inp₀).read mv 1) (checkedCells (fun i : Fin (jj + 1) =>
      (TM.guessBlocksTapes guessReg w t W₀ (Fin.castAdd r i.castSucc).castSucc).cells) par res
      (TM.parkTape inp₀).read dr 1))).read ≠ Γ.start) :
    (walkStepTM r tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew guessReg w t
      targets accIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₀)
      (fun inp work out =>
        work (Fin.last (jj + 2 + r))
          = TM.guessBlocksTapes guessReg w t W₀ (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r, (Fin.natAdd (jj + 2) c).castSucc ≠ accIdx →
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = (TM.parkTape inp₀).move (dc.dec (checkedCells (fun i : Fin (jj + 1) =>
            (TM.guessBlocksTapes guessReg w t W₀
              (Fin.castAdd r i.castSucc).castSucc).cells) par res
            (TM.parkTape inp₀).read mv 1) (checkedCells (fun i : Fin (jj + 1) =>
            (TM.guessBlocksTapes guessReg w t W₀
              (Fin.castAdd r i.castSucc).castSucc).cells) par res
            (TM.parkTape inp₀).read dr 1)) ∧
        out = TM.parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc =
          (Fin.snoc (fun i : Fin (jj + 1) =>
            (⟨1, checkedCells (fun i : Fin (jj + 1) =>
              (TM.guessBlocksTapes guessReg w t W₀
                (Fin.castAdd r i.castSucc).castSucc).cells) par res
              (TM.parkTape inp₀).read i⟩ : Tape))
          ((⟨1, (TM.guessBlocksTapes guessReg w t W₀
              (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ : Tape).write
            (Γ.ofBool ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
              jold jnew).emit
              ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
                jold jnew).run
                (TM.scanCol (checkedCells (fun i : Fin (jj + 1) =>
                  (TM.guessBlocksTapes guessReg w t W₀
                    (Fin.castAdd r i.castSucc).castSucc).cells) par res
                  (TM.parkTape inp₀).read)) len)))) : Fin (jj + 2) → Tape) i) ∧
        work accIdx = ⟨(W₀ accIdx).head, Function.update (W₀ accIdx).cells (W₀ accIdx).head
          (if (walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew).emit
              ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew).run
                (TM.scanCol (checkedCells (fun i : Fin (jj + 1) =>
                  (TM.guessBlocksTapes guessReg w t W₀
                    (Fin.castAdd r i.castSucc).castSucc).cells) par res
                  (TM.parkTape inp₀).read)) len) = true ∧ (W₀ accIdx).read = Γ.one
            then Γ.one else Γ.zero)⟩)
      (TM.guessBlocksTime w t + 1 + (1 + 1 + (targets.length * (B + 3) + 1)) + 1 +
        (2 + 1 + (2 * len + 3) + 1 + 1 + 1 + 1)) := by
  classical
  set G := TM.guessBlocksTapes guessReg w t W₀ with hG
  set cells : Fin (jj + 1) → ℕ → Γ :=
    fun i => (G (Fin.castAdd r i.castSucc).castSucc).cells with hcells
  set resT : Tape := ⟨1, (G (Fin.castAdd r (Fin.last (jj + 1))).castSucc).cells⟩ with hresT
  obtain ⟨ginv, ghh, -, -, -⟩ := TM.guessBlocksTapes_spec guessReg hj w t W₀ hinvW hhW hinj
  have hstage := TM.guessStageTM_hoareTime guessReg hj w t targets hnodup B hB inp₀ out₀ W₀
    hinpSI houtSI hinp hout hinvW hhW hinj hbound
  have hresSI : resT.StartInvariant :=
    ⟨(ginv ((Fin.castAdd r (Fin.last (jj + 1))).castSucc)).1,
      fun q hq => (ginv ((Fin.castAdd r (Fin.last (jj + 1))).castSucc)).2 q hq⟩
  have hD := checkMove_hoareTime tm nn S par mv dr res cntOld cntNew wc advance dc
    jold jnew cells len (TM.parkTape inp₀) (TM.parkTape out₀) resT hok ht hresSI le_rfl hpr ht'
  set v : Bool := (walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc
      jold jnew).emit
    ((walkStepScanner tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew).run
      (TM.scanCol (checkedCells cells par res (TM.parkTape inp₀).read)) len) with hvdef
  set W₁ : Fin (jj + 2) → Tape :=
    Fin.snoc (fun i : Fin (jj + 1) =>
      (⟨1, checkedCells cells par res (TM.parkTape inp₀).read i⟩ : Tape))
      (resT.write (Γ.ofBool v)) with hW₁
  set movedInp : Tape := (TM.parkTape inp₀).move
    (dc.dec (checkedCells cells par res (TM.parkTape inp₀).read mv 1)
      (checkedCells cells par res (TM.parkTape inp₀).read dr 1)) with hmovedInp
  have hGns : ∀ i, (G i).read ≠ Γ.start := fun i => (ginv i).read_ne_start (ghh i)
  have hGaux : ∀ c : Fin r, G (Fin.natAdd (jj + 2) c).castSucc
      = W₀ (Fin.natAdd (jj + 2) c).castSucc := by
    intro c
    refine (TM.guessBlocksTapes_spec guessReg hj w t W₀ hinvW hhW hinj).2.2.2.1
      _ (fun hc => ?_) (fun p hp hc => hauxG p c hp hc.symm)
    exact absurd (congrArg Fin.val hc) (by simp [Fin.natAdd]; omega)
  have hresW : (resT.write (Γ.ofBool v)).StartInvariant := by
    have := hresSI.write (Γw.ofBool v)
    rwa [Γw.ofBool_toΓ] at this
  have hW₁inv : ∀ i, (W₁ i).StartInvariant := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁, Fin.snoc_last]
      exact hresW
    · intro q
      rw [hW₁, Fin.snoc_castSucc]
      exact ⟨ht'.start q, fun p hp => ht'.ne_start q p hp⟩
  have hW₁head : ∀ i, 1 ≤ (W₁ i).head := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁, Fin.snoc_last]
      show 1 ≤ (resT.write (Γ.ofBool v)).head
      rw [Tape.write_head]
    · intro q
      rw [hW₁, Fin.snoc_castSucc]
  have hand : (TM.andCellTM (Fin.castAdd r (Fin.last (jj + 1))).castSucc accIdx).HoareTime
      (fun inp work out =>
        work (Fin.last (jj + 2 + r)) = G (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r,
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = movedInp ∧ out = TM.parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc = W₁ i))
      (fun inp work out =>
        work (Fin.last (jj + 2 + r)) = G (Fin.last (jj + 2 + r)) ∧
        (∀ c : Fin r, (Fin.natAdd (jj + 2) c).castSucc ≠ accIdx →
          work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc) ∧
        inp = movedInp ∧ out = TM.parkTape out₀ ∧
        (∀ i : Fin (jj + 2), work (Fin.castAdd r i).castSucc = W₁ i) ∧
        work accIdx = ⟨(W₀ accIdx).head, Function.update (W₀ accIdx).cells (W₀ accIdx).head
          (if v = true ∧ (W₀ accIdx).read = Γ.one then Γ.one else Γ.zero)⟩)
      1 := by
    rintro inp work out ⟨hglast, hgaux, rfl, rfl, hregs⟩
    have hidx : ∀ P : Fin (jj + 2 + r + 1) → Prop, P (Fin.last (jj + 2 + r)) →
        (∀ i : Fin (jj + 2), P (Fin.castAdd r i).castSucc) →
        (∀ c : Fin r, P (Fin.natAdd (jj + 2) c).castSucc) → ∀ i, P i := by
      intro P hlastP hregP hauxP i
      refine Fin.lastCases hlastP ?_ i
      intro k
      exact Fin.addCases (fun i => hregP i) (fun c => hauxP c) k
    have hacc : work accIdx = W₀ accIdx := by
      refine hidx (fun i => i = accIdx → work i = W₀ i) ?_ ?_ ?_ accIdx rfl
      · exact fun hc => absurd hc.symm haccLast
      · exact fun i hc => absurd hc.symm (haccReg i)
      · exact fun c _ => hgaux c
    have hinv' : ∀ i, (work i).StartInvariant := by
      refine hidx _ ?_ ?_ ?_
      · rw [hglast]; exact ginv _
      · intro i; rw [hregs i]; exact hW₁inv i
      · intro c; rw [hgaux c]; exact hinvW _
    have hh' : ∀ i, 1 ≤ (work i).head := by
      refine hidx _ ?_ ?_ ?_
      · rw [hglast]; exact ghh _
      · intro i; rw [hregs i]; exact hW₁head i
      · intro c; rw [hgaux c]; exact hhW _
    obtain ⟨c', tt, htt, hreach, hhalt, hin', hout', hother', hacc'⟩ :=
      TM.andCellTM_hoareTime (Fin.castAdd r (Fin.last (jj + 1))).castSucc accIdx
        movedInp (TM.parkTape out₀) work hinv' hh' hmoved
        (TM.parkTape_parked houtSI).read_ne_start movedInp work (TM.parkTape out₀)
        ⟨rfl, rfl, rfl⟩
    have hsrcRead : (work (Fin.castAdd r (Fin.last (jj + 1))).castSucc).read = Γ.ofBool v := by
      rw [hregs (Fin.last (jj + 1)), hW₁, Fin.snoc_last]
      show (resT.write (Γ.ofBool v)).read = _
      rw [Tape.write, ite_eq_right (show resT.head ≠ 0 by rw [hresT]; exact one_ne_zero)]
      show Function.update resT.cells resT.head (Γ.ofBool v) resT.head = _
      rw [Function.update_self]
    refine ⟨c', tt, htt, hreach, hhalt, ?_, ?_, hin', hout', ?_, ?_⟩
    · rw [hother' _ (Ne.symm haccLast), hglast]
    · intro c hc
      rw [hother' _ hc, hgaux c]
    · intro i
      rw [hother' _ (fun hcc => haccReg i hcc.symm), hregs i]
    · rw [hacc', hacc, hsrcRead]
      have hcond : (Γ.ofBool v = Γ.one) ↔ (v = true) := by
        cases v <;> simp [Γ.ofBool]
      simp only [hcond]
  have hmany := TM.liftMany_hoareTime _ hD r
    (fun c => W₀ (Fin.natAdd (jj + 2) c).castSucc)
    (fun c => (hinvW _).read_ne_start (hhW _))
  have hlift := TM.liftLast_hoareTime _ hmany (G (Fin.last (jj + 2 + r)))
    (hGns (Fin.last (jj + 2 + r)))
  refine TM.seqTM_hoareTime _ _ hstage ?_ (TM.seqTM_hoareTime _ _ hlift ?_ hand)
  · rintro inp work out ⟨hlast, hinpP, hwork, houtP⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show TM.transitionTape (work (Fin.last (jj + 2 + r))) = G (Fin.last (jj + 2 + r))
      rw [hlast]
      exact TM.transitionTape_eq_self (hGns _)
    · intro c
      show TM.transitionTape (work (Fin.natAdd (jj + 2) c).castSucc) = _
      have hc : work (Fin.natAdd (jj + 2) c).castSucc
          = TM.parkTape (G (Fin.natAdd (jj + 2) c).castSucc) := by
        have := congrFun hwork (Fin.natAdd (jj + 2) c)
        rw [this, ite_eq_right (haux c)]
      rw [hc, hGaux c, TM.parkTape_eq_self (hhW _)]
      exact TM.transitionTape_eq_self ((hinvW _).read_ne_start (hhW _))
    · rw [hinpP]
      exact TM.transitionInput_eq_self (TM.parkTape_parked hinpSI).read_ne_start
    · rw [houtP]
      exact TM.transitionTape_eq_self (TM.parkTape_parked houtSI).read_ne_start
    · funext i
      show TM.transitionTape (work (Fin.castAdd r i).castSucc) = _
      have hi : work (Fin.castAdd r i).castSucc
          = (⟨1, (G (Fin.castAdd r i).castSucc).cells⟩ : Tape) := by
        have := congrFun hwork (Fin.castAdd r i)
        rw [this, ite_eq_left (hall i)]
      rw [hi, TM.transitionTape_eq_self (by
        show (⟨1, (G (Fin.castAdd r i).castSucc).cells⟩ : Tape).read ≠ Γ.start
        exact fun hc => (ginv (Fin.castAdd r i).castSucc).2 1 le_rfl hc)]
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
      · intro q
        rw [Fin.snoc_castSucc]
  · rintro inp work out ⟨hlast, hgaux, hin, hout', hregs⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show TM.transitionTape (work (Fin.last (jj + 2 + r))) = _
      rw [hlast]
      exact TM.transitionTape_eq_self (hGns _)
    · intro c
      have h : work (Fin.natAdd (jj + 2) c).castSucc = W₀ (Fin.natAdd (jj + 2) c).castSucc :=
        hgaux c
      show TM.transitionTape (work (Fin.natAdd (jj + 2) c).castSucc) = _
      rw [h]
      exact TM.transitionTape_eq_self ((hinvW _).read_ne_start (hhW _))
    · rw [hin]
      exact TM.transitionInput_eq_self hmoved
    · rw [hout']
      exact TM.transitionTape_eq_self (TM.parkTape_parked houtSI).read_ne_start
    · intro i
      have h : work (Fin.castAdd r i).castSucc = W₁ i := congrFun hregs i
      show TM.transitionTape (work (Fin.castAdd r i).castSucc) = _
      rw [h]
      exact TM.transitionTape_eq_self ((hW₁inv i).read_ne_start (hW₁head i))
/-- Its advancing states: only the guess stage consumes guesses. -/
noncomputable def walkStepAdv {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) :
    (walkStepTM r tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew guessReg w t
      targets accIdx).Q → Bool :=
  TM.seqAdv (TM.seqAdv (TM.guessBlocksAdv guessReg w t) (fun _ => false))
    (TM.seqAdv (fun _ => false) (fun _ => false))

/-- **A walk step respects the guess protocol.** Only the guess stage advances the guess head; the
checks and the input-head move never consult it. -/
theorem guessProtocol_walkStepTM {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ) (advance : Bool) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1))
    (haccLast : accIdx ≠ Fin.last (jj + 2 + r)) :
    TM.GuessProtocol
      (walkStepTM r tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew guessReg w t
        targets accIdx)
      (walkStepAdv r tm nn S par mv dr res cntOld cntNew wc advance dc jold jnew guessReg w t
        targets accIdx) :=
  TM.guessProtocol_seqTM (TM.guessProtocol_guessStageTM guessReg w t targets)
    (TM.guessProtocol_seqTM (TM.guessProtocol_liftLast _)
      (TM.guessProtocol_andCellTM _ accIdx (by
        intro hc
        have hv := congrArg Fin.val hc
        have h1 : ((Fin.castAdd r (Fin.last (jj + 1))).castSucc
          : Fin (jj + 2 + r + 1)).val = jj + 1 := rfl
        have h2 : (Fin.last (jj + 2 + r) : Fin (jj + 2 + r + 1)).val = jj + 2 + r := rfl
        omega) haccLast))

/-! ## The loop's test

`TM.loopTM` decides whether to continue by reading cell one of the **output** tape, while a scan
writes its verdict to a work register. So a test is a scan followed by
`TM.writeOutputBitTM`, which publishes that register's bit on the output tape. The walk's test
compares the counter against the register holding the target count. -/

/-- **What the test decides**: the counter and the target agree over the counter's width. -/
theorem counterTest_verdict {jj : ℕ} (cnt target : Fin (jj + 1)) (wc len : ℕ) (hw : wc ≤ len)
    (cols : ℕ → Fin (jj + 1) → Γ) :
    ((Scanner.eq jj cnt target).upTo wc).emit
        (((Scanner.eq jj cnt target).upTo wc).run cols len) = true ↔
      ∀ q, 1 ≤ q → q ≤ wc → cols q cnt = cols q target := by
  rw [Scanner.upTo_emit_run _ (Scanner.rightOnly_eq jj cnt target) wc len hw]
  show (Scanner.eq jj cnt target).run cols wc = true ↔ _
  rw [Scanner.eq_run]

/-- **The counter and the target agree exactly when they hold the same number.** -/
theorem counterTest_decides {jj : ℕ} (cnt target : Fin (jj + 1)) (wc len : ℕ) (hw : wc ≤ len)
    (cols : ℕ → Fin (jj + 1) → Γ) (u v : ℕ) (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hcnt : HoldsBits cols 0 cnt (bitsOfLenLE wc u))
    (htar : HoldsBits cols 0 target (bitsOfLenLE wc v)) :
    ((Scanner.eq jj cnt target).upTo wc).emit
        (((Scanner.eq jj cnt target).upTo wc).run cols len) = true ↔ u = v := by
  rw [counterTest_verdict cnt target wc len hw cols]
  constructor
  · intro h
    have hbits : bitsOfLenLE wc u = bitsOfLenLE wc v := by
      refine List.ext_getElem (by rw [bitsOfLenLE_length, bitsOfLenLE_length]) ?_
      intro q h1 h2
      have hq : q < wc := by rw [bitsOfLenLE_length] at h1; exact h1
      have hc := h (q + 1) (by omega) (by omega)
      rw [show q + 1 = 0 + q + 1 by omega, hcnt q h1, htar q h2] at hc
      exact ofBool_injective hc
    have := congrArg binValLE hbits
    rwa [binValLE_bitsOfLenLE wc u hu, binValLE_bitsOfLenLE wc v hv] at this
  · intro h q h1 h2
    subst h
    have hq : q - 1 < wc := by omega
    have hc := hcnt (q - 1) (by rw [bitsOfLenLE_length]; exact hq)
    have ht := htar (q - 1) (by rw [bitsOfLenLE_length]; exact hq)
    rw [Nat.zero_add, show q - 1 + 1 = q by omega] at hc ht
    rw [hc, ht]

/-- The loop's test: stop when the counter reaches its target, or when a check has failed. A
failed check leaves the loop early, with the counter short of its target, and the comparison
afterwards rejects. -/
noncomputable def loopTestScanner {jj : ℕ} (cnt target acc : Fin (jj + 1)) (wc : ℕ) :
    Scanner jj :=
  Scanner.or ((Scanner.eq jj cnt target).upTo wc) ((Scanner.isNotConst jj acc Γ.one).upTo 1)

/-- **What the loop's test decides.** -/
theorem loopTestScanner_verdict {jj : ℕ} (cnt target acc : Fin (jj + 1)) (wc len : ℕ)
    (hw : wc ≤ len) (h1 : 1 ≤ len) (cols : ℕ → Fin (jj + 1) → Γ) :
    (loopTestScanner cnt target acc wc).emit
        ((loopTestScanner cnt target acc wc).run cols len) = true ↔
      ((∀ q, 1 ≤ q → q ≤ wc → cols q cnt = cols q target) ∨ cols 1 acc ≠ Γ.one) := by
  rw [loopTestScanner, Scanner.or_emit_run, counterTest_verdict cnt target wc len hw cols,
    Scanner.isNotConst_cell jj acc Γ.one cols len h1]

/-- **When the checks have passed, the loop stops exactly when the counter reaches its
target.** -/
theorem loopTestScanner_decides {jj : ℕ} (cnt target acc : Fin (jj + 1)) (wc len : ℕ)
    (hw : wc ≤ len) (h1 : 1 ≤ len) (cols : ℕ → Fin (jj + 1) → Γ) (u v : ℕ)
    (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hcnt : HoldsBits cols 0 cnt (bitsOfLenLE wc u))
    (htgt : HoldsBits cols 0 target (bitsOfLenLE wc v))
    (hacc : cols 1 acc = Γ.one) :
    (loopTestScanner cnt target acc wc).emit
        ((loopTestScanner cnt target acc wc).run cols len) = true ↔ u = v := by
  rw [loopTestScanner_verdict cnt target acc wc len hw h1 cols]
  constructor
  · rintro (hall | hne)
    · exact (counterTest_decides cnt target wc len hw cols u v hu hv hcnt htgt).mp
        ((counterTest_verdict cnt target wc len hw cols).mpr hall)
    · exact absurd hacc hne
  · intro huv
    refine Or.inl ((counterTest_verdict cnt target wc len hw cols).mp ?_)
    exact (counterTest_decides cnt target wc len hw cols u v hu hv hcnt htgt).mpr huv

/-- **A failed check stops the loop.** -/
theorem loopTestScanner_of_fail {jj : ℕ} (cnt target acc : Fin (jj + 1)) (wc len : ℕ)
    (hw : wc ≤ len) (h1 : 1 ≤ len) (cols : ℕ → Fin (jj + 1) → Γ)
    (hacc : cols 1 acc ≠ Γ.one) :
    (loopTestScanner cnt target acc wc).emit
      ((loopTestScanner cnt target acc wc).run cols len) = true :=
  (loopTestScanner_verdict cnt target acc wc len hw h1 cols).mpr (Or.inr hacc)

/-- The loop's test as a machine: the comparison, then the verdict published where `TM.loopTM`
reads it. -/
noncomputable def loopTestTM {jj : ℕ} (cnt target acc : Fin (jj + 1)) (wc : ℕ) : TM (jj + 2) :=
  TM.seqTM (TM.twoPassTM (loopTestScanner cnt target acc wc))
    (TM.writeOutputBitTM (Fin.last (jj + 1)))

/-- **A published test's contract.** The scan runs, and the publish step puts its verdict where
`TM.loopTM` looks for it: cell one of the output tape. -/
theorem publishTestTM_hoareTime {jj : ℕ} (Sc : Scanner jj) (len : ℕ)
    (cells : Fin (jj + 1) → ℕ → Γ) (inp₀ out₀ resT : Tape)
    (hok : TM.ScanOk inp₀ resT out₀) (ht : TM.ScanTape cells len)
    (hinpP : TM.Parked inp₀) (houtP : TM.Parked out₀) (hresSI : resT.StartInvariant)
    (hresH : resT.head = 1) :
    (TM.seqTM (TM.twoPassTM Sc) (TM.writeOutputBitTM (Fin.last (jj + 1)))).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) resT)
      (fun inp work out => inp = inp₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape))
          (resT.write (Γ.ofBool (Sc.emit (Sc.run (TM.scanCol cells) len)))) ∧
        out = out₀.write (Γ.ofBool (Sc.emit (Sc.run (TM.scanCol cells) len))))
      (2 * len + 3 + 1 + 1) := by
  classical
  set v : Bool := Sc.emit (Sc.run (TM.scanCol cells) len) with hv
  set W₁ : Fin (jj + 2) → Tape :=
    Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) (resT.write (Γ.ofBool v)) with hW₁
  have hW₁cast : ∀ i : Fin (jj + 1), W₁ i.castSucc = (⟨1, cells i⟩ : Tape) := by
    intro i
    rw [hW₁, Fin.snoc_castSucc]
  have hW₁last : W₁ (Fin.last (jj + 1)) = resT.write (Γ.ofBool v) := by rw [hW₁, Fin.snoc_last]
  have hresW : (resT.write (Γ.ofBool v)).StartInvariant := by
    have := hresSI.write (Γw.ofBool v)
    rwa [Γw.ofBool_toΓ] at this
  have hparked : ∀ i, TM.Parked (W₁ i) := by
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [hW₁last]
      exact ⟨by rw [Tape.write_head, hresH], fun q hq => hresW.2 q hq⟩
    · intro q
      rw [hW₁cast q]
      exact ⟨le_rfl, fun p hp => ht.ne_start q p hp⟩
  have hread : (W₁ (Fin.last (jj + 1))).read = Γ.ofBool v := by
    rw [hW₁last, Tape.read, Tape.write_head, hresH, Tape.write, ite_eq_right (by rw [hresH]; omega),
      hresH]
    show Function.update resT.cells 1 (Γ.ofBool v) 1 = _
    rw [Function.update_self]
  have hpub := TM.writeOutputBitTM_hoareTime_frame (Fin.last (jj + 1)) inp₀ W₁ out₀
    hinpP hparked houtP
  have hpub' : (TM.writeOutputBitTM (Fin.last (jj + 1))).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧ work = W₁)
      (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀.write (Γ.ofBool v)) 1 := by
    refine hpub.consequence (fun _ _ _ h => ⟨h.1, h.2.2, h.2.1⟩) (fun _ _ _ h => ?_) le_rfl
    refine ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2, hread]
    cases v <;> rfl
  refine TM.seqTM_hoareTime _ _
    (TM.twoPassTM_hoareTime Sc cells len inp₀ out₀ resT hok ht)
    ?_ hpub'
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨TM.transitionInput_eq_self hinpP.read_ne_start,
    TM.transitionTape_eq_self houtP.read_ne_start, ?_⟩
  funext i
  exact TM.transitionTape_eq_self (hparked i).read_ne_start

/-! ## The walk, as a machine

A walk step guesses *every* register — that uniformity is what makes the guess stage's output
match the scan's precondition — so the register holding the old code is overwritten each
iteration, and nothing would pin it to the previous iteration's new code. Rather than copy a
register, the loop's body runs **two** steps with the roles swapped: the first carries the code
from `jold` to `jnew`, the second from `jnew` back to `jold`. After an iteration the code is where
it started.

Walks of even length lose nothing, because a step may leave the code alone: a walk of any shorter
length is one of these padded with stays.

The loop below is built on `TM.loopTM`, whose test channel is the *output* tape. That is fine for
reasoning about the walk in isolation, but the machine `NL_subset_coNL_of_counting` asks for must
be a transducer, and `TM.loopTM` rewinds the output tape. The final assembly therefore drives the
same body with `TM.binaryForTM`, whose counter and limit live on binary work tapes and which
`IsTransducer.binaryForTM` shows to be output-safe. -/

/-- The body of the walk: two steps, with the code's registers — and the counter's — swapping
roles. Only the second step advances the counter, so it names the loop's iteration. -/
noncomputable def walkPairTM {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cnt cnt' : Fin (jj + 1)) (wc : ℕ) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg guessReg' : ℕ → Fin (jj + 2 + r + 1))
    (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) : TM (jj + 2 + r + 1) :=
  TM.seqTM
    (walkStepTM r tm nn S par mv dr res cnt cnt' wc false dc jold jnew guessReg w t targets
      accIdx)
    (walkStepTM r tm nn S par mv dr res cnt' cnt wc false dc jnew jold guessReg' w t targets
      accIdx)

/-- Its advancing states. -/
noncomputable def walkPairAdv {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cnt cnt' : Fin (jj + 1)) (wc : ℕ) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg guessReg' : ℕ → Fin (jj + 2 + r + 1))
    (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1)) :
    (walkPairTM r tm nn S par mv dr res cnt cnt' wc dc jold jnew guessReg guessReg' w t
        targets accIdx).Q →
      Bool :=
  TM.seqAdv
    (walkStepAdv r tm nn S par mv dr res cnt cnt' wc false dc jold jnew guessReg w t targets
      accIdx)
    (walkStepAdv r tm nn S par mv dr res cnt' cnt wc false dc jnew jold guessReg' w t targets
      accIdx)

/-- **The paired step respects the guess protocol.** -/
theorem guessProtocol_walkPairTM {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cnt cnt' : Fin (jj + 1)) (wc : ℕ) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg guessReg' : ℕ → Fin (jj + 2 + r + 1))
    (w : ℕ → ℕ) (t : ℕ)
    (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1))
    (haccLast : accIdx ≠ Fin.last (jj + 2 + r)) :
    TM.GuessProtocol
      (walkPairTM r tm nn S par mv dr res cnt cnt' wc dc jold jnew guessReg guessReg' w t
        targets accIdx)
      (walkPairAdv r tm nn S par mv dr res cnt cnt' wc dc jold jnew guessReg guessReg' w t
        targets accIdx) :=
  TM.guessProtocol_seqTM
    (guessProtocol_walkStepTM r tm nn S par mv dr res cnt cnt' wc false dc jold jnew guessReg
      w t targets accIdx haccLast)
    (guessProtocol_walkStepTM r tm nn S par mv dr res cnt' cnt wc false dc jnew jold guessReg'
      w t targets accIdx haccLast)

/-- **The walk as a machine**: paired steps, counted by the loop driver's own binary counter.
`TM.binaryForTM` is output-safe, which `TM.loopTM` — whose test channel is the output tape — is
not, and the whole machine has to be a transducer. -/
noncomputable def walkLoopTM {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cnt cnt' : Fin (jj + 1)) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg guessReg' : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ)
    (t wc : ℕ) (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1))
    (counterIdx limitIdx : Fin (jj + 2 + r + 1)) : TM (jj + 2 + r + 1) :=
  TM.binaryForTM
    (walkPairTM r tm nn S par mv dr res cnt cnt' wc dc jold jnew guessReg guessReg' w t
        targets accIdx)
    counterIdx limitIdx

/-- **The walk respects the guess protocol.** Only the body's guess stage advances the guess
head; the loop driver rewrites every tape it does not own and holds its head still. -/
theorem guessProtocol_walkLoopTM {kk jj : ℕ} (r : ℕ) (tm : NTM kk) (nn S : ℕ)
    (par mv dr res cnt cnt' : Fin (jj + 1)) (dc : DirCodec)
    (jold jnew : ℕ → Fin (jj + 1)) (guessReg guessReg' : ℕ → Fin (jj + 2 + r + 1)) (w : ℕ → ℕ)
    (t wc : ℕ) (targets : List (Fin (jj + 2 + r))) (accIdx : Fin (jj + 2 + r + 1))
    (counterIdx limitIdx : Fin (jj + 2 + r + 1))
    (haccLast : accIdx ≠ Fin.last (jj + 2 + r))
    (hcounter : counterIdx ≠ Fin.last (jj + 2 + r))
    (hlimit : limitIdx ≠ Fin.last (jj + 2 + r)) :
    TM.GuessProtocol
      (walkLoopTM r tm nn S par mv dr res cnt cnt' dc jold jnew guessReg guessReg' w t wc targets
        accIdx counterIdx limitIdx)
      (TM.binaryForAdv
        (walkPairAdv r tm nn S par mv dr res cnt cnt' wc dc jold jnew guessReg guessReg' w t
        targets accIdx)
        counterIdx limitIdx) :=
  TM.guessProtocol_binaryForTM
    (guessProtocol_walkPairTM r tm nn S par mv dr res cnt cnt' wc dc jold jnew guessReg guessReg'
      w t targets accIdx haccLast) counterIdx limitIdx hcounter hlimit

/-- **A walk taken two steps at a time reaches everything a walk of any shorter length does.**
The machine's loop body is a pair of steps, so its walks have even length; padding with steps that
stay put covers the rest. -/
theorem mem_reachCodes_of_pairWalk {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a₀ : Code tm.Q kk x.length S) (N i : ℕ) (hi : i ≤ 2 * N)
    (f : ℕ → Code tm.Q kk x.length S) (h0 : f 0 = a₀)
    (hstep : ∀ j < i, f (j + 1) = f j ∨ f (j + 1) ∈ NTM.codeSucc tm x S (f j)) :
    f i ∈ NTM.reachCodes tm x S a₀ (2 * N) :=
  NTM.reachCodes_mono a₀ hi (mem_reachCodes_of_walk tm x S a₀ i f h0 hstep)

/-! ## The input head follows the simulated one

`TM.inMoveTM` moves the machine's own input head by the direction the walk step's check pinned.
That direction is the one the simulated transition takes, and a tape's head moves exactly as
`Complexity.movedIdx` says — including at the left marker, where both a leftward move and
`movedIdx` stay put. -/

/-- **A tape's head moves as `Complexity.movedIdx` says.** -/
theorem move_head_eq_movedIdx (t : Tape) (d : Dir3) : (t.move d).head = movedIdx d t.head := by
  cases d <;> rfl

/-- **The input head lands where the code says.** -/
theorem move_head_of_dir (t : Tape) (C : DirCodec) (d : Dir3) (m g : Γ)
    (hm : m = C.encMove d) (hg : g = C.enc d) :
    (t.move (C.dec m g)).head = movedIdx d t.head := by
  rw [hm, hg, C.dec_enc, move_head_eq_movedIdx]

/-- **A walk step's scan accepts a step that stays put.** -/
theorem walkStepScanner_accepts_stay {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ)
    (advance : Bool) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1))
    (a : Code tm.Q kk x.length S) (u v : ℕ)
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S a p))
    (hmv : cols 1 mv = dc.encMove Dir3.stay) (hdr : cols 1 dr = dc.enc Dir3.stay)
    (hwc : wc ≤ walkScanLen tm x.length S) (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hcntOld : HoldsBits cols 0 cntOld (bitsOfLenLE wc u))
    (hcntNew : HoldsBits cols 0 cntNew (bitsOfLenLE wc v))
    (hmove : if advance then v = u + 1 else u = v) :
    (walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').emit
      ((walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').run cols
        (walkScanLen tm x.length S)) = true :=
  walkStepScanner_accepts tm x S cols par mv dr res cntOld cntNew wc advance dc j j'
    hwc u v hu hv hcntOld hcntNew hmove
    (walkCodeScanner_accepts_stay tm x S cols par mv dr res dc j j' a ha hb hmv hdr)

/-- **A walk step's scan accepts a genuine advancing step.** Everything the checks need is
supplied: the registers' contents, the direction cells, the counter's move, and the input check's
verdict. -/
theorem walkStepScanner_accepts_succ {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res cntOld cntNew : Fin (jj + 1)) (wc : ℕ)
    (advance : Bool) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1))
    (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (u v : ℕ)
    (hpar : HoldsBits cols 0 par ((succParamsCodec tm.Q kk).enc P))
    (ha : ∀ p, p < kk + 3 → HoldsBits cols 0 (j p) (codeBlockScan tm x S a p))
    (hb : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (codeBlockScan tm x S b p))
    (hq : a.1 = P.q) (hstate : b.1 = succState tm P)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym)
    (hhead : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val)
    (hwork : ∀ i, (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val ∧
      ∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
        else (a.2.2.1 i).2 p)
    (hout : b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ∧
      ∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
        then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p)
    (hleft : (succTrans tm P).2.2.2.1 = Dir3.left → 0 < a.2.1.val)
    (hmv : cols 1 mv = dc.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val))
    (hdr : cols 1 dr = dc.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val))
    (hin : P.inSym = inSymOf tm x S a)
    (hres : a.2.1.val ≠ 0 → cols 1 res = Γ.one)
    (hwc : wc ≤ walkScanLen tm x.length S) (hu : u < 2 ^ wc) (hv : v < 2 ^ wc)
    (hcntOld : HoldsBits cols 0 cntOld (bitsOfLenLE wc u))
    (hcntNew : HoldsBits cols 0 cntNew (bitsOfLenLE wc v))
    (hmove : if advance then v = u + 1 else u = v) :
    (walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').emit
      ((walkStepScanner tm x.length S par mv dr res cntOld cntNew wc advance dc j j').run cols
        (walkScanLen tm x.length S)) = true := by
  refine walkStepScanner_accepts tm x S cols par mv dr res cntOld cntNew wc advance dc j j'
    hwc u v hu hv hcntOld hcntNew hmove ?_
  refine walkCodeScanner_accepts_succ tm x S cols par mv dr res dc j j' a b P hpar ha hb hq
    hstate hwsym hosym hhead hwork hout hleft ?_ ?_
  · exact dirCheckScanner_accepts tm x S cols par mv dr (codeRegsOf j).hd (codeRegsOf j').hd dc
      P a b hpar (holdsCodeScan_of_blocks tm x S cols j a ha).2.1
      (holdsCodeScan_of_blocks tm x S cols j' b hb).2.1 hhead hmv hdr
  · exact inSymScanner_accepts tm x S cols par (codeRegsOf j).hd res P a hpar
      (holdsCodeScan_of_blocks tm x S cols j a ha).2.1 hin hres

/-! ## The ruler register

A two-pass scan turns around when it meets a blank on register `0`, so that register fixes the
scan's length: it must carry non-blank symbols for exactly as many cells as the scan is to read,
and a blank immediately after. The guess writes it like any other register — a block of ones as
wide as `Complexity.walkScanLen` — which is why register `0` of the layout is a ruler and the
code's registers start at one. -/

/-- The ruler register's contents: ones for the length of the scan. -/
def rulerBlock (len : ℕ) : List Bool := List.replicate len true

@[simp] theorem rulerBlock_length (len : ℕ) : (rulerBlock len).length = len :=
  List.length_replicate

theorem rulerBlock_getElem (len q : ℕ) (hq : q < len) : (rulerBlock len)[q]'(by simpa using hq)
    = true := by
  show (List.replicate len true)[q]'(by simpa using hq) = true
  simp

/-- **A register of ones as long as the scan makes the scan well formed.** The blank just past the
ruler is what stops the rightward pass; it is not written by the guess, so it is the one thing a
caller must know about the tape rather than about the guess. -/
theorem scanTape_of_ruler {jj : ℕ} (cells : Fin (jj + 1) → ℕ → Γ) (len : ℕ)
    (hstart : ∀ i, cells i 0 = Γ.start) (hne : ∀ i q, 1 ≤ q → cells i q ≠ Γ.start)
    (hruler : ∀ q, 1 ≤ q → q ≤ len → cells 0 q = Γ.one)
    (hblank : cells 0 (len + 1) = Γ.blank) : TM.ScanTape cells len where
  start := hstart
  ne_start := hne
  ne_blank q h1 h2 := by
    rw [hruler q h1 h2]
    exact fun hc => Γ.noConfusion hc
  blank := hblank

/-- **A register holding the ruler block is a ruler.** -/
theorem ruler_of_holds {jj : ℕ} (cols : ℕ → Fin (jj + 1) → Γ) (r : Fin (jj + 1)) (len : ℕ)
    (h : HoldsBits cols 0 r (rulerBlock len)) : ∀ q, 1 ≤ q → q ≤ len → cols q r = Γ.one := by
  intro q h1 h2
  have hq : q - 1 < len := by omega
  have hc := h (q - 1) (by simpa using hq)
  rw [Nat.zero_add, show q - 1 + 1 = q by omega, rulerBlock_getElem len (q - 1) hq] at hc
  exact hc

/-! ## Moving a head that is pinned away from the marker

The machine's input head sits at `max h 1`, so it must move by the direction that takes
`max h 1` to `max h' 1` — which is the simulated direction only when both `h` and `h'` are off the
marker, and "stay" otherwise. Both conditions are fields of the two codes, so both are decided by
the same scan. -/

/-- **The adjusted direction moves a pinned head to where it should be.** -/
theorem move_adjusted (t : Tape) (d : Dir3) (h : ℕ) (ht : t.head = max h 1) :
    (t.move (adjustedDir d h)).head = max (movedIdx d h) 1 := by
  rw [move_head_eq_movedIdx, ht, adjustedDir]
  by_cases h0 : h = 0
  · rw [ite_eq_left h0, h0]
    cases d <;> simp [movedIdx]
  · rw [ite_eq_right h0]
    by_cases h1 : movedIdx d h = 0
    · rw [ite_eq_left h1, h1]
      cases d <;> simp only [movedIdx] at h1 ⊢ <;> omega
    · rw [ite_eq_right h1]
      cases d <;> simp only [movedIdx] at h1 ⊢ <;> omega

/-- **One walk step carries the input head to where the next code says.** Whichever branch the
step took, the direction register holds `Complexity.adjustedDir` of the step's direction, and a
head parked at `max h 1` lands parked at `max h' 1`. -/
theorem move_of_walkStep (C : DirCodec) (t : Tape) (h h' : ℕ) (d : Dir3) (m g : Γ)
    (ht : t.head = max h 1) (hm : m = C.encMove (adjustedDir d h))
    (hg : g = C.enc (adjustedDir d h)) (hh' : h' = movedIdx d h) :
    t.move (C.dec m g) = ⟨max h' 1, t.cells⟩ := by
  refine Tape.ext ?_ (Tape.move_cells t _)
  rw [hm, hg, C.dec_enc, hh']
  exact move_adjusted t d h ht

/-- **A step that stays put leaves the input head where it was.** -/
theorem move_of_walkStay (C : DirCodec) (t : Tape) (h : ℕ) (m g : Γ)
    (ht : t.head = max h 1) (hm : m = C.encMove Dir3.stay) (hg : g = C.enc Dir3.stay) :
    t.move (C.dec m g) = ⟨max h 1, t.cells⟩ := by
  have hstay : adjustedDir Dir3.stay h = Dir3.stay := by
    rw [adjustedDir]
    split_ifs <;> rfl
  refine move_of_walkStep C t h h Dir3.stay m g ht ?_ ?_ rfl
  · rw [hm, hstay]
  · rw [hg, hstay]

/-- **What one walk step establishes about the tapes.** Either branch of the step leaves the
input head parked where the new code says, and the code itself is one step of the walk. -/
theorem walkStep_transports (C : DirCodec) {kk : ℕ} {tm : NTM kk} {x : List Bool} {S : ℕ}
    (a b : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (t : Tape) (m g : Γ)
    (ht : t.head = max a.2.1.val 1)
    (hstep : (b = a ∧ m = C.encMove Dir3.stay ∧ g = C.enc Dir3.stay) ∨
      (b ∈ NTM.codeSucc tm x S a ∧
        b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
        m = C.encMove (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val) ∧
        g = C.enc (adjustedDir (succTrans tm P).2.2.2.1 a.2.1.val))) :
    (b = a ∨ b ∈ NTM.codeSucc tm x S a) ∧ t.move (C.dec m g) = ⟨max b.2.1.val 1, t.cells⟩ := by
  rcases hstep with ⟨hba, hm, hg⟩ | ⟨hsucc, hmove, hm, hg⟩
  · refine ⟨Or.inl hba, ?_⟩
    rw [hba]
    exact move_of_walkStay C t a.2.1.val m g ht hm hg
  · exact ⟨Or.inr hsucc, move_of_walkStep C t a.2.1.val b.2.1.val
      (succTrans tm P).2.2.2.1 m g ht hm hg hmove⟩

/-! ## The fields of a genuine successor

The completeness direction starts from a walk that really happens and must produce the guesses
that make every check pass. `Complexity.paramsOf` names the transition a code takes on a given
choice, and its fields are what the checks compare against. -/

/-- **A genuine successor's fields are what the checks want.** The clamps are the space
discipline: the step must stay inside the window, which is where the codes live. -/
theorem succ_fields_of_eq {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a b : Code tm.Q kk x.length S) (β : Bool) (hb : b = succCode tm x S β a)
    (hin : movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hw : ∀ i, movedIdx (succDir tm (paramsOf tm x S a β) i) (a.2.2.1 i).1.val ≤ S)
    (ho : movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.2.2 a.2.2.2.1.val ≤ S + 1) :
    a.1 = (paramsOf tm x S a β).q ∧
      b.1 = succState tm (paramsOf tm x S a β) ∧
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = (paramsOf tm x S a β).wSym i) ∧
      a.2.2.2.2 a.2.2.2.1 = (paramsOf tm x S a β).oSym ∧
      b.2.1.val = movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.1 a.2.1.val ∧
      (∀ i, (b.2.2.1 i).1.val = movedIdx (succDir tm (paramsOf tm x S a β) i)
          (a.2.2.1 i).1.val ∧
        ∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val
          then succWrite tm (paramsOf tm x S a β) i else (a.2.2.1 i).2 p) ∧
      (b.2.2.2.1.val = movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.2.2 a.2.2.2.1.val ∧
        ∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
          then (((succTrans tm (paramsOf tm x S a β)).2.2.1 : Γw) : Γ) else a.2.2.2.2 p) := by
  obtain ⟨hstate, hhead, hwork, hout⟩ :=
    (eq_succCode_iff tm x S a b β hin hw ho).mp hb
  exact ⟨rfl, hstate, fun i => rfl, rfl, hhead, hwork, hout⟩

/-- **The input symbol a genuine successor's parameters name.** -/
theorem succ_inSym {kk : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (a : Code tm.Q kk x.length S) (β : Bool) :
    (paramsOf tm x S a β).inSym = inSymOf tm x S a := rfl

/-! ## The walk's register layout

Every register the walk uses is guessed, so the layout has to name them all and say how wide each
block is. The roles are: the ruler that fixes the scan's length, the parameter block, the
direction cell, the input check's verdict, the accumulator the loop's test reads, the two counter
registers, the target the counter is compared against, and the two code register tuples. -/

/-- The role a guessed block plays in the walk. -/
inductive BlockRole (kk : ℕ) where
  /-- The ruler that fixes the scan's length. -/
  | ruler
  /-- The guessed transition's parameters. -/
  | par
  /-- Whether the input head is to move at all. -/
  | mv
  /-- Which way it is to move. -/
  | dr
  /-- The input check's verdict. -/
  | res
  /-- The accumulator the loop's test reads. -/
  | acc
  /-- The counter. -/
  | cnt
  /-- The counter's partner. -/
  | cnt'
  /-- The target the counter is compared against. -/
  | target
  /-- Block `p` of the first code tuple. -/
  | codeA (p : ℕ)
  /-- Block `p` of the second. -/
  | codeB (p : ℕ)
  deriving DecidableEq

/-- Which register plays which role in the walk, and that the roles are distinct. -/
structure WalkLayout (kk jj : ℕ) where
  /-- What each block is for. -/
  role : ℕ → BlockRole kk
  /-- The block index of each register: block `p` is written to register `reg p`. -/
  reg : ℕ → Fin (jj + 1)
  /-- The number of blocks, one per register. -/
  blocks : ℕ
  /-- Distinct blocks go to distinct registers. -/
  reg_inj : ∀ p q, p < blocks → q < blocks → reg p = reg q → p = q
  /-- The ruler's block. -/
  rulerIdx : ℕ
  /-- The parameter block's. -/
  parIdx : ℕ
  /-- The move cell's. -/
  mvIdx : ℕ
  /-- The direction cell's. -/
  drIdx : ℕ
  /-- The input check's verdict register. -/
  resIdx : ℕ
  /-- The accumulator the loop's test reads. -/
  accIdx : ℕ
  /-- The counter, and the register it swaps with. -/
  cntIdx : ℕ
  /-- The other counter register. -/
  cnt'Idx : ℕ
  /-- The target the counter is compared against. -/
  targetIdx : ℕ
  /-- The first code tuple's blocks, `kk + 3` of them. -/
  codeAIdx : ℕ → ℕ
  /-- The second code tuple's blocks. -/
  codeBIdx : ℕ → ℕ
  /-- How many blocks come before the two code tuples: the scan's scratch. A step guesses the
  scratch and one code tuple, and leaves the other tuple where the previous step put it — which is
  what chains the walk. -/
  scratch : ℕ
  /-- The old code's blocks follow the scratch. -/
  codeA_eq : ∀ p, p < kk + 3 → codeAIdx p = scratch + p
  /-- The new code's follow those. -/
  codeB_eq : ∀ p, p < kk + 3 → codeBIdx p = scratch + (kk + 3) + p
  /-- And nothing follows them. -/
  blocks_eq : blocks = scratch + (kk + 3) + (kk + 3)
  /-- The ruler is register zero, where a scan looks for its length. -/
  ruler_zero : reg rulerIdx = 0
  /-- The ruler is scratch. -/
  ruler_scratch : rulerIdx < scratch
  /-- So is the parameter block. -/
  par_scratch : parIdx < scratch
  /-- So is the move cell. -/
  mv_scratch : mvIdx < scratch
  /-- So is the direction cell. -/
  dr_scratch : drIdx < scratch
  /-- So is the verdict register. -/
  res_scratch : resIdx < scratch
  /-- So is the accumulator. -/
  acc_scratch : accIdx < scratch
  /-- So is the counter. -/
  cnt_scratch : cntIdx < scratch
  /-- So is its partner. -/
  cnt'_scratch : cnt'Idx < scratch
  /-- So is the target. -/
  target_scratch : targetIdx < scratch
  /-- The roles agree with the indices. -/
  role_ruler : role rulerIdx = BlockRole.ruler
  /-- The parameter block's role. -/
  role_par : role parIdx = BlockRole.par
  /-- The move cell's. -/
  role_mv : role mvIdx = BlockRole.mv
  /-- The direction cell's. -/
  role_dr : role drIdx = BlockRole.dr
  /-- The verdict register's. -/
  role_res : role resIdx = BlockRole.res
  /-- The accumulator's. -/
  role_acc : role accIdx = BlockRole.acc
  /-- The counter's. -/
  role_cnt : role cntIdx = BlockRole.cnt
  /-- Its partner's. -/
  role_cnt' : role cnt'Idx = BlockRole.cnt'
  /-- The target's. -/
  role_target : role targetIdx = BlockRole.target
  /-- Each code block's. -/
  role_codeA : ∀ p, p < kk + 3 → role (codeAIdx p) = BlockRole.codeA p
  /-- And the other tuple's. -/
  role_codeB : ∀ p, p < kk + 3 → role (codeBIdx p) = BlockRole.codeB p

namespace WalkLayout

variable {kk jj : ℕ} (L : WalkLayout kk jj)

/-- The ruler is a block. -/
theorem ruler_lt : L.rulerIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.ruler_scratch; omega

/-- The parameter block is a block. -/
theorem par_lt : L.parIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.par_scratch; omega

/-- The move cell is a block. -/
theorem mv_lt : L.mvIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.mv_scratch; omega

/-- The direction cell is a block. -/
theorem dr_lt : L.drIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.dr_scratch; omega

/-- The verdict register is a block. -/
theorem res_lt : L.resIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.res_scratch; omega

/-- The accumulator is a block. -/
theorem acc_lt : L.accIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.acc_scratch; omega

/-- The counter is a block. -/
theorem cnt_lt : L.cntIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.cnt_scratch; omega

/-- So is its partner. -/
theorem cnt'_lt : L.cnt'Idx < L.blocks := by
  rw [L.blocks_eq]; have := L.cnt'_scratch; omega

/-- So is the target. -/
theorem target_lt : L.targetIdx < L.blocks := by
  rw [L.blocks_eq]; have := L.target_scratch; omega

/-- So is each of the old code's blocks. -/
theorem codeA_lt : ∀ p, p < kk + 3 → L.codeAIdx p < L.blocks := by
  intro p hp
  rw [L.codeA_eq p hp, L.blocks_eq]
  omega

/-- And each of the new code's. -/
theorem codeB_lt : ∀ p, p < kk + 3 → L.codeBIdx p < L.blocks := by
  intro p hp
  rw [L.codeB_eq p hp, L.blocks_eq]
  omega

/-- **The blocks one step of the pair guesses**: the scratch, and one code tuple. The first step
of a pair writes the new code's blocks and leaves the old code's registers alone; the second does
the reverse. That is what chains a walk — the check of each step compares its guess against what
the previous step really left behind — and what returns every code to its own registers after a
pair. -/
def stepIdx (second : Bool) (p : ℕ) : ℕ :=
  if p < L.scratch then p else if second then p else p + (kk + 3)

/-- How many blocks a step guesses. -/
def stepBlocks : ℕ := L.scratch + (kk + 3)

/-- A step's blocks are blocks. -/
theorem stepIdx_lt (second : Bool) (p : ℕ) (hp : p < L.stepBlocks) :
    L.stepIdx second p < L.blocks := by
  rw [stepIdx, blocks_eq]
  rw [stepBlocks] at hp
  split <;> [omega; (split <;> omega)]

/-- A step guesses each of its blocks once. -/
theorem stepIdx_inj (second : Bool) : ∀ p q, p < L.stepBlocks → q < L.stepBlocks →
    L.stepIdx second p = L.stepIdx second q → p = q := by
  intro p q hp hq h
  rw [stepIdx, stepIdx] at h
  split at h <;> split at h <;> first | omega | (split at h <;> omega)

/-- The second step of a pair guesses the old code's blocks. -/
theorem stepIdx_codeA (p : ℕ) (hp : p < kk + 3) :
    L.stepIdx true (L.scratch + p) = L.codeAIdx p := by
  rw [stepIdx, ite_eq_right (by omega), ite_eq_left rfl, L.codeA_eq p hp]

/-- The first step guesses the new code's. -/
theorem stepIdx_codeB (p : ℕ) (hp : p < kk + 3) :
    L.stepIdx false (L.scratch + p) = L.codeBIdx p := by
  rw [stepIdx, ite_eq_right (by omega), ite_eq_right (by simp), L.codeB_eq p hp]
  omega

/-- The first step guesses none of the old code's blocks. -/
theorem stepIdx_ne_codeA (p q : ℕ) (_hp : p < L.stepBlocks) (hq : q < kk + 3) :
    L.stepIdx false p ≠ L.codeAIdx q := by
  rw [stepIdx, L.codeA_eq q hq]
  split <;> [omega; (rw [ite_eq_right (by simp)]; omega)]

/-- The second guesses none of the new code's. -/
theorem stepIdx_ne_codeB (p q : ℕ) (hp : p < L.stepBlocks) (hq : q < kk + 3) :
    L.stepIdx true p ≠ L.codeBIdx q := by
  rw [stepIdx, L.codeB_eq q hq]
  rw [stepBlocks] at hp
  split <;> [omega; (rw [ite_eq_left rfl]; omega)]

/-- The parameter register. -/
def par : Fin (jj + 1) := L.reg L.parIdx

/-- The move register. -/
def mv : Fin (jj + 1) := L.reg L.mvIdx

/-- The direction register. -/
def dr : Fin (jj + 1) := L.reg L.drIdx

/-- The input check's verdict register. -/
def res : Fin (jj + 1) := L.reg L.resIdx

/-- The accumulator. -/
def acc : Fin (jj + 1) := L.reg L.accIdx

/-- The counter. -/
def cnt : Fin (jj + 1) := L.reg L.cntIdx

/-- The counter's partner. -/
def cnt' : Fin (jj + 1) := L.reg L.cnt'Idx

/-- The target. -/
def target : Fin (jj + 1) := L.reg L.targetIdx

/-- The first code tuple's registers. -/
def codeA : ℕ → Fin (jj + 1) := fun p => L.reg (L.codeAIdx p)

/-- The second code tuple's registers. -/
def codeB : ℕ → Fin (jj + 1) := fun p => L.reg (L.codeBIdx p)

/-- **Blocks with different roles live in different registers.** -/
theorem reg_ne {p q : ℕ} (hp : p < L.blocks) (hq : q < L.blocks) (h : L.role p ≠ L.role q) :
    L.reg p ≠ L.reg q := by
  intro hc
  exact h (by rw [L.reg_inj p q hp hq hc])

/-- The verdict register is not a code register. -/
theorem codeA_ne_res {r : ℕ} (hr : r < kk + 3) : L.codeA r ≠ L.res :=
  L.reg_ne (L.codeA_lt r hr) L.res_lt (by
    rw [L.role_codeA r hr, L.role_res]
    exact fun hc => by simp at hc)

/-- Nor is the other tuple's. -/
theorem codeB_ne_res {r : ℕ} (hr : r < kk + 3) : L.codeB r ≠ L.res :=
  L.reg_ne (L.codeB_lt r hr) L.res_lt (by
    rw [L.role_codeB r hr, L.role_res]
    exact fun hc => by simp at hc)

/-- Nor the parameter block. -/
theorem par_ne_res : L.par ≠ L.res :=
  L.reg_ne L.par_lt L.res_lt (by
    rw [L.role_par, L.role_res]
    exact fun hc => by simp at hc)

/-- Nor the move cell. -/
theorem mv_ne_res : L.mv ≠ L.res :=
  L.reg_ne L.mv_lt L.res_lt (by
    rw [L.role_mv, L.role_res]
    exact fun hc => by simp at hc)

/-- Nor the direction cell. -/
theorem dr_ne_res : L.dr ≠ L.res :=
  L.reg_ne L.dr_lt L.res_lt (by
    rw [L.role_dr, L.role_res]
    exact fun hc => by simp at hc)

/-- Nor either counter. -/
theorem cnt_ne_res : L.cnt ≠ L.res :=
  L.reg_ne L.cnt_lt L.res_lt (by
    rw [L.role_cnt, L.role_res]
    exact fun hc => by simp at hc)

/-- Nor the counter's partner. -/
theorem cnt'_ne_res : L.cnt' ≠ L.res :=
  L.reg_ne L.cnt'_lt L.res_lt (by
    rw [L.role_cnt', L.role_res]
    exact fun hc => by simp at hc)

end WalkLayout

/-- The widths the layout's blocks are guessed at. A block of width `n` writes `n + 1` bits, so a
one-cell register — the direction, a verdict — has width zero. -/
structure WalkWidths (kk jj : ℕ) (tm : NTM kk) (nn S wc : ℕ) extends WalkLayout kk jj where
  /-- How wide each block is guessed. -/
  width : ℕ → ℕ
  /-- The ruler spans the whole scan. -/
  width_ruler : width toWalkLayout.rulerIdx = walkScanLen tm nn S - 1
  /-- The parameter block spans a transition's parameters. -/
  width_par : width toWalkLayout.parIdx = (succParamsCodec tm.Q kk).width - 1
  /-- Whether to move is one cell. -/
  width_mv : width toWalkLayout.mvIdx = 0
  /-- A direction is one cell. -/
  width_dr : width toWalkLayout.drIdx = 0
  /-- So is a verdict. -/
  width_res : width toWalkLayout.resIdx = 0
  /-- And so is the accumulator. -/
  width_acc : width toWalkLayout.accIdx = 0
  /-- The counters and the target span the counter's width. -/
  width_cnt : width toWalkLayout.cntIdx = wc - 1
  /-- The counter's partner is the same width. -/
  width_cnt' : width toWalkLayout.cnt'Idx = wc - 1
  /-- And so is the target. -/
  width_target : width toWalkLayout.targetIdx = wc - 1
  /-- A code's blocks are as wide as the walk's layout says. -/
  width_codeA : ∀ p, p < kk + 3 → width (toWalkLayout.codeAIdx p) = codeWidthScan tm nn S p
  /-- And the other tuple's the same. -/
  width_codeB : ∀ p, p < kk + 3 → width (toWalkLayout.codeBIdx p) = codeWidthScan tm nn S p

/-- **How wide that block is guessed.** Both steps of a pair guess the same widths — a code's two
tuples are laid out alike — so one width function serves both, and the guess stream advances by
the same amount at every stage. -/
def stepWidth {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ} (L : WalkWidths kk jj tm nn S wc)
    (p : ℕ) : ℕ :=
  L.width (L.toWalkLayout.stepIdx true p)

/-- A scratch block is guessed at its own width. -/
theorem stepWidth_scratch {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (p : ℕ) (hp : p < L.toWalkLayout.scratch) :
    stepWidth L p = L.width p := by
  rw [stepWidth, WalkLayout.stepIdx, ite_eq_left hp]

/-- A code block is guessed at the code's width. -/
theorem stepWidth_code {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (p : ℕ) (hp : p < kk + 3) :
    stepWidth L (L.toWalkLayout.scratch + p) = codeWidthScan tm nn S p := by
  rw [stepWidth, L.toWalkLayout.stepIdx_codeA p hp, L.width_codeA p hp]

/-- **The first step of a pair guesses its blocks at those same widths.** -/
theorem width_stepIdx_false {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (p : ℕ) (hp : p < L.toWalkLayout.stepBlocks) :
    L.width (L.toWalkLayout.stepIdx false p) = stepWidth L p := by
  by_cases hs : p < L.toWalkLayout.scratch
  · rw [stepWidth, WalkLayout.stepIdx, WalkLayout.stepIdx, ite_eq_left hs, ite_eq_left hs]
  · have hp' : p - L.toWalkLayout.scratch < kk + 3 := by
      rw [WalkLayout.stepBlocks] at hp
      omega
    have hpe : p = L.toWalkLayout.scratch + (p - L.toWalkLayout.scratch) := by omega
    rw [hpe, L.toWalkLayout.stepIdx_codeB _ hp', L.width_codeB _ hp',
      stepWidth_code L _ hp']

/-- **What one stage of the walk must guess**: the ruler, the transition's parameters, the two
direction cells, the counters and the target, and the two code tuples. Everything else is a
verdict register, whose guessed value is overwritten before it is read. -/
noncomputable def stageBits {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) : ℕ → ℕ → Bool :=
  fun p q =>
    match L.toWalkLayout.role p with
    | BlockRole.ruler => true
    | BlockRole.par => ((succParamsCodec tm.Q kk).enc P).getD q false
    | BlockRole.mv => decide (dc.encMove d = Γ.one)
    | BlockRole.dr => decide (dc.enc d = Γ.one)
    | BlockRole.res => false
    | BlockRole.acc => accBit
    | BlockRole.cnt => (bitsOfLenLE wc cOld).getD q false
    | BlockRole.cnt' => (bitsOfLenLE wc cNew).getD q false
    | BlockRole.target => (bitsOfLenLE wc tgt).getD q false
    | BlockRole.codeA r => (codeBlockScan tm x S aOld r).getD q false
    | BlockRole.codeB r => (codeBlockScan tm x S aNew r).getD q false

/-- **The code blocks a stage guesses are the code's own.** -/
theorem stageBits_codeA {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) (r : ℕ) (hr : r < kk + 3) (q : ℕ) :
    stageBits L x dc P d cOld cNew tgt accBit aOld aNew (L.toWalkLayout.codeAIdx r) q
      = (codeBlockScan tm x S aOld r).getD q false := by
  rw [stageBits]
  simp only [L.toWalkLayout.role_codeA r hr]

/-- **And the other tuple's are the successor's.** -/
theorem stageBits_codeB {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) (r : ℕ) (hr : r < kk + 3) (q : ℕ) :
    stageBits L x dc P d cOld cNew tgt accBit aOld aNew (L.toWalkLayout.codeBIdx r) q
      = (codeBlockScan tm x S aNew r).getD q false := by
  rw [stageBits]
  simp only [L.toWalkLayout.role_codeB r hr]

/-- **The parameter block a stage guesses is the transition's encoding.** -/
theorem stageBits_par {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) (q : ℕ) :
    stageBits L x dc P d cOld cNew tgt accBit aOld aNew L.toWalkLayout.parIdx q
      = ((succParamsCodec tm.Q kk).enc P).getD q false := by
  rw [stageBits]
  simp only [L.toWalkLayout.role_par]

/-- **The counter a stage guesses holds its value.** -/
theorem stageBits_cnt {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) (q : ℕ) :
    stageBits L x dc P d cOld cNew tgt accBit aOld aNew L.toWalkLayout.cntIdx q
      = (bitsOfLenLE wc cOld).getD q false := by
  rw [stageBits]
  simp only [L.toWalkLayout.role_cnt]

/-- **And its partner the next value.** -/
theorem stageBits_cnt' {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) (q : ℕ) :
    stageBits L x dc P d cOld cNew tgt accBit aOld aNew L.toWalkLayout.cnt'Idx q
      = (bitsOfLenLE wc cNew).getD q false := by
  rw [stageBits]
  simp only [L.toWalkLayout.role_cnt']

/-- **And the target its own.** -/
theorem stageBits_target {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (P : SuccParams tm.Q kk) (d : Dir3) (cOld cNew tgt : ℕ) (accBit : Bool)
    (aOld aNew : Code tm.Q kk x.length S) (q : ℕ) :
    stageBits L x dc P d cOld cNew tgt accBit aOld aNew L.toWalkLayout.targetIdx q
      = (bitsOfLenLE wc tgt).getD q false := by
  rw [stageBits]
  simp only [L.toWalkLayout.role_target]

/-- The certificate for a whole walk: what every stage guesses, given the codes it visits, the
transitions it takes, the directions those imply and the counter values. -/
noncomputable def walkCert {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) : ℕ → ℕ → ℕ → Bool :=
  fun s => stageBits L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s) (f (s + 1))

/-- **A stage's code blocks come off the certificate as that stage's codes.** -/
theorem walkCert_codeA {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (s r : ℕ) (hr : r < kk + 3) (q : ℕ) :
    walkCert L x dc Ps ds cOlds cNews tgt f s (L.toWalkLayout.codeAIdx r) q
      = (codeBlockScan tm x S (f s) r).getD q false :=
  stageBits_codeA L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s) (f (s + 1)) r hr q

/-- **And the other tuple's as the next code's.** -/
theorem walkCert_codeB {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (s r : ℕ) (hr : r < kk + 3) (q : ℕ) :
    walkCert L x dc Ps ds cOlds cNews tgt f s (L.toWalkLayout.codeBIdx r) q
      = (codeBlockScan tm x S (f (s + 1)) r).getD q false :=
  stageBits_codeB L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s) (f (s + 1)) r hr q

/-- Embed a register index into the walk machine's tape set: the registers, then the scan's
result tape, then the guess tape. -/
def walkReg {jj r : ℕ} (i : Fin (jj + 1)) : Fin (jj + 2 + r + 1) :=
  (Fin.castAdd r i.castSucc).castSucc

/-- How many guess bits an iteration of the walk consumes: one stage per step, two steps to an
iteration. -/
def walkGuessStride (w : ℕ → ℕ) (t : ℕ) : ℕ := 2 * TM.guessOffset w t

/-- A register of the walk is never the guess tape. -/
theorem walkReg_ne_last {jj r : ℕ} (i : Fin (jj + 1)) : walkReg i ≠ Fin.last (jj + 2 + r) := by
  intro hc
  have hv := congrArg Fin.val hc
  have h1 : (walkReg i : Fin (jj + 2 + r + 1)).val = i.val := rfl
  have h2 : (Fin.last (jj + 2 + r) : Fin (jj + 2 + r + 1)).val = jj + 2 + r := rfl
  have := i.isLt
  omega

/-- **Distinct registers are distinct tapes.** -/
theorem walkReg_inj {jj r : ℕ} {i i' : Fin (jj + 1)}
    (h : (walkReg (r := r) i : Fin (jj + 2 + r + 1)) = walkReg i') : i = i' := by
  have hv := congrArg Fin.val h
  have h1 : (walkReg (r := r) i : Fin (jj + 2 + r + 1)).val = i.val := rfl
  have h2 : (walkReg (r := r) i' : Fin (jj + 2 + r + 1)).val = i'.val := rfl
  exact Fin.ext (by omega)

/-- **The tape a step's `p`-th guessed block goes to.** -/
def stepReg {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ} (L : WalkWidths kk jj tm nn S wc)
    (second : Bool) (p : ℕ) : Fin (jj + 2 + r + 1) :=
  walkReg (L.toWalkLayout.reg (L.toWalkLayout.stepIdx second p))

/-- A block's own bits fit in the width it is guessed at. -/
theorem blockLen_le_codeWidthScan {kk : ℕ} (tm : NTM kk) (nn S r : ℕ) :
    blockLen tm nn S r ≤ codeWidthScan tm nn S r + 1 := by
  simp only [blockLen, codeWidthScan, codeWidth]
  split_ifs <;> omega

/-- **After a stage, each register holds the bits the certificate names for it.** -/
theorem holdsBits_block_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks b g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.blocks) (bits : List Bool)
    (hbits : ∀ q, (hq : q < bits.length) → b s p q = bits[q])
    (hlen : bits.length ≤ L.width p + 1) :
    HoldsBits (fun c i =>
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W i).cells c) 0 (walkReg (L.toWalkLayout.reg p)) bits := by
  have hbits' := holdsBits_of_guessBlocks (fun p => walkReg (L.toWalkLayout.reg p))
    (fun p => walkReg_ne_last _) L.width L.toWalkLayout.blocks W hinv hh
    (fun p q hp hq hpq => L.toWalkLayout.reg_inj p q hp hq (by
      have hbeta : (walkReg (L.toWalkLayout.reg p) : Fin (jj + 2 + r + 1)).val
        = (walkReg (L.toWalkLayout.reg q) : Fin (jj + 2 + r + 1)).val := congrArg Fin.val hpq
      exact Fin.ext (by
        have h1 : (walkReg (L.toWalkLayout.reg p) : Fin (jj + 2 + r + 1)).val
          = (L.toWalkLayout.reg p).val := rfl
        have h2 : (walkReg (L.toWalkLayout.reg q) : Fin (jj + 2 + r + 1)).val
          = (L.toWalkLayout.reg q).val := rfl
        omega)))
    hr1 (b s) (TM.blocks_of_stageBlocks hs s hgf)
  exact (hbits' p hp).of_isPrefix (isPrefix_ofFn _ hlen hbits)

/-- **What a step's guess leaves on each of its own blocks.** The stage version guesses every
block; a step guesses only its own, and this says nothing about the rest — which is what lets the
other code tuple survive the step untouched. -/
theorem holdsBits_block_of_step {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (second : Bool)
    (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks b g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.stepBlocks) (bits : List Bool)
    (hbits : ∀ q, (hq : q < bits.length) → b s p q = bits[q])
    (hlen : bits.length ≤ stepWidth L p + 1) :
    HoldsBits (fun c i =>
      (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
        L.toWalkLayout.stepBlocks W i).cells c) 0 (stepReg L second p) bits := by
  have hbits' := holdsBits_of_guessBlocks (stepReg L second)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (fun p q hp hq hpq => L.toWalkLayout.stepIdx_inj second p q hp hq
      (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt second p hp)
        (L.toWalkLayout.stepIdx_lt second q hq) (walkReg_inj hpq)))
    hr1 (b s) (TM.blocks_of_stageBlocks hs s hgf)
  exact (hbits' p hp).of_isPrefix (isPrefix_ofFn _ hlen hbits)

/-- **The old code's registers hold the code the certificate names.** -/
theorem holdsBits_codeA_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ r, r < kk + 3 → HoldsBits (fun c i =>
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W i).cells c) 0
      (walkReg (L.toWalkLayout.codeA r)) (codeBlockScan tm x S (f s) r) := by
  intro r hr
  refine holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf (L.toWalkLayout.codeAIdx r)
    (L.toWalkLayout.codeA_lt r hr) _ (fun q hq => ?_) ?_
  · rw [walkCert_codeA L x dc Ps ds cOlds cNews tgt f s r hr q,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  · rw [codeBlockScan_length, L.width_codeA r hr]
    exact blockLen_le_codeWidthScan tm x.length S r

/-- **The new code's registers hold the next code.** -/
theorem holdsBits_codeB_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ r, r < kk + 3 → HoldsBits (fun c i =>
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W i).cells c) 0
      (walkReg (L.toWalkLayout.codeB r)) (codeBlockScan tm x S (f (s + 1)) r) := by
  intro r hr
  refine holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf (L.toWalkLayout.codeBIdx r)
    (L.toWalkLayout.codeB_lt r hr) _ (fun q hq => ?_) ?_
  · rw [walkCert_codeB L x dc Ps ds cOlds cNews tgt f s r hr q,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  · rw [codeBlockScan_length, L.width_codeB r hr]
    exact blockLen_le_codeWidthScan tm x.length S r

/-- **The parameter register holds the transition the certificate names.** -/
theorem holdsBits_par_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    HoldsBits (fun c i =>
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W i).cells c) 0
      (walkReg L.toWalkLayout.par) ((succParamsCodec tm.Q kk).enc (Ps s)) := by
  refine holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.parIdx
    L.toWalkLayout.par_lt _ (fun q hq => ?_) ?_
  · rw [walkCert, stageBits_par L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s)
      (f (s + 1)) q, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  · rw [(succParamsCodec tm.Q kk).enc_length, L.width_par]
    omega

/-- **A counter register holds the value the certificate names.** -/
theorem holdsBits_cnt_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    HoldsBits (fun c i =>
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W i).cells c) 0
      (walkReg L.toWalkLayout.cnt) (bitsOfLenLE wc (cOlds s)) := by
  refine holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.cntIdx
    L.toWalkLayout.cnt_lt _ (fun q hq => ?_) ?_
  · rw [walkCert, stageBits_cnt L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s)
      (f (s + 1)) q, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  · rw [bitsOfLenLE_length, L.width_cnt]
    omega

/-- **A one-cell register holds the symbol the certificate names.** -/
theorem cell_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks b g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.blocks) (hw : L.width p = 0) (sym : Γ)
    (hbit : sym = Γ.zero ∨ sym = Γ.one) (hcert : b s p 0 = decide (sym = Γ.one)) :
    (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
      L.toWalkLayout.blocks W (walkReg (L.toWalkLayout.reg p))).cells 1 = sym := by
  have h := holdsBits_block_of_stage x L b g hs s W hinv hh hr1 hgf p hp
    [decide (sym = Γ.one)] (fun q hq => by
      have hq0 : q = 0 := by simpa using hq
      subst hq0
      exact hcert) (by rw [hw]; simp)
  have hc := h 0 (by simp)
  have hc' : (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
      L.toWalkLayout.blocks W (walkReg (L.toWalkLayout.reg p))).cells 1
      = Γ.ofBool ([decide (sym = Γ.one)][0]'(by simp)) := hc
  rw [hc']
  exact ofBool_decide_one hbit

/-- **The move register holds what the certificate names.** -/
theorem cell_mv_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
      L.toWalkLayout.blocks W (walkReg L.toWalkLayout.mv)).cells 1 = dc.encMove (ds s) :=
  cell_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.mvIdx L.toWalkLayout.mv_lt
    L.width_mv _ (dc.encMove_bit (ds s)) (by
      rw [walkCert, stageBits]
      simp only [L.toWalkLayout.role_mv])

/-- **The direction register holds what the certificate names.** -/
theorem cell_dr_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
      L.toWalkLayout.blocks W (walkReg L.toWalkLayout.dr)).cells 1 = dc.enc (ds s) :=
  cell_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.drIdx L.toWalkLayout.dr_lt
    L.width_dr _ (dc.enc_bit (ds s)) (by
      rw [walkCert, stageBits]
      simp only [L.toWalkLayout.role_dr])

/-- **The ruler register spans the scan.** This is what makes the scan's length well defined. -/
theorem ruler_of_stage {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ q, 1 ≤ q → q ≤ walkScanLen tm x.length S →
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells q
        = Γ.one := by
  have h := holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.rulerIdx
    L.toWalkLayout.ruler_lt (rulerBlock (walkScanLen tm x.length S)) (fun q hq => ?_) ?_
  · exact ruler_of_holds _ _ _ h
  · rw [walkCert, stageBits]
    simp only [L.toWalkLayout.role_ruler]
    rw [rulerBlock_getElem _ q (by simpa using hq)]
  · rw [rulerBlock_length, L.width_ruler]
    have := one_le_walkScanLen tm x.length S
    omega

/-- The registers a stage leaves behind, indexed by register. -/
noncomputable def stageCells {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (W : Fin (jj + 2 + r + 1) → Tape) : Fin (jj + 1) → ℕ → Γ :=
  fun i q => (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
    L.toWalkLayout.blocks W (walkReg i)).cells q

/-- The same, as the scan sees them: indexed by cell first. -/
noncomputable def stageCols {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (W : Fin (jj + 2 + r + 1) → Tape) : ℕ → Fin (jj + 1) → Γ :=
  fun q i => stageCells L W i q

/-- **Distinct blocks are guessed into distinct tapes.** -/
theorem walkReg_reg_inj {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) :
    ∀ p q, p < L.toWalkLayout.blocks → q < L.toWalkLayout.blocks →
      (walkReg (r := r) (L.toWalkLayout.reg p) : Fin (jj + 2 + r + 1))
        = walkReg (L.toWalkLayout.reg q) → p = q := by
  intro p q hp hq hpq
  refine L.toWalkLayout.reg_inj p q hp hq (Fin.ext ?_)
  have hbeta : (walkReg (r := r) (L.toWalkLayout.reg p) : Fin (jj + 2 + r + 1)).val
    = (walkReg (r := r) (L.toWalkLayout.reg q) : Fin (jj + 2 + r + 1)).val :=
    congrArg Fin.val hpq
  have h1 : (walkReg (r := r) (L.toWalkLayout.reg p) : Fin (jj + 2 + r + 1)).val
    = (L.toWalkLayout.reg p).val := rfl
  have h2 : (walkReg (r := r) (L.toWalkLayout.reg q) : Fin (jj + 2 + r + 1)).val
    = (L.toWalkLayout.reg q).val := rfl
  omega

/-- **A register that no block is guessed into keeps what it held.** This is what chains a walk:
the step that guesses the new code leaves the old code's registers alone, so its check compares
the guess against what the previous step really left behind, not against a fresh guess. -/
theorem stageCells_retained {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (i : Fin (jj + 1))
    (hne : ∀ p, p < L.toWalkLayout.blocks → i ≠ L.toWalkLayout.reg p) :
    stageCells (r := r) L W i = (W (walkReg i)).cells := by
  have h := (TM.guessBlocksTapes_spec (fun p => walkReg (L.toWalkLayout.reg p))
    (fun p => walkReg_ne_last _) L.width L.toWalkLayout.blocks W hinv hh
    (walkReg_reg_inj L)).2.2.2.1 (walkReg i) (walkReg_ne_last i)
    (fun p hp hc => hne p hp (by
      have hv := congrArg Fin.val hc
      have h1 : (walkReg (r := r) i : Fin (jj + 2 + r + 1)).val = i.val := rfl
      have h2 : (walkReg (r := r) (L.toWalkLayout.reg p) : Fin (jj + 2 + r + 1)).val
        = (L.toWalkLayout.reg p).val := rfl
      exact Fin.ext (by omega)))
  funext q
  show (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
    L.toWalkLayout.blocks W (walkReg i)).cells q = _
  rw [h]

/-- The registers a step's guess leaves behind: its own blocks as the certificate names them,
every other tape exactly as it was. -/
noncomputable def stepCells {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (second : Bool) (W : Fin (jj + 2 + r + 1) → Tape) :
    Fin (jj + 1) → ℕ → Γ :=
  fun i q => (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
    L.toWalkLayout.stepBlocks W (walkReg i)).cells q

/-- The certificate a step guesses, read through the step's own block numbering. The two codes
are given per stage, because which family is the old one alternates along a pair. -/
noncomputable def stepCert {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (aOld aNew : ℕ → Code tm.Q kk x.length S) (second : Bool) : ℕ → ℕ → ℕ → Bool :=
  fun s p => stageBits L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (aOld s) (aNew s)
    (L.toWalkLayout.stepIdx second p)

/-- A scratch block keeps its own number in a step's numbering. -/
theorem stepReg_scratch {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (second : Bool) (p : ℕ)
    (hp : p < L.toWalkLayout.scratch) :
    (stepReg L second p : Fin (jj + 2 + r + 1)) = walkReg (L.toWalkLayout.reg p) := by
  rw [stepReg, WalkLayout.stepIdx, ite_eq_left hp]

/-- And so does its certificate. -/
theorem stepCert_scratch {kk jj : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (x : List Bool) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (aOld aNew : ℕ → Code tm.Q kk x.length S) (second : Bool) (s p : ℕ)
    (hp : p < L.toWalkLayout.scratch) :
    stepCert L x dc Ps ds cOlds cNews tgt aOld aNew second s p
      = stageBits L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (aOld s) (aNew s) p := by
  rw [stepCert, WalkLayout.stepIdx, ite_eq_left hp]

/-- **A register no block of the step is guessed into keeps what it held.** -/
theorem stepCells_retained {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (second : Bool) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head) (i : Fin (jj + 1))
    (hne : ∀ p, p < L.toWalkLayout.stepBlocks →
      (walkReg i : Fin (jj + 2 + r + 1)) ≠ stepReg L second p) :
    stepCells L second W i = (W (walkReg i)).cells := by
  have h := (TM.guessBlocksTapes_spec (stepReg L second)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (fun p q hp hq hpq => L.toWalkLayout.stepIdx_inj second p q hp hq
      (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt second p hp)
        (L.toWalkLayout.stepIdx_lt second q hq) (walkReg_inj hpq)))).2.2.2.1
    (walkReg i) (walkReg_ne_last i) hne
  funext q
  show (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
    L.toWalkLayout.stepBlocks W (walkReg i)).cells q = _
  rw [h]

/-- **What a stage leaves on the parameter register, as the scan sees it.** -/
theorem stageCols_par {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    HoldsBits (stageCols L W) 0 L.toWalkLayout.par
      ((succParamsCodec tm.Q kk).enc (Ps s)) :=
  holdsBits_par_of_stage x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **And on the old code's registers.** -/
theorem stageCols_codeA {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ r, r < kk + 3 → HoldsBits (stageCols L W) 0 (L.toWalkLayout.codeA r)
      (codeBlockScan tm x S (f s) r) :=
  holdsBits_codeA_of_stage x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **And on the new code's.** -/
theorem stageCols_codeB {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ r, r < kk + 3 → HoldsBits (stageCols L W) 0 (L.toWalkLayout.codeB r)
      (codeBlockScan tm x S (f (s + 1)) r) :=
  holdsBits_codeB_of_stage x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **And on the counter.** -/
theorem stageCols_cnt {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    HoldsBits (stageCols L W) 0 L.toWalkLayout.cnt (bitsOfLenLE wc (cOlds s)) :=
  holdsBits_cnt_of_stage x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **And on the counter's partner.** -/
theorem stageCols_cnt' {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    HoldsBits (stageCols L W) 0 L.toWalkLayout.cnt' (bitsOfLenLE wc (cNews s)) := by
  refine holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.cnt'Idx
    L.toWalkLayout.cnt'_lt _ (fun q hq => ?_) ?_
  · rw [walkCert, stageBits_cnt' L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s)
      (f (s + 1)) q, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  · rw [bitsOfLenLE_length, L.width_cnt']
    omega

/-- **And on the target the counter is compared against.** -/
theorem stageCols_target {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    HoldsBits (stageCols L W) 0 L.toWalkLayout.target (bitsOfLenLE wc tgt) := by
  refine holdsBits_block_of_stage x L _ g hs s W hinv hh hr1 hgf L.toWalkLayout.targetIdx
    L.toWalkLayout.target_lt _ (fun q hq => ?_) ?_
  · rw [walkCert, stageBits_target L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s)
      (f (s + 1)) q, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  · rw [bitsOfLenLE_length, L.width_target]
    omega

/-- **And on the move cell.** -/
theorem stageCols_mv {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    stageCols L W 1 L.toWalkLayout.mv = dc.encMove (ds s) :=
  cell_mv_of_stage x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **And on the direction cell.** -/
theorem stageCols_dr {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    stageCols L W 1 L.toWalkLayout.dr = dc.enc (ds s) :=
  cell_dr_of_stage x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **What the registers hold when a stage's scan runs.** The scan cannot tell whether a register
was guessed at this stage or left behind by an earlier one, so the acceptance lemmas take this
bundle rather than the guess that produced it. -/
structure StageCols {kk jj : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1))
    (s : ℕ) (cells : Fin (jj + 1) → ℕ → Γ) : Prop where
  /-- The parameter block names the transition the step takes. -/
  par : HoldsBits (fun q i => cells i q) 0 L.toWalkLayout.par
    ((succParamsCodec tm.Q kk).enc (Ps s))
  /-- The old code's registers hold the code the step starts from. -/
  codeA : ∀ p, p < kk + 3 → HoldsBits (fun q i => cells i q) 0 (cA p)
    (codeBlockScan tm x S (f s) p)
  /-- The new code's registers hold the code it reaches. -/
  codeB : ∀ p, p < kk + 3 → HoldsBits (fun q i => cells i q) 0 (cB p)
    (codeBlockScan tm x S (f (s + 1)) p)
  /-- The counter. -/
  cnt : HoldsBits (fun q i => cells i q) 0 cO (bitsOfLenLE wc (cOlds s))
  /-- Its partner, which the step compares it against. -/
  cnt' : HoldsBits (fun q i => cells i q) 0 cN (bitsOfLenLE wc (cNews s))
  /-- The target the walk is counting towards. -/
  target : HoldsBits (fun q i => cells i q) 0 L.toWalkLayout.target (bitsOfLenLE wc tgt)
  /-- The move cell of the guessed direction. -/
  mv : cells L.toWalkLayout.mv 1 = dc.encMove (ds s)
  /-- Its direction cell. -/
  dr : cells L.toWalkLayout.dr 1 = dc.enc (ds s)

/-- **When the two counter registers agree, their roles can be exchanged.** The walk's counter
registers are vestigial — `TM.binaryForTM` owns the loop's index — so both steps of a pair check
only that the counter is unchanged, and it does not matter which register plays which role. -/
theorem StageCols.swapCnt {kk jj : ℕ} {tm : NTM kk} {S wc : ℕ} {x : List Bool}
    {L : WalkWidths kk jj tm x.length S wc} {dc : DirCodec}
    {Ps : ℕ → SuccParams tm.Q kk} {ds : ℕ → Dir3} {cOlds cNews : ℕ → ℕ} {tgt : ℕ}
    {f : ℕ → Code tm.Q kk x.length S} {cA cB : ℕ → Fin (jj + 1)} {cO cN : Fin (jj + 1)}
    {s : ℕ} {cells : Fin (jj + 1) → ℕ → Γ}
    (h : StageCols x L dc Ps ds cOlds cNews tgt f cA cB cO cN s cells)
    (hval : cNews s = cOlds s) :
    StageCols x L dc Ps ds cOlds cNews tgt f cA cB cN cO s cells where
  par := h.par
  codeA := h.codeA
  codeB := h.codeB
  cnt := by rw [← hval]; exact h.cnt'
  cnt' := by rw [hval]; exact h.cnt
  target := h.target
  mv := h.mv
  dr := h.dr

/-- **A stage's guess establishes the bundle.** -/
theorem stageCols_holds {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool)
    (hs : TM.StageBlocks L.width L.toWalkLayout.blocks
      (walkCert L x dc Ps ds cOlds cNews tgt f) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.blocks →
      (W (walkReg (L.toWalkLayout.reg p))).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    StageCols x L dc Ps ds cOlds cNews tgt f L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.cnt L.toWalkLayout.cnt' s (stageCells L W) where
  par := stageCols_par x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  codeA := stageCols_codeA x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  codeB := stageCols_codeB x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  cnt := stageCols_cnt x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  cnt' := stageCols_cnt' x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  target := stageCols_target x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  mv := stageCols_mv x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf
  dr := stageCols_dr x L dc Ps ds cOlds cNews tgt f g hs s W hinv hh hr1 hgf

/-- **A one-cell block of a step's guess.** -/
theorem cell_of_step {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (second : Bool)
    (b : ℕ → ℕ → ℕ → Bool) (g : ℕ → Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks b g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (p : ℕ) (hp : p < L.toWalkLayout.stepBlocks) (hw : stepWidth L p = 0) (sym : Γ)
    (hbit : sym = Γ.zero ∨ sym = Γ.one) (hcert : b s p 0 = decide (sym = Γ.one)) :
    (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
      L.toWalkLayout.stepBlocks W (stepReg L second p)).cells 1 = sym := by
  have h := holdsBits_block_of_step x L second b g hs s W hinv hh hr1 hgf p hp
    [decide (sym = Γ.one)] (fun q hq => by
      have hq0 : q = 0 := by simpa using hq
      subst hq0
      exact hcert) (by rw [hw]; simp)
  have hc := h 0 (by simp)
  have hc' : (TM.guessBlocksTapes (stepReg L second) (stepWidth L)
      L.toWalkLayout.stepBlocks W (stepReg L second p)).cells 1
      = Γ.ofBool ([decide (sym = Γ.one)][0]'(by simp)) := hc
  rw [hc']
  exact ofBool_decide_one hbit

/-- **What a step's registers hold when its scan runs.** The step's own blocks come from the
certificate; the other code tuple is whatever the previous step left behind, which the caller
supplies. That is the chaining — each check compares a guess against a retained code, never two
guesses against each other. -/
theorem stepCols_holds {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f aOld aNew : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (second : Bool)
    (cA cB : ℕ → Fin (jj + 1)) (s : ℕ)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (stepCert L x dc Ps ds cOlds cNews tgt aOld aNew second) g)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (hcB : ∀ p, p < kk + 3 →
      (stepReg L second (L.toWalkLayout.scratch + p) : Fin (jj + 2 + r + 1)) = walkReg (cB p))
    (hcertB : ∀ p, p < kk + 3 → ∀ q,
      stepCert L x dc Ps ds cOlds cNews tgt aOld aNew second s (L.toWalkLayout.scratch + p) q
        = (codeBlockScan tm x S (f (s + 1)) p).getD q false)
    (hret : ∀ p, p < kk + 3 → HoldsBits (fun q i => (W (walkReg i)).cells q) 0 (cA p)
      (codeBlockScan tm x S (f s) p))
    (hretReg : ∀ p, p < kk + 3 → ∀ p', p' < L.toWalkLayout.stepBlocks →
      (walkReg (cA p) : Fin (jj + 2 + r + 1)) ≠ stepReg L second p') :
    StageCols x L dc Ps ds cOlds cNews tgt f cA cB L.toWalkLayout.cnt L.toWalkLayout.cnt' s
      (stepCells L second W) := by
  have hscratch : ∀ p, p < L.toWalkLayout.scratch → p < L.toWalkLayout.stepBlocks := by
    intro p hp
    rw [WalkLayout.stepBlocks]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := holdsBits_block_of_step x L second _ g hs s W hinv hh hr1 hgf
      L.toWalkLayout.parIdx (hscratch _ L.toWalkLayout.par_scratch)
      ((succParamsCodec tm.Q kk).enc (Ps s)) (fun q hq => by
        rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
            L.toWalkLayout.par_scratch,
          stageBits_par L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (aOld s) (aNew s) q,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]) (by
        rw [(succParamsCodec tm.Q kk).enc_length,
          stepWidth_scratch L _ L.toWalkLayout.par_scratch, L.width_par]
        omega)
    rw [stepReg_scratch L second _ L.toWalkLayout.par_scratch] at h
    exact h
  · intro p hp
    have hr := stepCells_retained L second W hinv hh (cA p) (hretReg p hp)
    intro q hq
    have h := hret p hp q hq
    show stepCells L second W (cA p) (0 + q + 1) = _
    rw [hr]
    exact h
  · intro p hp
    have h := holdsBits_block_of_step x L second _ g hs s W hinv hh hr1 hgf
      (L.toWalkLayout.scratch + p) (by
        rw [WalkLayout.stepBlocks]
        omega)
      (codeBlockScan tm x S (f (s + 1)) p) (fun q hq => by
        rw [hcertB p hp q, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
          Option.getD_some]) (by
        rw [codeBlockScan_length, stepWidth_code L p hp]
        exact blockLen_le_codeWidthScan tm x.length S p)
    rw [hcB p hp] at h
    exact h
  · have h := holdsBits_block_of_step x L second _ g hs s W hinv hh hr1 hgf
      L.toWalkLayout.cntIdx (hscratch _ L.toWalkLayout.cnt_scratch)
      (bitsOfLenLE wc (cOlds s)) (fun q hq => by
        rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
            L.toWalkLayout.cnt_scratch,
          stageBits_cnt L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (aOld s) (aNew s) q,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]) (by
        rw [bitsOfLenLE_length, stepWidth_scratch L _ L.toWalkLayout.cnt_scratch, L.width_cnt]
        omega)
    rw [stepReg_scratch L second _ L.toWalkLayout.cnt_scratch] at h
    exact h
  · have h := holdsBits_block_of_step x L second _ g hs s W hinv hh hr1 hgf
      L.toWalkLayout.cnt'Idx (hscratch _ L.toWalkLayout.cnt'_scratch)
      (bitsOfLenLE wc (cNews s)) (fun q hq => by
        rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
            L.toWalkLayout.cnt'_scratch,
          stageBits_cnt' L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (aOld s) (aNew s) q,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]) (by
        rw [bitsOfLenLE_length, stepWidth_scratch L _ L.toWalkLayout.cnt'_scratch, L.width_cnt']
        omega)
    rw [stepReg_scratch L second _ L.toWalkLayout.cnt'_scratch] at h
    exact h
  · have h := holdsBits_block_of_step x L second _ g hs s W hinv hh hr1 hgf
      L.toWalkLayout.targetIdx (hscratch _ L.toWalkLayout.target_scratch)
      (bitsOfLenLE wc tgt) (fun q hq => by
        rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
            L.toWalkLayout.target_scratch,
          stageBits_target L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (aOld s) (aNew s) q,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]) (by
        rw [bitsOfLenLE_length, stepWidth_scratch L _ L.toWalkLayout.target_scratch,
          L.width_target]
        omega)
    rw [stepReg_scratch L second _ L.toWalkLayout.target_scratch] at h
    exact h
  · have h := cell_of_step x L second _ g hs s W hinv hh hr1 hgf L.toWalkLayout.mvIdx
      (hscratch _ L.toWalkLayout.mv_scratch)
      (by rw [stepWidth_scratch L _ L.toWalkLayout.mv_scratch, L.width_mv]) _
      (dc.encMove_bit (ds s)) (by
        rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
            L.toWalkLayout.mv_scratch, stageBits]
        simp only [L.toWalkLayout.role_mv])
    rw [stepReg_scratch L second _ L.toWalkLayout.mv_scratch] at h
    exact h
  · have h := cell_of_step x L second _ g hs s W hinv hh hr1 hgf L.toWalkLayout.drIdx
      (hscratch _ L.toWalkLayout.dr_scratch)
      (by rw [stepWidth_scratch L _ L.toWalkLayout.dr_scratch, L.width_dr]) _
      (dc.enc_bit (ds s)) (by
        rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
            L.toWalkLayout.dr_scratch, stageBits]
        simp only [L.toWalkLayout.role_dr])
    rw [stepReg_scratch L second _ L.toWalkLayout.dr_scratch] at h
    exact h

/-- **The first step of a pair.** It guesses the new code's registers and keeps the old code's,
so its scan compares its guess against what the step before really left behind. -/
theorem stepCols_holds_first {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (stepCert L x dc Ps ds cOlds cNews tgt f (fun s => f (s + 1)) false) g)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L false p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (hret : ∀ p, p < kk + 3 → HoldsBits (fun q i => (W (walkReg i)).cells q) 0
      (L.toWalkLayout.codeA p) (codeBlockScan tm x S (f s) p)) :
    StageCols x L dc Ps ds cOlds cNews tgt f L.toWalkLayout.codeA L.toWalkLayout.codeB
      L.toWalkLayout.cnt L.toWalkLayout.cnt' s (stepCells L false W) := by
  refine stepCols_holds x L dc Ps ds cOlds cNews tgt f f (fun s => f (s + 1)) g false _ _ s hs
    W hinv hh hr1 hgf (fun p hp => ?_) (fun p hp q => ?_) hret (fun p hp p' hp' hc => ?_)
  · rw [stepReg, L.toWalkLayout.stepIdx_codeB p hp]
    rfl
  · rw [stepCert, L.toWalkLayout.stepIdx_codeB p hp,
      stageBits_codeB L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f s) (f (s + 1)) p hp q]
  · exact L.toWalkLayout.stepIdx_ne_codeA p' p hp' hp
      (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt false p' hp')
        (L.toWalkLayout.codeA_lt p hp) (walkReg_inj hc).symm)

/-- **The second step of a pair.** The families have swapped roles: it guesses the old code's
registers and keeps the new code's, which is what returns each code to the registers it started
in. -/
theorem stepCols_holds_second {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (stepCert L x dc Ps ds cOlds cNews tgt (fun s => f (s + 1)) f true) g)
    (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L true p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (hret : ∀ p, p < kk + 3 → HoldsBits (fun q i => (W (walkReg i)).cells q) 0
      (L.toWalkLayout.codeB p) (codeBlockScan tm x S (f s) p)) :
    StageCols x L dc Ps ds cOlds cNews tgt f L.toWalkLayout.codeB L.toWalkLayout.codeA
      L.toWalkLayout.cnt L.toWalkLayout.cnt' s (stepCells L true W) := by
  refine stepCols_holds x L dc Ps ds cOlds cNews tgt f (fun s => f (s + 1)) f g true _ _ s hs
    W hinv hh hr1 hgf (fun p hp => ?_) (fun p hp q => ?_) hret (fun p hp p' hp' hc => ?_)
  · rw [stepReg, L.toWalkLayout.stepIdx_codeA p hp]
    rfl
  · rw [stepCert, L.toWalkLayout.stepIdx_codeA p hp,
      stageBits_codeA L x dc (Ps s) (ds s) (cOlds s) (cNews s) tgt true (f (s + 1)) (f s) p hp q]
  · exact L.toWalkLayout.stepIdx_ne_codeB p' p hp' hp
      (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt true p' hp')
        (L.toWalkLayout.codeB_lt p hp) (walkReg_inj hc).symm)

/-- **A stage of a walk that stays put is accepted.** Every hypothesis is now about the walk and
the guess tape: the certificate supplies the registers, and the input check leaves them alone. -/
theorem stage_accepts_stay {kk jj : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1))
    (hcA : ∀ p, p < kk + 3 → cA p ≠ L.toWalkLayout.res)
    (hcB : ∀ p, p < kk + 3 → cB p ≠ L.toWalkLayout.res)
    (hcO : cO ≠ L.toWalkLayout.res) (hcN : cN ≠ L.toWalkLayout.res)
    (s : ℕ) (cells : Fin (jj + 1) → ℕ → Γ)
    (hc : StageCols x L dc Ps ds cOlds cNews tgt f cA cB cO cN s cells)
    (advance : Bool) (gsym : Γ)
    (hstay : f (s + 1) = f s) (hd : ds s = Dir3.stay)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hu : cOlds s < 2 ^ wc) (hv : cNews s < 2 ^ wc)
    (hmove : if advance then cNews s = cOlds s + 1 else cOlds s = cNews s) :
    (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).emit
      ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).run
        (fun q i => checkedCells cells L.toWalkLayout.par L.toWalkLayout.res gsym i q)
        (walkScanLen tm x.length S)) = true := by
  refine walkStepScanner_accepts_stay tm x S _ L.toWalkLayout.par L.toWalkLayout.mv
    L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc
    cA cB (f s) (cOlds s) (cNews s) ?_ ?_ ?_ ?_ hwc hu hv
    ?_ ?_ hmove
  · intro p hp
    exact holdsBits_checked (hcA p hp)
      (hc.codeA p hp)
  · intro p hp
    have hcb := hc.codeB p hp
    rw [hstay] at hcb
    exact holdsBits_checked (hcB p hp) hcb
  · show checkedCells cells L.toWalkLayout.par L.toWalkLayout.res gsym
      L.toWalkLayout.mv 1 = _
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.mv_ne_res]
    rw [hc.mv, hd]
  · show checkedCells cells L.toWalkLayout.par L.toWalkLayout.res gsym
      L.toWalkLayout.dr 1 = _
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.dr_ne_res]
    rw [hc.dr, hd]
  · exact holdsBits_checked hcO hc.cnt
  · exact holdsBits_checked hcN hc.cnt'

/-- **A stage of a walk that advances is accepted.** The input check's verdict is not assumed: it
follows, because the certificate names the transition the code really takes, whose input symbol is
the one the machine's own head is over. -/
theorem stage_accepts_succ {kk jj : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (cA cB : ℕ → Fin (jj + 1)) (cO cN : Fin (jj + 1))
    (hcA : ∀ p, p < kk + 3 → cA p ≠ L.toWalkLayout.res)
    (hcB : ∀ p, p < kk + 3 → cB p ≠ L.toWalkLayout.res)
    (hcO : cO ≠ L.toWalkLayout.res) (hcN : cN ≠ L.toWalkLayout.res)
    (s : ℕ) (cells : Fin (jj + 1) → ℕ → Γ)
    (hc : StageCols x L dc Ps ds cOlds cNews tgt f cA cB cO cN s cells)
    (advance : Bool) (β : Bool)
    (hPs : Ps s = paramsOf tm x S (f s) β)
    (hsucc : f (s + 1) = succCode tm x S β (f s))
    (hds : ds s = adjustedDir (succTrans tm (Ps s)).2.2.2.1 (f s).2.1.val)
    (hclampIn : movedIdx (succTrans tm (Ps s)).2.2.2.1 (f s).2.1.val ≤ x.length + S + 1)
    (hclampW : ∀ i, movedIdx (succDir tm (Ps s) i) ((f s).2.2.1 i).1.val ≤ S)
    (hclampO : movedIdx (succTrans tm (Ps s)).2.2.2.2.2 (f s).2.2.2.1.val ≤ S + 1)
    (hleft : (succTrans tm (Ps s)).2.2.2.1 = Dir3.left → 0 < (f s).2.1.val)
    (hwc : wc ≤ walkScanLen tm x.length S)
    (hu : cOlds s < 2 ^ wc) (hv : cNews s < 2 ^ wc)
    (hmove : if advance then cNews s = cOlds s + 1 else cOlds s = cNews s) :
    (walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).emit
      ((walkStepScanner tm x.length S L.toWalkLayout.par L.toWalkLayout.mv L.toWalkLayout.dr
        L.toWalkLayout.res cO cN wc advance dc cA cB).run
        (fun q i => checkedCells cells L.toWalkLayout.par L.toWalkLayout.res
          (inSymOf tm x S (f s)) i q)
        (walkScanLen tm x.length S)) = true := by
  have hpar := hc.par
  have hinSym : (Ps s).inSym = inSymOf tm x S (f s) := by
    rw [hPs]
    rfl
  obtain ⟨hq, hstate, hwsym, hosym, hhead, hwork, hout⟩ :=
    succ_fields_of_eq tm x S (f s) (f (s + 1)) β hsucc (by rw [← hPs] at *; exact hclampIn)
      (by rw [← hPs] at *; exact hclampW) (by rw [← hPs] at *; exact hclampO)
  rw [← hPs] at hq hstate hwsym hosym hhead hwork hout
  refine walkStepScanner_accepts_succ tm x S _ L.toWalkLayout.par L.toWalkLayout.mv
    L.toWalkLayout.dr L.toWalkLayout.res cO cN wc advance dc
    cA cB (f s) (f (s + 1)) (Ps s) (cOlds s) (cNews s)
    (holdsBits_checked L.toWalkLayout.par_ne_res hpar) ?_ ?_ hq hstate hwsym hosym hhead hwork
    hout hleft ?_ ?_ hinSym ?_ hwc hu hv ?_ ?_ hmove
  · intro p hp
    exact holdsBits_checked (hcA p hp)
      (hc.codeA p hp)
  · intro p hp
    exact holdsBits_checked (hcB p hp)
      (hc.codeB p hp)
  · show checkedCells cells L.toWalkLayout.par L.toWalkLayout.res _
      L.toWalkLayout.mv 1 = _
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.mv_ne_res]
    rw [hc.mv, hds]
  · show checkedCells cells L.toWalkLayout.par L.toWalkLayout.res _
      L.toWalkLayout.dr 1 = _
    rw [checked_cell _ _ _ _ _ L.toWalkLayout.dr_ne_res]
    rw [hc.dr, hds]
  · intro _
    show checkedCells cells L.toWalkLayout.par L.toWalkLayout.res _
      L.toWalkLayout.res 1 = _
    rw [checkedCells_res]
    have hv := inMatchVerdict_of_inSym tm (fun q i => cells i q) L.toWalkLayout.par (Ps s)
      (inSymOf tm x S (f s)) hpar hinSym
    have hv' : TM.inMatchVerdict gammaBits (inSymOf tm x S (f s))
        (cells L.toWalkLayout.par 1) (cells L.toWalkLayout.par 2) = true := hv
    rw [hv']
    rfl
  · exact holdsBits_checked hcO hc.cnt
  · exact holdsBits_checked hcN hc.cnt'

/-- **A step's ruler register spans the scan**, which is what makes the scan well formed. -/
theorem ruler_of_step {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (aOld aNew : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (second : Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (stepCert L x dc Ps ds cOlds cNews tgt aOld aNew second) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    ∀ q, 1 ≤ q → q ≤ walkScanLen tm x.length S →
      stepCells L second W (L.toWalkLayout.reg L.toWalkLayout.rulerIdx) q = Γ.one := by
  have hlt : L.toWalkLayout.rulerIdx < L.toWalkLayout.stepBlocks := by
    rw [WalkLayout.stepBlocks]
    have := L.toWalkLayout.ruler_scratch
    omega
  have h := holdsBits_block_of_step x L second _ g hs s W hinv hh hr1 hgf
    L.toWalkLayout.rulerIdx hlt (rulerBlock (walkScanLen tm x.length S)) (fun q hq => ?_) ?_
  · rw [stepReg_scratch L second _ L.toWalkLayout.ruler_scratch] at h
    exact ruler_of_holds _ _ _ h
  · rw [stepCert_scratch L x dc Ps ds cOlds cNews tgt aOld aNew second s _
      L.toWalkLayout.ruler_scratch, stageBits]
    simp only [L.toWalkLayout.role_ruler]
    rw [rulerBlock_getElem _ q (by simpa using hq)]
  · rw [rulerBlock_length, stepWidth_scratch L _ L.toWalkLayout.ruler_scratch, L.width_ruler]
    have := one_le_walkScanLen tm x.length S
    omega

/-- **A step's registers make a well-formed scan.** The ruler spans the scan, and the blank that
stops the scan is the ruler tape's own — the guess writes up to the ruler's width and no further,
so a caller only has to know that the tape was blank there to begin with. -/
theorem scanTape_of_step {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (dc : DirCodec)
    (Ps : ℕ → SuccParams tm.Q kk) (ds : ℕ → Dir3) (cOlds cNews : ℕ → ℕ) (tgt : ℕ)
    (aOld aNew : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (second : Bool)
    (hs : TM.StageBlocks (stepWidth L) L.toWalkLayout.stepBlocks
      (stepCert L x dc Ps ds cOlds cNews tgt aOld aNew second) g)
    (s : ℕ) (W : Fin (jj + 2 + r + 1) → Tape) (hinv : ∀ i, (W i).StartInvariant)
    (hh : ∀ i, 1 ≤ (W i).head)
    (hr1 : ∀ p, p < L.toWalkLayout.stepBlocks → (W (stepReg L second p)).head = 1)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r))))
    (hblank : (W (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells
      (walkScanLen tm x.length S + 1) = Γ.blank) :
    TM.ScanTape (stepCells L second W) (walkScanLen tm x.length S) := by
  have hlt : L.toWalkLayout.rulerIdx < L.toWalkLayout.stepBlocks := by
    rw [WalkLayout.stepBlocks]
    have := L.toWalkLayout.ruler_scratch
    omega
  obtain ⟨ginv, -, -, -, -⟩ := TM.guessBlocksTapes_spec (stepReg L second)
    (fun p => walkReg_ne_last _) (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
    (fun p q hp hq hpq => L.toWalkLayout.stepIdx_inj second p q hp hq
      (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt second p hp)
        (L.toWalkLayout.stepIdx_lt second q hq) (walkReg_inj hpq)))
  refine scanTape_of_ruler (stepCells L second W) (walkScanLen tm x.length S)
    (fun i => (ginv (walkReg i)).1) (fun i q hq => (ginv (walkReg i)).2 q hq) (fun q h1 h2 => ?_)
    ?_
  · rw [← L.toWalkLayout.ruler_zero]
    exact ruler_of_step x L dc Ps ds cOlds cNews tgt aOld aNew g second hs s W hinv hh hr1 hgf
      q h1 h2
  · have hbeyond := TM.guessBlocksTapes_beyond (stepReg L second) (fun p => walkReg_ne_last _)
      (stepWidth L) L.toWalkLayout.stepBlocks W hinv hh
      (fun p q hp hq hpq => L.toWalkLayout.stepIdx_inj second p q hp hq
        (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt second p hp)
          (L.toWalkLayout.stepIdx_lt second q hq) (walkReg_inj hpq)))
      L.toWalkLayout.rulerIdx hlt (walkScanLen tm x.length S + 1) ?_
    · rw [← L.toWalkLayout.ruler_zero]
      show (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W
        (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells _ = _
      rw [← stepReg_scratch L second _ L.toWalkLayout.ruler_scratch, hbeyond,
        stepReg_scratch L second _ L.toWalkLayout.ruler_scratch, hblank]
    · rw [hr1 _ hlt, stepWidth_scratch L _ L.toWalkLayout.ruler_scratch, L.width_ruler]
      have := one_le_walkScanLen tm x.length S
      omega

/-- **A step advances the guess tape by exactly its own consumption**, so the guess-tape clause of
the walk's invariant is re-established one step further on. -/
theorem guessFrom_after_step {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (second : Bool) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (g : ℕ → Bool) (s : ℕ)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    TM.GuessFrom
      (fun q => g ((s + 1) * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (TM.guessBlocksTapes (stepReg L second) (stepWidth L) L.toWalkLayout.stepBlocks W
        (Fin.last (jj + 2 + r))) := by
  have h := TM.guessFrom_after (stepReg L second) (fun p => walkReg_ne_last _) (stepWidth L)
    L.toWalkLayout.stepBlocks W hinv hh
    (fun p q hp hq hpq => L.toWalkLayout.stepIdx_inj second p q hp hq
      (L.toWalkLayout.reg_inj _ _ (L.toWalkLayout.stepIdx_lt second p hp)
        (L.toWalkLayout.stepIdx_lt second q hq) (walkReg_inj hpq))) _ hgf
  intro q
  have hq := h q
  rw [hq]
  refine congrArg Γ.ofBool (congrArg g ?_)
  rw [Nat.succ_mul]
  omega

/-- **A stage advances the guess tape by exactly its own consumption.** So the guess-tape clause
of the invariant is re-established one stage further on. -/
theorem guessFrom_after_stage {kk jj r : ℕ} {tm : NTM kk} {nn S wc : ℕ}
    (L : WalkWidths kk jj tm nn S wc) (W : Fin (jj + 2 + r + 1) → Tape)
    (hinv : ∀ i, (W i).StartInvariant) (hh : ∀ i, 1 ≤ (W i).head)
    (g : ℕ → Bool) (s : ℕ)
    (hgf : TM.GuessFrom
      (fun q => g (s * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (W (Fin.last (jj + 2 + r)))) :
    TM.GuessFrom
      (fun q => g ((s + 1) * TM.guessOffset L.width L.toWalkLayout.blocks + q))
      (TM.guessBlocksTapes (fun p => walkReg (L.toWalkLayout.reg p)) L.width
        L.toWalkLayout.blocks W (Fin.last (jj + 2 + r))) := by
  have h := TM.guessFrom_after (fun p => walkReg (L.toWalkLayout.reg p))
    (fun p => walkReg_ne_last _) L.width L.toWalkLayout.blocks W hinv hh
    (walkReg_reg_inj L) _ hgf
  intro q
  have hq := h q
  rw [hq]
  refine congrArg Γ.ofBool (congrArg g ?_)
  rw [Nat.succ_mul]
  omega

/-! ## The walk loop's invariant

After `j` iterations the counter names `j`, the code registers hold the `2j`-th code of the walk
— two steps per iteration — and the machine's own input head sits where that code's input head
does, which is what lets `TM.inMatchTM` check the guessed symbol against the real tape. -/

/-- **What holds between the steps of a walk.** The registers are parked and the ruler tape's
blank still stops the scan; the code the next step will check against sits in the family that step
retains; the machine's own input head is where that code says; and the guess tape is positioned at
the step's own share of the certificate. -/
def WalkStepInv {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ} (x : List Bool)
    (L : WalkWidths kk jj tm x.length S wc) (cOld : ℕ → Fin (jj + 1))
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (s : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work out =>
    (∀ i, (work i).StartInvariant) ∧ (∀ i, 1 ≤ (work i).head) ∧
    (∀ i : Fin (jj + 1), (work (walkReg i)).head = 1) ∧
    (work (walkReg (L.toWalkLayout.reg L.toWalkLayout.rulerIdx))).cells
      (walkScanLen tm x.length S + 1) = Γ.blank ∧
    (∀ p, p < kk + 3 → HoldsBits (fun q i => (work (walkReg i)).cells q) 0 (cOld p)
      (codeBlockScan tm x S (f s) p)) ∧
    inp = ⟨max (f s).2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
    out.StartInvariant ∧ 1 ≤ out.head ∧
    TM.GuessFrom
      (fun q => g (s * TM.guessOffset (stepWidth L) L.toWalkLayout.stepBlocks + q))
      (work (Fin.last (jj + 2 + r)))

/-- The walk loop's invariant after `j` iterations. -/
def WalkLoopInv {kk jj r : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cnt : Fin (jj + 1)) (wc : ℕ) (jold : ℕ → Fin (jj + 1))
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (w : ℕ → ℕ) (t : ℕ) (j : ℕ) :
    TM.TapePred (jj + 2 + r + 1) :=
  fun inp work _out =>
    j < 2 ^ wc ∧
      HoldsBits (fun p i => (work i).cells p) 0 (walkReg cnt) (bitsOfLenLE wc j) ∧
      (∀ p, p < kk + 3 → HoldsBits (fun q i => (work i).cells q) 0 (walkReg (jold p))
        (codeBlockScan tm x S (f (2 * j)) p)) ∧
      inp = ⟨max (f (2 * j)).2.1.val 1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
      TM.GuessFrom (fun q => g (j * walkGuessStride w t + q)) (work (Fin.last (jj + 2 + r)))

/-- **The invariant pins the counter**, so `Complexity.counterLoop_hoareTime` applies to the
walk. -/
theorem holdsCounter_of_walkLoopInv {kk jj r : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cnt : Fin (jj + 1)) (wc : ℕ) (jold : ℕ → Fin (jj + 1))
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (w : ℕ → ℕ) (t : ℕ) (j : ℕ) (inp : Tape)
    (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkLoopInv tm x S cnt wc jold f g w t j inp work out) :
    HoldsCounter (walkReg cnt) wc j inp work out :=
  ⟨h.1, h.2.1⟩

/-- **The invariant says what symbol the simulated input head is over**, whenever that head is
off the marker. At the marker no machine can keep its own head in place, and none needs to: the
symbol there is `▷`, which the code's head field already says. -/
theorem inSym_of_walkLoopInv {kk jj r : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cnt : Fin (jj + 1)) (wc : ℕ) (jold : ℕ → Fin (jj + 1))
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (w : ℕ → ℕ) (t : ℕ) (j : ℕ) (inp : Tape)
    (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkLoopInv tm x S cnt wc jold f g w t j inp work out)
    (hne : (f (2 * j)).2.1.val ≠ 0) : inp.read = inSymOf tm x S (f (2 * j)) := by
  rw [h.2.2.2.1, Tape.read, inSymOf]
  show (Tape.init (x.map Γ.ofBool)).cells (max (f (2 * j)).2.1.val 1) = _
  rw [show max (f (2 * j)).2.1.val 1 = (f (2 * j)).2.1.val by omega]

/-- **The machine's input head is never on the marker**, which is what lets a step read it. -/
theorem inp_read_ne_start_of_walkLoopInv {kk jj r : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cnt : Fin (jj + 1)) (wc : ℕ) (jold : ℕ → Fin (jj + 1))
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (w : ℕ → ℕ) (t : ℕ) (j : ℕ) (inp : Tape)
    (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkLoopInv tm x S cnt wc jold f g w t j inp work out) :
    inp.read ≠ Γ.start := by
  rw [h.2.2.2.1]
  show (Tape.init (x.map Γ.ofBool)).cells (max (f (2 * j)).2.1.val 1) ≠ Γ.start
  exact Tape.init_ofBool_cells_ne_start x _ (le_max_right _ _)

/-- **The invariant says what the guess tape still holds**, which is what lets an iteration find
the guesses it needs. -/
theorem guessFrom_of_walkLoopInv {kk jj r : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cnt : Fin (jj + 1)) (wc : ℕ) (jold : ℕ → Fin (jj + 1))
    (f : ℕ → Code tm.Q kk x.length S) (g : ℕ → Bool) (w : ℕ → ℕ) (t : ℕ) (j : ℕ) (inp : Tape)
    (work : Fin (jj + 2 + r + 1) → Tape) (out : Tape)
    (h : WalkLoopInv tm x S cnt wc jold f g w t j inp work out) :
    TM.GuessFrom (fun q => g (j * walkGuessStride w t + q)) (work (Fin.last (jj + 2 + r))) :=
  h.2.2.2.2

/-- **The blocks an iteration guesses are read off the stream.** The first stage of iteration `j`
starts at `j * walkGuessStride w t`, the second a stage further on. -/
theorem walkGuessStride_split (w : ℕ → ℕ) (t j : ℕ) :
    (j + 1) * walkGuessStride w t
      = j * walkGuessStride w t + TM.guessOffset w t + TM.guessOffset w t := by
  show (j + 1) * (2 * TM.guessOffset w t)
    = j * (2 * TM.guessOffset w t) + TM.guessOffset w t + TM.guessOffset w t
  rw [Nat.succ_mul]
  omega


/-- **The walk loop.** Given a body that carries the invariant one step forward, and a test that
halts at `N`, the loop carries the initial code to the `N`-th code of the walk. The counter names
the loop's index, which is what makes the rule's variant decrease. -/
theorem walkLoop_hoareTime (tm : NTM kk) (x : List Bool) (S : ℕ) {jj : ℕ}
    (R : CodeRegs kk jj) (cnt : Fin (jj + 1)) (wc : ℕ)
    (f : ℕ → Code tm.Q kk x.length S) (N b : ℕ)
    (body test : TM (jj + 1)) {post : TM.TapePred (jj + 1)}
    (hstep : ∀ j, j < N → ∀ inp work out, WalkInv tm x S R cnt wc f j inp work out →
      ∃ inp' work' out' t, t ≤ b ∧
        (TM.loopTM body test).reachesIn t
          ⟨(TM.loopTM body test).qstart, inp, work, out⟩
          ⟨(TM.loopTM body test).qstart, inp', work', out'⟩ ∧
        WalkInv tm x S R cnt wc f (j + 1) inp' work' out')
    (hstop : ∀ inp work out, WalkInv tm x S R cnt wc f N inp work out →
      ∃ c' t, t ≤ b ∧
        (TM.loopTM body test).reachesIn t
          ⟨(TM.loopTM body test).qstart, inp, work, out⟩ c' ∧
        (TM.loopTM body test).halted c' ∧ post c'.input c'.work c'.output) :
    (TM.loopTM body test).HoareTime (WalkInv tm x S R cnt wc f 0) post ((N + 1) * b) :=
  TM.loopTM_hoareTime_indexed body test
    (idx := fun _ work _ => counterVal cnt wc work)
    (fun j inp work out h => counterVal_of_walkInv tm x S R cnt wc f j inp work out h)
    hstep hstop

/-- **The counter reads back the value a counter predicate pins.** -/
theorem counterVal_of_holdsCounter {jj : ℕ} (cnt : Fin (jj + 1)) (wc v : ℕ)
    (inp : Tape) (work : Fin (jj + 1) → Tape) (out : Tape)
    (h : HoldsCounter cnt wc v inp work out) : counterVal cnt wc work = v := by
  obtain ⟨hv, hcnt⟩ := h
  have hbits : (List.ofFn fun q : Fin wc => decide ((work cnt).cells (q.val + 1) = Γ.one))
      = bitsOfLenLE wc v := by
    refine List.ext_getElem (by simp [bitsOfLenLE_length]) ?_
    intro q h1 h2
    have hq : q < wc := by simpa using h1
    have hc := hcnt q (by rw [bitsOfLenLE_length]; exact hq)
    simp only [Nat.zero_add] at hc
    simp only [List.getElem_ofFn]
    show decide ((work cnt).cells (q + 1) = Γ.one) = _
    rw [hc]
    cases (bitsOfLenLE wc v)[q]'(by rw [bitsOfLenLE_length]; exact hq) <;> simp [Γ.ofBool]
  rw [counterVal, hbits, binValLE_bitsOfLenLE wc v hv]

/-- **The increment check advances a counter.** A loop does not compute its next index: it
guesses it into a second register and checks it here. -/
theorem counter_succ_of_plusOne {jj : ℕ} (cnt cnt' : Fin (jj + 1)) (wc u v : ℕ)
    (inp : Tape) (work : Fin (jj + 1) → Tape) (out : Tape)
    (hu : HoldsCounter cnt wc u inp work out) (hv : HoldsCounter cnt' wc v inp work out)
    (hscan : (Scanner.plusOne jj cnt cnt').emit
      ((Scanner.plusOne jj cnt cnt').run (fun p i => (work i).cells p) wc) = true) :
    v = u + 1 :=
  (plusOne_of_holds (fun p i => (work i).cells p) cnt cnt' wc u v hu.1 hv.1 hu.2 hv.2).mp hscan

/-- **A counter-driven loop.** Any invariant family whose members pin the counter to their index
satisfies the indexed loop rule — the counter names the index, so the rule's variant decreases.
The walk, the enumeration of codes and the enumeration of rounds all have this shape. -/
theorem counterLoop_hoareTime {jj : ℕ} (cnt : Fin (jj + 1)) (wc : ℕ)
    (E : ℕ → TM.TapePred (jj + 1))
    (hE : ∀ j inp work out, E j inp work out → HoldsCounter cnt wc j inp work out)
    (N b : ℕ) (body test : TM (jj + 1)) {post : TM.TapePred (jj + 1)}
    (hstep : ∀ j, j < N → ∀ inp work out, E j inp work out →
      ∃ inp' work' out' t, t ≤ b ∧
        (TM.loopTM body test).reachesIn t
          ⟨(TM.loopTM body test).qstart, inp, work, out⟩
          ⟨(TM.loopTM body test).qstart, inp', work', out'⟩ ∧
        E (j + 1) inp' work' out')
    (hstop : ∀ inp work out, E N inp work out →
      ∃ c' t, t ≤ b ∧
        (TM.loopTM body test).reachesIn t
          ⟨(TM.loopTM body test).qstart, inp, work, out⟩ c' ∧
        (TM.loopTM body test).halted c' ∧ post c'.input c'.work c'.output) :
    (TM.loopTM body test).HoareTime (E 0) post ((N + 1) * b) :=
  TM.loopTM_hoareTime_indexed body test
    (idx := fun _ work _ => counterVal cnt wc work)
    (fun j inp work out h =>
      counterVal_of_holdsCounter cnt wc j inp work out (hE j inp work out h))
    hstep hstop

end Complexity
