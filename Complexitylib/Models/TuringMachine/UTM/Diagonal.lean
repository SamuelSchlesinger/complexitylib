/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.PairSelf
public import Complexitylib.Models.TuringMachine.UTM.Internal.TermCheck
public import Complexitylib.Models.TuringMachine.UTM.ClockedUtm
public import Complexitylib.Models.TuringMachine.UTM.Internal.NegOut
public import Complexitylib.Models.TuringMachine.UTM.HierarchySupport
public import Complexitylib.Models.TuringMachine.UTM.ClockConstructible
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

/-!
# The time-hierarchy diagonalizer `diagTM`

The 8-tape machine `D := diagTM clk` at the heart of the time hierarchy
theorem. On input `x` it:

1. builds the self-pair `pair x x` on work tape 7 (`pairSelfTM`);
2. decides `TerminatedRegion x` by a single input scan (`termCheckTM`);
   malformed inputs are routed to a fixed `0` output (`writeTM Γw.zero`);
3. for well-formed inputs: blanks the verdict cell (`blankOutTM`), builds
   the unary clock `regTape (g |x|)` on work tape 6 (the abstract
   clock-constructibility witness `clk`), runs the clocked universal
   machine on the self-pair (`retargetInput clockedUtmTM`), and finally
   **negates** output cell 1 (`negOutTM`) — accepting exactly when the
   simulated machine does *not* accept within `g |x|` steps.

## Main definitions

- `TM.ClockWitness` — the body of `ClockConstructible`, named
- `TM.blankOutTM` — write `□` at output cell 1, framing everything else
- `TM.diagTM`, `TM.diagLang`, `TM.diagTime`

## Main results

- `TM.clockConstructible_iff`
- `TM.diagTM_decidesInTime` — `diagTM clk` decides `diagLang clk` in time
  `diagTime C g`
- `TM.diagTM_flips` — on terminated inputs whose interpreted machine halts
  within the clock budget, membership in `diagLang clk` is the *negation*
  of the simulated machine's acceptance
- `TM.diagTime_le_poly` — `diagTime C g n ≤ (C + 786) * ((n+1)² * (g n + 1))`

## Implementation notes

Two landed specs do not quite fit and are bridged locally:

* `writeTM` writes `□` under **every work-tape head**, which would corrupt
  the pair tape; `blankOutTM` (mirroring `negOutTM`) blanks output cell 1
  while framing the input and all work tapes exactly.
* `ClockWitness`'s postcondition only guarantees that the output tape is
  `▷`-clean — not that it is restored to blank — so the landed
  `clockedUtmTM_hoareTime_*` (whose precondition demands a blank output
  tape) cannot be applied after `clk`. We re-derive them here with a
  merely `▷`-clean output precondition (`cleanUtmPre`): `initTM` is
  output-idle, so its Hoare triple transports to any clean output tape by
  an output-swap simulation; every other ingredient already accepts a
  clean output tape.
-/


public section

namespace Complexity

namespace TM

open UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- Part 0: `ClockWitness` — the body of `ClockConstructible`, named
-- ════════════════════════════════════════════════════════════════════════

/-- The body of `ClockConstructible`, with the machine and constant
    exposed: `tm` writes the unary clock `regTape (g |x|)` on work tape 6
    within `C * (g |x| + |x| + 1)` steps, framing the rest of the
    diagonalizer's tape layout. See `ClockConstructible` for the design
    discussion. -/
def ClockWitness (tm : TM 8) (C : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (work₀ : Fin 8 → Tape),
    (∀ i, 1 ≤ (work₀ i).head ∧ (work₀ i).read ≠ Γ.start) →
    work₀ (5 : Fin 8) = (Tape.init []).move Dir3.right →
    work₀ (6 : Fin 8) = (Tape.init []).move Dir3.right →
    tm.HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = work₀ ∧
        out.head = 1 ∧ out.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work (6 : Fin 8) = regTape (g x.length) ∧
        out.head = 1 ∧ out.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (C * (g x.length + x.length + 1))

/-- `ClockConstructible` is exactly the existential closure of
    `ClockWitness`. -/
theorem clockConstructible_iff {g : ℕ → ℕ} :
    ClockConstructible g ↔ ∃ (tm : TM 8) (C : ℕ), ClockWitness tm C g :=
  Iff.rfl

-- ════════════════════════════════════════════════════════════════════════
-- Part 1: small tape helpers
-- ════════════════════════════════════════════════════════════════════════

section Helpers

/-- The started blank tape reads `□`. -/
private theorem blankStarted_read :
    ((Tape.init []).move Dir3.right).read = Γ.blank := by
  exact Tape.init_nil_move_right_read

private theorem blankStarted_read_ne_start :
    ((Tape.init []).move Dir3.right).read ≠ Γ.start := by
  rw [blankStarted_read]; decide

/-- A started `ofBool` data tape never reads `▷`. -/
private theorem started_read_ne_start (l : List Bool) :
    ((Tape.init (l.map Γ.ofBool)).move Dir3.right).read ≠ Γ.start := by
  exact Tape.init_ofBool_move_right_read_ne_start l

end Helpers

-- ════════════════════════════════════════════════════════════════════════
-- Part 2: `blankOutTM` — blank output cell 1, framing everything else
-- ════════════════════════════════════════════════════════════════════════

/-- Replace output cell 1 with `□` and halt with the output head parked at
    cell 1. Mirrors `negOutTM` exactly (rewind → right to cell 1 → write →
    halt); unlike `writeTM`, the input tape and all work tapes are exactly
    unchanged (`readBackWrite` writes and `idleDir` moves). -/
def blankOutTM {n : ℕ} : TM n where
  Q := NegOutPhase
  qstart := .rewind
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewind =>
      if oHead = Γ.start then
        (.goRight, fun i => readBackWrite (wHeads i), .blank,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
      else
        (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.left)
    | .goRight =>
      (.write, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .write =>
      (.done, fun i => readBackWrite (wHeads i), .blank,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rewind =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
      · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
        intro h; next hn => exact absurd h hn
    | .goRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .write =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section BlankOut

variable {n : ℕ}

/-- Rewind loop of `blankOutTM` (mirrors `negOutTM`'s). -/
private theorem blankOutTM_rewind_loop
    (inp₀ : Tape) (work₀ : Fin n → Tape) (W : ℕ → Γ)
    (hW0 : W 0 = Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hw : ∀ i, (work₀ i).read ≠ Γ.start) :
    ∀ (h : ℕ) (c : Cfg n (blankOutTM (n := n)).Q),
      c.state = NegOutPhase.rewind →
      c.output.cells = W →
      c.output.head = h →
      c.input = inp₀ → c.work = work₀ →
      ∃ c',
        (blankOutTM (n := n)).reachesIn (h + 1) c c' ∧
        c'.state = NegOutPhase.goRight ∧
        c'.output.head = 1 ∧
        c'.output.cells = W ∧
        c'.input = inp₀ ∧ c'.work = work₀ := by
  intro h
  induction h with
  | zero =>
    intro c hst hcW hhead hin hwk
    have hread : c.output.read = Γ.start := by
      simp [Tape.read, hhead, hcW, hW0]
    have hstep : ∃ c₁, (blankOutTM (n := n)).step c = some c₁ ∧
        c₁.state = NegOutPhase.goRight ∧
        c₁.output.head = 1 ∧ c₁.output.cells = W ∧
        c₁.input = inp₀ ∧ c₁.work = work₀ := by
      simp only [TM.step, ↓reduceIte, hst, blankOutTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)
    obtain ⟨c₁, hstep', hst1, hh1, hc1, hin1, hw1⟩ := hstep
    exact ⟨c₁, .step hstep' .zero, hst1, hh1, hc1, hin1, hw1⟩
  | succ h ih =>
    intro c hst hcW hhead hin hwk
    have hread_ne : c.output.read ≠ Γ.start := by
      simp only [Tape.read, hhead, hcW]
      exact hWns (h + 1) (by omega)
    have hstep : ∃ c₁, (blankOutTM (n := n)).step c = some c₁ ∧
        c₁.state = NegOutPhase.rewind ∧
        c₁.output.head = h ∧ c₁.output.cells = W ∧
        c₁.input = inp₀ ∧ c₁.work = work₀ := by
      simp only [TM.step, ↓reduceIte, hst, blankOutTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      · dsimp only []
        rw [tape_readBackWrite_preserves c.output Dir3.left (Or.inr hread_ne), hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)
    obtain ⟨c₁, hstep', hst1, hh1, hc1, hin1, hw1⟩ := hstep
    obtain ⟨c', hreach, hst', hh', hc', hin', hw'⟩ := ih c₁ hst1 hc1 hh1 hin1 hw1
    exact ⟨c', .step hstep' hreach, hst', hh', hc', hin', hw'⟩

/-- Buffer step of `blankOutTM` at cell 1 (contents preserved). -/
private theorem blankOutTM_goRight_step
    (inp₀ : Tape) (work₀ : Fin n → Tape) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hw : ∀ i, (work₀ i).read ≠ Γ.start)
    (c : Cfg n (blankOutTM (n := n)).Q)
    (hst : c.state = NegOutPhase.goRight)
    (hcW : c.output.cells = W) (hhead : c.output.head = 1)
    (hin : c.input = inp₀) (hwk : c.work = work₀) :
    ∃ c', (blankOutTM (n := n)).step c = some c' ∧
      c'.state = NegOutPhase.write ∧
      c'.output = c.output ∧
      c'.input = inp₀ ∧ c'.work = work₀ := by
  have hread_ne : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hhead, hcW]
    exact hWns 1 le_rfl
  simp only [TM.step, hst, blankOutTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · dsimp only []; exact transitionTape_eq_self hread_ne
  · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
  · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)

/-- Write step of `blankOutTM`: blank cell 1 and halt. -/
private theorem blankOutTM_write_step
    (inp₀ : Tape) (work₀ : Fin n → Tape) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hw : ∀ i, (work₀ i).read ≠ Γ.start)
    (c : Cfg n (blankOutTM (n := n)).Q)
    (hst : c.state = NegOutPhase.write)
    (hcW : c.output.cells = W) (hhead : c.output.head = 1)
    (hin : c.input = inp₀) (hwk : c.work = work₀) :
    ∃ c', (blankOutTM (n := n)).step c = some c' ∧
      (blankOutTM (n := n)).halted c' ∧
      c'.output.head = 1 ∧
      c'.output.cells = Function.update W 1 Γ.blank ∧
      c'.input = inp₀ ∧ c'.work = work₀ := by
  have hread_ne : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hhead, hcW]
    exact hWns 1 le_rfl
  have hoDir : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, hread_ne]
  simp only [TM.step, hst, blankOutTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [hoDir, Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
  · dsimp only []
    simp [hoDir, Tape.writeAndMove, Tape.move, Tape.write, hhead, hcW]
  · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
  · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)

/-- **`blankOutTM` specification** (ghost form, exact frames). Starting from
    pinned tapes `inp₀`/`work₀`/`out₀` with a well-formed output tape (cell 0
    is `▷`, no `▷` at cells ≥ 1, head ≤ `B`) and no tape head resting on `▷`,
    `blankOutTM` halts within `B + 3` steps having blanked output cell 1,
    all other output cells unchanged, output head parked at cell 1, and the
    input and work tapes exactly unchanged. -/
theorem blankOutTM_hoareTime (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (B : ℕ)
    (h0 : out₀.cells 0 = Γ.start) (hns : ∀ j, 1 ≤ j → out₀.cells j ≠ Γ.start)
    (hB : out₀.head ≤ B)
    (hinp : inp₀.read ≠ Γ.start) (hw : ∀ i, (work₀ i).read ≠ Γ.start) :
    (blankOutTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧
        out.cells = Function.update out₀.cells 1 Γ.blank ∧
        out.head = 1)
      (B + 3) := by
  intro inp work out ⟨hinp_eq, hwork_eq, hout_eq⟩
  subst inp; subst work; subst out
  obtain ⟨c₁, hr1, hst1, hh1, hc1, hin1, hw1⟩ :=
    blankOutTM_rewind_loop inp₀ work₀ out₀.cells h0 hns hinp hw out₀.head
      { state := NegOutPhase.rewind, input := inp₀, work := work₀, output := out₀ }
      rfl rfl rfl rfl rfl
  obtain ⟨c₂, hs2, hst2, hout2, hin2, hw2⟩ :=
    blankOutTM_goRight_step inp₀ work₀ out₀.cells hns hinp hw c₁ hst1 hc1 hh1 hin1 hw1
  obtain ⟨c₃, hs3, hhalt, hh3, hc3, hin3, hw3⟩ :=
    blankOutTM_write_step inp₀ work₀ out₀.cells hns hinp hw c₂ hst2
      (by rw [hout2, hc1]) (by rw [hout2, hh1]) hin2 hw2
  exact ⟨c₃, (out₀.head + 1) + 1 + 1, by omega,
    reachesIn_trans _ (reachesIn_trans _ hr1 (.step hs2 .zero)) (.step hs3 .zero),
    hhalt, hin3, hw3, hc3, hh3⟩

end BlankOut

-- ════════════════════════════════════════════════════════════════════════
-- Part 3: `initTM` is output-idle — output-swap simulation
-- ════════════════════════════════════════════════════════════════════════

section InitSwap

/-- `initTM`'s transition inspects the output head only through the
    read-back write and the idle move: on every non-halt state, the target
    state, work writes, input direction, and work directions are
    independent of the output read. -/
private theorem initTM_δ_split (q : InitQ) (hq : q ≠ .done) (i : Γ)
    (w : Fin 6 → Γ) :
    ∃ q' ww inD wD, ∀ o : Γ,
      initTM.δ q i w o = (q', ww, readBackWrite o, inD, wD, idleDir o) := by
  match q with
  | .done => exact absurd rfl hq
  | .start => exact ⟨_, _, _, _, fun o => rfl⟩
  | .readFst p => cases i <;> exact ⟨_, _, _, _, fun o => rfl⟩
  | .readSnd f p =>
    cases i <;> cases f <;>
      first
        | exact ⟨_, _, _, _, fun o => rfl⟩
        | (cases p <;> exact ⟨_, _, _, _, fun o => rfl⟩)
  | .copyX => cases i <;> exact ⟨_, _, _, _, fun o => rfl⟩
  | .copyField =>
    have harm : ∀ o : Γ, initTM.δ .copyField i w o =
        match w 4 with
        | Γ.zero =>
            (InitQ.copyField,
             fun j => if j = 3 then Γw.zero else readBackWrite (w j),
             readBackWrite o, idleDir i,
             fun j => if j = 3 then Dir3.right else if j = 4 then Dir3.right
                      else idleDir (w j),
             idleDir o)
        | Γ.one =>
            (InitQ.copyField,
             fun j => if j = 3 then Γw.one else readBackWrite (w j),
             readBackWrite o, idleDir i,
             fun j => if j = 3 then Dir3.right else if j = 4 then Dir3.right
                      else idleDir (w j),
             idleDir o)
        | Γ.blank =>
            (InitQ.rewindDesc2, fun j => readBackWrite (w j), readBackWrite o,
             idleDir i, fun j => idleDir (w j), idleDir o)
        | Γ.start =>
            (InitQ.done, fun j => readBackWrite (w j), readBackWrite o,
             idleDir i, fun j => idleDir (w j), idleDir o) :=
      fun o => rfl
    rcases h4 : w 4 with _ | _ | _ | _ <;>
      exact ⟨_, _, _, _, fun o => by rw [harm o, h4]; rfl⟩
  | .rewindDesc =>
    have harm : ∀ o : Γ, initTM.δ .rewindDesc i w o =
        if w 4 = Γ.start then
          (InitQ.copyField, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 4 then Dir3.right else idleDir (w j), idleDir o)
        else
          (InitQ.rewindDesc, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 4 then Dir3.left else idleDir (w j), idleDir o) :=
      fun o => rfl
    by_cases hs : w 4 = Γ.start
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_left hs]; exact rfl⟩
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_right hs]; exact rfl⟩
  | .rewindDesc2 =>
    have harm : ∀ o : Γ, initTM.δ .rewindDesc2 i w o =
        if w 4 = Γ.start then
          (InitQ.rewindState, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 4 then Dir3.right else idleDir (w j), idleDir o)
        else
          (InitQ.rewindDesc2, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 4 then Dir3.left else idleDir (w j), idleDir o) :=
      fun o => rfl
    by_cases hs : w 4 = Γ.start
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_left hs]; exact rfl⟩
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_right hs]; exact rfl⟩
  | .rewindState =>
    have harm : ∀ o : Γ, initTM.δ .rewindState i w o =
        if w 3 = Γ.start then
          (InitQ.rewindV0, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 3 then Dir3.right else idleDir (w j), idleDir o)
        else
          (InitQ.rewindState, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 3 then Dir3.left else idleDir (w j), idleDir o) :=
      fun o => rfl
    by_cases hs : w 3 = Γ.start
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_left hs]; exact rfl⟩
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_right hs]; exact rfl⟩
  | .rewindV0 =>
    have harm : ∀ o : Γ, initTM.δ .rewindV0 i w o =
        if w 0 = Γ.start then
          (InitQ.done, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 0 then Dir3.right else idleDir (w j), idleDir o)
        else
          (InitQ.rewindV0, fun j => readBackWrite (w j), readBackWrite o,
           idleDir i,
           fun j => if j = 0 then Dir3.left else idleDir (w j), idleDir o) :=
      fun o => rfl
    by_cases hs : w 0 = Γ.start
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_left hs]; exact rfl⟩
    · exact ⟨_, _, _, _, fun o => by rw [harm o, ite_eq_right hs]; exact rfl⟩

/-- One `initTM` step commutes with replacing the output tape by any other
    tape parked off `▷`; the original output tape is preserved exactly. -/
private theorem initTM_step_swap {c c' : Cfg 6 initTM.Q}
    (h : initTM.step c = some c') (hc : c.output.read ≠ Γ.start)
    (O : Tape) (hO : O.read ≠ Γ.start) :
    initTM.step { c with output := O } = some { c' with output := O } ∧
      c'.output = c.output := by
  have hq := state_ne_qhalt_of_step h
  obtain ⟨q', ww, inD, wD, hδ⟩ :=
    initTM_δ_split c.state hq c.input.read (fun i => (c.work i).read)
  rw [TM.step, ite_eq_right hq, hδ c.output.read] at h
  dsimp only [] at h
  rw [Option.some.injEq] at h
  subst h
  refine ⟨?_, Tape.writeAndMove_readBack_idle_of_ne_start _ hc⟩
  have hq' : ¬ ({ c with output := O } : Cfg 6 initTM.Q).state = initTM.qhalt := hq
  rw [TM.step, ite_eq_right hq', hδ O.read]
  dsimp only []
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, rfl, ?_⟩)
  exact Tape.writeAndMove_readBack_idle_of_ne_start _ hO

/-- Whole runs of `initTM` commute with replacing the output tape by any
    tape parked off `▷`. -/
private theorem initTM_run_swap (O : Tape) (hO : O.read ≠ Γ.start) :
    ∀ {t : ℕ} {c c' : Cfg 6 initTM.Q}, initTM.reachesIn t c c' →
      c.output.read ≠ Γ.start →
      initTM.reachesIn t { c with output := O } { c' with output := O } := by
  intro t c c' h
  induction h with
  | zero => exact fun _ => .zero
  | step hstep hrest ih =>
    intro hc
    obtain ⟨hstep', hout⟩ := initTM_step_swap hstep hc O hO
    exact .step hstep' (ih (by rw [hout]; exact hc))

/-- **`initTM` specification, clean-output form.** The started spec
    (`initTM_hoareTime_started`) transported to an arbitrary `▷`-clean
    output tape: `initTM` is output-idle, so the blank-output run swaps
    its output tape for any clean one. The output tape is returned
    `▷`-clean with head at cell 1. -/
private theorem initTM_hoareTime_clean (α x : List Bool) :
    initTM.HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        (∀ i : Fin 6, work i = (Tape.init []).move Dir3.right) ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head = 1)
      (fun inp work out =>
        inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
        (work 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
          else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (work 0).head = 1 ∧
        (work 1).HoldsExact [] ∧ (work 1).head = 1 ∧
        (work 2).HoldsExact [] ∧ (work 2).head = 1 ∧
        (work 3).HoldsExact (takeField (groupPairs α)).1 ∧ (work 3).head = 1 ∧
        (work 4).HoldsExact (groupPairs α) ∧ (work 4).head = 1 ∧
        (work 5).HoldsExact [] ∧ (work 5).head = 1 ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head = 1)
      (4 * (pair α x).length + 4 * (groupPairs α).length + 24) := by
  rintro inp work out ⟨hic, hih, hw, ho0, hons, hoh⟩
  have hOr : out.read ≠ Γ.start := by
    rw [Tape.read, hoh]
    exact hons 1 le_rfl
  have hblankr : (⟨1, (Tape.init []).cells⟩ : Tape).read ≠ Γ.start :=
    Tape.init_nil_cells_ne_start 1 le_rfl
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    initTM_hoareTime_started α x inp work ⟨1, (Tape.init []).cells⟩
      ⟨hic, hih, hw, rfl, rfl⟩
  have hreach' := initTM_run_swap out hOr hreach hblankr
  obtain ⟨hic', hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h,
    hw5, hw5h, -, -⟩ := hpost
  exact ⟨{ c' with output := out }, t, ht, hreach', hhalt,
    hic', hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h,
    ho0, hons, hoh⟩

end InitSwap

-- ════════════════════════════════════════════════════════════════════════
-- Part 4: the clocked universal machine from a `▷`-clean output tape
--
-- Local re-derivation of `clockedUtmTM_hoareTime_halt` /
-- `clockedUtmTM_hoareTime_timeout` with the output-tape precondition
-- weakened from "exactly blank" to "`▷`-clean, head at cell 1" — the shape
-- the abstract clock witness leaves behind. Mirrors `ClockedUtm.lean`.
-- ════════════════════════════════════════════════════════════════════════

section CleanUtm

/-- Runs never alter the input tape's cells. -/
private theorem reachesIn_input_cells_eq {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c'.input.cells = c.input.cells := by
  intro t
  induction t with
  | zero =>
    intro c c' h
    cases h
    rfl
  | succ t ih =>
    intro c c' h
    cases h with
    | step hstep hrest =>
      next c'' =>
      have h1 : c''.input.cells = c.input.cells := by
        unfold TM.step at hstep
        split at hstep
        · exact absurd hstep (by simp)
        · simp only [Option.some.injEq] at hstep
          subst hstep
          exact Tape.move_cells ..
      rw [ih hrest, h1]

/-- Runs preserve output-tape well-formedness. -/
private theorem reachesIn_output_wf {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c.output.StartInvariant → c'.output.StartInvariant := by
  intro t
  induction t with
  | zero =>
    intro c c' h hwf
    cases h
    exact hwf
  | succ t ih =>
    intro c c' h hwf
    cases h with
    | step hstep hrest =>
      refine ih hrest ?_
      unfold TM.step at hstep
      split at hstep
      · exact absurd hstep (by simp)
      · simp only [Option.some.injEq] at hstep
        subst hstep
        exact hwf.writeAndMove _ _

/-- Writing a `Γw` symbol and moving preserves the structural tape
    invariant. -/
private theorem writeAndMove_tapeInvariant {t : Tape} (h : Tape.StartInvariant t)
    (s : Γw) (d : Dir3) : Tape.StartInvariant (t.writeAndMove s.toΓ d) := by
  obtain ⟨h0, hns⟩ := h
  have hcells : (t.writeAndMove s.toΓ d).cells = (t.write s.toΓ).cells :=
    Tape.move_cells _ _
  constructor
  · rw [hcells]
    unfold Tape.write
    split
    · exact h0
    · next hh =>
      show Function.update t.cells t.head s.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hh)]
      exact h0
  · intro j hj
    rw [hcells]
    unfold Tape.write
    split
    · exact hns j hj
    · show Function.update t.cells t.head s.toΓ j ≠ Γ.start
      rcases eq_or_ne j t.head with rfl | hne
      · rw [Function.update_self]
        exact Γw.toΓ_ne_start s
      · rw [Function.update_of_ne hne]
        exact hns j hj

/-- Runs preserve the work tapes' structural invariant. -/
private theorem reachesIn_work_inv {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      (∀ i, Tape.StartInvariant (c.work i)) → ∀ i, Tape.StartInvariant (c'.work i) := by
  intro t
  induction t with
  | zero =>
    intro c c' h hinv
    cases h
    exact hinv
  | succ t ih =>
    intro c c' h hinv
    cases h with
    | step hstep hrest =>
      refine ih hrest ?_
      unfold TM.step at hstep
      split at hstep
      · exact absurd hstep (by simp)
      · simp only [Option.some.injEq] at hstep
        subst hstep
        intro i
        exact writeAndMove_tapeInvariant (hinv i) _ _

-- ── Fin-7 index bookkeeping ──

private theorem natAdd_eq_clkT (j : Fin 1) : Fin.natAdd 6 j = clkT := by
  obtain ⟨jv, hj⟩ := j
  obtain rfl : jv = 0 := by omega
  rfl

private theorem castAdd_ne_clkT (k : Fin 6) : Fin.castAdd 1 k ≠ clkT := by
  intro h
  have hv : k.val = 6 := congrArg Fin.val h
  have := k.isLt
  omega

private theorem val_lt_of_ne_clkT {k : Fin 7} (h : k ≠ clkT) : k.val < 6 := by
  have h7 := k.isLt
  have hc : (clkT : Fin 7).val = 6 := rfl
  rcases Nat.lt_or_ge k.val 6 with h6 | h6
  · exact h6
  · exact absurd (Fin.ext (by omega : k.val = clkT.val)) h

-- ── register-cell parking ──

private theorem clk_read_ne_start {t : Tape} {v : ℕ}
    (hc : t.cells = regCells v) (hh : t.head = max v 1) :
    t.read ≠ Γ.start := by
  rw [Tape.read, hh, hc]
  exact regCells_ne_start (le_max_right v 1)

private theorem regT_read_ne_start' (V : ℕ) : (regTape V).read ≠ Γ.start := by
  show regCells V 1 ≠ Γ.start
  exact regCells_ne_start le_rfl

-- ── SimInv bookkeeping ──

private theorem simInv_work_reads (α : List Bool)
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) (i : Fin 6) : (work i).read ≠ Γ.start := by
  by_cases hiS : i = stT
  · subst hiS
    obtain ⟨S, hSh, -, -⟩ := hinv.state_syms_ne_blank
    exact SimInv.read_ne_start_of_holdsExact hSh hinv.state_head.ge
  · by_cases hiD : i = dsT
    · subst hiD
      exact SimInv.read_ne_start_of_holdsExact hinv.desc hinv.desc_head.ge
    · exact hinv.others_read i hiS hiD

private theorem simInv_work_wf (α : List Bool)
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) (i : Fin 6) : (work i).StartInvariant := by
  rcases i with ⟨iv, hv⟩
  rcases iv with _ | _ | _ | _ | _ | _ | n
  · exact hinv.vin.startInvariant hinv.wf_in
  · exact hinv.vwk.startInvariant hinv.wf_wk
  · exact hinv.vout.startInvariant hinv.wf_out
  · obtain ⟨S, hSh, -, -⟩ := hinv.state_syms_ne_blank
    exact Tape.HoldsExact.startInvariant hSh
  · exact Tape.HoldsExact.startInvariant hinv.desc
  · exact Tape.HoldsExact.startInvariant hinv.scratch
  · exact absurd hv (by omega)

private theorem work7_reads_ne_clk {α : List Bool}
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {w : Fin 7 → Tape} {out : Tape}
    (hsi : SimInv α mc inp (fun k : Fin 6 => w (Fin.castAdd 1 k)) out) :
    ∀ k : Fin 7, k ≠ clkT → (w k).read ≠ Γ.start := by
  intro k hk
  exact simInv_work_reads α hsi ⟨k.val, val_lt_of_ne_clkT hk⟩

private theorem work7_reads {α : List Bool}
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {w : Fin 7 → Tape} {out : Tape} {v : ℕ}
    (hsi : SimInv α mc inp (fun k : Fin 6 => w (Fin.castAdd 1 k)) out)
    (hc : (w clkT).cells = regCells v) (hh : (w clkT).head = max v 1) :
    ∀ k : Fin 7, (w k).read ≠ Γ.start := by
  intro k
  by_cases hk : k = clkT
  · subst hk
    exact clk_read_ne_start hc hh
  · exact work7_reads_ne_clk hsi k hk

private theorem simInv_with_out {α : List Bool}
    {mc : Cfg 1 (decodeDesc α).toTM.Q}
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (h : SimInv α mc inp work out) {out' : Tape} (hread : out'.read ≠ Γ.start) :
    SimInv α mc inp work out' :=
  ⟨h.vin, h.vwk, h.vout, h.wf_in, h.wf_wk, h.wf_out, h.state, h.state_head,
   h.desc, h.desc_head, h.scratch, h.scratch_head, h.inp_read, hread⟩

private theorem takeField_fst_length_le (l : List Γw) :
    (takeField l).1.length ≤ l.length := by
  rcases takeField_structure l with hsp | ⟨hsp, -⟩
  · have := congrArg List.length hsp
    simp only [List.length_append, List.length_cons] at this
    omega
  · exact le_of_eq (congrArg List.length hsp)

private theorem qhaltField_length_le (l : List Γw) :
    (qhaltField l).length ≤ l.length :=
  le_trans (takeField_fst_length_le (takeField l).2) (takeField_rest_length l)

private theorem simInv_verdict_len (α : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q)
    {inp : Tape} {work : Fin 6 → Tape} {out : Tape}
    (hinv : SimInv α mc inp work out) :
    ∃ stSyms, (work stT).HoldsExact stSyms ∧ (∀ s ∈ stSyms, s ≠ Γw.blank) ∧
      stSyms.length ≤ (groupPairs α).length ∧
      ((stSyms = qhaltField (groupPairs α))
        ↔ mc.state = (decodeDesc α).toTM.qhalt) := by
  obtain ⟨S, hhold, hnb, hwhich⟩ := hinv.state_syms_ne_blank
  refine ⟨S, hhold, hnb, ?_, ?_⟩
  · rcases hwhich with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [bitsToSyms_length, Nat.length_toBits, decodeDesc_w]
      exact takeField_fst_length_le _
    · exact qhaltField_length_le _
  · rcases hwhich with ⟨hlt, rfl⟩ | ⟨hq, rfl⟩
    · rw [verdict_running α hlt]
      constructor
      · intro hv
        exact Fin.val_injective (by
          show mc.state.val = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w)
          exact hv)
      · intro hs
        show mc.state.val = min (decodeDesc α).qhalt (2 ^ (decodeDesc α).w)
        rw [hs]
        rfl
    · exact iff_of_true rfl hq

private theorem output_first_blank_shift {n : ℕ} {tm : TM n} {T : ℕ}
    {x : List Bool} {c' : Cfg n tm.Q}
    (h : tm.reachesIn T (tm.initCfg x) c') :
    ∃ m, m ≤ T ∧ c'.output.cells (m + 1) = Γ.blank ∧
      ∀ j, j < m → c'.output.cells (j + 1) ≠ Γ.blank := by
  classical
  have hblank : c'.output.cells (T + 1) = Γ.blank := by
    rw [reachesIn_output_cells_far h (T + 1) (by show (0 : ℕ) + T < T + 1; omega)]
    show (Tape.init []).cells (T + 1) = Γ.blank
    simp [Tape.init]
  have hP : ∃ m, c'.output.cells (m + 1) = Γ.blank := ⟨T, hblank⟩
  refine ⟨Nat.find hP, ?_, Nat.find_spec hP, fun j hj => Nat.find_min hP hj⟩
  exact Nat.le_of_not_lt fun hcon => (Nat.find_min hP hcon) hblank

-- ── the clean precondition and phase predicates ──

/-- `clockedUtmPre` with the output tape merely `▷`-clean (head at cell 1)
    rather than exactly blank — the shape the abstract clock witness
    guarantees. -/
private def cleanUtmPre (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ inp.head = 1 ∧
    (∀ i : Fin 6, work (Fin.castAdd 1 i) = (Tape.init []).move Dir3.right) ∧
    work clkT = regTape V ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

/-- The six UTM work tapes' shape at the exit of the init phase. -/
private def body6ShapeD (α x : List Bool) (w : Fin 6 → Tape) : Prop :=
  (w 0).cells = (fun k => if k = 0 then Γ.start else if k = 1 then Γ.blank
    else (((x.map Γ.ofBool))[k - 2]?).getD Γ.blank) ∧ (w 0).head = 1 ∧
  (w 1).HoldsExact [] ∧ (w 1).head = 1 ∧
  (w 2).HoldsExact [] ∧ (w 2).head = 1 ∧
  (w 3).HoldsExact (takeField (groupPairs α)).1 ∧ (w 3).head = 1 ∧
  (w 4).HoldsExact (groupPairs α) ∧ (w 4).head = 1 ∧
  (w 5).HoldsExact [] ∧ (w 5).head = 1

private def initPost7D (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    body6ShapeD α x (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1 ∧
    work clkT = regTape V

private def seekPreD (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ 1 ≤ inp.head ∧
    body6ShapeD α x (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
    work clkT = regTape V ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

private def seekPostD (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧ 1 ≤ inp.head ∧
    body6ShapeD α x (fun k : Fin 6 => work (Fin.castAdd 1 k)) ∧
    (work clkT).cells = regCells V ∧ (work clkT).head = max V 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

private def loopPreD (α x : List Bool) (V : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    SimInv α ((decodeDesc α).toTM.initCfg x) inp
      (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells V ∧ (work clkT).head = max V 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

private def loopExitD (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells v ∧ (work clkT).head = max v 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1 ∧ out.cells 1 = Γ.one

private def testExitD (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) : TapePred 7 :=
  fun inp work out =>
    inp.cells = (Tape.init ((pair α x).map Γ.ofBool)).cells ∧
    SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells v ∧ (work clkT).head = max v 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1 ∧
    out.cells 1 = (if mc.state = (decodeDesc α).toTM.qhalt
      then Γ.one else Γ.zero)

private def branchPreD (α : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) : TapePred 7 :=
  fun inp work out =>
    SimInv α mc inp (fun k : Fin 6 => work (Fin.castAdd 1 k)) out ∧
    (work clkT).cells = regCells v ∧ (work clkT).head = max v 1 ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

private theorem body6ShapeD_reads {α x : List Bool} {w : Fin 6 → Tape}
    (h : body6ShapeD α x w) : ∀ k : Fin 6, (w k).read ≠ Γ.start := by
  obtain ⟨hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h⟩ := h
  intro k
  rcases k with ⟨kv, hv⟩
  rcases kv with _ | _ | _ | _ | _ | _ | n
  · show (w 0).read ≠ Γ.start
    rw [Tape.read, hw0h, hw0c]
    simp
  · exact SimInv.read_ne_start_of_holdsExact hw1 hw1h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw2 hw2h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw3 hw3h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw4 hw4h.ge
  · exact SimInv.read_ne_start_of_holdsExact hw5 hw5h.ge
  · exact absurd hv (by omega)

-- ── phase 1: the lifted init ──

private theorem initPhaseD (α x : List Bool) (V : ℕ) :
    (initTM.liftTM 1).HoareTime (cleanUtmPre α x V) (initPost7D α x V)
      (4 * (pair α x).length + 4 * (groupPairs α).length + 24) := by
  have hex : ∀ j : Fin 1, 1 ≤ (regTape V).head ∧ (regTape V).read ≠ Γ.start :=
    fun _ => ⟨le_rfl, regT_read_ne_start' V⟩
  refine (liftTM_hoareTime_frame initTM (fun _ : Fin 1 => regTape V) hex
    (initTM_hoareTime_clean α x)).consequence ?_ ?_ le_rfl
  · rintro inp work out ⟨hic, hih, hw, hclk, ho0, hons, hoh⟩
    exact ⟨⟨hic, hih, hw, ho0, hons, hoh⟩,
      fun j => by rw [natAdd_eq_clkT j]; exact hclk⟩
  · rintro inp work out ⟨⟨hic, hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h,
      hw4, hw4h, hw5, hw5h, ho0, hons, hoh⟩, hpin⟩
    refine ⟨hic, ⟨hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h,
      hw5, hw5h⟩, ho0, hons, hoh, ?_⟩
    rw [← natAdd_eq_clkT ⟨0, Nat.zero_lt_one⟩]
    exact hpin _

private theorem initSeamD (α x : List Bool) (V : ℕ) :
    ∀ inp work out, initPost7D α x V inp work out →
      seekPreD α x V (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hshape, ho0, hons, hoh, hclk⟩
  have hinp0 : inp.cells 0 = Γ.start := by
    rw [hic]
    simp [Tape.init]
  have hout_read : out.read ≠ Γ.start := by
    rw [Tape.read, hoh]
    exact hons 1 le_rfl
  have hwtr : (fun i : Fin 7 => transitionTape (work i)) = work := by
    funext i
    refine transitionTape_eq_self ?_
    by_cases hi : i = clkT
    · subst hi
      rw [hclk]
      exact regT_read_ne_start' V
    · exact body6ShapeD_reads hshape ⟨i.val, val_lt_of_ne_clkT hi⟩
  have hotr : transitionTape out = out := transitionTape_eq_self hout_read
  rw [hwtr, hotr]
  exact ⟨by rw [transitionInput_cells]; exact hic,
    transitionInput_head_ge inp hinp0, hshape, hclk, ho0, hons, hoh⟩

-- ── phase 2: the frontier seek ──

private theorem seekPhaseD (α x : List Bool) (V : ℕ) :
    seekFrontierTM.HoareTime (seekPreD α x V) (seekPostD α x V) (V + 3) := by
  rintro inp work out ⟨hic, hih, hshape, hclk, ho0, hons, hoh⟩
  have hinp : inp.read ≠ Γ.start := by
    rw [Tape.read, hic]
    exact (Tape.StartInvariant.init_ofBool (pair α x)).2 inp.head hih
  have hothers : ∀ i : Fin 7, i ≠ clkT → (work i).read ≠ Γ.start := fun i hi =>
    body6ShapeD_reads hshape ⟨i.val, val_lt_of_ne_clkT hi⟩
  have hout : out.read ≠ Γ.start := by
    rw [Tape.read, hoh]
    exact hons 1 le_rfl
  obtain ⟨c', t, ht, hr, hh, hin', hwoth, hckc, hckh, hout'⟩ :=
    seekFrontierTM_hoareTime V inp work out hclk hinp hothers hout
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hr, hh, ?_, ?_, ?_, hckc, hckh, ?_, ?_, ?_⟩
  · rw [hin']
    exact hic
  · rw [hin']
    exact hih
  · have hproj : (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
        = fun k : Fin 6 => work (Fin.castAdd 1 k) :=
      funext fun k => hwoth _ (castAdd_ne_clkT k)
    rw [hproj]
    exact hshape
  · rw [hout']
    exact ho0
  · rw [hout']
    exact hons
  · rw [hout']
    exact hoh

private theorem seekSeamD (α x : List Bool) (V : ℕ) :
    ∀ inp work out, seekPostD α x V inp work out →
      loopPreD α x V (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hih, hshape, hckc, hckh, ho0, hons, hoh⟩
  have hinp0 : inp.cells 0 = Γ.start := by
    rw [hic]
    simp [Tape.init]
  have hout_read : out.read ≠ Γ.start := by
    rw [Tape.read, hoh]
    exact hons 1 le_rfl
  have hwtr : (fun i : Fin 7 => transitionTape (work i)) = work := by
    funext i
    refine transitionTape_eq_self ?_
    by_cases hi : i = clkT
    · subst hi
      exact clk_read_ne_start hckc hckh
    · exact body6ShapeD_reads hshape ⟨i.val, val_lt_of_ne_clkT hi⟩
  have hotr : transitionTape out = out := transitionTape_eq_self hout_read
  rw [hwtr, hotr]
  obtain ⟨hw0c, hw0h, hw1, hw1h, hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h⟩ :=
    hshape
  refine ⟨by rw [transitionInput_cells]; exact hic, ?_, hckc, hckh, ho0, hons, hoh⟩
  have hsiF := initPost_simInv α x (transitionInput inp)
    (fun k : Fin 6 => work (Fin.castAdd 1 k)) ⟨1, (Tape.init []).cells⟩
    ⟨by rw [transitionInput_cells]; exact hic, hw0c, hw0h, hw1, hw1h,
     hw2, hw2h, hw3, hw3h, hw4, hw4h, hw5, hw5h, rfl, rfl⟩
    (transitionInput_head_ge inp hinp0)
  exact simInv_with_out hsiF hout_read

-- ── phase 3: the clocked loop ──

private theorem loopPhase_haltD (α x : List Bool) (hterm : TerminatedRegion α)
    (V T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    clockedLoop.HoareTime (loopPreD α x V) (loopExitD α x mcF (V - max T 1))
      ((V + 1) * (utmStepTime α + 10)) := by
  rintro inp work out ⟨hic, hinv, hckc, hckh, h0, hns, hoh⟩
  obtain ⟨c', t, ht, hr, hh, hsi', hckc', hckh', h0', hns', hoh', hone'⟩ :=
    (clocked_loop_simulates α x hterm V inp work out hinv hckc hckh
      h0 hns hoh).1 T mcF hTV hrun hhalt
  refine ⟨c', t, le_trans ht (Nat.mul_le_mul_right _ (by omega)), hr, hh,
    (reachesIn_input_cells_eq hr).trans hic,
    hsi', hckc', hckh', h0', hns', hoh', hone'⟩

private theorem loopPhase_timeoutD (α x : List Bool) (hterm : TerminatedRegion α)
    (V : ℕ) (hV : 1 ≤ V) (mcV : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn V ((decodeDesc α).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc α).toTM.halted mcV) :
    clockedLoop.HoareTime (loopPreD α x V) (loopExitD α x mcV 0)
      ((V + 1) * (utmStepTime α + 10)) := by
  rintro inp work out ⟨hic, hinv, hckc, hckh, h0, hns, hoh⟩
  obtain ⟨c', t, ht, hr, hh, hsi', hckc', hckh', h0', hns', hoh', hone'⟩ :=
    (clocked_loop_simulates α x hterm V inp work out hinv hckc hckh
      h0 hns hoh).2 mcV hV hrun hnh
  refine ⟨c', t, ht, hr, hh,
    (reachesIn_input_cells_eq hr).trans hic,
    hsi', hckc', ?_, h0', hns', hoh', hone'⟩
  rw [hckh']
  exact (max_eq_right (Nat.zero_le 1)).symm

private theorem loopSeamD (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) :
    ∀ inp work out, loopExitD α x mc v inp work out →
      loopExitD α x mc v (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hsi, hckc, hckh, h0, hns, hoh, hone⟩
  have h1 : transitionInput inp = inp := transitionInput_eq_self hsi.inp_read
  have h2 : (fun i => transitionTape (work i)) = work :=
    funext fun i => transitionTape_eq_self (work7_reads hsi hckc hckh i)
  have h3 : transitionTape out = out := transitionTape_eq_self hsi.out_read
  rw [h1, h2, h3]
  exact ⟨hic, hsi, hckc, hckh, h0, hns, hoh, hone⟩

-- ── phase 4a: the lifted halt test ──

private theorem testPhaseD (α x : List Bool) (mc : Cfg 1 (decodeDesc α).toTM.Q)
    (v : ℕ) :
    (haltTestTM.liftTM 1).HoareTime (loopExitD α x mc v) (testExitD α x mc v)
      (4 * (groupPairs α).length + 12) := by
  rintro inp work out ⟨hic, hsi, hckc, hckh, hoc0, hons, hoh, -⟩
  obtain ⟨S, hSh, hSnb, hSlen, hSiff⟩ := simInv_verdict_len α mc hsi
  have h6 := haltTestTM_hoareTime S (groupPairs α) hSnb inp
    (fun k : Fin 6 => work (Fin.castAdd 1 k)) out
    hSh hsi.state_head hsi.desc hsi.desc_head hoc0 hons hoh hsi.inp_read
    (fun k h3 h4 => hsi.others_read k h3 h4)
  have hex : ∀ j : Fin 1, 1 ≤ (work clkT).head ∧ (work clkT).read ≠ Γ.start :=
    fun _ => ⟨by rw [hckh]; exact le_max_right v 1,
      clk_read_ne_start hckc hckh⟩
  obtain ⟨c', t, ht, hr, hh, ⟨hin', hwoth, hw3, hw4, hoc', hoh'⟩, hpin⟩ :=
    liftTM_hoareTime_frame haltTestTM (fun _ : Fin 1 => work clkT) hex h6
      inp work out ⟨⟨rfl, rfl, rfl⟩, fun j => congrArg work (natAdd_eq_clkT j)⟩
  have hwproj : (fun k : Fin 6 => c'.work (Fin.castAdd 1 k))
      = fun k : Fin 6 => work (Fin.castAdd 1 k) := by
    funext k
    by_cases h3 : k = 3
    · subst h3; exact hw3
    · by_cases h4 : k = 4
      · subst h4; exact hw4
      · exact hwoth k h3 h4
  have hwclk : c'.work clkT = work clkT := by
    have h := hpin ⟨0, Nat.zero_lt_one⟩
    rwa [natAdd_eq_clkT] at h
  have hvd : (if S = (takeField (takeField (groupPairs α)).2).1
        then Γ.one else Γ.zero)
      = (if mc.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
    by_cases hq : mc.state = (decodeDesc α).toTM.qhalt
    · rw [ite_eq_left hq, ite_eq_left
        (show S = (takeField (takeField (groupPairs α)).2).1 from hSiff.mpr hq)]
    · rw [ite_eq_right hq, ite_eq_right
        (show ¬S = (takeField (takeField (groupPairs α)).2).1 from
          fun hc => hq (hSiff.mp hc))]
  have hoc1' : c'.output.cells 1
      = (if mc.state = (decodeDesc α).toTM.qhalt then Γ.one else Γ.zero) := by
    rw [hoc', Function.update_self]
    exact hvd
  have hor' : c'.output.read ≠ Γ.start := by
    rw [Tape.read, hoh', hoc1']
    split <;> simp
  refine ⟨c', t, by omega, hr, hh, by rw [hin']; exact hic, ?_, ?_, ?_, ?_, ?_,
    hoh', hoc1'⟩
  · rw [hin', hwproj]
    exact simInv_with_out hsi hor'
  · rw [hwclk]
    exact hckc
  · rw [hwclk]
    exact hckh
  · rw [hoc', Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
    exact hoc0
  · intro j hj
    rw [hoc']
    by_cases hj1 : j = 1
    · subst hj1
      rw [Function.update_self]
      split <;> simp
    · rw [Function.update_of_ne hj1]
      exact hons j hj

-- ── `ifTM` side conditions on the test's exit shape ──

private theorem testExit_allWFD (α x : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) :
    ∀ inp work out, testExitD α x mc v inp work out →
      AllTapesWF inp work out := by
  rintro inp work out ⟨hic, hsi, hckc, hckh, h0, hns, -, -⟩
  refine ⟨?_, ?_, ?_, ?_, h0, hns⟩
  · rw [hic]
    simp [Tape.init]
  · intro j hj
    rw [hic]
    exact (Tape.StartInvariant.init_ofBool (pair α x)).2 j hj
  · intro i
    by_cases hi : i = clkT
    · subst hi
      rw [hckc]
      rfl
    · exact (simInv_work_wf α hsi ⟨i.val, val_lt_of_ne_clkT hi⟩).1
  · intro i j hj
    by_cases hi : i = clkT
    · subst hi
      rw [hckc]
      exact regCells_ne_start hj
    · exact (simInv_work_wf α hsi ⟨i.val, val_lt_of_ne_clkT hi⟩).2 j hj

private theorem testExit_headD (α x : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) :
    ∀ inp work out, testExitD α x mc v inp work out → out.head ≤ 1 := by
  rintro inp work out ⟨-, -, -, -, -, -, hoh, -⟩
  exact le_of_eq hoh

private theorem testExit_to_branchD (α x : List Bool)
    (mc : Cfg 1 (decodeDesc α).toTM.Q) (v : ℕ) :
    ∀ inp work out, testExitD α x mc v inp work out →
      branchPreD α mc v (transitionInput inp)
        (fun i => transitionTape (work i)) ⟨1, out.cells⟩ := by
  rintro inp work out ⟨-, hsi, hckc, hckh, h0, hns, -, -⟩
  have h1 : transitionInput inp = inp := transitionInput_eq_self hsi.inp_read
  have h2 : (fun i => transitionTape (work i)) = work :=
    funext fun i => transitionTape_eq_self (work7_reads hsi hckc hckh i)
  rw [h1, h2]
  have hread : (⟨1, out.cells⟩ : Tape).read ≠ Γ.start := by
    show out.cells 1 ≠ Γ.start
    exact hns 1 le_rfl
  exact ⟨simInv_with_out hsi hread, hckc, hckh, h0, hns, rfl⟩

-- ── phase 4b: the lifted extract (then-branch, halt case) ──

private theorem extractPhaseD (α x : List Bool) (V T m v : ℕ)
    (mcF : Cfg 1 (decodeDesc α).toTM.Q)
    (hmT : m ≤ T) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hmb : mcF.output.cells (m + 1) = Γ.blank)
    (hmnb : ∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) :
    (extractTM.liftTM 1).HoareTime (branchPreD α mcF v)
      (fun _ _ out => ∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1))
      (2 * V + 9) := by
  rintro inp work out ⟨hsi, hckc, hckh, h0, hns, hoh⟩
  have hvout : VShift mcF.output (work (Fin.castAdd 1 2)) := hsi.vout
  have hcells2 : ∀ k, (work (Fin.castAdd 1 2)).cells (k + 2)
      = mcF.output.cells (k + 1) := by
    intro k
    rw [hvout.1]
    simp only [show ¬(k + 2 = 0) by omega, show ¬(k + 2 = 1) by omega,
      ite_false, show k + 2 - 1 = k + 1 by omega]
  have hblank2 : (work (Fin.castAdd 1 2)).cells (m + 2) = Γ.blank := by
    rw [hcells2 m]
    exact hmb
  have hnb2 : ∀ j, j < m → (work (Fin.castAdd 1 2)).cells (j + 2) ≠ Γ.blank := by
    intro j hj
    rw [hcells2 j]
    exact hmnb j hj
  have hwf2 : (work (Fin.castAdd 1 2)).StartInvariant := hvout.startInvariant hsi.wf_out
  have hheadF : mcF.output.head ≤ T := by
    have h := reachesIn_output_head_le hrun
    have h0' : ((decodeDesc α).toTM.initCfg x).output.head = 0 := rfl
    omega
  have hhead2 : (work (Fin.castAdd 1 2)).head ≤ V + 1 := by
    have h := hvout.head_eq
    omega
  have h6 := extractTM_hoareTime m (V + 1) inp
    (fun k : Fin 6 => work (Fin.castAdd 1 k)) out
    hblank2 hnb2 hwf2 hhead2 hvout.head_pos h0 hns hoh hsi.inp_read
    (fun i _ => simInv_work_reads α hsi i)
  have hex : ∀ j : Fin 1, 1 ≤ (work clkT).head ∧ (work clkT).read ≠ Γ.start :=
    fun _ => ⟨by rw [hckh]; exact le_max_right v 1,
      clk_read_ne_start hckc hckh⟩
  obtain ⟨c', t, ht, hr, hh, ⟨hin', hwoth, hw2c, hocopy⟩, hpin⟩ :=
    liftTM_hoareTime_frame extractTM (fun _ : Fin 1 => work clkT) hex h6
      inp work out ⟨⟨rfl, rfl, rfl⟩, fun j => congrArg work (natAdd_eq_clkT j)⟩
  refine ⟨c', t, by omega, hr, hh, ?_⟩
  intro j hj
  rw [hocopy j hj, hcells2 j]

-- ── the clean-output headline triples ──

/-- `clockedUtmTM_hoareTime_halt` from a merely `▷`-clean output tape. -/
private theorem cleanUtm_halt (α x : List Bool)
    (hterm : TerminatedRegion α)
    (V T : ℕ) (mcF : Cfg 1 (decodeDesc α).toTM.Q) (hTV : T ≤ V)
    (hrun : (decodeDesc α).toTM.reachesIn T ((decodeDesc α).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc α).toTM.halted mcF) :
    clockedUtmTM.HoareTime (cleanUtmPre α x V)
      (fun _ _ out => ∃ m, m ≤ T ∧
        mcF.output.cells (m + 1) = Γ.blank ∧
        (∀ j, j < m → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
        (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1)))
      (clockedUtmTime α x V) := by
  obtain ⟨m, hmT, hmb, hmnb⟩ := output_first_blank_shift hrun
  have h_then : (extractTM.liftTM 1).HoareTime (branchPreD α mcF (V - max T 1))
      (fun _ _ out =>
        (∀ j, j ≤ m → out.cells (j + 1) = mcF.output.cells (j + 1)) ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (2 * V + 9) := by
    refine HoareTime.with_output_wf
      (extractPhaseD α x V T m (V - max T 1) mcF hmT hTV hrun hmb hmnb) ?_
    rintro inp work out ⟨-, -, -, h0, hns, -⟩
    exact ⟨h0, hns⟩
  have h_else : (writeTM Γw.one : TM 7).HoareTime (fun _ _ _ => False)
      (fun _ _ _ => False) (2 * V + 9) := fun _ _ _ h => h.elim
  have h_if : (ifTM (haltTestTM.liftTM 1) (extractTM.liftTM 1)
      (writeTM Γw.one)).HoareTime (loopExitD α x mcF (V - max T 1))
      (fun _ _ out => ∃ m', m' ≤ T ∧
        mcF.output.cells (m' + 1) = Γ.blank ∧
        (∀ j, j < m' → mcF.output.cells (j + 1) ≠ Γ.blank) ∧
        (∀ j, j ≤ m' → out.cells (j + 1) = mcF.output.cells (j + 1)))
      (4 * (groupPairs α).length + 12 + 1 + (2 * V + 9) + 5) := by
    refine HoareTime.mono_bound
      (ifTM_hoareTime (haltTestTM.liftTM 1) (extractTM.liftTM 1)
        (writeTM Γw.one)
        (testPhaseD α x mcF (V - max T 1))
        (testExit_allWFD α x mcF (V - max T 1))
        (testExit_headD α x mcF (V - max T 1)) ?_ ?_ h_then h_else ?_ ?_)
      (le_of_eq (by rw [Nat.max_self]))
    · rintro inp work out htest -
      exact testExit_to_branchD α x mcF (V - max T 1) inp work out htest
    · rintro inp work out ⟨-, -, -, -, -, -, -, hcell1⟩ hne
      rw [ite_eq_left hhalt] at hcell1
      exact absurd hcell1 hne
    · rintro inp work out ⟨hcopy, h0, hns⟩
      refine ⟨m, hmT, hmb, hmnb, ?_⟩
      intro j hj
      rw [transitionTape_cells out hns]
      exact hcopy j hj
    · exact fun _ _ _ h => h.elim
  refine HoareTime.mono_bound
    (seqTM_hoareTime (initTM.liftTM 1) _ (initPhaseD α x V) (initSeamD α x V)
      (seqTM_hoareTime seekFrontierTM _ (seekPhaseD α x V) (seekSeamD α x V)
        (seqTM_hoareTime clockedLoop _
          (loopPhase_haltD α x hterm V T mcF hTV hrun hhalt)
          (loopSeamD α x mcF (V - max T 1)) h_if))) ?_
  unfold clockedUtmTime
  generalize (V + 1) * (utmStepTime α + 10) = L
  omega

/-- `clockedUtmTM_hoareTime_timeout` from a merely `▷`-clean output tape. -/
private theorem cleanUtm_timeout (α x : List Bool)
    (hterm : TerminatedRegion α)
    (V : ℕ) (hV : 1 ≤ V) (mcV : Cfg 1 (decodeDesc α).toTM.Q)
    (hrun : (decodeDesc α).toTM.reachesIn V ((decodeDesc α).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc α).toTM.halted mcV) :
    clockedUtmTM.HoareTime (cleanUtmPre α x V)
      (fun _ _ out => out.cells 1 = Γ.one)
      (clockedUtmTime α x V) := by
  have h_then : (extractTM.liftTM 1).HoareTime (fun _ _ _ => False)
      (fun _ _ _ => False) (2 * V + 9) := fun _ _ _ h => h.elim
  have h_else : (writeTM Γw.one).HoareTime (branchPreD α mcV 0)
      (fun _ _ out => out.cells 1 = Γw.one.toΓ ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (2 * V + 9) := by
    refine HoareTime.mono_bound (HoareTime.with_output_wf
      ((writeTM_hoareTime Γw.one 1).weaken_pre ?_) ?_) (by omega)
    · rintro inp work out ⟨-, -, -, h0, hns, hoh⟩
      exact ⟨h0, hns, le_of_eq hoh⟩
    · rintro inp work out ⟨-, -, -, h0, hns, -⟩
      exact ⟨h0, hns⟩
  have h_if : (ifTM (haltTestTM.liftTM 1) (extractTM.liftTM 1)
      (writeTM Γw.one)).HoareTime (loopExitD α x mcV 0)
      (fun _ _ out => out.cells 1 = Γ.one)
      (4 * (groupPairs α).length + 12 + 1 + (2 * V + 9) + 5) := by
    refine HoareTime.mono_bound
      (ifTM_hoareTime (haltTestTM.liftTM 1) (extractTM.liftTM 1)
        (writeTM Γw.one)
        (testPhaseD α x mcV 0) (testExit_allWFD α x mcV 0)
        (testExit_headD α x mcV 0) ?_ ?_ h_then h_else ?_ ?_)
      (le_of_eq (by rw [Nat.max_self]))
    · rintro inp work out ⟨-, -, -, -, -, -, -, hcell1⟩ hone
      rw [hcell1, ite_eq_right hnh] at hone
      exact absurd hone (by decide)
    · rintro inp work out htest -
      exact testExit_to_branchD α x mcV 0 inp work out htest
    · exact fun _ _ _ h => h.elim
    · rintro inp work out ⟨h1, h0, hns⟩
      rw [transitionTape_cells out hns]
      exact h1
  refine HoareTime.mono_bound
    (seqTM_hoareTime (initTM.liftTM 1) _ (initPhaseD α x V) (initSeamD α x V)
      (seqTM_hoareTime seekFrontierTM _ (seekPhaseD α x V) (seekSeamD α x V)
        (seqTM_hoareTime clockedLoop _
          (loopPhase_timeoutD α x hterm V hV mcV hrun hnh)
          (loopSeamD α x mcV 0) h_if))) ?_
  unfold clockedUtmTime
  generalize (V + 1) * (utmStepTime α + 10) = L
  omega

end CleanUtm

-- ════════════════════════════════════════════════════════════════════════
-- Part 5: the diagonalizer, its language, and its time bound
-- ════════════════════════════════════════════════════════════════════════

/-- **The time-hierarchy diagonalizer.** Build `pair x x` on tape 7; check
    `TerminatedRegion x` (malformed inputs output `0`); otherwise blank the
    verdict cell, build the clock `regTape (g |x|)` on tape 6 (`clk`), run the
    clocked universal machine on the self-pair, and negate output cell 1. -/
def diagTM (clk : TM 8) : TM 8 :=
  seqTM pairSelfTM
    (ifTM UTMBody.termCheckTM
      (seqTM blankOutTM
        (seqTM clk (seqTM (retargetInput UTMBody.clockedUtmTM) negOutTM)))
      (writeTM Γw.zero))

/-- The language the diagonalizer decides: inputs on which it halts with
    `1` at output cell 1. -/
def diagLang (clk : TM 8) : Language :=
  {x | ∃ (c : Cfg 8 (diagTM clk).Q) (t : ℕ),
    (diagTM clk).reachesIn t ((diagTM clk).initCfg x) c ∧
    (diagTM clk).halted c ∧ c.output.cells 1 = Γ.one}

/-- The diagonalizer's running-time bound (a closed form; see
    `diagTime_le_poly` for the clean polynomial bound). -/
def diagTime (C : ℕ) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  C * (g n + n + 1) + 2 * ((g n + 1) * (240 * (n + 1) ^ 2 + 10))
    + 6 * g n + 65 * n + 215

/-- Coarse closed-form bound for `clockedUtmTime x x V` at `n = |x|`. -/
private def utmB (n V : ℕ) : ℕ :=
  (V + 1) * (240 * (n + 1) ^ 2 + 10) + 3 * V + 20 * n + 65

private theorem clockedUtmTime_le (x : List Bool) (V : ℕ) :
    clockedUtmTime x x V ≤ utmB x.length V := by
  have h1 := utmStepTime_le_sq x
  have h2 := groupPairs_length_le x
  have h3 : (pair x x).length = 3 * x.length + 2 := by
    rw [pair_length]; omega
  have hP : (V + 1) * (utmStepTime x + 10)
      ≤ (V + 1) * (240 * (x.length + 1) ^ 2 + 10) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold clockedUtmTime utmB
  rw [h3]
  omega

-- ════════════════════════════════════════════════════════════════════════
-- Part 6: run uniqueness and membership
-- ════════════════════════════════════════════════════════════════════════

section RunUnique

private theorem step_none_of_halted {n : ℕ} {tm : TM n} {c : Cfg n tm.Q}
    (h : tm.halted c) : tm.step c = none := by
  unfold TM.step
  rw [ite_eq_left h]

/-- A halted endpoint absorbs longer runs: any run at least as long as a
    halting run ends at the same configuration. -/
private theorem run_unique_of_halted {n : ℕ} {tm : TM n} :
    ∀ {t₂ t₁ : ℕ} {c₀ c₁ c₂ : Cfg n tm.Q},
      tm.reachesIn t₁ c₀ c₁ → tm.halted c₁ → t₁ ≤ t₂ →
      tm.reachesIn t₂ c₀ c₂ → c₂ = c₁ := by
  intro t₂
  induction t₂ with
  | zero =>
    intro t₁ c₀ c₁ c₂ h₁ _ ht h₂
    obtain rfl : t₁ = 0 := by omega
    cases h₁
    cases h₂
    rfl
  | succ t₂ ih =>
    intro t₁ c₀ c₁ c₂ h₁ hh ht h₂
    cases h₂ with
    | step hs₂ hrest₂ =>
      cases h₁ with
      | zero =>
        rw [step_none_of_halted hh] at hs₂
        exact absurd hs₂ (by simp)
      | step hs₁ hrest₁ =>
        have heq : some _ = some _ := hs₁.symm.trans hs₂
        rw [Option.some.injEq] at heq
        subst heq
        exact ih hrest₁ hh (by omega) hrest₂

/-- Membership in `diagLang clk` is decided by any halting run from the
    initial configuration. -/
private theorem diag_mem_iff (clk : TM 8) {x : List Bool}
    {c : Cfg 8 (diagTM clk).Q} {t : ℕ}
    (hrun : (diagTM clk).reachesIn t ((diagTM clk).initCfg x) c)
    (hhalt : (diagTM clk).halted c) :
    x ∈ diagLang clk ↔ c.output.cells 1 = Γ.one := by
  constructor
  · rintro ⟨c', t', hrun', hhalt', hone⟩
    rcases le_total t' t with hle | hle
    · rw [run_unique_of_halted hrun' hhalt' hle hrun]
      exact hone
    · rw [← run_unique_of_halted hrun hhalt hle hrun']
      exact hone
  · intro h
    exact ⟨c, t, hrun, hhalt, h⟩

end RunUnique

-- ════════════════════════════════════════════════════════════════════════
-- Part 7: the diagonalizer's tape layout after `pairSelfTM`
-- ════════════════════════════════════════════════════════════════════════

section DiagLayout

/-- The (frozen) input tape: `x`'s cells, head parked at cell 1. -/
private def inpX (x : List Bool) : Tape := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩

/-- The diagonalizer's work-tape layout after `pairSelfTM`: the self-pair
    started on tape 7, started blank tapes elsewhere. -/
private def workX (x : List Bool) : Fin 8 → Tape :=
  fun i => if i = 7 then (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right
           else (Tape.init []).move Dir3.right

/-- The blank output tape with head parked at cell 1. -/
private def blankT : Tape := ⟨1, (Tape.init []).cells⟩

/-- The output tape holding the `1` verdict at cell 1, head at cell 1. -/
private def outVX : Tape := ⟨1, Function.update (Tape.init []).cells 1 Γ.one⟩

private theorem workX_7 (x : List Bool) :
    workX x 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right := by
  simp [workX]

private theorem workX_ne7 (x : List Bool) {i : Fin 8} (h : i ≠ 7) :
    workX x i = (Tape.init []).move Dir3.right := by
  simp only [workX]
  rw [ite_eq_right h]

private theorem workX_park (x : List Bool) :
    ∀ i, 1 ≤ (workX x i).head ∧ (workX x i).read ≠ Γ.start := by
  intro i
  by_cases h7 : i = 7
  · subst h7
    rw [workX_7]
    exact ⟨le_rfl, started_read_ne_start _⟩
  · rw [workX_ne7 x h7]
    exact ⟨le_rfl, blankStarted_read_ne_start⟩

private theorem workX_inv (x : List Bool) : ∀ i, Tape.StartInvariant (workX x i) := by
  intro i
  by_cases h7 : i = 7
  · subst h7
    rw [workX_7]
    constructor
    · rw [Tape.move_cells]
      rfl
    · intro j hj
      rw [Tape.move_cells]
      exact Tape.init_ofBool_cells_ne_start _ _ hj
  · rw [workX_ne7 x h7]
    constructor
    · rw [Tape.move_cells]
      rfl
    · intro j hj
      rw [Tape.move_cells]
      exact Tape.init_nil_cells_ne_start _ hj

private theorem inpX_read (x : List Bool) : (inpX x).read ≠ Γ.start := by
  show (Tape.init (x.map Γ.ofBool)).cells 1 ≠ Γ.start
  exact Tape.init_ofBool_cells_ne_start x 1 le_rfl

private theorem regT_inv (V : ℕ) : Tape.StartInvariant (regTape V) :=
  ⟨rfl, fun _ hj => regCells_ne_start hj⟩

private theorem outVX_cells0 : outVX.cells 0 = Γ.start := by
  show Function.update (Tape.init []).cells 1 Γ.one 0 = Γ.start
  rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
  rfl

private theorem outVX_ne_start : ∀ j, 1 ≤ j → outVX.cells j ≠ Γ.start := by
  intro j hj
  show Function.update (Tape.init []).cells 1 Γ.one j ≠ Γ.start
  by_cases hj1 : j = 1
  · subst hj1
    rw [Function.update_self]
    decide
  · rw [Function.update_of_ne hj1]
    exact Tape.init_nil_cells_ne_start _ hj

private theorem outVX_collapse :
    Function.update outVX.cells 1 Γ.blank = (Tape.init []).cells := by
  show Function.update (Function.update (Tape.init []).cells 1 Γ.one) 1 Γ.blank
    = (Tape.init []).cells
  rw [Function.update_idem,
    show Γ.blank = (Tape.init []).cells 1 from (Tape.init_nil_cells_succ 0).symm]
  exact Function.update_eq_self _ _

end DiagLayout

-- ════════════════════════════════════════════════════════════════════════
-- Part 8: the then-branch phases
-- ════════════════════════════════════════════════════════════════════════

section ThenPhases

/-- `retargetInput` moves the real input head only idly: a parked real
    input tape is frozen by every step. -/
private theorem retargetInput_step_input {k : ℕ} {M : TM k}
    {c c' : Cfg (k + 1) (retargetInput M).Q}
    (h : (retargetInput M).step c = some c') (hread : c.input.read ≠ Γ.start) :
    c'.input = c.input := by
  have hq := state_ne_qhalt_of_step h
  rw [TM.step, ite_eq_right hq] at h
  dsimp only [] at h
  rw [Option.some.injEq] at h
  subst h
  show c.input.move (idleDir c.input.read) = c.input
  rw [idleDir, ite_eq_right hread]
  rfl

private theorem retargetInput_run_input {k : ℕ} {M : TM k} :
    ∀ {t : ℕ} {c c' : Cfg (k + 1) (retargetInput M).Q},
      (retargetInput M).reachesIn t c c' →
      c.input.read ≠ Γ.start → c'.input = c.input := by
  intro t c c' h
  induction h with
  | zero => exact fun _ => rfl
  | step hstep _ ih =>
    intro hr
    have h1 := retargetInput_step_input hstep hr
    rw [ih (by rw [h1]; exact hr), h1]

/-- The tape shape entering the retargeted clocked UTM: frozen input,
    clock `regTape V` on tape 6, `pairSelfTM`'s layout elsewhere, clean
    output. -/
private def retargetPre (x : List Bool) (V : ℕ) : TapePred 8 :=
  fun inp work out =>
    inp = inpX x ∧
    (∀ i : Fin 8, i ≠ 6 → work i = workX x i) ∧ work 6 = regTape V ∧
    out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
    out.head = 1

/-- The retargeted view of `retargetPre` realizes the clocked UTM's clean
    precondition. -/
private theorem retargetPre_to_inner (x : List Bool) (V : ℕ)
    {work : Fin 8 → Tape} {out : Tape}
    (hwoth : ∀ i : Fin 8, i ≠ 6 → work i = workX x i) (hw6 : work 6 = regTape V)
    (ho0 : out.cells 0 = Γ.start) (hons : ∀ j, 1 ≤ j → out.cells j ≠ Γ.start)
    (hoh : out.head = 1) :
    cleanUtmPre x x V (work ⟨7, by omega⟩)
      (fun i : Fin 7 => work ⟨i.val, by omega⟩) out := by
  have h7 : work (7 : Fin 8)
      = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right := by
    rw [hwoth 7 (by decide), workX_7]
  refine ⟨?_, ?_, ?_, ?_, ho0, hons, hoh⟩
  · show (work ⟨7, by omega⟩).cells = _
    rw [show work ⟨7, by omega⟩ = work (7 : Fin 8) from rfl, h7, Tape.move_cells]
  · show (work ⟨7, by omega⟩).head = 1
    rw [show work ⟨7, by omega⟩ = work (7 : Fin 8) from rfl, h7]
    rfl
  · intro i
    show work ⟨(Fin.castAdd 1 i).val, by omega⟩ = (Tape.init []).move Dir3.right
    have hlt : i.val < 6 := i.isLt
    have hne6 : (⟨(Fin.castAdd 1 i).val, by omega⟩ : Fin 8) ≠ 6 := by
      refine Fin.ne_of_val_ne ?_
      show i.val ≠ 6
      omega
    have hne7 : (⟨(Fin.castAdd 1 i).val, by omega⟩ : Fin 8) ≠ 7 := by
      refine Fin.ne_of_val_ne ?_
      show i.val ≠ 7
      omega
    rw [hwoth _ hne6, workX_ne7 x hne7]
  · show work ⟨(clkT).val, by omega⟩ = regTape V
    exact hw6

/-- The retargeted clocked-UTM phase, halting case: output cell 1 ends up
    agreeing with the interpreted machine's output cell 1. -/
private theorem retargetPhase_halt (x : List Bool) (hterm : TerminatedRegion x)
    (V T : ℕ) (mcF : Cfg 1 (decodeDesc x).toTM.Q) (hTV : T ≤ V)
    (hrun : (decodeDesc x).toTM.reachesIn T ((decodeDesc x).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc x).toTM.halted mcF) :
    (retargetInput clockedUtmTM).HoareTime (retargetPre x V)
      (fun inp work out =>
        inp = inpX x ∧ (∀ i, Tape.StartInvariant (work i)) ∧
        out.cells 1 = mcF.output.cells 1 ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head ≤ utmB x.length V + 1)
      (utmB x.length V) := by
  have hpre_inp : ∀ inp work out, cleanUtmPre x x V inp work out →
      Tape.StartInvariant inp := by
    rintro inp work out ⟨hic, -, -, -, -, -, -⟩
    constructor
    · rw [hic]
      rfl
    · intro j hj
      rw [hic]
      exact Tape.init_ofBool_cells_ne_start _ _ hj
  have hpre_work : ∀ inp work out, cleanUtmPre x x V inp work out →
      ∀ i, Tape.StartInvariant (work i) := by
    rintro inp work out ⟨-, -, hsix, hclk, -, -, -⟩ i
    by_cases hi : i = clkT
    · subst hi
      rw [hclk]
      exact regT_inv V
    · have hb := hsix ⟨i.val, val_lt_of_ne_clkT hi⟩
      have hcast : Fin.castAdd 1 (⟨i.val, val_lt_of_ne_clkT hi⟩ : Fin 6) = i :=
        Fin.ext rfl
      rw [hcast] at hb
      rw [hb]
      exact ⟨by rw [Tape.move_cells]; rfl,
        fun j hj => by rw [Tape.move_cells]; exact Tape.init_nil_cells_ne_start j hj⟩
  have hpre_out : ∀ inp work out, cleanUtmPre x x V inp work out →
      Tape.StartInvariant out := by
    rintro inp work out ⟨-, -, -, -, h0, hns, -⟩
    exact ⟨h0, hns⟩
  have hRT := retargetInput_hoareTime clockedUtmTM
    (cleanUtm_halt x x hterm V T mcF hTV hrun hhalt) hpre_inp hpre_work hpre_out
  rintro inp work out ⟨rfl, hwoth, hw6, ho0, hons, hoh⟩
  obtain ⟨c', t, ht, hreach, hhalt', hpost⟩ :=
    hRT (inpX x) work out (retargetPre_to_inner x V hwoth hw6 ho0 hons hoh)
  have htU : t ≤ utmB x.length V := le_trans ht (clockedUtmTime_le x V)
  refine ⟨c', t, htU, hreach, hhalt', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact retargetInput_run_input hreach (inpX_read x)
  · refine reachesIn_work_inv hreach ?_
    intro i
    show Tape.StartInvariant (work i)
    by_cases hi : i = 6
    · subst hi
      rw [hw6]
      exact regT_inv V
    · rw [hwoth i hi]
      exact workX_inv x i
  · obtain ⟨vin, iw, ⟨m, hmT, hmb, hmnb, hagree⟩, -, -⟩ := hpost
    have h0m := hagree 0 (Nat.zero_le m)
    simpa using h0m
  · exact (reachesIn_output_wf hreach ⟨ho0, hons⟩).1
  · exact (reachesIn_output_wf hreach ⟨ho0, hons⟩).2
  · have h : c'.output.head ≤ out.head + t := reachesIn_output_head_le hreach
    omega

/-- The retargeted clocked-UTM phase, timeout case: output cell 1 ends up
    holding the timeout sentinel `1`. -/
private theorem retargetPhase_timeout (x : List Bool) (hterm : TerminatedRegion x)
    (V : ℕ) (hV : 1 ≤ V) (mcV : Cfg 1 (decodeDesc x).toTM.Q)
    (hrun : (decodeDesc x).toTM.reachesIn V ((decodeDesc x).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc x).toTM.halted mcV) :
    (retargetInput clockedUtmTM).HoareTime (retargetPre x V)
      (fun inp work out =>
        inp = inpX x ∧ (∀ i, Tape.StartInvariant (work i)) ∧
        out.cells 1 = Γ.one ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head ≤ utmB x.length V + 1)
      (utmB x.length V) := by
  have hpre_inp : ∀ inp work out, cleanUtmPre x x V inp work out →
      Tape.StartInvariant inp := by
    rintro inp work out ⟨hic, -, -, -, -, -, -⟩
    constructor
    · rw [hic]
      rfl
    · intro j hj
      rw [hic]
      exact Tape.init_ofBool_cells_ne_start _ _ hj
  have hpre_work : ∀ inp work out, cleanUtmPre x x V inp work out →
      ∀ i, Tape.StartInvariant (work i) := by
    rintro inp work out ⟨-, -, hsix, hclk, -, -, -⟩ i
    by_cases hi : i = clkT
    · subst hi
      rw [hclk]
      exact regT_inv V
    · have hb := hsix ⟨i.val, val_lt_of_ne_clkT hi⟩
      have hcast : Fin.castAdd 1 (⟨i.val, val_lt_of_ne_clkT hi⟩ : Fin 6) = i :=
        Fin.ext rfl
      rw [hcast] at hb
      rw [hb]
      exact ⟨by rw [Tape.move_cells]; rfl,
        fun j hj => by rw [Tape.move_cells]; exact Tape.init_nil_cells_ne_start j hj⟩
  have hpre_out : ∀ inp work out, cleanUtmPre x x V inp work out →
      Tape.StartInvariant out := by
    rintro inp work out ⟨-, -, -, -, h0, hns, -⟩
    exact ⟨h0, hns⟩
  have hRT := retargetInput_hoareTime clockedUtmTM
    (cleanUtm_timeout x x hterm V hV mcV hrun hnh) hpre_inp hpre_work hpre_out
  rintro inp work out ⟨rfl, hwoth, hw6, ho0, hons, hoh⟩
  obtain ⟨c', t, ht, hreach, hhalt', hpost⟩ :=
    hRT (inpX x) work out (retargetPre_to_inner x V hwoth hw6 ho0 hons hoh)
  have htU : t ≤ utmB x.length V := le_trans ht (clockedUtmTime_le x V)
  refine ⟨c', t, htU, hreach, hhalt', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact retargetInput_run_input hreach (inpX_read x)
  · refine reachesIn_work_inv hreach ?_
    intro i
    show Tape.StartInvariant (work i)
    by_cases hi : i = 6
    · subst hi
      rw [hw6]
      exact regT_inv V
    · rw [hwoth i hi]
      exact workX_inv x i
  · obtain ⟨vin, iw, hone, -, -⟩ := hpost
    exact hone
  · exact (reachesIn_output_wf hreach ⟨ho0, hons⟩).1
  · exact (reachesIn_output_wf hreach ⟨ho0, hons⟩).2
  · have h : c'.output.head ≤ out.head + t := reachesIn_output_head_le hreach
    omega

/-- The final negation phase: with output cell 1 pinned to `s` and the
    tapes parked, `negOutTM` leaves the binary negation of `s = 1` at
    output cell 1 (and a `▷`-clean output tape). -/
private theorem negOutPhase (s : Γ) (B : ℕ) :
    (negOutTM (n := 8)).HoareTime
      (fun inp work out =>
        inp.read ≠ Γ.start ∧
        (∀ i, 1 ≤ (work i).head ∧ (work i).read ≠ Γ.start) ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
        out.head ≤ B ∧ out.cells 1 = s)
      (fun _ _ out =>
        out.cells 1 = (if s = Γ.one then Γ.zero else Γ.one) ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (B + 3) := by
  intro inp work out ⟨hinp, hw, h0, hns, hB, hs⟩
  obtain ⟨c', t, ht, hreach, hhalt, hin', hwk', hoc', hoh'⟩ :=
    negOutTM_hoareTime inp work out B h0 hns hB hinp (fun i => (hw i).2)
      inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨c', t, ht, hreach, hhalt, ?_, ?_, ?_⟩
  · show c'.output.cells 1 = _
    rw [hoc', Function.update_self, hs]
  · rw [hoc', Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
    exact h0
  · intro j hj
    rw [hoc']
    by_cases hj1 : j = 1
    · subst hj1
      rw [Function.update_self]
      split <;> decide
    · rw [Function.update_of_ne hj1]
      exact hns j hj

end ThenPhases

-- ════════════════════════════════════════════════════════════════════════
-- Part 9: the then-branch chains and their seams
-- ════════════════════════════════════════════════════════════════════════

section ThenChain

/-- Total time bound of the then-branch (blank, clock, retargeted UTM,
    negation, plus the three seam steps). -/
private def thenBound (C : ℕ) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  1 + 3 + 1 + (C * (g n + n + 1) + 1 +
    (utmB n (g n) + 1 + (utmB n (g n) + 2 + 3)))

/-- Seam blank → clock. -/
private theorem seamA12 (x : List Bool) :
    ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp = inpX x ∧ work = workX x ∧
       out.cells = Function.update outVX.cells 1 Γ.blank ∧ out.head = 1) →
      ((transitionInput inp).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
       (transitionInput inp).head = 1 ∧
       (fun i => transitionTape (work i)) = workX x ∧
       (transitionTape out).head = 1 ∧
       (transitionTape out).cells 0 = Γ.start ∧
       (∀ j, 1 ≤ j → (transitionTape out).cells j ≠ Γ.start)) := by
  rintro inp work out ⟨rfl, rfl, hoc, hoh⟩
  have hout_eq : out = blankT := by
    refine Tape.ext hoh ?_
    rw [hoc, outVX_collapse]
    rfl
  subst hout_eq
  have hti : transitionInput (inpX x) = inpX x := transitionInput_eq_self (inpX_read x)
  have htw : (fun i => transitionTape (workX x i)) = workX x :=
    funext fun i => transitionTape_eq_self (workX_park x i).2
  have hto : transitionTape blankT = blankT :=
    transitionTape_eq_self (show blankT.read ≠ Γ.start from
      Tape.init_nil_cells_ne_start 1 le_rfl)
  rw [hti, htw, hto]
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun j hj => Tape.init_nil_cells_ne_start j hj⟩

/-- Seam clock → retargeted UTM. -/
private theorem seamA23 (x : List Bool) (V : ℕ) :
    ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
       (∀ i, i ≠ (6 : Fin 8) → work i = workX x i) ∧
       work (6 : Fin 8) = regTape V ∧
       out.head = 1 ∧ out.cells 0 = Γ.start ∧
       (∀ j, 1 ≤ j → out.cells j ≠ Γ.start)) →
      retargetPre x V (transitionInput inp)
        (fun i => transitionTape (work i)) (transitionTape out) := by
  rintro inp work out ⟨hic, hih, hwoth, hw6, hoh, ho0, hons⟩
  have hinp_read : inp.read ≠ Γ.start := by
    rw [Tape.read, hih, hic]
    exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
  have hti : transitionInput inp = inp := transitionInput_eq_self hinp_read
  have htw : (fun i => transitionTape (work i)) = work := by
    funext i
    by_cases hi : i = 6
    · subst hi
      rw [hw6]
      exact transitionTape_eq_self (regT_read_ne_start' V)
    · rw [hwoth i hi]
      exact transitionTape_eq_self (workX_park x i).2
  have hto : transitionTape out = out :=
    transitionTape_eq_self (by rw [Tape.read, hoh]; exact hons 1 le_rfl)
  rw [hti, htw, hto]
  exact ⟨Tape.ext hih hic, hwoth, hw6, ho0, hons, hoh⟩

/-- Seam retargeted UTM → negation. -/
private theorem seamA34 (x : List Bool) (V : ℕ) (s : Γ) :
    ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp = inpX x ∧ (∀ i, Tape.StartInvariant (work i)) ∧
       out.cells 1 = s ∧ out.cells 0 = Γ.start ∧
       (∀ j, 1 ≤ j → out.cells j ≠ Γ.start) ∧
       out.head ≤ utmB x.length V + 1) →
      ((transitionInput inp).read ≠ Γ.start ∧
       (∀ i, 1 ≤ (transitionTape (work i)).head ∧
         (transitionTape (work i)).read ≠ Γ.start) ∧
       (transitionTape out).cells 0 = Γ.start ∧
       (∀ j, 1 ≤ j → (transitionTape out).cells j ≠ Γ.start) ∧
       (transitionTape out).head ≤ utmB x.length V + 2 ∧
       (transitionTape out).cells 1 = s) := by
  rintro inp work out ⟨rfl, hwinv, hs, ho0, hons, hoB⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [transitionInput_eq_self (inpX_read x)]
    exact inpX_read x
  · intro i
    have h0 := (hwinv i).1
    have hns := (hwinv i).2
    have hh := one_le_head_transitionTape (work i) h0
    have hcells := transitionTape_cells (work i) hns
    refine ⟨hh, ?_⟩
    rw [Tape.read, hcells]
    exact hns _ hh
  · rw [transitionTape_cells out hons]
    exact ho0
  · intro j hj
    rw [transitionTape_cells out hons]
    exact hons j hj
  · exact head_transitionTape_le ho0 hoB
  · rw [transitionTape_cells out hons]
    exact hs

/-- The then-branch, halting case: final output cell 1 is the binary
    negation of the interpreted machine's output cell 1. -/
private theorem thenChain_halt (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g) (x : List Bool) (hterm : TerminatedRegion x)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc x).toTM.Q) (hT : T ≤ g x.length)
    (hrun : (decodeDesc x).toTM.reachesIn T ((decodeDesc x).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc x).toTM.halted mcF) :
    (seqTM blankOutTM
      (seqTM clk (seqTM (retargetInput clockedUtmTM) negOutTM))).HoareTime
      (fun inp work out => inp = inpX x ∧ work = workX x ∧ out = outVX)
      (fun _ _ out =>
        out.cells 1 = (if mcF.output.cells 1 = Γ.one then Γ.zero else Γ.one) ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (thenBound C g x.length) := by
  have hA1 := blankOutTM_hoareTime (inpX x) (workX x) outVX 1 outVX_cells0
    outVX_ne_start le_rfl (inpX_read x) (fun i => (workX_park x i).2)
  have hA2 := hclk x (workX x) (workX_park x) (workX_ne7 x (by decide))
    (workX_ne7 x (by decide))
  have hA3 := retargetPhase_halt x hterm (g x.length) T mcF hT hrun hhalt
  have hA4 := negOutPhase (mcF.output.cells 1) (utmB x.length (g x.length) + 2)
  exact seqTM_hoareTime blankOutTM _ hA1
    (by intro inp work out h; exact seamA12 x inp work out h)
    (seqTM_hoareTime clk _ hA2
      (by intro inp work out h; exact seamA23 x (g x.length) inp work out h)
      (seqTM_hoareTime (retargetInput clockedUtmTM) _ hA3
        (by intro inp work out h
            exact seamA34 x (g x.length) (mcF.output.cells 1) inp work out h)
        hA4))

/-- The then-branch, timeout case: final output cell 1 is `0` (the
    negation of the timeout sentinel `1`). -/
private theorem thenChain_timeout (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g) (x : List Bool) (hterm : TerminatedRegion x)
    (hV : 1 ≤ g x.length) (mcV : Cfg 1 (decodeDesc x).toTM.Q)
    (hrun : (decodeDesc x).toTM.reachesIn (g x.length)
      ((decodeDesc x).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc x).toTM.halted mcV) :
    (seqTM blankOutTM
      (seqTM clk (seqTM (retargetInput clockedUtmTM) negOutTM))).HoareTime
      (fun inp work out => inp = inpX x ∧ work = workX x ∧ out = outVX)
      (fun _ _ out =>
        out.cells 1 = Γ.zero ∧
        out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
      (thenBound C g x.length) := by
  have hA1 := blankOutTM_hoareTime (inpX x) (workX x) outVX 1 outVX_cells0
    outVX_ne_start le_rfl (inpX_read x) (fun i => (workX_park x i).2)
  have hA2 := hclk x (workX x) (workX_park x) (workX_ne7 x (by decide))
    (workX_ne7 x (by decide))
  have hA3 := retargetPhase_timeout x hterm (g x.length) hV mcV hrun hnh
  have hA4 := (negOutPhase Γ.one (utmB x.length (g x.length) + 2)).strengthen_post
    (post' := fun _ _ out =>
      out.cells 1 = Γ.zero ∧
      out.cells 0 = Γ.start ∧ (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
    (by rintro inp work out ⟨h1, h0, hns⟩
        refine ⟨?_, h0, hns⟩
        rw [h1, ite_eq_left rfl])
  exact seqTM_hoareTime blankOutTM _ hA1
    (by intro inp work out h; exact seamA12 x inp work out h)
    (seqTM_hoareTime clk _ hA2
      (by intro inp work out h; exact seamA23 x (g x.length) inp work out h)
      (seqTM_hoareTime (retargetInput clockedUtmTM) _ hA3
        (by intro inp work out h
            exact seamA34 x (g x.length) Γ.one inp work out h)
        hA4))

end ThenChain

-- ════════════════════════════════════════════════════════════════════════
-- Part 10: the front (pairSelf + termCheck) and the three case triples
-- ════════════════════════════════════════════════════════════════════════

section CaseTriples

/-- Seam `pairSelfTM` → `termCheckTM`. -/
private theorem frontSeam (x : List Bool) :
    ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
       (∀ i : Fin 8, i ≠ 7 → work i = (Tape.init []).move Dir3.right) ∧
       work 7 = (Tape.init ((pair x x).map Γ.ofBool)).move Dir3.right ∧
       out.cells = (Tape.init []).cells ∧ out.head = 1) →
      ((transitionInput inp).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
       (transitionInput inp).head = 1 ∧
       (fun i => transitionTape (work i)) = workX x ∧
       transitionTape out = blankT) := by
  rintro inp work out ⟨hic, hih, hwoth, hw7, hoc, hoh⟩
  have hinp_read : inp.read ≠ Γ.start := by
    rw [Tape.read, hih, hic]
    exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
  have hti : transitionInput inp = inp := transitionInput_eq_self hinp_read
  have hout_eq : out = blankT := Tape.ext hoh hoc
  subst hout_eq
  have hto : transitionTape blankT = blankT :=
    transitionTape_eq_self (show blankT.read ≠ Γ.start from
      Tape.init_nil_cells_ne_start 1 le_rfl)
  refine ⟨by rw [hti]; exact hic, by rw [hti]; exact hih, ?_, hto⟩
  funext i
  by_cases hi : i = 7
  · subst hi
    rw [hw7, workX_7]
    exact transitionTape_eq_self (started_read_ne_start _)
  · rw [hwoth i hi, workX_ne7 x hi]
    exact transitionTape_eq_self blankStarted_read_ne_start

/-- The termCheck postcondition is well-formed on every tape. -/
private theorem termPost_wf (x : List Bool) :
    ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
       work = workX x ∧
       out.cells = Function.update blankT.cells 1
         (if terminatedRegionB x then Γ.one else Γ.zero) ∧
       out.head = 1) →
      AllTapesWF inp work out := by
  rintro inp work out ⟨hic, hih, rfl, hoc, hoh⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hic]
    rfl
  · intro j hj
    rw [hic]
    exact Tape.init_ofBool_cells_ne_start x _ hj
  · intro i
    exact (workX_inv x i).1
  · intro i j hj
    exact (workX_inv x i).2 j hj
  · rw [hoc, Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
    rfl
  · intro j hj
    rw [hoc]
    by_cases hj1 : j = 1
    · subst hj1
      rw [Function.update_self]
      split <;> decide
    · rw [Function.update_of_ne hj1]
      exact Tape.init_nil_cells_ne_start _ hj

/-- Routing to the then-branch on well-formed inputs. -/
private theorem toThen_good (x : List Bool) (hb : terminatedRegionB x = true) :
    ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
       work = workX x ∧
       out.cells = Function.update blankT.cells 1
         (if terminatedRegionB x then Γ.one else Γ.zero) ∧
       out.head = 1) →
      out.cells 1 = Γ.one →
      (transitionInput inp = inpX x ∧
       (fun i => transitionTape (work i)) = workX x ∧
       (⟨1, out.cells⟩ : Tape) = outVX) := by
  rintro inp work out ⟨hic, hih, rfl, hoc, hoh⟩ -
  have hinp_read : inp.read ≠ Γ.start := by
    rw [Tape.read, hih, hic]
    exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [transitionInput_eq_self hinp_read]
    exact Tape.ext hih hic
  · funext i
    exact transitionTape_eq_self (workX_park x i).2
  · refine Tape.ext rfl ?_
    show out.cells = outVX.cells
    rw [hoc, hb, ite_eq_left rfl]
    rfl

/-- **Case triple, malformed input**: `terminatedRegionB x = false` routes
    to the else-branch, which writes `0`. -/
private theorem diag_triple_bad (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (x : List Bool) (hb : terminatedRegionB x = false) :
    (diagTM clk).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i : Fin 8, work i = Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.cells 1 = Γ.zero)
      (pairSelfTime x.length + 1 +
        (2 * x.length + 8 + 1 +
          max (thenBound C g x.length) (thenBound C g x.length) + 5)) := by
  have h_test := termCheckTM_hoareTime x (workX x) blankT (workX_park x) rfl
    (fun j hj => Tape.init_nil_cells_ne_start j hj) rfl
  have h_then : (seqTM blankOutTM
      (seqTM clk (seqTM (retargetInput clockedUtmTM) negOutTM))).HoareTime
      (fun _ _ _ => False) (fun _ _ _ => False) (thenBound C g x.length) :=
    fun _ _ _ h => h.elim
  have h_else := HoareTime.mono_bound
    ((writeTM_hoareTime (n := 8) Γw.zero 1).with_output_wf
      (fun _ _ _ h => ⟨h.1, h.2.1⟩))
    (show 1 + 3 ≤ thenBound C g x.length by unfold thenBound; omega)
  have h_if : (ifTM UTMBody.termCheckTM
      (seqTM blankOutTM
        (seqTM clk (seqTM (retargetInput UTMBody.clockedUtmTM) negOutTM)))
      (writeTM Γw.zero)).HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = workX x ∧ out = blankT)
      (fun _ _ out => out.cells 1 = Γ.zero)
      (2 * x.length + 8 + 1 +
        max (thenBound C g x.length) (thenBound C g x.length) + 5) := by
    refine ifTM_hoareTime UTMBody.termCheckTM _ (writeTM Γw.zero) h_test
      (termPost_wf x) (fun inp work out h => le_of_eq h.2.2.2.2)
      ?_ ?_ h_then h_else ?_ ?_
    · rintro inp work out ⟨-, -, -, hoc, -⟩ hone
      rw [hoc, Function.update_self, hb] at hone
      rw [ite_eq_right (by decide)] at hone
      exact absurd hone (by decide)
    · rintro inp work out ⟨-, -, -, hoc, -⟩ -
      refine ⟨?_, ?_, ?_⟩
      · show out.cells 0 = Γ.start
        rw [hoc, Function.update_of_ne (by omega : (0 : ℕ) ≠ 1)]
        rfl
      · intro j hj
        show out.cells j ≠ Γ.start
        rw [hoc]
        by_cases hj1 : j = 1
        · subst hj1
          rw [Function.update_self]
          split <;> decide
        · rw [Function.update_of_ne hj1]
          exact Tape.init_nil_cells_ne_start _ hj
      · show (⟨1, out.cells⟩ : Tape).head ≤ 1
        exact le_rfl
    · exact fun _ _ _ h => h.elim
    · rintro inp work out ⟨h1, h0, hns⟩
      show (transitionTape out).cells 1 = Γ.zero
      rw [transitionTape_cells out hns, h1]
      rfl
  exact seqTM_hoareTime pairSelfTM _ (pairSelfTM_hoareTime x)
    (by intro inp work out h; exact frontSeam x inp work out h) h_if

/-- **Case triple, halt within budget**: the then-branch computes the
    binary negation of the interpreted machine's output cell 1. -/
private theorem diag_triple_halt (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g) (x : List Bool)
    (hb : terminatedRegionB x = true)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc x).toTM.Q) (hT : T ≤ g x.length)
    (hrun : (decodeDesc x).toTM.reachesIn T ((decodeDesc x).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc x).toTM.halted mcF) :
    (diagTM clk).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i : Fin 8, work i = Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.cells 1
        = (if mcF.output.cells 1 = Γ.one then Γ.zero else Γ.one))
      (pairSelfTime x.length + 1 +
        (2 * x.length + 8 + 1 +
          max (thenBound C g x.length) (thenBound C g x.length) + 5)) := by
  have hterm : TerminatedRegion x := (terminatedRegionB_iff x).mp hb
  have h_test := termCheckTM_hoareTime x (workX x) blankT (workX_park x) rfl
    (fun j hj => Tape.init_nil_cells_ne_start j hj) rfl
  have h_then := thenChain_halt clk C g hclk x hterm T mcF hT hrun hhalt
  have h_else : (writeTM Γw.zero : TM 8).HoareTime
      (fun _ _ _ => False) (fun _ _ _ => False) (thenBound C g x.length) :=
    fun _ _ _ h => h.elim
  have h_if : (ifTM UTMBody.termCheckTM
      (seqTM blankOutTM
        (seqTM clk (seqTM (retargetInput UTMBody.clockedUtmTM) negOutTM)))
      (writeTM Γw.zero)).HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = workX x ∧ out = blankT)
      (fun _ _ out => out.cells 1
        = (if mcF.output.cells 1 = Γ.one then Γ.zero else Γ.one))
      (2 * x.length + 8 + 1 +
        max (thenBound C g x.length) (thenBound C g x.length) + 5) := by
    refine ifTM_hoareTime UTMBody.termCheckTM _ (writeTM Γw.zero) h_test
      (termPost_wf x) (fun inp work out h => le_of_eq h.2.2.2.2)
      ?_ ?_ h_then h_else ?_ ?_
    · intro inp work out h hone
      exact toThen_good x hb inp work out h hone
    · rintro inp work out ⟨-, -, -, hoc, -⟩ hne
      refine absurd ?_ hne
      rw [hoc, Function.update_self, ite_eq_left hb]
    · rintro inp work out ⟨h1, h0, hns⟩
      show (transitionTape out).cells 1 = _
      rw [transitionTape_cells out hns]
      exact h1
    · exact fun _ _ _ h => h.elim
  exact seqTM_hoareTime pairSelfTM _ (pairSelfTM_hoareTime x)
    (by intro inp work out h; exact frontSeam x inp work out h) h_if

/-- **Case triple, timeout**: the then-branch negates the timeout sentinel,
    outputting `0`. -/
private theorem diag_triple_timeout (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g) (x : List Bool)
    (hb : terminatedRegionB x = true)
    (hV : 1 ≤ g x.length) (mcV : Cfg 1 (decodeDesc x).toTM.Q)
    (hrun : (decodeDesc x).toTM.reachesIn (g x.length)
      ((decodeDesc x).toTM.initCfg x) mcV)
    (hnh : ¬(decodeDesc x).toTM.halted mcV) :
    (diagTM clk).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        (∀ i : Fin 8, work i = Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.cells 1 = Γ.zero)
      (pairSelfTime x.length + 1 +
        (2 * x.length + 8 + 1 +
          max (thenBound C g x.length) (thenBound C g x.length) + 5)) := by
  have hterm : TerminatedRegion x := (terminatedRegionB_iff x).mp hb
  have h_test := termCheckTM_hoareTime x (workX x) blankT (workX_park x) rfl
    (fun j hj => Tape.init_nil_cells_ne_start j hj) rfl
  have h_then := thenChain_timeout clk C g hclk x hterm hV mcV hrun hnh
  have h_else : (writeTM Γw.zero : TM 8).HoareTime
      (fun _ _ _ => False) (fun _ _ _ => False) (thenBound C g x.length) :=
    fun _ _ _ h => h.elim
  have h_if : (ifTM UTMBody.termCheckTM
      (seqTM blankOutTM
        (seqTM clk (seqTM (retargetInput UTMBody.clockedUtmTM) negOutTM)))
      (writeTM Γw.zero)).HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = workX x ∧ out = blankT)
      (fun _ _ out => out.cells 1 = Γ.zero)
      (2 * x.length + 8 + 1 +
        max (thenBound C g x.length) (thenBound C g x.length) + 5) := by
    refine ifTM_hoareTime UTMBody.termCheckTM _ (writeTM Γw.zero) h_test
      (termPost_wf x) (fun inp work out h => le_of_eq h.2.2.2.2)
      ?_ ?_ h_then h_else ?_ ?_
    · intro inp work out h hone
      exact toThen_good x hb inp work out h hone
    · rintro inp work out ⟨-, -, -, hoc, -⟩ hne
      refine absurd ?_ hne
      rw [hoc, Function.update_self, ite_eq_left hb]
    · rintro inp work out ⟨h1, h0, hns⟩
      show (transitionTape out).cells 1 = Γ.zero
      rw [transitionTape_cells out hns]
      exact h1
    · exact fun _ _ _ h => h.elim
  exact seqTM_hoareTime pairSelfTM _ (pairSelfTM_hoareTime x)
    (by intro inp work out h; exact frontSeam x inp work out h) h_if

/-- The composite front-plus-branch bound is exactly `diagTime`. -/
private theorem diag_bound_le (C : ℕ) (g : ℕ → ℕ) (n : ℕ) :
    pairSelfTime n + 1 +
        (2 * n + 8 + 1 + max (thenBound C g n) (thenBound C g n) + 5)
      ≤ diagTime C g n := by
  rw [Nat.max_self]
  unfold pairSelfTime thenBound utmB diagTime
  generalize C * (g n + n + 1) = A
  generalize (g n + 1) * (240 * (n + 1) ^ 2 + 10) = B
  omega

end CaseTriples

-- ════════════════════════════════════════════════════════════════════════
-- Part 11: the headline theorems
-- ════════════════════════════════════════════════════════════════════════

/-- **The diagonalizer decides its language in time `diagTime C g`.** For
    any clock-constructibility witness `(clk, C)` for `g ≥ 1`, the machine
    `diagTM clk` decides `diagLang clk` within `diagTime C g` steps. -/
theorem diagTM_decidesInTime (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g) (hg1 : ∀ n, 1 ≤ g n) :
    (diagTM clk).DecidesInTime (diagLang clk) (diagTime C g) := by
  intro x
  by_cases hb : terminatedRegionB x = true
  · rcases TM.halt_or_run_dichotomy (decodeDesc x).toTM
        ((decodeDesc x).toTM.initCfg x) (g x.length) with
      ⟨T, mcF, hT, hrun, hhF⟩ | ⟨mcV, hrunV, hnh⟩
    · obtain ⟨c, t, ht, hreach, hhalt, hcell⟩ :=
        diag_triple_halt clk C g hclk x hb T mcF hT hrun hhF
          (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
          ⟨rfl, fun _ => rfl, rfl⟩
      have hmem := diag_mem_iff clk hreach hhalt
      refine ⟨c, t, le_trans ht (diag_bound_le C g x.length), hreach, hhalt,
        fun hin => hmem.mp hin, ?_⟩
      intro hnot
      by_cases hm : mcF.output.cells 1 = Γ.one
      · rw [hcell, ite_eq_left hm]
      · exact absurd (hmem.mpr (by rw [hcell, ite_eq_right hm])) hnot
    · obtain ⟨c, t, ht, hreach, hhalt, hcell⟩ :=
        diag_triple_timeout clk C g hclk x hb (hg1 x.length) mcV hrunV hnh
          (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
          ⟨rfl, fun _ => rfl, rfl⟩
      have hmem := diag_mem_iff clk hreach hhalt
      exact ⟨c, t, le_trans ht (diag_bound_le C g x.length), hreach, hhalt,
        fun hin => hmem.mp hin, fun _ => hcell⟩
  · have hb' : terminatedRegionB x = false := by
      cases hbe : terminatedRegionB x
      · rfl
      · exact absurd hbe hb
    obtain ⟨c, t, ht, hreach, hhalt, hcell⟩ :=
      diag_triple_bad clk C g x hb'
        (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
        ⟨rfl, fun _ => rfl, rfl⟩
    have hmem := diag_mem_iff clk hreach hhalt
    exact ⟨c, t, le_trans ht (diag_bound_le C g x.length), hreach, hhalt,
      fun hin => hmem.mp hin, fun _ => hcell⟩

/-- **The diagonal flip.** On a well-formed input `x` whose interpreted
    machine halts within the clock budget at `mcF`, the diagonalizer
    accepts `x` exactly when the interpreted machine does **not**. -/
theorem diagTM_flips_of_halts (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g)
    (x : List Bool) (hterm : TerminatedRegion x)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc x).toTM.Q) (hT : T ≤ g x.length)
    (hrun : (decodeDesc x).toTM.reachesIn T ((decodeDesc x).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc x).toTM.halted mcF) :
    (x ∈ diagLang clk ↔ mcF.output.cells 1 ≠ Γ.one) := by
  have hb : terminatedRegionB x = true := (terminatedRegionB_iff x).mpr hterm
  obtain ⟨c, t, ht, hreach, hhalt', hcell⟩ :=
    diag_triple_halt clk C g hclk x hb T mcF hT hrun hhalt
      (Tape.init (x.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
      ⟨rfl, fun _ => rfl, rfl⟩
  rw [diag_mem_iff clk hreach hhalt', hcell]
  by_cases hm : mcF.output.cells 1 = Γ.one
  · rw [ite_eq_left hm]
    simp [hm]
  · rw [ite_eq_right hm]
    simp [hm]

set_option linter.unusedVariables false in
/-- Compatibility form of `diagTM_flips_of_halts`. The positivity hypothesis
    is not needed for the flip itself, but remains in this public signature for
    callers of the original theorem. -/
-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem diagTM_flips (clk : TM 8) (C : ℕ) (g : ℕ → ℕ)
    (hclk : ClockWitness clk C g) (hg1 : ∀ n, 1 ≤ g n)
    (x : List Bool) (hterm : TerminatedRegion x)
    (T : ℕ) (mcF : Cfg 1 (decodeDesc x).toTM.Q) (hT : T ≤ g x.length)
    (hrun : (decodeDesc x).toTM.reachesIn T ((decodeDesc x).toTM.initCfg x) mcF)
    (hhalt : (decodeDesc x).toTM.halted mcF) :
    (x ∈ diagLang clk ↔ mcF.output.cells 1 ≠ Γ.one) :=
  diagTM_flips_of_halts clk C g hclk x hterm T mcF hT hrun hhalt

/-- **Polynomial envelope for the diagonalizer's time bound**:
    `diagTime C g n ≤ (C + 786) * ((n + 1)² * (g n + 1))`. -/
theorem diagTime_le_poly (C : ℕ) (g : ℕ → ℕ) :
    ∀ n, diagTime C g n ≤ (C + 786) * ((n + 1) ^ 2 * (g n + 1)) := by
  intro n
  unfold diagTime
  have hP1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hPn : n + 1 ≤ (n + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hG1 : g n + 1 ≤ (n + 1) ^ 2 * (g n + 1) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hPle : (n + 1) ^ 2 ≤ (n + 1) ^ 2 * (g n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h1 : g n + n + 1 ≤ (n + 1) ^ 2 * (g n + 1) := by
    have hmul : (n + 1) * (g n + 1) ≤ (n + 1) ^ 2 * (g n + 1) :=
      Nat.mul_le_mul_right _ hPn
    nlinarith
  have hC : C * (g n + n + 1) ≤ C * ((n + 1) ^ 2 * (g n + 1)) :=
    Nat.mul_le_mul_left _ h1
  have hn1 : n + 1 ≤ (n + 1) ^ 2 * (g n + 1) := le_trans hPn hPle
  have hone : 1 ≤ (n + 1) ^ 2 * (g n + 1) := le_trans hP1 hPle
  nlinarith [hC, hG1, hn1, hone]

end TM

end Complexity
