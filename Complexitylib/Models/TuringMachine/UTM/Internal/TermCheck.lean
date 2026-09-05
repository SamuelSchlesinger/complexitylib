/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Internal.BodyIteration
public import Complexitylib.Models.TuringMachine.Subroutines.Counter

/-!
# `termCheckTM`: deciding `TerminatedRegion` by a single input scan

The body machine's per-iteration theorem (`bodyIteration`) carries the side
condition `TerminatedRegion α` on the encoded description. The time-hierarchy
diagonalizer must decide this property of its own input **by machine**, so it
can route the (malformed) inputs violating it around the universal simulation.

Contents:

1. `terminatedRegionB` — a Boolean version of `TerminatedRegion`, with the
   bridge `terminatedRegionB_iff`.
2. `scanStep`/`ctrlVerdict` — a six-state symbol-level automaton whose
   left-fold over `groupPairs α` computes `terminatedRegionB α`
   (`scanVerdict_eq`): track the two `□` separators of the `takeField`
   decomposition, then inspect the first two symbols of the entry region.
3. `termCheckTM : TM 8` — the machine: a single left-to-right scan of the
   input decoding bit **pairs** into symbols (`symOfPair`) and driving the
   automaton, then an input rewind to cell 1 and a verdict write at output
   cell 1. All 8 work tapes idle throughout.
4. `termCheckTM_hoareTime` — the Hoare specification: `2·|x| + 8` steps,
   input head returned to cell 1, work tapes preserved exactly, verdict
   `Γ.one`/`Γ.zero` at output cell 1 (output head parked back at 1).
-/


public section

namespace Complexity

namespace TM.UTMBody

-- ════════════════════════════════════════════════════════════════════════
-- The Boolean decider and its bridge to `TerminatedRegion`
-- ════════════════════════════════════════════════════════════════════════

/-- Boolean version of `TerminatedRegion`: the entry region (after the two
    `takeField` splits) fails the check exactly when it starts with a `□`
    followed by a non-`□` symbol. -/
def terminatedRegionB (α : List Bool) : Bool :=
  match (takeField (takeField (groupPairs α)).2).2 with
  | Γw.blank :: s :: _ => decide (s = Γw.blank)
  | _ => true

/-- `terminatedRegionB` decides `TerminatedRegion`. -/
theorem terminatedRegionB_iff (α : List Bool) :
    terminatedRegionB α = true ↔ TerminatedRegion α := by
  unfold terminatedRegionB TerminatedRegion
  cases hR : (takeField (takeField (groupPairs α)).2).2 with
  | nil => simp
  | cons s₀ tail =>
    cases tail with
    | nil => cases s₀ <;> simp
    | cons s₁ rest =>
      cases s₀ with
      | blank => cases s₁ <;> simp
      | zero => simp
      | one => simp

-- ════════════════════════════════════════════════════════════════════════
-- The symbol-level scan automaton
-- ════════════════════════════════════════════════════════════════════════

/-- Control of the symbol-level scan deciding `terminatedRegionB`:

* `seek1`/`seek2` — before the first/second `□` separator;
* `look1`/`look2` — examining the first/second symbol of the entry region;
* `good`/`bad` — verdict absorbed (region terminated / not terminated). -/
inductive TermCtrl where
  | seek1 | seek2 | look1 | look2 | good | bad
  deriving DecidableEq

instance : Fintype TermCtrl where
  elems := {.seek1, .seek2, .look1, .look2, .good, .bad}
  complete := fun x => by cases x <;> simp

/-- One decoded desc symbol updates the scan control: `□`s advance through
    the `takeField` structure, the first two region symbols decide the
    verdict, and verdicts are absorbing. -/
def scanStep : TermCtrl → Γw → TermCtrl
  | .seek1, .blank => .seek2
  | .seek1, _ => .seek1
  | .seek2, .blank => .look1
  | .seek2, _ => .seek2
  | .look1, .blank => .look2
  | .look1, _ => .good
  | .look2, .blank => .good
  | .look2, _ => .bad
  | .good, _ => .good
  | .bad, _ => .bad

/-- End-of-stream verdict: only `bad` rejects (a truncated region is fine —
    `TerminatedRegion` needs **two** symbols after the second `□` to fire). -/
def ctrlVerdict : TermCtrl → Bool
  | .bad => false
  | _ => true

private theorem scanStep_good (s : Γw) : scanStep .good s = .good := by
  cases s <;> rfl

private theorem scanStep_bad (s : Γw) : scanStep .bad s = .bad := by
  cases s <;> rfl

private theorem foldl_scanStep_good : ∀ l : List Γw, l.foldl scanStep .good = .good
  | [] => rfl
  | s :: rest => by rw [List.foldl_cons, scanStep_good]; exact foldl_scanStep_good rest

private theorem foldl_scanStep_bad : ∀ l : List Γw, l.foldl scanStep .bad = .bad
  | [] => rfl
  | s :: rest => by rw [List.foldl_cons, scanStep_bad]; exact foldl_scanStep_bad rest

private theorem foldl_scanStep_seek1 (l : List Γw) :
    ctrlVerdict (l.foldl scanStep .seek1)
      = ctrlVerdict ((takeField l).2.foldl scanStep .seek2) := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | blank => rfl
    | zero => exact ih
    | one => exact ih

private theorem foldl_scanStep_seek2 (l : List Γw) :
    ctrlVerdict (l.foldl scanStep .seek2)
      = ctrlVerdict ((takeField l).2.foldl scanStep .look1) := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | blank => rfl
    | zero => exact ih
    | one => exact ih

private theorem foldl_scanStep_look1 : ∀ l : List Γw,
    ctrlVerdict (l.foldl scanStep .look1)
      = match l with
        | Γw.blank :: s :: _ => decide (s = Γw.blank)
        | _ => true
  | [] => rfl
  | [s] => by cases s <;> rfl
  | .zero :: s :: rest => by
      show ctrlVerdict ((s :: rest).foldl scanStep .good) = true
      rw [foldl_scanStep_good]
      rfl
  | .one :: s :: rest => by
      show ctrlVerdict ((s :: rest).foldl scanStep .good) = true
      rw [foldl_scanStep_good]
      rfl
  | .blank :: s :: rest => by
      cases s with
      | blank =>
          show ctrlVerdict (rest.foldl scanStep .good) = decide (Γw.blank = Γw.blank)
          rw [foldl_scanStep_good]; rfl
      | zero =>
          show ctrlVerdict (rest.foldl scanStep .bad) = decide (Γw.zero = Γw.blank)
          rw [foldl_scanStep_bad]; rfl
      | one =>
          show ctrlVerdict (rest.foldl scanStep .bad) = decide (Γw.one = Γw.blank)
          rw [foldl_scanStep_bad]; rfl

/-- **The scan computes the region check**: folding the automaton over the
    decoded symbol stream of `α` and taking the end-of-stream verdict is
    exactly `terminatedRegionB α`. -/
theorem scanVerdict_eq (α : List Bool) :
    ctrlVerdict ((groupPairs α).foldl scanStep .seek1) = terminatedRegionB α := by
  rw [foldl_scanStep_seek1, foldl_scanStep_seek2, foldl_scanStep_look1]
  rfl

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `termCheckTM`:

* `readFst ctrl` — scanning, at the first bit of the current pair;
* `readSnd ctrl b` — scanning, at the second bit of a pair whose first bit
  was `b`;
* `rewind v` — walking the input head back to `▷`, verdict `v` in hand;
* `emit v` — input head at cell 1: write the verdict at output cell 1;
* `done` — halt. -/
inductive TermCheckQ where
  | readFst (ctrl : TermCtrl)
  | readSnd (ctrl : TermCtrl) (b : Bool)
  | rewind (v : Bool)
  | emit (v : Bool)
  | done
  deriving DecidableEq

instance : Fintype TermCheckQ where
  elems :=
    {.readFst .seek1, .readFst .seek2, .readFst .look1, .readFst .look2,
     .readFst .good, .readFst .bad,
     .readSnd .seek1 false, .readSnd .seek1 true,
     .readSnd .seek2 false, .readSnd .seek2 true,
     .readSnd .look1 false, .readSnd .look1 true,
     .readSnd .look2 false, .readSnd .look2 true,
     .readSnd .good false, .readSnd .good true,
     .readSnd .bad false, .readSnd .bad true,
     .rewind false, .rewind true, .emit false, .emit true, .done}
  complete := fun q => by
    match q with
    | .readFst c => cases c <;> simp
    | .readSnd c b => cases c <;> cases b <;> simp
    | .rewind v => cases v <;> simp
    | .emit v => cases v <;> simp
    | .done => simp

/-- **Terminated-region check**: scan the input left to right decoding bit
    pairs into desc symbols (`symOfPair`) and driving `scanStep`; at the
    input's first blank (end of `x`, or a dropped trailing odd bit) take
    `ctrlVerdict`, rewind the input head to cell 1, and write the verdict
    (`1` = terminated, `0` = not) at output cell 1. All 8 work tapes idle
    throughout. -/
def termCheckTM : TM 8 where
  Q := TermCheckQ
  qstart := .readFst .seek1
  qhalt := .done
  δ := fun q iHead wHeads oHead =>
    match q with
    | .readFst ctrl =>
      match iHead with
      | .start =>
          (.readFst ctrl, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | .blank =>
          (.rewind (ctrlVerdict ctrl), fun i => readBackWrite (wHeads i),
           readBackWrite oHead, Dir3.left, fun i => idleDir (wHeads i), idleDir oHead)
      | .zero =>
          (.readSnd ctrl false, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | .one =>
          (.readSnd ctrl true, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .readSnd ctrl b₀ =>
      match iHead with
      | .start =>
          (.readSnd ctrl b₀, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | .blank =>
          (.rewind (ctrlVerdict ctrl), fun i => readBackWrite (wHeads i),
           readBackWrite oHead, Dir3.left, fun i => idleDir (wHeads i), idleDir oHead)
      | .zero =>
          (.readFst (scanStep ctrl (symOfPair b₀ false)),
           fun i => readBackWrite (wHeads i), readBackWrite oHead,
           Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | .one =>
          (.readFst (scanStep ctrl (symOfPair b₀ true)),
           fun i => readBackWrite (wHeads i), readBackWrite oHead,
           Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewind v =>
      if iHead = Γ.start then
        (.emit v, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.rewind v, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.left, fun i => idleDir (wHeads i), idleDir oHead)
    | .emit v =>
        (.done, fun i => readBackWrite (wHeads i), (if v then Γw.one else Γw.zero),
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle q iHead wHeads oHead
  δ_right_of_start := by
    intro q iHead wHeads oHead
    match q with
    | .readFst ctrl =>
      match iHead with
      | .start =>
          exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      | .blank =>
          exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      | .zero =>
          exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      | .one =>
          exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .readSnd ctrl b₀ =>
      match iHead with
      | .start =>
          exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      | .blank =>
          exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      | .zero =>
          exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      | .one =>
          exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .rewind v =>
      dsimp only []
      split
      · exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
      · next hns =>
        exact ⟨fun hi => absurd hi hns, fun i => idleDir_right_of_start,
          idleDir_right_of_start⟩
    | .emit v =>
      exact ⟨idleDir_right_of_start, fun i => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Input-tape cell lemmas
-- ════════════════════════════════════════════════════════════════════════

section TermCheck

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

private theorem termCheck_ne_halt {s : TermCheckQ} {c : Cfg 8 termCheckTM.Q}
    (hst : c.state = s) (h : s ≠ .done) :
    ¬ c.state = termCheckTM.qhalt := by
  rw [hst]
  exact h

/-- `readFst` over the first bit `b` of a pair: remember it, move right. -/
private theorem termCheck_step_readFst_bit (c : Cfg 8 termCheckTM.Q)
    (ctrl : TermCtrl) (b : Bool)
    (hst : c.state = .readFst ctrl) (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .readSnd ctrl b, input := c.input.move .right,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  cases b <;>
  · simp only [Γ.ofBool] at hread
    simp only [termCheckTM, hst, hread]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
    · funext i
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
    · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `readFst` at the input's first blank: end of stream, take the verdict
    and turn left. -/
private theorem termCheck_step_readFst_blank (c : Cfg 8 termCheckTM.Q)
    (ctrl : TermCtrl)
    (hst : c.state = .readFst ctrl) (hread : c.input.read = Γ.blank)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .rewind (ctrlVerdict ctrl), input := c.input.move .left,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  simp only [termCheckTM, hst, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `readSnd` over the second bit `b₁` of a pair: feed `symOfPair b₀ b₁` to
    the automaton, move right. -/
private theorem termCheck_step_readSnd_bit (c : Cfg 8 termCheckTM.Q)
    (ctrl : TermCtrl) (b₀ b₁ : Bool)
    (hst : c.state = .readSnd ctrl b₀) (hread : c.input.read = Γ.ofBool b₁)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .readFst (scanStep ctrl (symOfPair b₀ b₁)),
        input := c.input.move .right, work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  cases b₁ <;>
  · simp only [Γ.ofBool] at hread
    simp only [termCheckTM, hst, hread]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
    · funext i
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
    · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `readSnd` at the input's first blank: the trailing odd bit is dropped
    (as in `groupPairs`), take the verdict and turn left. -/
private theorem termCheck_step_readSnd_blank (c : Cfg 8 termCheckTM.Q)
    (ctrl : TermCtrl) (b₀ : Bool)
    (hst : c.state = .readSnd ctrl b₀) (hread : c.input.read = Γ.blank)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .rewind (ctrlVerdict ctrl), input := c.input.move .left,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  simp only [termCheckTM, hst, hread]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `rewind` off the sentinel: keep walking left. -/
private theorem termCheck_step_rewind_left (c : Cfg 8 termCheckTM.Q) (v : Bool)
    (hst : c.state = .rewind v) (hread : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .rewind v, input := c.input.move .left,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  simp only [termCheckTM, hst, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `rewind` on the sentinel: bounce right to cell 1 and go write. -/
private theorem termCheck_step_rewind_start (c : Cfg 8 termCheckTM.Q) (v : Bool)
    (hst : c.state = .rewind v) (hread : c.input.read = Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .emit v, input := c.input.move .right,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  simp only [termCheckTM, hst, hread, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `emit`: write the verdict at the output head (cell 1) and halt. -/
private theorem termCheck_step_emit (c : Cfg 8 termCheckTM.Q) (v : Bool)
    (hst : c.state = .emit v) (hinp : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hout : c.output.read ≠ Γ.start) :
    termCheckTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output.write (if v then Γ.one else Γ.zero) } := by
  rw [TM.step, ite_eq_right (termCheck_ne_halt hst nofun)]
  simp only [termCheckTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hw i)
  · have hdir : idleDir c.output.read = Dir3.stay := by
      simp [idleDir, hout]
    show c.output.writeAndMove _ (idleDir c.output.read) = _
    rw [hdir]
    cases v <;> rfl

-- ════════════════════════════════════════════════════════════════════════
-- Run lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- **The scan sweep**: from `readFst ctrl` with `m` input bits remaining
    (head at cell `k + 1`), the machine consumes the rest of the input in
    pairs and, `m + 1` steps later, sits in `rewind` holding the verdict of
    the automaton folded over `groupPairs` of the remaining bits, input head
    at cell `|x|`. All work tapes and the output tape are untouched. -/
private theorem termCheck_scan_run :
    ∀ (m k : ℕ) (x : List Bool) (c : Cfg 8 termCheckTM.Q) (ctrl : TermCtrl),
      x.length = k + m →
      c.state = .readFst ctrl →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = k + 1 →
      (∀ i, (c.work i).read ≠ Γ.start) → c.output.read ≠ Γ.start →
      ∃ c', termCheckTM.reachesIn (m + 1) c c' ∧
        c'.state = .rewind (ctrlVerdict ((groupPairs (x.drop k)).foldl scanStep ctrl)) ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length ∧
        c'.work = c.work ∧ c'.output = c.output
  | 0, k, x, c, ctrl => by
    intro hk hst hic hih hw hout
    obtain rfl : k = x.length := by omega
    have hbl : c.input.read = Γ.blank := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_ge x x.length (le_refl _)
    have hstep := termCheck_step_readFst_blank c ctrl hst hbl hw hout
    refine ⟨_, .step hstep .zero, ?_, ?_, ?_, rfl, rfl⟩
    · rw [List.drop_length]
      rfl
    · show (c.input.move .left).cells = _
      rw [Tape.move_cells]
      exact hic
    · show c.input.head - 1 = x.length
      rw [hih]
      omega
  | 1, k, x, c, ctrl => by
    intro hk hst hic hih hw hout
    have hkx : k < x.length := by omega
    have hread : c.input.read = Γ.ofBool x[k] := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_lt x k hkx
    have hstep₁ := termCheck_step_readFst_bit c ctrl x[k] hst hread hw hout
    have hbl : (c.input.move .right).read = Γ.blank := by
      show c.input.cells (c.input.head + 1) = Γ.blank
      rw [hih, hic]
      exact Tape.init_ofBool_cells_ge x (k + 1) (by omega)
    have hstep₂ := termCheck_step_readSnd_blank
      { state := .readSnd ctrl x[k], input := c.input.move .right,
        work := c.work, output := c.output } ctrl x[k] rfl hbl hw hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), ?_, ?_, ?_, rfl, rfl⟩
    · have hdrop : x.drop k = [x[k]] := by
        rw [List.drop_eq_getElem_cons hkx,
          show k + 1 = x.length from by omega, List.drop_length]
      rw [hdrop]
      rfl
    · show ((c.input.move .right).move .left).cells = _
      rw [Tape.move_cells, Tape.move_cells]
      exact hic
    · show c.input.head + 1 - 1 = x.length
      rw [hih]
      omega
  | (m + 2), k, x, c, ctrl => by
    intro hk hst hic hih hw hout
    have hk0 : k < x.length := by omega
    have hk1 : k + 1 < x.length := by omega
    have hread₀ : c.input.read = Γ.ofBool x[k] := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_lt x k hk0
    have hstep₁ := termCheck_step_readFst_bit c ctrl x[k] hst hread₀ hw hout
    have hread₁ : (c.input.move .right).read = Γ.ofBool x[k + 1] := by
      show c.input.cells (c.input.head + 1) = _
      rw [hih, hic]
      exact Tape.init_ofBool_cells_lt x (k + 1) hk1
    have hstep₂ := termCheck_step_readSnd_bit
      { state := .readSnd ctrl x[k], input := c.input.move .right,
        work := c.work, output := c.output } ctrl x[k] x[k + 1] rfl hread₁ hw hout
    obtain ⟨c', hreach, hst', hic', hih', hw', ho'⟩ :=
      termCheck_scan_run m (k + 2) x
        { state := .readFst (scanStep ctrl (symOfPair x[k] x[k + 1])),
          input := (c.input.move .right).move .right,
          work := c.work, output := c.output }
        (scanStep ctrl (symOfPair x[k] x[k + 1]))
        (by omega) rfl
        (by show ((c.input.move .right).move .right).cells = _
            rw [Tape.move_cells, Tape.move_cells]
            exact hic)
        (by show c.input.head + 1 + 1 = k + 2 + 1
            rw [hih])
        hw hout
    refine ⟨c', .step hstep₁ (.step hstep₂ hreach), ?_, hic', hih', hw', ho'⟩
    rw [hst']
    have hdrop : x.drop k = x[k] :: x[k + 1] :: x.drop (k + 2) := by
      rw [List.drop_eq_getElem_cons hk0, List.drop_eq_getElem_cons hk1]
    rw [hdrop]
    rfl

/-- **The input rewind**: from `rewind v` with the input head at cell `h`,
    walk left to the sentinel and bounce to cell 1, reaching `emit v` in
    `h + 1` steps. All work tapes and the output tape are untouched. -/
private theorem termCheck_rewind_run :
    ∀ (h : ℕ) (x : List Bool) (v : Bool) (c : Cfg 8 termCheckTM.Q),
      c.state = .rewind v →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = h →
      (∀ i, (c.work i).read ≠ Γ.start) → c.output.read ≠ Γ.start →
      ∃ c', termCheckTM.reachesIn (h + 1) c c' ∧
        c'.state = .emit v ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = 1 ∧
        c'.work = c.work ∧ c'.output = c.output
  | 0, x, v, c => by
    intro hst hic hih hw hout
    have hrd : c.input.read = Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_cells_zero _
    have hstep := termCheck_step_rewind_start c v hst hrd hw hout
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, rfl, rfl⟩
    · show (c.input.move .right).cells = _
      rw [Tape.move_cells]
      exact hic
    · show c.input.head + 1 = 1
      rw [hih]
  | (h + 1), x, v, c => by
    intro hst hic hih hw hout
    have hrd : c.input.read ≠ Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_ne_start x _ (by omega)
    have hstep := termCheck_step_rewind_left c v hst hrd hw hout
    obtain ⟨c', hreach, hst', hic', hih', hw', ho'⟩ :=
      termCheck_rewind_run h x v
        { state := .rewind v, input := c.input.move .left,
          work := c.work, output := c.output }
        rfl
        (by show (c.input.move .left).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head - 1 = h
            rw [hih]
            omega)
        hw hout
    exact ⟨c', .step hstep hreach, hst', hic', hih', hw', ho'⟩

-- ════════════════════════════════════════════════════════════════════════
-- The Hoare specification
-- ════════════════════════════════════════════════════════════════════════

/-- **`termCheckTM` specification** (ghost-initial-tapes style): started on
    the input tape of `x` with head at cell 1, all work tapes parked
    (head ≥ 1, not reading `▷`) and the output tape `▷`-clean with head at
    cell 1, the machine halts within `2·|x| + 8` steps having written the
    `terminatedRegionB x` verdict (`1` = holds, `0` = fails) at output
    cell 1. The input head returns to cell 1, every work tape is preserved
    exactly, and the output head is parked back at cell 1. -/
theorem termCheckTM_hoareTime (x : List Bool) (work₀ : Fin 8 → Tape) (out₀ : Tape)
    (hw : ∀ i, 1 ≤ (work₀ i).head ∧ (work₀ i).read ≠ Γ.start)
    (hout0 : out₀.cells 0 = Γ.start) (houtns : ∀ j, 1 ≤ j → out₀.cells j ≠ Γ.start)
    (houth : out₀.head = 1) :
    termCheckTM.HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = work₀ ∧
        out.cells = Function.update out₀.cells 1
          (if terminatedRegionB x then Γ.one else Γ.zero) ∧
        out.head = 1)
      (2 * x.length + 8) := by
  rintro inp work out ⟨hic, hih, rfl, rfl⟩
  have hwr : ∀ i, (work i).read ≠ Γ.start := fun i => (hw i).2
  have houtr : out.read ≠ Γ.start := by
    rw [Tape.read, houth]
    exact houtns 1 le_rfl
  -- the scan sweep
  obtain ⟨c₁, hr₁, hst₁, hic₁, hih₁, hw₁, ho₁⟩ :=
    termCheck_scan_run x.length 0 x
      { state := termCheckTM.qstart, input := inp, work := work, output := out }
      .seek1 (by omega) rfl hic (by rw [hih]) hwr houtr
  have hw₁' : c₁.work = work := hw₁
  have ho₁' : c₁.output = out := ho₁
  have hw₁r : ∀ i, (c₁.work i).read ≠ Γ.start := fun i => by
    rw [hw₁']
    exact hwr i
  have ho₁r : c₁.output.read ≠ Γ.start := by
    rw [ho₁']
    exact houtr
  -- the rewind
  obtain ⟨c₂, hr₂, hst₂, hic₂, hih₂, hw₂, ho₂⟩ :=
    termCheck_rewind_run x.length x _ c₁ hst₁ hic₁ hih₁ hw₁r ho₁r
  have hw₂r : ∀ i, (c₂.work i).read ≠ Γ.start := fun i => by
    rw [hw₂]
    exact hw₁r i
  have ho₂r : c₂.output.read ≠ Γ.start := by
    rw [ho₂]
    exact ho₁r
  have hinp₂ : c₂.input.read ≠ Γ.start := by
    rw [Tape.read, hih₂, hic₂]
    exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
  -- the verdict write
  have hstep₃ := termCheck_step_emit c₂ _ hst₂ hinp₂ hw₂r ho₂r
  have hv : ctrlVerdict ((groupPairs (x.drop 0)).foldl scanStep .seek1)
      = terminatedRegionB x := by
    rw [List.drop_zero]
    exact scanVerdict_eq x
  refine ⟨_, x.length + 1 + (x.length + 1 + 1), by omega,
    reachesIn_trans _ hr₁ (reachesIn_trans _ hr₂ (.step hstep₃ .zero)),
    rfl, hic₂, hih₂, ?_, ?_, ?_⟩
  · show c₂.work = work
    rw [hw₂, hw₁']
  · show (c₂.output.write _).cells = _
    rw [hv, ho₂, ho₁', Tape.write, ite_eq_right (by rw [houth]; omega)]
    show Function.update out.cells out.head _ = _
    rw [houth]
  · show (c₂.output.write _).head = 1
    rw [Tape.write_head, ho₂, ho₁', houth]

end TermCheck

end TM.UTMBody

end Complexity
