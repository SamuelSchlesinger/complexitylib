/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Models.TuringMachine.ChoiceTape
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Tape.Encoding
public import Mathlib.Data.Fintype.Prod

/-!
# Scanning several tapes in lockstep with a finite control

Most of what a machine does to a fixed-width register is a scan: check that a layout is
well formed, read a bounded amount of information out of it, compare it against another
register, rewrite it. Each of those is a finite automaton walking the register from left to
right, and none of them can be written with `TM.loopTM`, whose body forgets its control state
between iterations.

`Complexity.Scanner` is that automaton, and `Complexity.TM.twoPassTM` runs it. The scan is two
passes: rightward to the first blank, gathering into the control state, then leftward back to the
left marker, this time checking what it passes against everything the rightward pass learned. A
single verdict bit is left on a result tape. Two passes is what makes the pattern useful — one
pass cannot act on what it has not yet read.

The scan only ever reads. That costs nothing, because on a nondeterministic machine anything that
would have to be computed can instead be guessed and checked — and checking is a scan. Tape
contents are therefore invariant across a scan, which is what keeps its contract short.

All the tapes move together, so a column of the scan is the tuple of symbols under the heads.
Tape `0` is the one whose blank ends the rightward pass; the others are read for as long as it
lasts.

## Main definitions

- `Complexity.Scanner` — a two-pass finite-state transducer over `j + 1` tapes
- `Complexity.TM.twoPassTM` — the machine that runs it
- `Complexity.Scanner.runR`, `Complexity.Scanner.runL`, `Complexity.Scanner.run` — what a scan
  computes
- `Complexity.Scanner.prefixed` — read parameters off the first cells, then run the check they
  choose
- `Complexity.Scanner.bitsStep` — the reader that puts several registers' leading bits in the
  control
- `Complexity.Scanner.chunkRun`, `Complexity.Scanner.chunkStepCell` — folding three columns at a
  time
- `Complexity.Scanner.comap` — run a check on a wider tape set by naming its columns
- `Complexity.Scanner.upTo`, `Complexity.Scanner.after` — freeze a check once it has read its own
  cells, or start it after a prefix, so checks of different lengths and positions share a scan
- `Complexity.Scanner.all`, `Complexity.Scanner.or` — run several checks in one scan, conjoining
  or disjoining their verdicts
- `Complexity.Scanner.eq`, `Complexity.Scanner.eq_range_run` — the comparison scanner, and what
  it decides when restricted to a range of cells
- `Complexity.Scanner.isConst`, `Complexity.Scanner.isConst_cell`,
  `Complexity.Scanner.isNotConst`, `Complexity.Scanner.isNotConst_cell` — checking one cell
  against a fixed symbol, or against its failing to be one
- `Complexity.Scanner.isConst_range_run`, `Complexity.Scanner.isNotConst_range_run` — the same
  over a range of cells, which is how a field is tested for being all zeros
- `Complexity.Scanner.plusOne` — the increment-check scanner
- `Complexity.Scanner.andAll`, `Complexity.Scanner.andSome`, `Complexity.Scanner.andFirst`,
  `Complexity.Scanner.firstCol` — the scanners that combine verdicts

## Main results

- `Complexity.TM.checkTM`, `Complexity.TM.checkTM_hoareTime` — a check run on the whole register
  set, reading the columns its map names
- `Complexity.TM.twoPassCfg_run` — a scan of a length-`len` tape takes `2 * len + 3` steps and
  halts with the automaton's verdict on the result tape, every other tape untouched
- `Complexity.TM.twoPassTM_hoareTime` — the same as a Hoare triple, for composition
- `Complexity.Scanner.eq_run` — the smallest example: comparing two of the tapes
- `Complexity.Scanner.prefixed_run` — a parameterized scan reports what its parameters chose
- `Complexity.Scanner.bitsStep_run` — what the field reader has read
- `Complexity.Scanner.cellFold_chunk` — three cells make a chunk
- `Complexity.Scanner.cellFold_shift`, `Complexity.Scanner.runR_eq_cellFold` — a check proved at
  the start of a scan applies wherever the scan puts it
- `Complexity.Scanner.plusOne_run` — one scan checks that one register holds one more than
  another
- `Complexity.Scanner.andAll_run`, `Complexity.Scanner.andSome_run`,
  `Complexity.Scanner.andFirst_run`, `Complexity.Scanner.firstCol_run` — and one scan reports
  any function of the verdicts
-/

@[expose] public section

namespace Complexity

/-- A two-pass finite-state transducer over `j + 1` tapes scanned in lockstep. The rightward pass
only reads; the leftward pass may rewrite the column it is on. -/
structure Scanner (j : ℕ) where
  /-- The control states of the automaton. -/
  σ : Type
  [decEqσ : DecidableEq σ]
  [finσ : Fintype σ]
  /-- Where the rightward pass starts. -/
  start : σ
  /-- The rightward pass: read a column, update the state. -/
  stepR : σ → (Fin (j + 1) → Γ) → σ
  /-- The leftward pass: read a column, update the state. -/
  stepL : σ → (Fin (j + 1) → Γ) → σ
  /-- The verdict left on the result tape. -/
  emit : σ → Bool

attribute [instance] Scanner.decEqσ Scanner.finσ

namespace Scanner

variable {j : ℕ}

/-- The state after the rightward pass has read cells `1` through `p`. -/
def runR (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) : ℕ → S.σ
  | 0 => S.start
  | p + 1 => S.stepR (runR S cols p) (cols (p + 1))

/-- The state the leftward pass ends in, having read cells `p` down to `1`. -/
def runL (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) : ℕ → S.σ → S.σ
  | 0, s => s
  | p + 1, s => S.runL cols p (S.stepL s (cols (p + 1)))

/-- **What a whole scan computes**: the rightward pass over cells `1 … len`, then the leftward
pass back over `len … 1`. -/
def run (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) (len : ℕ) : S.σ :=
  S.runL cols len (S.runR cols len)

/-! ## Scanners that only read on the way out

When everything a check needs is available before the cells it has to check — which is arranged by
laying the parameters out in the first few cells of the scan and starting the data after them —
the leftward pass has nothing to do. -/

/-- A scanner whose leftward pass is idle. -/
def ofRight {j : ℕ} (τ : Type) [DecidableEq τ] [Fintype τ] (start : τ)
    (step : τ → (Fin (j + 1) → Γ) → τ) (emit : τ → Bool) : Scanner j where
  σ := τ
  start := start
  stepR := step
  stepL s _ := s
  emit := emit

@[simp] theorem ofRight_runL {j : ℕ} (τ : Type) [DecidableEq τ] [Fintype τ] (start : τ)
    (step : τ → (Fin (j + 1) → Γ) → τ) (emit : τ → Bool) (cols : ℕ → Fin (j + 1) → Γ)
    (p : ℕ) (s : τ) : (ofRight τ start step emit).runL cols p s = s := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL]; exact ih _

theorem ofRight_run {j : ℕ} (τ : Type) [DecidableEq τ] [Fintype τ] (start : τ)
    (step : τ → (Fin (j + 1) → Γ) → τ) (emit : τ → Bool) (cols : ℕ → Fin (j + 1) → Γ)
    (len : ℕ) :
    (ofRight τ start step emit).run cols len = (ofRight τ start step emit).runR cols len := by
  rw [run]; apply ofRight_runL

/-! ## Running a scanner on a wider tape set

A check is written against the few registers it reads. Running it on a machine that has many
registers is a matter of saying which columns those are — not of moving the registers next to one
another, and not of giving each check its own copy of them. -/

/-- Read a scanner's columns through a map: the same automaton, run on a wider tape set. -/
def comap {j jj : ℕ} (S : Scanner j) (f : Fin (j + 1) → Fin (jj + 1)) : Scanner jj where
  σ := S.σ
  decEqσ := S.decEqσ
  finσ := S.finσ
  start := S.start
  stepR s cols := S.stepR s (fun i => cols (f i))
  stepL s cols := S.stepL s (fun i => cols (f i))
  emit := S.emit

@[simp] theorem comap_emit {j jj : ℕ} (S : Scanner j) (f : Fin (j + 1) → Fin (jj + 1)) :
    (S.comap f).emit = S.emit := rfl

theorem comap_runR {j jj : ℕ} (S : Scanner j) (f : Fin (j + 1) → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (p : ℕ) :
    (S.comap f).runR cols p = S.runR (fun q i => cols q (f i)) p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [runR, runR, ih]; rfl

theorem comap_runL {j jj : ℕ} (S : Scanner j) (f : Fin (j + 1) → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (p : ℕ) (s : S.σ) :
    (S.comap f).runL cols p s = S.runL (fun q i => cols q (f i)) p s := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL]; exact ih _

/-- **A scanner run through a map reads exactly the columns the map names.** -/
theorem comap_run {j jj : ℕ} (S : Scanner j) (f : Fin (j + 1) → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ) :
    (S.comap f).run cols len = S.run (fun q i => cols q (f i)) len := by
  rw [run, run, comap_runR, comap_runL]

/-! ## Stopping a check early

Checks read different numbers of cells, but a machine's scan has one length. A right-only check
can simply be frozen once it has read the cells it cares about: the columns past that point are
read and discarded, so a short check and a long one can share a scan. -/

/-- A scanner whose leftward pass does nothing — the shape of every check built with
`Complexity.Scanner.ofRight` or `Complexity.Scanner.prefixed`. -/
def RightOnly {j : ℕ} (S : Scanner j) : Prop := ∀ s cols, S.stepL s cols = s

theorem rightOnly_ofRight {j : ℕ} (τ : Type) [DecidableEq τ] [Fintype τ] (start : τ)
    (step : τ → (Fin (j + 1) → Γ) → τ) (emit : τ → Bool) :
    RightOnly (ofRight (j := j) τ start step emit) := fun _ _ => rfl

theorem rightOnly_comap {j jj : ℕ} {S : Scanner j} (h : RightOnly S)
    (f : Fin (j + 1) → Fin (jj + 1)) : RightOnly (S.comap f) := fun s _ => h s _

/-- A right-only scanner's leftward pass leaves the state alone. -/
theorem runL_of_rightOnly {j : ℕ} {S : Scanner j} (hS : RightOnly S)
    (cols : ℕ → Fin (j + 1) → Γ) : ∀ (p : ℕ) (s : S.σ), S.runL cols p s = s := by
  intro p
  induction p with
  | zero => intro s; rfl
  | succ p ih => intro s; simp only [runL]; rw [hS]; exact ih _

/-- The saturating position counter a frozen check carries. -/
def upToIdx (w p : ℕ) : Fin (w + 1) := ⟨min p w, by omega⟩

/-- Run a scanner over the first `w` cells, then freeze. -/
def upTo {j : ℕ} (S : Scanner j) (w : ℕ) : Scanner j where
  σ := S.σ × Fin (w + 1)
  decEqσ := instDecidableEqProd
  finσ := instFintypeProd _ _
  start := (S.start, upToIdx w 0)
  stepR s cols :=
    if h : s.2.val < w then (S.stepR s.1 cols, ⟨s.2.val + 1, by omega⟩) else s
  stepL s cols := (S.stepL s.1 cols, s.2)
  emit s := S.emit s.1

theorem upTo_runR {j : ℕ} (S : Scanner j) (w : ℕ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ) :
    (S.upTo w).runR cols p = (S.runR cols (min p w), upToIdx w p) := by
  induction p with
  | zero => rfl
  | succ p ih =>
      have hstep : (S.upTo w).runR cols (p + 1)
          = (S.upTo w).stepR ((S.upTo w).runR cols p) (cols (p + 1)) := rfl
      rw [hstep, ih]
      by_cases hpw : p < w
      · have hmin : min p w = p := by omega
        have hmin' : min (p + 1) w = p + 1 := by omega
        have hlt : ((upToIdx w p : Fin (w + 1)) : ℕ) < w := by
          show min p w < w
          omega
        show (if h : ((upToIdx w p : Fin (w + 1)) : ℕ) < w then
            (S.stepR (S.runR cols (min p w)) (cols (p + 1)),
              (⟨((upToIdx w p : Fin (w + 1)) : ℕ) + 1, by omega⟩ : Fin (w + 1)))
          else (S.runR cols (min p w), upToIdx w p)) = _
        rw [dite_eq_left hlt]
        refine Prod.ext ?_ (Fin.ext ?_)
        · show S.stepR (S.runR cols (min p w)) (cols (p + 1)) = S.runR cols (min (p + 1) w)
          rw [hmin, hmin']
          rfl
        · show ((upToIdx w p : Fin (w + 1)) : ℕ) + 1 = ((upToIdx w (p + 1) : Fin (w + 1)) : ℕ)
          show min p w + 1 = min (p + 1) w
          omega
      · have hge : ¬ ((upToIdx w p : Fin (w + 1)) : ℕ) < w := by
          show ¬ min p w < w
          omega
        show (if h : ((upToIdx w p : Fin (w + 1)) : ℕ) < w then
            (S.stepR (S.runR cols (min p w)) (cols (p + 1)),
              (⟨((upToIdx w p : Fin (w + 1)) : ℕ) + 1, by omega⟩ : Fin (w + 1)))
          else (S.runR cols (min p w), upToIdx w p)) = _
        rw [dite_eq_right hge]
        refine Prod.ext ?_ (Fin.ext ?_)
        · show S.runR cols (min p w) = S.runR cols (min (p + 1) w)
          rw [show min (p + 1) w = min p w by omega]
        · show min p w = min (p + 1) w
          omega

theorem upTo_runL {j : ℕ} (S : Scanner j) (w : ℕ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ)
    (s : (S.upTo w).σ) : (S.upTo w).runL cols p s = (S.runL cols p s.1, s.2) := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL, ih]; rfl

/-- **A frozen check gives the verdict it would have given on its own cells.** -/
theorem upTo_emit_run {j : ℕ} (S : Scanner j) (hS : RightOnly S) (w len : ℕ) (hw : w ≤ len)
    (cols : ℕ → Fin (j + 1) → Γ) :
    (S.upTo w).emit ((S.upTo w).run cols len) = S.emit (S.run cols w) := by
  rw [run, upTo_runL, upTo_runR, run, runL_of_rightOnly hS, runL_of_rightOnly hS]
  show S.emit (S.runR cols (min len w)) = S.emit (S.runR cols w)
  rw [min_eq_right hw]

/-- Skip the first `w` cells, then run a scanner over the rest. Together with
`Complexity.Scanner.upTo` this restricts a check to any range of cells, which is what pins a
guessed value against a field that does not sit at the start of its register. -/
def after {j : ℕ} (S : Scanner j) (w : ℕ) : Scanner j where
  σ := S.σ × Fin (w + 1)
  decEqσ := instDecidableEqProd
  finσ := instFintypeProd _ _
  start := (S.start, upToIdx w 0)
  stepR s cols :=
    if h : s.2.val < w then (s.1, ⟨s.2.val + 1, by omega⟩) else (S.stepR s.1 cols, s.2)
  stepL s cols := (S.stepL s.1 cols, s.2)
  emit s := S.emit s.1

theorem rightOnly_after {j : ℕ} {S : Scanner j} (h : RightOnly S) (w : ℕ) :
    RightOnly (S.after w) := fun s cols => Prod.ext (h s.1 cols) rfl

theorem after_runR {j : ℕ} (S : Scanner j) (w : ℕ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ) :
    (S.after w).runR cols p = (S.runR (fun q => cols (w + q)) (p - w), upToIdx w p) := by
  induction p with
  | zero => rw [show (0 : ℕ) - w = 0 from Nat.zero_sub w]; rfl
  | succ p ih =>
      have hstep : (S.after w).runR cols (p + 1)
          = (S.after w).stepR ((S.after w).runR cols p) (cols (p + 1)) := rfl
      rw [hstep, ih]
      by_cases hpw : p < w
      · have hlt : ((upToIdx w p : Fin (w + 1)) : ℕ) < w := by
          show min p w < w
          omega
        show (if h : ((upToIdx w p : Fin (w + 1)) : ℕ) < w then
            (S.runR (fun q => cols (w + q)) (p - w),
              (⟨((upToIdx w p : Fin (w + 1)) : ℕ) + 1, by omega⟩ : Fin (w + 1)))
          else (S.stepR (S.runR (fun q => cols (w + q)) (p - w)) (cols (p + 1)),
            upToIdx w p)) = _
        rw [dite_eq_left hlt]
        refine Prod.ext ?_ (Fin.ext ?_)
        · show S.runR (fun q => cols (w + q)) (p - w)
            = S.runR (fun q => cols (w + q)) (p + 1 - w)
          rw [show p + 1 - w = p - w by omega]
        · show ((upToIdx w p : Fin (w + 1)) : ℕ) + 1 = ((upToIdx w (p + 1) : Fin (w + 1)) : ℕ)
          show min p w + 1 = min (p + 1) w
          omega
      · have hge : ¬ ((upToIdx w p : Fin (w + 1)) : ℕ) < w := by
          show ¬ min p w < w
          omega
        show (if h : ((upToIdx w p : Fin (w + 1)) : ℕ) < w then
            (S.runR (fun q => cols (w + q)) (p - w),
              (⟨((upToIdx w p : Fin (w + 1)) : ℕ) + 1, by omega⟩ : Fin (w + 1)))
          else (S.stepR (S.runR (fun q => cols (w + q)) (p - w)) (cols (p + 1)),
            upToIdx w p)) = _
        rw [dite_eq_right hge]
        refine Prod.ext ?_ (Fin.ext ?_)
        · show S.stepR (S.runR (fun q => cols (w + q)) (p - w)) (cols (p + 1))
            = S.runR (fun q => cols (w + q)) (p + 1 - w)
          rw [show p + 1 - w = (p - w) + 1 by omega]
          show _ = S.stepR (S.runR (fun q => cols (w + q)) (p - w)) (cols (w + ((p - w) + 1)))
          rw [show w + ((p - w) + 1) = p + 1 by omega]
        · show min p w = min (p + 1) w
          omega

theorem after_runL {j : ℕ} (S : Scanner j) (w : ℕ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ)
    (s : (S.after w).σ) : (S.after w).runL cols p s = (S.runL cols p s.1, s.2) := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL, ih]; rfl

/-- **A check that skips a prefix reads the cells after it.** -/
theorem after_emit_run {j : ℕ} (S : Scanner j) (hS : RightOnly S) (w len : ℕ)
    (cols : ℕ → Fin (j + 1) → Γ) :
    (S.after w).emit ((S.after w).run cols len)
      = S.emit (S.run (fun q => cols (w + q)) (len - w)) := by
  rw [run, after_runL, after_runR, run, runL_of_rightOnly hS, runL_of_rightOnly hS]
  rfl

/-- **A check restricted to a range of cells.** -/
theorem range_emit_run {j : ℕ} (S : Scanner j) (hS : RightOnly S) (w₁ w₂ len : ℕ)
    (hw : w₂ ≤ len) (cols : ℕ → Fin (j + 1) → Γ) :
    ((S.after w₁).upTo w₂).emit (((S.after w₁).upTo w₂).run cols len)
      = S.emit (S.run (fun q => cols (w₁ + q)) (w₂ - w₁)) := by
  rw [upTo_emit_run _ (rightOnly_after hS w₁) w₂ len hw, after_emit_run S hS]

/-! ## Running several checks in one scan

A machine has one result tape, and a two-pass scan writes it at the very end. Rather than give
each check its own tape and combine the verdicts afterwards, the checks run *together*: one
automaton whose state is the tuple of theirs, whose verdict is their conjunction. Each component
still runs exactly the scan it would have run alone, so the lemmas about the individual checks
apply unchanged. -/

/-- Run several scanners at once, emitting the conjunction of their verdicts. -/
noncomputable def all {jj : ℕ} (n : ℕ) (S : Fin n → Scanner jj) : Scanner jj where
  σ := ∀ i, (S i).σ
  decEqσ := Classical.decEq _
  finσ := Pi.instFintype
  start := fun i => (S i).start
  stepR s cols := fun i => (S i).stepR (s i) cols
  stepL s cols := fun i => (S i).stepL (s i) cols
  emit s := decide (∀ i, (S i).emit (s i) = true)

theorem all_runR {jj : ℕ} (n : ℕ) (S : Fin n → Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ)
    (p : ℕ) (i : Fin n) : (all n S).runR cols p i = (S i).runR cols p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [runR, runR, ← ih]; rfl

theorem all_runL {jj : ℕ} (n : ℕ) (S : Fin n → Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ)
    (p : ℕ) (s : (all n S).σ) (i : Fin n) :
    (all n S).runL cols p s i = (S i).runL cols p (s i) := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL, runL, ih]; rfl

/-- **Each component of a joint scan runs its own scan.** -/
theorem all_run {jj : ℕ} (n : ℕ) (S : Fin n → Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ)
    (len : ℕ) (i : Fin n) : (all n S).run cols len i = (S i).run cols len := by
  rw [run, run, all_runL, all_runR]

/-- **A joint scan accepts exactly when every component does.** -/
theorem all_emit_run {jj : ℕ} (n : ℕ) (S : Fin n → Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ)
    (len : ℕ) : (all n S).emit ((all n S).run cols len) = true ↔
      ∀ i, (S i).emit ((S i).run cols len) = true := by
  show decide (∀ i, (S i).emit ((all n S).run cols len i) = true) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h i; rw [← all_run]; exact h i
  · intro h i; rw [all_run]; exact h i

/-- Run two scanners at once, emitting the disjunction of their verdicts: the walk's step either
keeps its configuration or advances it. -/
def or {jj : ℕ} (S T : Scanner jj) : Scanner jj where
  σ := S.σ × T.σ
  start := (S.start, T.start)
  stepR s cols := (S.stepR s.1 cols, T.stepR s.2 cols)
  stepL s cols := (S.stepL s.1 cols, T.stepL s.2 cols)
  emit s := S.emit s.1 || T.emit s.2

theorem or_runR {jj : ℕ} (S T : Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ) (p : ℕ) :
    (S.or T).runR cols p = (S.runR cols p, T.runR cols p) := by
  induction p with
  | zero => rfl
  | succ p ih => rw [runR, ih]; rfl

theorem or_runL {jj : ℕ} (S T : Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ) (p : ℕ)
    (s : S.σ × T.σ) : (S.or T).runL cols p s = (S.runL cols p s.1, T.runL cols p s.2) := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL]; exact ih _

/-- **A disjunctive scan accepts exactly when one of its halves does.** -/
theorem or_emit_run {jj : ℕ} (S T : Scanner jj) (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ) :
    (S.or T).emit ((S.or T).run cols len) = true ↔
      S.emit (S.run cols len) = true ∨ T.emit (T.run cols len) = true := by
  show (S.emit _ || T.emit _) = true ↔ _
  rw [run]; erw [or_runL, or_runR]
  simp [run]

/-! ## Reading parameters before checking

A check usually needs a few values — a symbol to compare against, a direction to move — that are
themselves on a register. Laying them out in the first cells of the scan and starting the data
after them lets one scan do both: read the parameters into the control, then run a check chosen by
them. -/

/-- The accumulated parameters after reading `p` columns. -/
def auxRun {j : ℕ} {α : Type} (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α)
    (cols : ℕ → Fin (j + 1) → Γ) : ℕ → α
  | 0 => a₀
  | p + 1 => readStep (auxRun a₀ readStep cols p) (cols (p + 1))

/-- The state of the parameterized check after `q` columns beyond the parameter block. -/
def mainRun {j : ℕ} {α τ : Type} (c : ℕ) (a : α) (mainStep : α → τ → (Fin (j + 1) → Γ) → τ)
    (cols : ℕ → Fin (j + 1) → Γ) (t₀ : τ) : ℕ → τ
  | 0 => t₀
  | q + 1 => mainStep a (mainRun c a mainStep cols t₀ q) (cols (c + q + 1))

/-- **Read `c` columns of parameters, then check.** -/
def prefixed {j : ℕ} (c : ℕ) (α τ : Type) [DecidableEq α] [Fintype α] [DecidableEq τ]
    [Fintype τ] (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α) (t₀ : α → τ)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (emit : α → τ → Bool) : Scanner j :=
  ofRight (Fin (c + 1) × α × τ) (⟨0, Nat.zero_lt_succ c⟩, a₀, t₀ a₀)
    (fun s col =>
      if h : s.1.val < c then
        let a' := readStep s.2.1 col
        (⟨s.1.val + 1, by omega⟩, a', if s.1.val + 1 = c then t₀ a' else s.2.2)
      else (s.1, s.2.1, mainStep s.2.1 s.2.2 col))
    (fun s => emit s.2.1 s.2.2)

variable {j : ℕ} {α τ : Type} [DecidableEq α] [Fintype α] [DecidableEq τ] [Fintype τ]

theorem rightOnly_prefixed (c : ℕ) (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α) (t₀ : α → τ)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (emit : α → τ → Bool) :
    RightOnly (prefixed c α τ a₀ readStep t₀ mainStep emit) := fun _ _ => rfl

theorem prefixed_stepR (c : ℕ) (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α) (t₀ : α → τ)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (emit : α → τ → Bool)
    (s : Fin (c + 1) × α × τ) (col : Fin (j + 1) → Γ) :
    (prefixed c α τ a₀ readStep t₀ mainStep emit).stepR s col
      = if h : s.1.val < c then
          (⟨s.1.val + 1, by omega⟩, readStep s.2.1 col,
            if s.1.val + 1 = c then t₀ (readStep s.2.1 col) else s.2.2)
        else (s.1, s.2.1, mainStep s.2.1 s.2.2 col) := rfl

/-- Through the parameter block, the scan is just accumulating parameters. -/
theorem prefixed_runR_le (c : ℕ) (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α) (t₀ : α → τ)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (emit : α → τ → Bool)
    (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p ≤ c, ((prefixed c α τ a₀ readStep t₀ mainStep emit).runR cols p).1.val = p ∧
      ((prefixed c α τ a₀ readStep t₀ mainStep emit).runR cols p).2.1
        = auxRun a₀ readStep cols p := by
  intro p
  induction p with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ p ih =>
      intro hp
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hlt : ((prefixed c α τ a₀ readStep t₀ mainStep emit).runR cols p).1.val < c := by
        rw [h1]; omega
      constructor
      · rw [runR]; erw [prefixed_stepR, dite_eq_left hlt]
        simpa using h1
      · rw [runR]; erw [prefixed_stepR, dite_eq_left hlt]; rw [auxRun, h2]

end Scanner

namespace Scanner

variable {j : ℕ} {α τ : Type} [DecidableEq α] [Fintype α] [DecidableEq τ] [Fintype τ]

/-- Past the parameter block, the scan runs the check the parameters chose. -/
theorem prefixed_runR (c : ℕ) (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α) (t₀ : α → τ)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (emit : α → τ → Bool)
    (cols : ℕ → Fin (j + 1) → Γ) (hc : 0 < c) :
    ∀ q : ℕ, (prefixed c α τ a₀ readStep t₀ mainStep emit).runR cols (c + q)
      = (⟨c, Nat.lt_succ_self c⟩, auxRun a₀ readStep cols c,
        mainRun c (auxRun a₀ readStep cols c) mainStep cols
          (t₀ (auxRun a₀ readStep cols c)) q) := by
  intro q
  induction q with
  | zero =>
      obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      subst hc'
      obtain ⟨h1, h2⟩ := prefixed_runR_le (c' + 1) a₀ readStep t₀ mainStep emit cols c' (by omega)
      have hlt : ((prefixed (c' + 1) α τ a₀ readStep t₀ mainStep emit).runR cols c').1.val
          < c' + 1 := by rw [h1]; omega
      rw [Nat.add_zero, runR]; erw [prefixed_stepR, dite_eq_left hlt, h2, mainRun]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact Fin.ext (by simpa using h1)
      · rw [auxRun]
      · rw [ite_eq_left (by omega), auxRun]
  | succ q ih =>
      have hnot : ¬ ((prefixed c α τ a₀ readStep t₀ mainStep emit).runR cols (c + q)).1.val
          < c := by
        rw [ih]
        exact Nat.lt_irrefl c
      rw [show c + (q + 1) = (c + q) + 1 by omega, runR]
      erw [prefixed_stepR, dite_eq_right hnot, ih]; rfl

/-- **What a parameterized scan reports**: the check the parameters chose, run on the data after
them. -/
theorem prefixed_run (c : ℕ) (a₀ : α) (readStep : α → (Fin (j + 1) → Γ) → α) (t₀ : α → τ)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (emit : α → τ → Bool)
    (cols : ℕ → Fin (j + 1) → Γ) (hc : 0 < c) (q : ℕ) :
    (prefixed c α τ a₀ readStep t₀ mainStep emit).emit
        ((prefixed c α τ a₀ readStep t₀ mainStep emit).run cols (c + q))
      = emit (auxRun a₀ readStep cols c)
          (mainRun c (auxRun a₀ readStep cols c) mainStep cols
            (t₀ (auxRun a₀ readStep cols c)) q) := by
  have hrunL : ∀ s : Fin (c + 1) × α × τ,
      (prefixed c α τ a₀ readStep t₀ mainStep emit).runL cols (c + q) s = s := fun s =>
    ofRight_runL (Fin (c + 1) × α × τ) _ _ _ cols (c + q) s
  rw [run]; erw [hrunL, prefixed_runR c a₀ readStep t₀ mainStep emit cols hc q]
  rfl

/-! ## Reading fixed-width fields into the control

The parameters a check needs — a state, a symbol, a direction — sit in the first few cells of
their own registers. This reads all of them at once: `s` registers, `w` cells each, into a table
of bits the check can consult. -/

/-- The bit a scan sees on a register at a given cell. -/
def bitAt {j : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (a : Fin (j + 1)) (p : ℕ) : Bool :=
  decide (cols p a = Γ.one)

/-- Read the first `w` cells of each of `s` registers into a table of bits. -/
def bitsStep {j : ℕ} (s w : ℕ) (regs : Fin s → Fin (j + 1))
    (x : Fin (w + 1) × (Fin s → Fin w → Bool)) (col : Fin (j + 1) → Γ) :
    Fin (w + 1) × (Fin s → Fin w → Bool) :=
  if h : x.1.val < w then
    (⟨x.1.val + 1, by omega⟩,
      fun t => Function.update (x.2 t) ⟨x.1.val, h⟩ (decide (col (regs t) = Γ.one)))
  else x

/-- **A field reader sees only the registers it names.** Two scans whose named registers agree
read the same table — which is what makes several checks reading the same parameter register
agree on the parameters. -/
theorem auxRun_bitsStep_congr {j s w : ℕ} (regs : Fin s → Fin (j + 1))
    (cols cols' : ℕ → Fin (j + 1) → Γ) (h : ∀ q t, cols q (regs t) = cols' q (regs t))
    (x₀ : Fin s → Fin w → Bool) : ∀ p : ℕ,
      auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (bitsStep s w regs) cols p
        = auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (bitsStep s w regs) cols' p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [auxRun, auxRun, ih]
      simp only [bitsStep, h (p + 1)]

/-- **What the field reader has read.** After `p ≤ w` columns the table holds the first `p` bits
of every register. -/
theorem bitsStep_run {j : ℕ} (s w : ℕ) (regs : Fin s → Fin (j + 1))
    (cols : ℕ → Fin (j + 1) → Γ) (x₀ : Fin s → Fin w → Bool) :
    ∀ p ≤ w,
      (auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (bitsStep s w regs) cols p).1.val = p ∧
      ∀ (t : Fin s) (i : Fin w), i.val < p →
        (auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (bitsStep s w regs) cols p).2 t i
          = bitAt cols (regs t) (i.val + 1) := by
  intro p
  induction p with
  | zero => intro _; exact ⟨rfl, fun _ _ h => absurd h (by omega)⟩
  | succ p ih =>
      intro hp
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hlt : (auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (bitsStep s w regs) cols p).1.val < w := by
        rw [h1]; omega
      rw [auxRun, bitsStep, dite_eq_left hlt]
      refine ⟨by simpa using h1, fun t i hi => ?_⟩
      dsimp only
      rcases Nat.lt_or_ge i.val p with h | h
      · rw [Function.update_of_ne, h2 t i h]
        intro hcontra
        rw [hcontra, h1] at h
        exact absurd h (by omega)
      · have hip : i.val = p := by omega
        have hieq : i = ⟨(auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (bitsStep s w regs) cols p).1.val,
            hlt⟩ := by
          apply Fin.ext
          rw [h1, hip]
        rw [hieq, Function.update_self, bitAt, h1]

/-! ## Folding three columns at a time

A marked block stores each cell as a chunk of three bits — the head marker first, so that a
rightward pass knows whether the head is on a cell before it reads that cell's symbol. Checks on
such a block are naturally written a chunk at a time, and `Complexity.Scanner.cellFold_chunk` says
that a cell-level fold which buffers two columns and acts on the third computes exactly the
chunk-level fold. -/

/-- A plain fold over the columns from `off + 1` onwards. -/
def cellFold {j : ℕ} {σ : Type} (g : σ → (Fin (j + 1) → Γ) → σ) (cols : ℕ → Fin (j + 1) → Γ)
    (off : ℕ) (s₀ : σ) : ℕ → σ
  | 0 => s₀
  | q + 1 => g (cellFold g cols off s₀ q) (cols (off + q + 1))

theorem mainRun_eq_cellFold {j : ℕ} {α τ : Type} (c : ℕ) (a : α)
    (mainStep : α → τ → (Fin (j + 1) → Γ) → τ) (cols : ℕ → Fin (j + 1) → Γ) (t₀ : τ) :
    ∀ q : ℕ, mainRun c a mainStep cols t₀ q = cellFold (mainStep a) cols c t₀ q := by
  intro q
  induction q with
  | zero => rfl
  | succ q ih => rw [mainRun, cellFold, ih]

/-- A fold started later is the same fold on shifted columns, so a check proved at the start of a
scan applies wherever the scan puts it. -/
theorem cellFold_shift {j : ℕ} {σ : Type} (g : σ → (Fin (j + 1) → Γ) → σ)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (s₀ : σ) :
    ∀ p : ℕ, cellFold g cols off s₀ p = cellFold g (fun t => cols (off + t)) 0 s₀ p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [cellFold, cellFold, ih]
      simp only [Nat.zero_add, Nat.add_assoc]

/-- A scanner's rightward pass is a plain fold. -/
theorem runR_eq_cellFold {j : ℕ} (S : Scanner j) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, S.runR cols p = cellFold S.stepR cols 0 S.start p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [runR, ih, cellFold]
      simp only [Nat.zero_add]

/-- A fold that consumes three columns at a time. -/
def chunkRun {j : ℕ} {χ : Type}
    (f : χ → (Fin (j + 1) → Γ) → (Fin (j + 1) → Γ) → (Fin (j + 1) → Γ) → χ)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (x₀ : χ) : ℕ → χ
  | 0 => x₀
  | p + 1 =>
    f (chunkRun f cols off x₀ p) (cols (off + 3 * p + 1)) (cols (off + 3 * p + 2))
      (cols (off + 3 * p + 3))

/-- The cell-level step that buffers two columns and acts on the third. -/
def chunkStepCell {j : ℕ} {χ : Type}
    (f : χ → (Fin (j + 1) → Γ) → (Fin (j + 1) → Γ) → (Fin (j + 1) → Γ) → χ)
    (s : Fin 3 × (Fin (j + 1) → Γ) × (Fin (j + 1) → Γ) × χ) (col : Fin (j + 1) → Γ) :
    Fin 3 × (Fin (j + 1) → Γ) × (Fin (j + 1) → Γ) × χ :=
  if s.1 = 0 then (1, col, s.2.2.1, s.2.2.2)
  else if s.1 = 1 then (2, s.2.1, col, s.2.2.2)
  else (0, s.2.1, s.2.2.1, f s.2.2.2 s.2.1 s.2.2.1 col)

/-- **Three cells make a chunk.** -/
theorem cellFold_chunk {j : ℕ} {χ : Type}
    (f : χ → (Fin (j + 1) → Γ) → (Fin (j + 1) → Γ) → (Fin (j + 1) → Γ) → χ)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (x₀ : χ) (u v : Fin (j + 1) → Γ) :
    ∀ p : ℕ,
      (cellFold (chunkStepCell f) cols off (0, u, v, x₀) (3 * p)).1 = 0 ∧
        (cellFold (chunkStepCell f) cols off (0, u, v, x₀) (3 * p)).2.2.2
          = chunkRun f cols off x₀ p := by
  intro p
  induction p with
  | zero => exact ⟨rfl, rfl⟩
  | succ p ih =>
      obtain ⟨h0, hx⟩ := ih
      have hstep : 3 * (p + 1) = 3 * p + 1 + 1 + 1 := by omega
      rw [hstep, cellFold, cellFold, cellFold]
      have e0 : chunkStepCell f (cellFold (chunkStepCell f) cols off (0, u, v, x₀) (3 * p))
          (cols (off + 3 * p + 1))
          = (1, cols (off + 3 * p + 1),
            (cellFold (chunkStepCell f) cols off (0, u, v, x₀) (3 * p)).2.2.1,
            chunkRun f cols off x₀ p) := by
        rw [chunkStepCell, ite_eq_left h0, hx]
      rw [e0]
      have e1 : chunkStepCell f
          (1, cols (off + 3 * p + 1),
            (cellFold (chunkStepCell f) cols off (0, u, v, x₀) (3 * p)).2.2.1,
            chunkRun f cols off x₀ p) (cols (off + (3 * p + 1) + 1))
          = (2, cols (off + 3 * p + 1), cols (off + (3 * p + 1) + 1),
            chunkRun f cols off x₀ p) := by
        rw [chunkStepCell]
        simp
      rw [e1, chunkStepCell]
      refine ⟨by simp, ?_⟩
      simp only [chunkRun]
      rw [show off + (3 * p + 1) + 1 = off + 3 * p + 2 by omega,
        show off + (3 * p + 2) + 1 = off + 3 * p + 3 by omega]
      rfl

/-! ## A first scanner: register equality -/

/-- Compare two of the scanned tapes cell by cell. -/
def eq (j : ℕ) (a b : Fin (j + 1)) : Scanner j where
  σ := Bool
  start := true
  stepR s cols := s && decide (cols a = cols b)
  stepL s _ := s
  emit := id

theorem rightOnly_eq (j : ℕ) (a b : Fin (j + 1)) : RightOnly (eq j a b) := fun _ _ => rfl

@[simp] theorem eq_runL (j : ℕ) (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ)
    (s : Bool) : (eq j a b).runL cols p s = s := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL]; exact ih _

theorem eq_runR (j : ℕ) (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (eq j a b).runR cols p = true ↔ ∀ q, 1 ≤ q → q ≤ p → cols q a = cols q b := by
  intro p
  induction p with
  | zero => simpa [runR, eq] using fun q h1 h2 => absurd h1 (by omega)
  | succ p ih =>
      rw [runR]
      show ((eq j a b).runR cols p && decide (cols (p + 1) a = cols (p + 1) b)) = true ↔ _
      erw [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hall, hlast⟩ q h1 h2
        rcases Nat.lt_or_ge q (p + 1) with hlt | hge
        · exact ih.mp hall q h1 (by omega)
        · rw [show q = p + 1 by omega]
          exact hlast
      · intro hall
        exact ⟨ih.mpr fun q h1 h2 => hall q h1 (by omega), hall (p + 1) (by omega) le_rfl⟩

/-- **What the equality scanner reports.** -/
theorem eq_run (j : ℕ) (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (len : ℕ) :
    (eq j a b).run cols len = true ↔ ∀ q, 1 ≤ q → q ≤ len → cols q a = cols q b := by
  rw [run]; erw [eq_runL, eq_runR]

/-- **A comparison restricted to a range of cells decides equality there.** This is how a small
guessed register is pinned against a field sitting anywhere inside a bigger one. -/
theorem eq_range_run (j : ℕ) (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ)
    (w₁ w₂ len : ℕ) (hw : w₂ ≤ len) :
    (((eq j a b).after w₁).upTo w₂).emit ((((eq j a b).after w₁).upTo w₂).run cols len) = true ↔
      ∀ q, w₁ < q → q ≤ w₂ → cols q a = cols q b := by
  rw [range_emit_run _ (rightOnly_eq j a b) w₁ w₂ len hw]
  show (eq j a b).run (fun q => cols (w₁ + q)) (w₂ - w₁) = true ↔ _
  rw [eq_run]
  constructor
  · intro h q h1 h2
    have := h (q - w₁) (by omega) (by omega)
    rwa [show w₁ + (q - w₁) = q by omega] at this
  · intro h q h1 h2
    exact h (w₁ + q) (by omega) (by omega)

/-- Check that a register carries a fixed symbol. Frozen to one cell by
`Complexity.Scanner.upTo` this reads a single cell, which is how a one-cell register — a
direction, say — is checked against a constant. -/
def isConst (j : ℕ) (a : Fin (j + 1)) (g : Γ) : Scanner j :=
  ofRight Bool true (fun s cols => s && decide (cols a = g)) id

theorem isConst_runR (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (isConst j a g).runR cols p = true ↔ ∀ q, 1 ≤ q → q ≤ p → cols q a = g := by
  intro p
  induction p with
  | zero => simpa [runR, isConst, ofRight] using fun q h1 h2 => absurd h1 (by omega)
  | succ p ih =>
      rw [runR]
      show ((isConst j a g).runR cols p && decide (cols (p + 1) a = g)) = true ↔ _
      erw [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hall, hlast⟩ q h1 h2
        rcases Nat.lt_or_ge q (p + 1) with hlt | hge
        · exact ih.mp hall q h1 (by omega)
        · rw [show q = p + 1 by omega]
          exact hlast
      · intro h
        exact ⟨ih.mpr fun q h1 h2 => h q h1 (by omega), h (p + 1) (by omega) le_rfl⟩

theorem isConst_runL (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ)
    (s : Bool) : (isConst j a g).runL cols p s = s := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL]; exact ih _

theorem isConst_run (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ) (len : ℕ) :
    (isConst j a g).run cols len = true ↔ ∀ q, 1 ≤ q → q ≤ len → cols q a = g := by
  rw [run]; erw [isConst_runL, isConst_runR]

theorem rightOnly_isConst (j : ℕ) (a : Fin (j + 1)) (g : Γ) : RightOnly (isConst j a g) :=
  fun _ _ => rfl

/-- **A check over a prefix of cells.** -/
theorem isConst_upTo_run (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ)
    (w len : ℕ) (hlen : w ≤ len) :
    ((isConst j a g).upTo w).emit (((isConst j a g).upTo w).run cols len) = true ↔
      ∀ q, 1 ≤ q → q ≤ w → cols q a = g := by
  rw [upTo_emit_run _ (rightOnly_isConst j a g) w len hlen]
  show (isConst j a g).run cols w = true ↔ _
  rw [isConst_run]

/-- **A one-cell check.** -/
theorem isConst_cell (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ) (len : ℕ)
    (hlen : 1 ≤ len) :
    ((isConst j a g).upTo 1).emit (((isConst j a g).upTo 1).run cols len) = true ↔
      cols 1 a = g := by
  rw [isConst_upTo_run j a g cols 1 len hlen]
  exact ⟨fun h => h 1 le_rfl le_rfl, fun h q h1 h2 => by rw [show q = 1 by omega]; exact h⟩

/-- Check that a register does **not** carry a fixed symbol. Frozen to one cell this is the
negation of `Complexity.Scanner.isConst`, which is what a loop's test needs when a failed check
should stop it. -/
def isNotConst (j : ℕ) (a : Fin (j + 1)) (g : Γ) : Scanner j :=
  ofRight Bool false (fun s cols => s || decide (cols a ≠ g)) id

theorem isNotConst_runR (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (isNotConst j a g).runR cols p = true ↔ ∃ q, 1 ≤ q ∧ q ≤ p ∧ cols q a ≠ g := by
  intro p
  induction p with
  | zero => simp [runR, isNotConst, ofRight]
  | succ p ih =>
      rw [runR]
      show ((isNotConst j a g).runR cols p || decide (cols (p + 1) a ≠ g)) = true ↔ _
      erw [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (hall | hlast)
        · obtain ⟨q, h1, h2, h3⟩ := ih.mp hall
          exact ⟨q, h1, by omega, h3⟩
        · exact ⟨p + 1, by omega, le_rfl, hlast⟩
      · rintro ⟨q, h1, h2, h3⟩
        rcases Nat.lt_or_ge q (p + 1) with hlt | hge
        · exact Or.inl (ih.mpr ⟨q, h1, by omega, h3⟩)
        · exact Or.inr (by rw [show p + 1 = q by omega]; exact h3)

theorem isNotConst_runL (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ)
    (s : Bool) : (isNotConst j a g).runL cols p s = s := by
  induction p generalizing s with
  | zero => rfl
  | succ p ih => simp only [runL]; exact ih _

theorem rightOnly_isNotConst (j : ℕ) (a : Fin (j + 1)) (g : Γ) :
    RightOnly (isNotConst j a g) := fun _ _ => rfl

/-- **A one-cell inequality check.** -/
theorem isNotConst_cell (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ)
    (len : ℕ) (hlen : 1 ≤ len) :
    ((isNotConst j a g).upTo 1).emit (((isNotConst j a g).upTo 1).run cols len) = true ↔
      cols 1 a ≠ g := by
  rw [upTo_emit_run _ (rightOnly_isNotConst j a g) 1 len hlen]
  show (isNotConst j a g).run cols 1 = true ↔ _
  rw [run]; erw [isNotConst_runL, isNotConst_runR]
  exact ⟨fun ⟨q, h1, h2, h3⟩ => by rwa [show q = 1 by omega] at h3,
    fun h => ⟨1, le_rfl, le_rfl, h⟩⟩

/-- **A constant check restricted to a range of cells.** -/
theorem isConst_range_run (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ)
    (w₁ w₂ len : ℕ) (hw : w₂ ≤ len) :
    (((isConst j a g).after w₁).upTo w₂).emit
        ((((isConst j a g).after w₁).upTo w₂).run cols len) = true ↔
      ∀ q, w₁ < q → q ≤ w₂ → cols q a = g := by
  rw [range_emit_run _ (rightOnly_isConst j a g) w₁ w₂ len hw]
  show (isConst j a g).run (fun q => cols (w₁ + q)) (w₂ - w₁) = true ↔ _
  rw [isConst_run]
  constructor
  · intro h q h1 h2
    have := h (q - w₁) (by omega) (by omega)
    rwa [show w₁ + (q - w₁) = q by omega] at this
  · intro h q h1 h2
    exact h (w₁ + q) (by omega) (by omega)

/-- **A difference check restricted to a range of cells.** -/
theorem isNotConst_range_run (j : ℕ) (a : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ)
    (w₁ w₂ len : ℕ) (hw : w₂ ≤ len) :
    (((isNotConst j a g).after w₁).upTo w₂).emit
        ((((isNotConst j a g).after w₁).upTo w₂).run cols len) = true ↔
      ∃ q, w₁ < q ∧ q ≤ w₂ ∧ cols q a ≠ g := by
  rw [range_emit_run _ (rightOnly_isNotConst j a g) w₁ w₂ len hw]
  show (isNotConst j a g).run (fun q => cols (w₁ + q)) (w₂ - w₁) = true ↔ _
  rw [run]; erw [isNotConst_runL, isNotConst_runR]
  constructor
  · rintro ⟨q, h1, h2, h3⟩
    exact ⟨w₁ + q, by omega, by omega, h3⟩
  · rintro ⟨q, h1, h2, h3⟩
    refine ⟨q - w₁, by omega, by omega, ?_⟩
    rwa [show w₁ + (q - w₁) = q by omega]

/-! ## A scanner that takes a conjunction

Each check writes its verdict to its own register; one more scan over those registers reports
whether they all said yes. -/

/-- Report whether every scanned tape carries `Γ.one` throughout. -/
def andAll (j : ℕ) : Scanner j :=
  ofRight Bool true (fun s cols => s && decide (∀ i, cols i = Γ.one)) id

@[simp] theorem andAll_stepR (j : ℕ) (s : Bool) (cols : Fin (j + 1) → Γ) :
    (andAll j).stepR s cols = (s && decide (∀ i, cols i = Γ.one)) := rfl

theorem andAll_runR (j : ℕ) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (andAll j).runR cols p = true ↔
      ∀ q, 1 ≤ q → q ≤ p → ∀ i, cols q i = Γ.one := by
  intro p
  induction p with
  | zero => exact ⟨fun _ q h1 h2 => absurd h1 (by omega), fun _ => rfl⟩
  | succ p ih =>
      rw [runR]
      show ((andAll j).runR cols p && decide (∀ i, cols (p + 1) i = Γ.one)) = true ↔ _
      erw [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hall, hlast⟩ q h1 h2
        rcases Nat.lt_or_ge q (p + 1) with h | h
        · exact ih.mp hall q h1 (by omega)
        · have hqp : q = p + 1 := by omega
          rw [hqp]
          exact hlast
      · intro hall
        exact ⟨ih.mpr fun q h1 h2 => hall q h1 (by omega), hall (p + 1) (by omega) le_rfl⟩

/-- **What the conjunction scanner reports.** -/
theorem andAll_run (j : ℕ) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ) :
    (andAll j).run cols p = true ↔ ∀ q, 1 ≤ q → q ≤ p → ∀ i, cols q i = Γ.one := by
  have hrunL : ∀ s : Bool, (andAll j).runL cols p s = s := fun s =>
    ofRight_runL Bool _ _ _ cols p s
  rw [run]; erw [hrunL, andAll_runR]

/-- Report whether the *designated* tapes all carry `Γ.one`. The verdict registers of a
composite check are scattered — each check owns a contiguous block, so their result tapes are
not adjacent — so the combining scan reads every tape and looks only at the ones it is told
to. -/
def andSome (j : ℕ) (P : Fin (j + 1) → Bool) : Scanner j :=
  ofRight Bool true (fun s cols => s && decide (∀ i, P i = true → cols i = Γ.one)) id

@[simp] theorem andSome_stepR (j : ℕ) (P : Fin (j + 1) → Bool) (s : Bool)
    (cols : Fin (j + 1) → Γ) :
    (andSome j P).stepR s cols = (s && decide (∀ i, P i = true → cols i = Γ.one)) := rfl

theorem andSome_runR (j : ℕ) (P : Fin (j + 1) → Bool) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (andSome j P).runR cols p = true ↔
      ∀ q, 1 ≤ q → q ≤ p → ∀ i, P i = true → cols q i = Γ.one := by
  intro p
  induction p with
  | zero => exact ⟨fun _ q h1 h2 => absurd h1 (by omega), fun _ => rfl⟩
  | succ p ih =>
      rw [runR]
      show ((andSome j P).runR cols p &&
        decide (∀ i, P i = true → cols (p + 1) i = Γ.one)) = true ↔ _
      erw [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hall, hlast⟩ q h1 h2
        rcases Nat.lt_or_ge q (p + 1) with h | h
        · exact ih.mp hall q h1 (by omega)
        · have hqp : q = p + 1 := by omega
          rw [hqp]
          exact hlast
      · intro hall
        exact ⟨ih.mpr fun q h1 h2 => hall q h1 (by omega), hall (p + 1) (by omega) le_rfl⟩

/-- **What the selective conjunction scanner reports.** -/
theorem andSome_run (j : ℕ) (P : Fin (j + 1) → Bool) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ) :
    (andSome j P).run cols p = true ↔
      ∀ q, 1 ≤ q → q ≤ p → ∀ i, P i = true → cols q i = Γ.one := by
  have hrunL : ∀ s : Bool, (andSome j P).runL cols p s = s := fun s =>
    ofRight_runL Bool _ _ _ cols p s
  rw [run]; erw [hrunL, andSome_runR]

/-- Report whether the designated tapes carry `Γ.one` in their **first** cell. A verdict register
holds a single bit and blanks after it, so a scan whose length is set by some longer register must
look only at the first column. -/
def andFirst (j : ℕ) (P : Fin (j + 1) → Bool) : Scanner j :=
  ofRight (Bool × Bool) (true, false)
    (fun s cols =>
      (if s.2 then s.1 else s.1 && decide (∀ i, P i = true → cols i = Γ.one), true))
    (fun s => s.1)

theorem andFirst_runR (j : ℕ) (P : Fin (j + 1) → Bool) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (andFirst j P).runR cols p
      = (if p = 0 then true else decide (∀ i, P i = true → cols 1 i = Γ.one),
        decide (0 < p)) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [runR, ih]
      show (if (decide (0 < p)) then _ else _, true) = _
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        simp
      · rw [ite_eq_left (by simpa using hp)]
        simp [Nat.ne_of_gt hp]

/-- **What the first-cell conjunction scanner reports.** -/
theorem andFirst_run (j : ℕ) (P : Fin (j + 1) → Bool) (cols : ℕ → Fin (j + 1) → Γ) (p : ℕ)
    (hp : 0 < p) :
    (andFirst j P).emit ((andFirst j P).run cols p) = true ↔
      ∀ i, P i = true → cols 1 i = Γ.one := by
  have hrunL : ∀ s : Bool × Bool, (andFirst j P).runL cols p s = s := fun s =>
    ofRight_runL (Bool × Bool) _ _ _ cols p s
  rw [run]; erw [hrunL, andFirst_runR]
  show (if p = 0 then true else decide (∀ i, P i = true → cols 1 i = Γ.one)) = true ↔ _
  rw [ite_eq_right (by omega), decide_eq_true_eq]

/-- Report an arbitrary function of the **first** column. Verdict registers hold a single bit
each, so a composite decision — "these checks all passed, *or* those did" — is a function of one
column, however long the scan turns out to be. -/
def firstCol (j : ℕ) (f : (Fin (j + 1) → Γ) → Bool) : Scanner j :=
  ofRight (Bool × Bool) (true, false)
    (fun s cols => (if s.2 then s.1 else f cols, true)) (fun s => s.1)

theorem firstCol_runR (j : ℕ) (f : (Fin (j + 1) → Γ) → Bool) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, (firstCol j f).runR cols p
      = (if p = 0 then true else f (cols 1), decide (0 < p)) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [runR, ih]
      show (if (decide (0 < p)) then _ else _, true) = _
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        simp
      · rw [ite_eq_left (by simpa using hp)]
        simp [Nat.ne_of_gt hp]

/-- **What the first-column scanner reports.** -/
theorem firstCol_run (j : ℕ) (f : (Fin (j + 1) → Γ) → Bool) (cols : ℕ → Fin (j + 1) → Γ)
    (p : ℕ) (hp : 0 < p) :
    (firstCol j f).emit ((firstCol j f).run cols p) = f (cols 1) := by
  have hrunL : ∀ s : Bool × Bool, (firstCol j f).runL cols p s = s := fun s =>
    ofRight_runL (Bool × Bool) _ _ _ cols p s
  rw [run]; erw [hrunL, firstCol_runR]
  show (if p = 0 then true else f (cols 1)) = _
  rw [ite_eq_right (by omega)]

/-! ## A scanner that checks an increment

Registers hold little-endian bits, so a scan meets them least significant first — which is the
order an increment carries in. -/

/-- The value of the first `p` bits of a register, read little-endian. -/
def valUpTo (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | p + 1 => valUpTo f p + (if f (p + 1) then 2 ^ p else 0)

/-- Check that register `b` holds one more than register `a`. -/
def plusOne (j : ℕ) (a b : Fin (j + 1)) : Scanner j :=
  ofRight (Bool × Bool) (true, true)
    (fun s cols =>
      let ba := decide (cols a = Γ.one)
      let bb := decide (cols b = Γ.one)
      (ba && s.1, s.2 && decide (bb = (xor ba s.1))))
    (fun s => !s.1 && s.2)

/-- The value of `p` bits fits in `p` bits. -/
theorem valUpTo_lt (f : ℕ → Bool) : ∀ p : ℕ, valUpTo f p < 2 ^ p := by
  intro p
  induction p with
  | zero => simp [valUpTo]
  | succ p ih =>
      have hpow : (2 : ℕ) ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [pow_succ]; omega
      rw [valUpTo]
      split <;> omega

/-- **The invariant of the increment check.** The carry is exactly "every bit of `a` so far was
one", and the running verdict says exactly that the bits of `b` so far are those of `a + 1`. -/
theorem plusOne_runR (j : ℕ) (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, ∃ c v : Bool, (plusOne j a b).runR cols p = (c, v) ∧
      (c = true ↔ valUpTo (bitAt cols a) p + 1 = 2 ^ p) ∧
      (v = true ↔ valUpTo (bitAt cols b) p + (if c then 2 ^ p else 0)
        = valUpTo (bitAt cols a) p + 1) := by
  intro p
  induction p with
  | zero => exact ⟨true, true, rfl, by simp [valUpTo], by simp [valUpTo]⟩
  | succ p ih =>
      obtain ⟨c, v, hrun, hcar, hinv⟩ := ih
      have hpow : (0 : ℕ) < 2 ^ p := Nat.two_pow_pos p
      have hpow2 : (2 : ℕ) ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [pow_succ]; omega
      have hlA : valUpTo (bitAt cols a) p < 2 ^ p := valUpTo_lt _ p
      have hlB : valUpTo (bitAt cols b) p < 2 ^ p := valUpTo_lt _ p
      refine ⟨bitAt cols a (p + 1) && c,
        v && decide (bitAt cols b (p + 1) = xor (bitAt cols a (p + 1)) c), ?_, ?_, ?_⟩
      · rw [runR, hrun]
        rfl
      · cases c <;> cases hA : bitAt cols a (p + 1) <;>
          simp_all [valUpTo] <;> omega
      · simp only [valUpTo, Bool.and_eq_true, decide_eq_true_eq]
        cases c <;> cases v <;>
          simp only [Bool.false_eq_true, ite_true, ite_false, Bool.xor_false, Bool.xor_true,
            true_iff, false_iff] at hinv hcar ⊢ <;>
          cases hA : bitAt cols a (p + 1) <;> cases hB : bitAt cols b (p + 1) <;>
          simp_all <;>
          omega

/-- **What the increment scanner reports.** -/
theorem plusOne_run (j : ℕ) (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (len : ℕ) :
    (plusOne j a b).emit ((plusOne j a b).run cols len) = true ↔
      valUpTo (bitAt cols b) len = valUpTo (bitAt cols a) len + 1 := by
  obtain ⟨c, v, hrun, hcar, hinv⟩ := plusOne_runR j a b cols len
  have hrunL : ∀ (s : Bool × Bool), (plusOne j a b).runL cols len s = s := fun s =>
    ofRight_runL (Bool × Bool) _ _ _ cols len s
  have hrun' : (plusOne j a b).run cols len = (c, v) := by
    rw [run]; erw [hrunL, hrun]
  rw [hrun']
  have hlB : valUpTo (bitAt cols b) len < 2 ^ len := valUpTo_lt _ len
  clear hrun hrun' hrunL
  show (!c && v) = true ↔ _
  cases c <;> cases v <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ite_true, ite_false, true_iff, false_iff] at hcar hinv ⊢ <;>
    omega

end Scanner

namespace TM

variable {j : ℕ}

/-- The control phases of `TM.twoPassTM`. -/
inductive TwoPassPhase where
  /-- Walking right to the first blank of tape `0`. -/
  | right
  /-- Walking back left to the left marker. -/
  | left
  /-- Publishing the verdict. -/
  | emit
  /-- Halted. -/
  | done
  deriving DecidableEq

instance : Fintype TwoPassPhase where
  elems := {.right, .left, .emit, .done}
  complete := fun x => by cases x <;> simp

/-- The control states of the scanning machine: a phase and the automaton's own state. -/
abbrev TwoPassQ (S : Scanner j) : Type := TwoPassPhase × S.σ

instance (S : Scanner j) : DecidableEq (TwoPassQ S) := by
  haveI := S.decEqσ
  exact inferInstanceAs (DecidableEq (TwoPassPhase × S.σ))

instance (S : Scanner j) : Fintype (TwoPassQ S) := by
  haveI := S.finσ
  exact inferInstanceAs (Fintype (TwoPassPhase × S.σ))

/-- **The scanning machine.** Work tapes `0 … j` are scanned in lockstep and work tape `j + 1`
receives the verdict. -/
def twoPassTM (S : Scanner j) : TM (j + 2) :=
  { Q := TwoPassQ S
    qstart := (.right, S.start)
    qhalt := (.done, S.start)
    δ := fun q iHead wHeads oHead =>
      let syms : Fin (j + 1) → Γ := fun i => wHeads i.castSucc
      let keep : Fin (j + 2) → Γw := fun i => readBackWrite (wHeads i)
      let idle : Fin (j + 2) → Dir3 := fun i => idleDir (wHeads i)
      let lastIdle : Dir3 := idleDir (wHeads (Fin.last (j + 1)))
      match q with
      | (.right, s) =>
        if syms 0 = Γ.blank then
          ((TwoPassPhase.left, s), keep, readBackWrite oHead, idleDir iHead,
            Fin.snoc (fun i => moveLeftDir (syms i)) lastIdle, idleDir oHead)
        else
          ((TwoPassPhase.right, S.stepR s syms), keep, readBackWrite oHead, idleDir iHead,
            Fin.snoc (fun _ => Dir3.right) lastIdle, idleDir oHead)
      | (.left, s) =>
        if syms 0 = Γ.start then
          ((TwoPassPhase.emit, s), keep, readBackWrite oHead, idleDir iHead,
            Fin.snoc (fun _ => Dir3.right) lastIdle, idleDir oHead)
        else
          ((TwoPassPhase.left, S.stepL s syms), keep, readBackWrite oHead, idleDir iHead,
            Fin.snoc (fun i => moveLeftDir (syms i)) lastIdle, idleDir oHead)
      | (.emit, s) =>
        ((TwoPassPhase.done, S.start),
          Fin.snoc (fun i => readBackWrite (syms i)) (if S.emit s then Γw.one else Γw.zero),
          readBackWrite oHead, idleDir iHead, idle, idleDir oHead)
      | (.done, s) => allIdle (TwoPassPhase.done, s) iHead wHeads oHead
    δ_right_of_start := by
      rintro ⟨p, s⟩ iHead wHeads oHead
      have hsnocR : ∀ (d : Fin (j + 1) → Dir3) (e : Dir3),
          (∀ i' : Fin (j + 1), wHeads i'.castSucc = Γ.start → d i' = Dir3.right) →
          (wHeads (Fin.last (j + 1)) = Γ.start → e = Dir3.right) →
          ∀ (i : Fin (j + 2)), wHeads i = Γ.start →
            (Fin.snoc d e : Fin (j + 2) → Dir3) i = Dir3.right := by
        intro d e hd he i
        refine Fin.lastCases ?_ ?_ i
        · intro hlast
          rw [Fin.snoc_last]
          exact he hlast
        · intro i' hcs
          rw [Fin.snoc_castSucc]
          exact hd i' hcs
      cases p with
      | right =>
          dsimp only
          split
          · exact ⟨idleDir_right_of_start, fun i hi =>
              hsnocR _ _ (fun _ h => moveLeftDir_right_of_start h)
                (fun h => idleDir_right_of_start h) i hi, idleDir_right_of_start⟩
          · exact ⟨idleDir_right_of_start, fun i hi =>
              hsnocR _ _ (fun _ _ => rfl) (fun h => idleDir_right_of_start h) i hi,
              idleDir_right_of_start⟩
      | left =>
          dsimp only
          split
          · exact ⟨idleDir_right_of_start, fun i hi =>
              hsnocR _ _ (fun _ _ => rfl) (fun h => idleDir_right_of_start h) i hi,
              idleDir_right_of_start⟩
          · exact ⟨idleDir_right_of_start, fun i hi =>
              hsnocR _ _ (fun _ h => moveLeftDir_right_of_start h)
                (fun h => idleDir_right_of_start h) i hi, idleDir_right_of_start⟩
      | emit =>
          exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
      | done => exact rightOfStart_allIdle iHead wHeads oHead }

/-! ## What one step does -/

private theorem move_idle {t : Tape} (h : t.read ≠ Γ.start) : t.move (idleDir t.read) = t := by
  rw [idleDir, ite_eq_right h]
  rfl

private theorem tape_keep {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack _ h, idleDir, ite_eq_right h]
  rfl

private theorem tape_right {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) Dir3.right = ⟨t.head + 1, t.cells⟩ := by
  rw [writeAndMove_readBack _ h]
  rfl

private theorem tape_left {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (moveLeftDir t.read) = ⟨t.head - 1, t.cells⟩ := by
  rw [writeAndMove_readBack _ h, moveLeftDir, ite_eq_right h]
  rfl

/-- The column of symbols under the scanned heads when they are all at cell `h`. -/
def scanCol (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) : Fin (j + 1) → Γ := fun i => cells i h

/-- A configuration of the scanning machine: every scanned head at cell `h`. -/
def twoPassCfg (S : Scanner j) (q : TwoPassQ S) (inp : Tape) (cells : Fin (j + 1) → ℕ → Γ)
    (h : ℕ) (res out : Tape) : Cfg (j + 2) (twoPassTM S).Q where
  state := q
  input := inp
  work := Fin.snoc (fun i => (⟨h, cells i⟩ : Tape)) res
  output := out

/-- The tapes a scan leaves alone: their heads are off the left marker, so every step writes them
back unchanged and idles them. -/
structure ScanOk (inp res out : Tape) : Prop where
  /-- The input head is off the left marker. -/
  inp : inp.read ≠ Γ.start
  /-- The result head is off the left marker. -/
  res : res.read ≠ Γ.start
  /-- The output head is off the left marker. -/
  out : out.read ≠ Γ.start

private theorem work_read (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res : Tape)
    (i : Fin (j + 1)) :
    ((Fin.snoc (fun i => (⟨h, cells i⟩ : Tape)) res : Fin (j + 2) → Tape) i.castSucc).read
      = cells i h := by
  rw [Fin.snoc_castSucc]
  rfl

private theorem work_read_last (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res : Tape) :
    ((Fin.snoc (fun i => (⟨h, cells i⟩ : Tape)) res : Fin (j + 2) → Tape)
      (Fin.last (j + 1))).read = res.read := by
  rw [Fin.snoc_last]

/-- The rightward pass, while tape `0` has not run out. -/
theorem twoPassCfg_step_right (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape)
    (hok : ScanOk inp res out) (hc : ∀ i, cells i h ≠ Γ.start) (hne : cells 0 h ≠ Γ.blank) :
    (twoPassTM S).stepCfg (twoPassCfg S (TwoPassPhase.right, s) inp cells h res out)
      = twoPassCfg S (TwoPassPhase.right, S.stepR s (scanCol cells h)) inp cells (h + 1)
          res out := by
  refine Cfg.ext ?_ ?_ ?_ ?_
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hne, ite_false]
    rfl
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hne, ite_false]
    exact move_idle hok.inp
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hne, ite_false]
      simp only [Fin.snoc_last]
      exact tape_keep hok.res
    · intro i'
      simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hne, ite_false]
      simp only [Fin.snoc_castSucc]
      exact tape_right (show (⟨h, cells i'⟩ : Tape).read ≠ Γ.start from hc i')
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hne, ite_false]
    exact tape_keep hok.out

private theorem tape_start_right {t : Tape} (hh : t.head = 0) (g : Γ) :
    t.writeAndMove g Dir3.right = ⟨1, t.cells⟩ := by
  show (t.write g).move Dir3.right = _
  rw [Tape.write, ite_eq_left hh]
  show (⟨t.head + 1, t.cells⟩ : Tape) = _
  rw [hh]

/-- The turn: tape `0` has run out, so the scan starts back. -/
theorem twoPassCfg_step_turn (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape)
    (hok : ScanOk inp res out) (hc : ∀ i, cells i h ≠ Γ.start) (hb : cells 0 h = Γ.blank) :
    (twoPassTM S).stepCfg (twoPassCfg S (TwoPassPhase.right, s) inp cells h res out)
      = twoPassCfg S (TwoPassPhase.left, s) inp cells (h - 1) res out := by
  refine Cfg.ext ?_ ?_ ?_ ?_
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hb, ite_true]
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hb, ite_true]
    exact move_idle hok.inp
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hb, ite_true]
      simp only [Fin.snoc_last]
      exact tape_keep hok.res
    · intro i'
      simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hb, ite_true]
      simp only [Fin.snoc_castSucc]
      exact tape_left (show (⟨h, cells i'⟩ : Tape).read ≠ Γ.start from hc i')
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hb, ite_true]
    exact tape_keep hok.out

/-- The leftward pass, while the left marker is not yet in sight. -/
theorem twoPassCfg_step_left (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape)
    (hok : ScanOk inp res out) (hc : ∀ i, cells i h ≠ Γ.start) :
    (twoPassTM S).stepCfg (twoPassCfg S (TwoPassPhase.left, s) inp cells h res out)
      = twoPassCfg S (TwoPassPhase.left, S.stepL s (scanCol cells h)) inp cells (h - 1)
          res out := by
  have hns : ¬ (cells 0 h = Γ.start) := hc 0
  refine Cfg.ext ?_ ?_ ?_ ?_
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hns, ite_false]
    rfl
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hns, ite_false]
    exact move_idle hok.inp
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hns, ite_false]
      simp only [Fin.snoc_last]
      exact tape_keep hok.res
    · intro i'
      simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hns, ite_false]
      simp only [Fin.snoc_castSucc]
      exact tape_left (show (⟨h, cells i'⟩ : Tape).read ≠ Γ.start from hc i')
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hns, ite_false]
    exact tape_keep hok.out

/-- The leftward pass reaches the marker and the scan turns to publishing. -/
theorem twoPassCfg_step_stop (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (res out : Tape)
    (hok : ScanOk inp res out) (hs : ∀ i, cells i 0 = Γ.start) :
    (twoPassTM S).stepCfg (twoPassCfg S (TwoPassPhase.left, s) inp cells 0 res out)
      = twoPassCfg S (TwoPassPhase.emit, s) inp cells 1 res out := by
  have hst : cells 0 0 = Γ.start := hs 0
  refine Cfg.ext ?_ ?_ ?_ ?_
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hst, ite_true]
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hst, ite_true]
    exact move_idle hok.inp
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hst, ite_true]
      simp only [Fin.snoc_last]
      exact tape_keep hok.res
    · intro i'
      simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hst, ite_true]
      simp only [Fin.snoc_castSucc]
      exact tape_start_right (show (⟨0, cells i'⟩ : Tape).head = 0 from rfl) _
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read, hst, ite_true]
    exact tape_keep hok.out

/-- Publishing the verdict: one bit onto the result tape, then halt. -/
theorem twoPassCfg_step_emit (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape)
    (hok : ScanOk inp res out) (hc : ∀ i, cells i h ≠ Γ.start) :
    (twoPassTM S).stepCfg (twoPassCfg S (TwoPassPhase.emit, s) inp cells h res out)
      = twoPassCfg S (TwoPassPhase.done, S.start) inp cells h
          (res.write (Γ.ofBool (S.emit s))) out := by
  refine Cfg.ext ?_ ?_ ?_ ?_
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM]
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM]
    exact move_idle hok.inp
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read_last]
      simp only [Fin.snoc_last]
      show res.writeAndMove _ (idleDir res.read) = _
      rw [idleDir, ite_eq_right hok.res]
      cases hb : S.emit s <;> rfl
    · intro i'
      simp only [TM.stepCfg, twoPassCfg, twoPassTM, work_read]
      simp only [Fin.snoc_castSucc]
      exact tape_keep (show (⟨h, cells i'⟩ : Tape).read ≠ Γ.start from hc i')
  · simp only [TM.stepCfg, twoPassCfg, twoPassTM]
    exact tape_keep hok.out

/-! ## What a whole scan does -/

/-- The tape shape a scan expects: every tape carries its left marker and nothing else does, and
tape `0` runs for exactly `len` cells. -/
structure ScanTape (cells : Fin (j + 1) → ℕ → Γ) (len : ℕ) : Prop where
  /-- Cell zero of every scanned tape is the left marker. -/
  start : ∀ i, cells i 0 = Γ.start
  /-- No other cell is. -/
  ne_start : ∀ i q, 1 ≤ q → cells i q ≠ Γ.start
  /-- Tape `0` is non-blank throughout its length. -/
  ne_blank : ∀ q, 1 ≤ q → q ≤ len → cells 0 q ≠ Γ.blank
  /-- And blank immediately after. -/
  blank : cells 0 (len + 1) = Γ.blank

private theorem not_halted_right (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape) :
    (twoPassCfg S (TwoPassPhase.right, s) inp cells h res out).state ≠ (twoPassTM S).qhalt := by
  intro hq
  exact TwoPassPhase.noConfusion (congrArg Prod.fst hq)

private theorem not_halted_left (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape) :
    (twoPassCfg S (TwoPassPhase.left, s) inp cells h res out).state ≠ (twoPassTM S).qhalt := by
  intro hq
  exact TwoPassPhase.noConfusion (congrArg Prod.fst hq)

private theorem not_halted_emit (S : Scanner j) (s : S.σ) (inp : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ) (res out : Tape) :
    (twoPassCfg S (TwoPassPhase.emit, s) inp cells h res out).state ≠ (twoPassTM S).qhalt := by
  intro hq
  exact TwoPassPhase.noConfusion (congrArg Prod.fst hq)

/-- **The rightward pass.** -/
theorem twoPassCfg_run_right (S : Scanner j) (inp res out : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (len : ℕ)
    (hok : ScanOk inp res out) (ht : ScanTape cells len) :
    ∀ d p, p + d = len →
      (twoPassTM S).reachesIn d
        (twoPassCfg S (TwoPassPhase.right, S.runR (scanCol cells) p) inp cells (p + 1) res out)
        (twoPassCfg S (TwoPassPhase.right, S.runR (scanCol cells) len) inp cells (len + 1)
          res out) := by
  intro d
  induction d with
  | zero =>
      intro p hp
      rw [show p = len by omega]
      exact reachesIn.zero
  | succ d ih =>
      intro p hp
      have hne : cells 0 (p + 1) ≠ Γ.blank := ht.ne_blank (p + 1) (by omega) (by omega)
      have hc : ∀ i, cells i (p + 1) ≠ Γ.start := fun i => ht.ne_start i (p + 1) (by omega)
      refine reachesIn.step ?_ (ih (p + 1) (by omega))
      rw [step_of_not_halted _ (not_halted_right S _ inp cells (p + 1) res out),
        twoPassCfg_step_right S _ inp cells (p + 1) res out hok hc hne]
      rfl

/-- **The leftward pass.** -/
theorem twoPassCfg_run_left (S : Scanner j) (inp res out : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (len : ℕ)
    (hok : ScanOk inp res out) (ht : ScanTape cells len) :
    ∀ (h : ℕ) (s : S.σ),
      (twoPassTM S).reachesIn h
        (twoPassCfg S (TwoPassPhase.left, s) inp cells h res out)
        (twoPassCfg S (TwoPassPhase.left, S.runL (scanCol cells) h s) inp cells 0 res out) := by
  intro h
  induction h with
  | zero => intro s; exact reachesIn.zero
  | succ h ih =>
      intro s
      have hc : ∀ i, cells i (h + 1) ≠ Γ.start := fun i => ht.ne_start i (h + 1) (by omega)
      refine reachesIn.step ?_ (ih _)
      rw [step_of_not_halted _ (not_halted_left S _ inp cells (h + 1) res out),
        twoPassCfg_step_left S _ inp cells (h + 1) res out hok hc]
      rfl

/-- **A whole scan.** Started with every scanned head on cell one, the machine walks tape `0` to
its first blank and back, and halts with the automaton's verdict written on the result tape.
Nothing else on any tape moves. -/
theorem twoPassCfg_run (S : Scanner j) (inp res out : Tape)
    (cells : Fin (j + 1) → ℕ → Γ) (len : ℕ)
    (hok : ScanOk inp res out) (ht : ScanTape cells len) :
    (twoPassTM S).reachesIn (2 * len + 3)
      (twoPassCfg S (twoPassTM S).qstart inp cells 1 res out)
      (twoPassCfg S (TwoPassPhase.done, S.start) inp cells 1
        (res.write (Γ.ofBool (S.emit (S.run (scanCol cells) len)))) out) := by
  have hcL : ∀ i, cells i (len + 1) ≠ Γ.start := fun i => ht.ne_start i (len + 1) (by omega)
  have hc1 : ∀ i, cells i 1 ≠ Γ.start := fun i => ht.ne_start i 1 (by omega)
  have hstart : (twoPassCfg S (twoPassTM S).qstart inp cells 1 res out)
      = twoPassCfg S (TwoPassPhase.right, S.runR (scanCol cells) 0) inp cells (0 + 1) res out :=
    rfl
  have hturn : (twoPassTM S).reachesIn 1
      (twoPassCfg S (TwoPassPhase.right, S.runR (scanCol cells) len) inp cells (len + 1) res out)
      (twoPassCfg S (TwoPassPhase.left, S.runR (scanCol cells) len) inp cells len res out) := by
    refine reachesIn.step ?_ reachesIn.zero
    rw [step_of_not_halted _ (not_halted_right S _ inp cells (len + 1) res out),
      twoPassCfg_step_turn S _ inp cells (len + 1) res out hok hcL ht.blank]
    rfl
  have hstop : (twoPassTM S).reachesIn 1
      (twoPassCfg S (TwoPassPhase.left, S.run (scanCol cells) len) inp cells 0 res out)
      (twoPassCfg S (TwoPassPhase.emit, S.run (scanCol cells) len) inp cells 1 res out) := by
    refine reachesIn.step ?_ reachesIn.zero
    rw [step_of_not_halted _ (not_halted_left S _ inp cells 0 res out),
      twoPassCfg_step_stop S _ inp cells res out hok ht.start]
  have hemit : (twoPassTM S).reachesIn 1
      (twoPassCfg S (TwoPassPhase.emit, S.run (scanCol cells) len) inp cells 1 res out)
      (twoPassCfg S (TwoPassPhase.done, S.start) inp cells 1
        (res.write (Γ.ofBool (S.emit (S.run (scanCol cells) len)))) out) := by
    refine reachesIn.step ?_ reachesIn.zero
    rw [step_of_not_halted _ (not_halted_emit S _ inp cells 1 res out),
      twoPassCfg_step_emit S _ inp cells 1 res out hok hc1]
  have hcount : 2 * len + 3 = len + (1 + (len + (1 + 1))) := by omega
  rw [hstart, hcount]
  refine (twoPassTM S).reachesIn_trans (twoPassCfg_run_right S inp res out cells len hok ht len 0
    (by omega)) ?_
  refine (twoPassTM S).reachesIn_trans hturn ?_
  refine (twoPassTM S).reachesIn_trans (twoPassCfg_run_left S inp res out cells len hok ht len _)
    ?_
  exact (twoPassTM S).reachesIn_trans hstop hemit

/-- A scan ends halted. -/
theorem twoPassCfg_halted (S : Scanner j) (inp : Tape) (cells : Fin (j + 1) → ℕ → Γ) (h : ℕ)
    (res out : Tape) :
    (twoPassTM S).halted (twoPassCfg S (TwoPassPhase.done, S.start) inp cells h res out) := rfl

/-- **The scan as a Hoare triple**, which is the form `TM.seqTM` and `TM.loopTM` compose. -/
theorem twoPassTM_hoareTime (S : Scanner j) (cells : Fin (j + 1) → ℕ → Γ) (len : ℕ)
    (inp₀ out₀ res₀ : Tape) (hok : ScanOk inp₀ res₀ out₀) (ht : ScanTape cells len) :
    (twoPassTM S).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) res₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape))
          (res₀.write (Γ.ofBool (S.emit (S.run (scanCol cells) len)))))
      (2 * len + 3) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact ⟨_, 2 * len + 3, le_rfl, twoPassCfg_run S _ _ _ cells len hok ht,
    twoPassCfg_halted S _ cells 1 _ _, rfl, rfl, rfl⟩

/-- **A check on the whole register set.** The scanner names the columns it reads, so a check
needs neither its registers moved next to one another nor a private copy of them. -/
def checkTM {jd jj : ℕ} (S : Scanner jd) (f : Fin (jd + 1) → Fin (jj + 1)) : TM (jj + 2) :=
  twoPassTM (S.comap f)

/-- **Its contract**: the verdict of the scanner, read off the named columns. -/
theorem checkTM_hoareTime {jd jj : ℕ} (S : Scanner jd) (f : Fin (jd + 1) → Fin (jj + 1))
    (cells : Fin (jj + 1) → ℕ → Γ) (len : ℕ) (inp₀ out₀ res₀ : Tape)
    (hok : ScanOk inp₀ res₀ out₀) (ht : ScanTape cells len) :
    (checkTM S f).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape)) res₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work = Fin.snoc (fun i => (⟨1, cells i⟩ : Tape))
          (res₀.write (Γ.ofBool (S.emit (S.run (fun q i => cells (f i) q) len)))))
      (2 * len + 3) := by
  have h := twoPassTM_hoareTime (S.comap f) cells len inp₀ out₀ res₀ hok ht
  simpa only [checkTM, Scanner.comap_run, Scanner.comap_emit, scanCol] using h

end TM

end Complexity
