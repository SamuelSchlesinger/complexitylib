/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Classes.Containments

/-!
# `{x : #false x = #true x}`: equal-count / "balanced" language

The balanced language contains every string with as many `false`s as
`true`s — any interleaving, not just the blocked form `0ⁿ 1ⁿ`. The TM
generalizes `anbnTM` by tracking which bit is currently in excess in the
control state, while using the single work tape as a unary counter for
the size of the excess.

**Invariant**: after consuming a prefix `p`, the work head position
equals `|#false(p) - #true(p)|`, and the control state records whether
`#false > #true` (`scanExcess0`), `#true > #false` (`scanExcess1`), or
equality (either state with head at cell 0).

Emptiness (`h = 0`) is detected structurally by the work head reading
`▷` at cell 0 — the same trick as in `anbnTM`.

## Main definitions

- `TM.balancedTM` — 5-state 1-work-tape push-down machine.
- `Language.balanced` — `{x | x.count false = x.count true}`.

## Main results

- `TM.balancedTM_reachesIn` — halts in `|x| + 3` steps on every input.
- `balanced_in_DTIME`, `balanced_mem_P`.
-/


public section

namespace Complexity

open Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Control state
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `balancedTM`.

    - `start`       : initial state. Moves all heads from cell 0 (▷) to cell 1.
    - `initWork`    : rewinds the work head back to cell 0.
    - `scanExcess0` : scanning; the stack (unary counter) holds `#false - #true`.
                      `h = 0` (work reads `▷`) means equality so far.
    - `scanExcess1` : scanning; the stack holds `#true - #false`.
    - `done`        : halted. -/
inductive BalancedPhase where
  | start | initWork | scanExcess0 | scanExcess1 | done
  deriving DecidableEq

instance : Fintype BalancedPhase where
  elems := {.start, .initWork, .scanExcess0, .scanExcess1, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- The push-down TM
-- ════════════════════════════════════════════════════════════════════════

/-- Push-down TM deciding the balanced language. One work tape is used
    as a unary counter. The sign (which bit is in excess) is encoded in
    the control state; the stack height is the absolute difference. -/
@[expose] def balancedTM : TM 1 where
  Q := BalancedPhase
  qstart := .start
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .start =>
      -- All heads at 0 reading ▷: move right. Writes at cell 0 are no-ops.
      (.initWork, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | .initWork =>
      -- Rewind work head from cell 1 to cell 0. Input and output stay.
      (.scanExcess0, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => moveLeftDir (wHeads i), idleDir oHead)
    | .scanExcess0 =>
      if iHead = Γ.blank then
        -- End of input: accept iff stack empty (= balanced so far).
        if wHeads 0 = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), .one,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.done, fun i => readBackWrite (wHeads i), .zero,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.zero then
        -- Saw a `0`: push. (Already at `scanExcess0`, or was at `h=0`.)
        (.scanExcess0, fun _ => .one, readBackWrite oHead,
         .right, fun _ => .right, idleDir oHead)
      else if iHead = Γ.one then
        if wHeads 0 = Γ.start then
          -- `h = 0` (balanced so far) and saw `1`: push, switch sign.
          (.scanExcess1, fun _ => .one, readBackWrite oHead,
           .right, fun _ => .right, idleDir oHead)
        else
          -- `h ≥ 1` excess 0 and saw `1`: pop. Stay in `scanExcess0` —
          -- if `h` drops to `0`, the next step will detect it.
          (.scanExcess0, fun _ => .blank, readBackWrite oHead,
           .right, fun i => moveLeftDir (wHeads i), idleDir oHead)
      else
        -- iHead = Γ.start: vacuous in real runs, but δ must be total.
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanExcess1 =>
      if iHead = Γ.blank then
        if wHeads 0 = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), .one,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.done, fun i => readBackWrite (wHeads i), .zero,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.one then
        -- Saw a `1`: push.
        (.scanExcess1, fun _ => .one, readBackWrite oHead,
         .right, fun _ => .right, idleDir oHead)
      else if iHead = Γ.zero then
        if wHeads 0 = Γ.start then
          -- `h = 0` and saw `0`: push, switch sign.
          (.scanExcess0, fun _ => .one, readBackWrite oHead,
           .right, fun _ => .right, idleDir oHead)
        else
          -- `h ≥ 1` excess 1 and saw `0`: pop.
          (.scanExcess1, fun _ => .blank, readBackWrite oHead,
           .right, fun i => moveLeftDir (wHeads i), idleDir oHead)
      else
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done =>
      allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .start =>
      exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    | .initWork =>
      exact ⟨idleDir_right_of_start, fun _ h => by
               simp only [moveLeftDir, h, ↓reduceIte],
             idleDir_right_of_start⟩
    | .scanExcess0 =>
      dsimp only []
      split
      · split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
      split
      · refine ⟨fun h => by simp_all, fun _ _ => rfl, idleDir_right_of_start⟩
      split
      · split
        · exact ⟨fun _ => rfl, fun _ _ => rfl, idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ hi => by
            simp only [moveLeftDir, hi, ↓reduceIte],
            idleDir_right_of_start⟩
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .scanExcess1 =>
      dsimp only []
      split
      · split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
      split
      · refine ⟨fun h => by simp_all, fun _ _ => rfl, idleDir_right_of_start⟩
      split
      · split
        · exact ⟨fun _ => rfl, fun _ _ => rfl, idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ hi => by
            simp only [moveLeftDir, hi, ↓reduceIte],
            idleDir_right_of_start⟩
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .done =>
      exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Step 1: `.start` → `.initWork`. All three heads advance from 0 to 1. -/
private theorem balancedTM_step_start
    (c : Cfg 1 balancedTM.Q) (hst : c.state = .start)
    (hih : c.input.head = 0) (hwh : ∀ i, (c.work i).head = 0)
    (hoh : c.output.head = 0) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.initWork ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 1) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hih]
  · intro i
    simp [Tape.writeAndMove, Tape.move, Tape.write, hwh i]
  · intro i
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hwh i]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hoh]

/-- Step 2: `.initWork` → `.scanExcess0`. Work rewinds from 1 to 0. -/
private theorem balancedTM_step_initWork
    (c : Cfg 1 balancedTM.Q) (hst : c.state = .initWork)
    (hih : c.input.head = 1) (hih_nb : c.input.cells 1 ≠ Γ.start)
    (hwh : ∀ i, (c.work i).head = 1)
    (hw_nb : ∀ i, (c.work i).cells 1 ≠ Γ.start)
    (hoh : c.output.head = 1) (hoh_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess0 ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 0) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte]
  have hi_read : c.input.read ≠ Γ.start := by
    simp only [Tape.read, hih]; exact hih_nb
  have ho_read : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hoh]; exact hoh_nb
  have hw_read : ∀ i, (c.work i).read ≠ Γ.start := by
    intro i; simp only [Tape.read, hwh i]; exact hw_nb i
  have hi_stay : idleDir c.input.read = Dir3.stay := by
    simp [idleDir, hi_read]
  have ho_stay : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, ho_read]
  have hw_left : ∀ i, moveLeftDir (c.work i).read = Dir3.left := fun i => by
    simp [moveLeftDir, hw_read i]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hi_stay, hih]
  · simp [Tape.move, hi_stay]
  · intro i
    simp [Tape.writeAndMove, Tape.move, Tape.write, hw_left i, hwh i]
  · intro i
    exact tape_readBackWrite_preserves (c.work i) _ (Or.inr (hw_read i))
  · simp [Tape.writeAndMove, Tape.move, Tape.write, ho_stay, hoh]
  · exact tape_readBackWrite_preserves c.output _ (Or.inr ho_read)

-- ════════════════════════════════════════════════════════════════════════
-- Helper: writing from `Γw` preserves "no ▷ at cells ≥ 1"
-- ════════════════════════════════════════════════════════════════════════

/-- Writing a symbol from `Γw` preserves the "no ▷ at cells ≥ 1" invariant. -/
private theorem writeAndMove_preserves_nonStart (t : Tape) (s : Γw) (d : Dir3)
    (hinv : ∀ j ≥ 1, t.cells j ≠ Γ.start) :
    ∀ j ≥ 1, (t.writeAndMove (s : Γ) d).cells j ≠ Γ.start := by
  intro j hj
  simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
  split
  · exact hinv j hj
  · by_cases hjh : j = t.head
    · subst hjh
      simp only [Function.update_self]
      cases s <;> simp [Γw.toΓ]
    · show Function.update t.cells t.head s.toΓ j ≠ Γ.start
      rw [Function.update_of_ne hjh]
      exact hinv j hj

-- ════════════════════════════════════════════════════════════════════════
-- Expected output function
-- ════════════════════════════════════════════════════════════════════════

/-- The output that `balancedTM` produces when run from scan state `s`
    with stack height `h` and remaining input `rest`. Structurally
    recursive on `rest`. -/
def balancedExpected : BalancedPhase → ℕ → List Bool → Γw
  -- End-of-input: accept iff the stack is empty.
  | .scanExcess0, 0, [] => .one
  | .scanExcess0, _ + 1, [] => .zero
  | .scanExcess1, 0, [] => .one
  | .scanExcess1, _ + 1, [] => .zero
  -- scanExcess0: `false` pushes, `true` pops or switches.
  | .scanExcess0, h, false :: rest => balancedExpected .scanExcess0 (h + 1) rest
  | .scanExcess0, 0, true :: rest => balancedExpected .scanExcess1 1 rest
  | .scanExcess0, h + 1, true :: rest => balancedExpected .scanExcess0 h rest
  -- scanExcess1: `true` pushes, `false` pops or switches.
  | .scanExcess1, h, true :: rest => balancedExpected .scanExcess1 (h + 1) rest
  | .scanExcess1, 0, false :: rest => balancedExpected .scanExcess0 1 rest
  | .scanExcess1, h + 1, false :: rest => balancedExpected .scanExcess1 h rest
  -- Non-scan states: vacuous (never queried).
  | .start, _, _ => .blank
  | .initWork, _, _ => .blank
  | .done, _, _ => .blank

-- ════════════════════════════════════════════════════════════════════════
-- Scan invariant
-- ════════════════════════════════════════════════════════════════════════

/-- Invariants for a configuration during the scan phase. Identical shape
    to `AnBn.BalancedScanInv`: the input is a suffix of `x.map Γ.ofBool` starting at
    position `k + 1`, the work head equals the stack height `h`, and the
    output tape is pristine at head position `1`. -/
structure BalancedScanInv (c : Cfg 1 balancedTM.Q) (x : List Bool) (k h : ℕ) : Prop where
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  wh : (c.work 0).head = h
  wstart : (c.work 0).cells 0 = Γ.start
  wns : ∀ j, j ≥ 1 → (c.work 0).cells j ≠ Γ.start
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace BalancedScanInv
variable {c : Cfg 1 balancedTM.Q} {x : List Bool} {k h : ℕ}

/-- `Tape.init` at a position ≥ 1 is never `Γ.start`. -/
private theorem Tape.init_ns (l : List Γ)
    (hl : ∀ b ∈ l, b ≠ Γ.start) (j : ℕ) (hj : j ≥ 1) :
    (Tape.init l).cells j ≠ Γ.start := by
  have hj' : j ≠ 0 := by omega
  simp only [Tape.init, hj', ↓reduceIte]
  rcases hget : l[j - 1]? with _ | v
  · simp
  · have hmem := List.mem_of_getElem? hget
    have := hl v hmem
    simp [this]

private theorem map_ofBool_ns (x : List Bool) (b : Γ) :
    b ∈ x.map Γ.ofBool → b ≠ Γ.start := by
  intro hb
  rw [List.mem_map] at hb
  obtain ⟨b', _, hb'⟩ := hb
  cases b' <;> (simp [Γ.ofBool] at hb'; subst hb'; decide)

/-- Input reads the `k`-th bit when `k < x.length`. -/
private theorem read_bit (inv : BalancedScanInv c x k h) (hk : k < x.length) :
    c.input.read = Γ.ofBool (x[k]'hk) := by
  have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
  simp only [Tape.read, inv.ih, inv.ic]
  show (Tape.init (x.map Γ.ofBool)).cells (k + 1) = _
  have hkmap : k < (x.map Γ.ofBool).length := by rw [hmap_len]; exact hk
  simp only [Tape.init, show k + 1 ≠ 0 from by omega, ↓reduceIte,
    Nat.add_sub_cancel, List.getElem?_eq_getElem hkmap, Option.getD_some,
    List.getElem_map]

/-- Input reads blank when `k = x.length`. -/
private theorem read_blank (inv : BalancedScanInv c x x.length h) : c.input.read = Γ.blank := by
  simp only [Tape.read, inv.ih, inv.ic]
  show (Tape.init (x.map Γ.ofBool)).cells (x.length + 1) = Γ.blank
  simp [Tape.init]

/-- Input cells are never ▷ at positions ≥ 1. -/
private theorem input_ns (inv : BalancedScanInv c x k h) :
    ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start := by
  intro j hj
  rw [inv.ic]
  exact Tape.init_ns _ (map_ofBool_ns x) j hj

/-- Work reads ▷ iff the work head is at 0. -/
private theorem work_read_start_iff (inv : BalancedScanInv c x k h) :
    (c.work 0).read = Γ.start ↔ h = 0 := by
  simp only [Tape.read, inv.wh]
  constructor
  · intro hr
    by_contra hne
    have h1 : h ≥ 1 := by omega
    exact inv.wns h h1 hr
  · intro h0; rw [h0]; exact inv.wstart

private theorem output_read (inv : BalancedScanInv c x k h) : c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : BalancedScanInv c x k h) :
    idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read]

end BalancedScanInv

-- ════════════════════════════════════════════════════════════════════════
-- Scan step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Halt from `scanExcess0` at blank with empty stack → done, output 1. -/
private theorem balancedTM_step_scanExcess0_halt_empty
    (c : Cfg 1 balancedTM.Q) (x : List Bool)
    (hst : c.state = .scanExcess0) (inv : BalancedScanInv c x x.length 0) :
    ∃ c', balancedTM.step c = some c' ∧ balancedTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ (idleDir c.output.read)).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- Halt from `scanExcess0` at blank with non-empty stack → done, output 0. -/
private theorem balancedTM_step_scanExcess0_halt_nonempty
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (h : ℕ) (hh : h ≥ 1)
    (hst : c.state = .scanExcess0) (inv : BalancedScanInv c x x.length h) :
    ∃ c', balancedTM.step c = some c' ∧ balancedTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_right hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ (idleDir c.output.read)).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- Halt from `scanExcess1` at blank with empty stack → done, output 1. -/
private theorem balancedTM_step_scanExcess1_halt_empty
    (c : Cfg 1 balancedTM.Q) (x : List Bool)
    (hst : c.state = .scanExcess1) (inv : BalancedScanInv c x x.length 0) :
    ∃ c', balancedTM.step c = some c' ∧ balancedTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ _).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- Halt from `scanExcess1` at blank with non-empty stack → done, output 0. -/
private theorem balancedTM_step_scanExcess1_halt_nonempty
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (h : ℕ) (hh : h ≥ 1)
    (hst : c.state = .scanExcess1) (inv : BalancedScanInv c x x.length h) :
    ∃ c', balancedTM.step c = some c' ∧ balancedTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_right hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ _).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- Push step: `scanExcess0 + iHead=0` → `scanExcess0`, `h → h + 1`, `k → k + 1`. -/
private theorem balancedTM_step_scanExcess0_push
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanExcess0) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : BalancedScanInv c x k h) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess0 ∧ BalancedScanInv c' x (k + 1) (h + 1) := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_one : c.input.read ≠ Γ.one := by rw [hir]; decide
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_left hir, ite_eq_right hir_ne_one]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).head = h + 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, inv.wh]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.one.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · intro j hj
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Switch step: `scanExcess0 + iHead=1 + h=0` → `scanExcess1`, `h=0→1`. -/
private theorem balancedTM_step_scanExcess0_switch
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .scanExcess0) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : BalancedScanInv c x k 0) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess1 ∧ BalancedScanInv c' x (k + 1) 1 := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).head = 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, inv.wh]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.one.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · intro j hj
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Pop step: `scanExcess0 + iHead=1 + h=h'+1` → `scanExcess0`, `h'+1→h'`. -/
private theorem balancedTM_step_scanExcess0_pop
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanExcess0) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : BalancedScanInv c x k (h + 1)) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess0 ∧ BalancedScanInv c' x (k + 1) h := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr_ne : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_right hwr_ne]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · have hmv : moveLeftDir (c.work 0).read = Dir3.left := by
      simp [moveLeftDir, hwr_ne]
    show ((c.work 0).writeAndMove Γw.blank.toΓ (moveLeftDir (c.work 0).read)).head = h
    simp only [Tape.writeAndMove, hmv, Tape.move, Tape.write_head, inv.wh]
    omega
  · show ((c.work 0).writeAndMove Γw.blank.toΓ (moveLeftDir (c.work 0).read)).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.blank.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · intro j hj
    show ((c.work 0).writeAndMove Γw.blank.toΓ _).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Push step: `scanExcess1 + iHead=1` → `scanExcess1`, `h → h + 1`. -/
private theorem balancedTM_step_scanExcess1_push
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanExcess1) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : BalancedScanInv c x k h) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess1 ∧ BalancedScanInv c' x (k + 1) (h + 1) := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).head = h + 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, inv.wh]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.one.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · intro j hj
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Switch step: `scanExcess1 + iHead=0 + h=0` → `scanExcess0`, `h=0→1`. -/
private theorem balancedTM_step_scanExcess1_switch
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .scanExcess1) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : BalancedScanInv c x k 0) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess0 ∧ BalancedScanInv c' x (k + 1) 1 := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_one : c.input.read ≠ Γ.one := by rw [hir]; decide
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_one, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).head = 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, inv.wh]
  · show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.one.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · intro j hj
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Pop step: `scanExcess1 + iHead=0 + h=h'+1` → `scanExcess1`, `h'+1→h'`. -/
private theorem balancedTM_step_scanExcess1_pop
    (c : Cfg 1 balancedTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanExcess1) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : BalancedScanInv c x k (h + 1)) :
    ∃ c', balancedTM.step c = some c' ∧
      c'.state = BalancedPhase.scanExcess1 ∧ BalancedScanInv c' x (k + 1) h := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_one : c.input.read ≠ Γ.one := by rw [hir]; decide
  have hwr_ne : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, balancedTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_one, ite_eq_left hir, ite_eq_right hwr_ne]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · have hmv : moveLeftDir (c.work 0).read = Dir3.left := by
      simp [moveLeftDir, hwr_ne]
    show ((c.work 0).writeAndMove Γw.blank.toΓ _).head = h
    simp only [Tape.writeAndMove, hmv, Tape.move, Tape.write_head, inv.wh]
    omega
  · show ((c.work 0).writeAndMove Γw.blank.toΓ _).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.blank.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · intro j hj
    show ((c.work 0).writeAndMove Γw.blank.toΓ _).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

-- ════════════════════════════════════════════════════════════════════════
-- Scan induction lemma
-- ════════════════════════════════════════════════════════════════════════

/-- **Main scan invariant**: from state `s ∈ {scanExcess0, scanExcess1}`
    with stack height `h` and remaining input `rest`, the TM halts in
    `rest.length + 1` steps, writing `balancedExpected s h rest` to the
    output. -/
private theorem balancedTM_scan_to_halt (x : List Bool) :
    ∀ (rest : List Bool) (s : BalancedPhase) (k h : ℕ) (c : Cfg 1 balancedTM.Q),
      (s = .scanExcess0 ∨ s = .scanExcess1) →
      c.state = s → k + rest.length = x.length → rest = x.drop k →
      BalancedScanInv c x k h →
      ∃ c', balancedTM.reachesIn (rest.length + 1) c c' ∧
        balancedTM.halted c' ∧
        c'.output.cells 1 = (balancedExpected s h rest).toΓ := by
  intro rest
  induction rest with
  | nil =>
    intro s k h c hs hst hlen _ inv
    have hk : k = x.length := by simpa using hlen
    subst hk
    rcases hs with hs | hs <;> rcases h with _ | h' <;> subst hs
    · -- scanExcess0 + h=0 → output 1
      obtain ⟨c', hstep, hhalt, hout⟩ := balancedTM_step_scanExcess0_halt_empty c x hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [balancedExpected, hout, Γw.toΓ]⟩
    · -- scanExcess0 + h≥1 → output 0
      obtain ⟨c', hstep, hhalt, hout⟩ :=
        balancedTM_step_scanExcess0_halt_nonempty c x (h' + 1) (by omega) hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [balancedExpected, hout, Γw.toΓ]⟩
    · -- scanExcess1 + h=0 → output 1
      obtain ⟨c', hstep, hhalt, hout⟩ := balancedTM_step_scanExcess1_halt_empty c x hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [balancedExpected, hout, Γw.toΓ]⟩
    · -- scanExcess1 + h≥1 → output 0
      obtain ⟨c', hstep, hhalt, hout⟩ :=
        balancedTM_step_scanExcess1_halt_nonempty c x (h' + 1) (by omega) hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [balancedExpected, hout, Γw.toΓ]⟩
  | cons b rest' ih =>
    intro s k h c hs hst hlen hrest inv
    have hcons_len : (b :: rest').length = rest'.length + 1 := rfl
    have hk : k < x.length := by rw [hcons_len] at hlen; omega
    have hbit : x[k]'hk = b := by
      have hsymm : x.drop k = b :: rest' := hrest.symm
      have h1 : (x.drop k)[0]? = some b := by rw [hsymm]; rfl
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hk] at h1
      exact Option.some.inj h1
    have hlen' : (k + 1) + rest'.length = x.length := by
      rw [hcons_len] at hlen; omega
    have hrest' : rest' = x.drop (k + 1) := by
      rw [← List.drop_drop, ← hrest]; simp
    rcases hs with hs | hs <;> subst hs <;> cases b
    · -- scanExcess0 + false bit (push)
      obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
        balancedTM_step_scanExcess0_push c x k h hst hk hbit inv
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        ih .scanExcess0 (k + 1) (h + 1) c₁ (Or.inl rfl) hst₁ hlen' hrest' inv₁
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]; simp [balancedExpected]
    · -- scanExcess0 + true bit
      cases h with
      | zero =>
        -- switch to scanExcess1 with h=1
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          balancedTM_step_scanExcess0_switch c x k hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanExcess1 (k + 1) 1 c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [balancedExpected]
      | succ h' =>
        -- pop, stay scanExcess0 with h=h'
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          balancedTM_step_scanExcess0_pop c x k h' hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanExcess0 (k + 1) h' c₁ (Or.inl rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [balancedExpected]
    · -- scanExcess1 + false bit
      cases h with
      | zero =>
        -- switch to scanExcess0 with h=1
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          balancedTM_step_scanExcess1_switch c x k hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanExcess0 (k + 1) 1 c₁ (Or.inl rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [balancedExpected]
      | succ h' =>
        -- pop, stay scanExcess1 with h=h'
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          balancedTM_step_scanExcess1_pop c x k h' hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanExcess1 (k + 1) h' c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [balancedExpected]
    · -- scanExcess1 + true bit (push)
      obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
        balancedTM_step_scanExcess1_push c x k h hst hk hbit inv
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        ih .scanExcess1 (k + 1) (h + 1) c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]; simp [balancedExpected]

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `balancedTM` halts in `|x| + 3` steps on every input, writing the
    correct answer (`Γ.one` iff `x.count false = x.count true`, else
    `Γ.zero`) to output cell 1. -/
theorem balancedTM_reachesIn (x : List Bool) :
    ∃ c', balancedTM.reachesIn (x.length + 3) (balancedTM.initCfg x) c' ∧
      balancedTM.halted c' ∧
      c'.output.cells 1 = (balancedExpected .scanExcess0 0 x).toΓ := by
  -- Step 1: .start → .initWork
  obtain ⟨c₁, hstep1, hst1, hih1, hic1, hwh1, hwc1, hoh1, hoc1⟩ :=
    balancedTM_step_start (balancedTM.initCfg x) rfl rfl (by intro _; rfl) rfl
  -- Step 2: .initWork → .scanExcess0
  have hi_nb : c₁.input.cells 1 ≠ Γ.start := by
    rw [hic1]
    show (Tape.init (x.map Γ.ofBool)).cells 1 ≠ Γ.start
    exact BalancedScanInv.Tape.init_ns _ (BalancedScanInv.map_ofBool_ns x) 1 (by omega)
  have hw_nb : ∀ i, (c₁.work i).cells 1 ≠ Γ.start := by
    intro i
    rw [hwc1 i]
    have : (balancedTM.initCfg x).work i = Tape.init [] := by rfl
    rw [this]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  have ho_nb : c₁.output.cells 1 ≠ Γ.start := by
    rw [hoc1]
    have : (balancedTM.initCfg x).output = Tape.init [] := by rfl
    rw [this]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  obtain ⟨c₂, hstep2, hst2, hih2, hic2, hwh2, hwc2, hoh2, hoc2⟩ :=
    balancedTM_step_initWork c₁ hst1 hih1 hi_nb hwh1 hw_nb hoh1 ho_nb
  have hinv : BalancedScanInv c₂ x 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hic2, hic1]
    · simp [hih2]
    · exact hwh2 0
    · rw [hwc2 0, hwc1 0]
      have : (balancedTM.initCfg x).work 0 = Tape.init [] := by rfl
      rw [this]
      show (Tape.init []).cells 0 = Γ.start
      simp [Tape.init]
    · intro j hj
      rw [hwc2 0, hwc1 0]
      have : (balancedTM.initCfg x).work 0 = Tape.init [] := by rfl
      rw [this]
      show (Tape.init []).cells j ≠ Γ.start
      have hj' : j ≠ 0 := by omega
      simp [Tape.init, hj']
    · exact hoh2
    · rw [hoc2]; exact ho_nb
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    balancedTM_scan_to_halt x x .scanExcess0 0 0 c₂ (Or.inl rfl) hst2 (by simp) (by simp) hinv
  refine ⟨c', ?_, hhalt, hout⟩
  -- 1 (start) + 1 (initWork) + (|x| + 1) (scan) = |x| + 3
  have hsteps : x.length + 3 = x.length + 1 + 1 + 1 := by ring
  rw [hsteps]
  exact .step hstep1 (.step hstep2 hreach)

end TM

namespace Language

/-- **The balanced language** — strings with equal numbers of `false`s and
    `true`s. Generalizes `anbn` to arbitrary interleavings. -/
def balanced : Language :=
  {x : List Bool | x.count false = x.count true}

end Language

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Characterization of `balancedExpected` in terms of string shape
-- ════════════════════════════════════════════════════════════════════════

/-- Signed counter: `#false(x) - #true(x)` as an integer. -/
private def boolDiff (x : List Bool) : ℤ :=
  (x.count false : ℤ) - (x.count true : ℤ)

private theorem boolDiff_nil : boolDiff [] = 0 := by
  simp [boolDiff]

private theorem boolDiff_cons_false (rest : List Bool) :
    boolDiff (false :: rest) = boolDiff rest + 1 := by
  simp [boolDiff]; ring

private theorem boolDiff_cons_true (rest : List Bool) :
    boolDiff (true :: rest) = boolDiff rest - 1 := by
  simp [boolDiff]; ring

/-- **Combined characterization**: after consuming a suffix from either
    scan state, the output is `.one` iff the signed count-difference of
    the remaining input equals the signed stack height (with the
    convention that `scanExcess0` means the stack is "negative" — excess
    `false`s — so we need `boolDiff rest = -h`, and `scanExcess1` means
    "positive" so we need `boolDiff rest = +h`).

    Proved by a single induction on `rest.length` to avoid mutual
    recursion between the two scan states. -/
private theorem balancedExpected_scan_eq_one_iff :
    ∀ (rest : List Bool) (s : BalancedPhase) (h : ℕ),
      (s = .scanExcess0 ∨ s = .scanExcess1) →
      (balancedExpected s h rest = .one ↔
        boolDiff rest = (if s = .scanExcess0 then -(h : ℤ) else (h : ℤ))) := by
  intro rest
  induction rest with
  | nil =>
    intro s h hs
    rcases hs with hs | hs <;> subst hs <;> simp only [ite_true, ite_false, reduceCtorEq]
    · cases h with
      | zero => simp [balancedExpected, boolDiff_nil]
      | succ h' =>
        simp only [balancedExpected, boolDiff_nil]
        refine ⟨fun hh => absurd hh (by decide), fun h1 => ?_⟩
        exfalso; push_cast at h1; omega
    · cases h with
      | zero => simp [balancedExpected, boolDiff_nil]
      | succ h' =>
        simp only [balancedExpected, boolDiff_nil]
        refine ⟨fun hh => absurd hh (by decide), fun h1 => ?_⟩
        exfalso; push_cast at h1; omega
  | cons b rest' ih =>
    intro s h hs
    rcases hs with hs | hs <;> subst hs <;> cases b
    · -- scanExcess0 + false → scanExcess0 (h+1)
      simp only [balancedExpected, boolDiff_cons_false, ite_true]
      rw [ih .scanExcess0 (h + 1) (Or.inl rfl)]
      simp only [ite_true]
      constructor
      · intro hh; push_cast at hh ⊢; linarith
      · intro hh; push_cast at hh ⊢; linarith
    · -- scanExcess0 + true: h=0 switches to scanExcess1 1; h+1 pops to scanExcess0 h
      cases h with
      | zero =>
        simp only [balancedExpected, boolDiff_cons_true, ite_true]
        rw [ih .scanExcess1 1 (Or.inr rfl)]
        simp only [reduceCtorEq, ite_false]
        push_cast
        constructor
        · intro hh; linarith
        · intro hh; linarith
      | succ h' =>
        simp only [balancedExpected, boolDiff_cons_true, ite_true]
        rw [ih .scanExcess0 h' (Or.inl rfl)]
        simp only [ite_true]
        constructor
        · intro hh; push_cast at hh ⊢; linarith
        · intro hh; push_cast at hh ⊢; linarith
    · -- scanExcess1 + false: h=0 switches to scanExcess0 1; h+1 pops to scanExcess1 h
      cases h with
      | zero =>
        simp only [balancedExpected, boolDiff_cons_false, reduceCtorEq, ite_false]
        rw [ih .scanExcess0 1 (Or.inl rfl)]
        simp only [ite_true]
        push_cast
        constructor
        · intro hh; linarith
        · intro hh; linarith
      | succ h' =>
        simp only [balancedExpected, boolDiff_cons_false, reduceCtorEq, ite_false]
        rw [ih .scanExcess1 h' (Or.inr rfl)]
        simp only [reduceCtorEq, ite_false]
        constructor
        · intro hh; push_cast at hh ⊢; linarith
        · intro hh; push_cast at hh ⊢; linarith
    · -- scanExcess1 + true → scanExcess1 (h+1)
      simp only [balancedExpected, boolDiff_cons_true, reduceCtorEq, ite_false]
      rw [ih .scanExcess1 (h + 1) (Or.inr rfl)]
      simp only [reduceCtorEq, ite_false]
      constructor
      · intro hh; push_cast at hh ⊢; linarith
      · intro hh; push_cast at hh ⊢; linarith

/-- `boolDiff x = 0` iff `x.count false = x.count true`. -/
private theorem boolDiff_eq_zero_iff (x : List Bool) :
    boolDiff x = 0 ↔ x.count false = x.count true := by
  simp [boolDiff, sub_eq_zero]

/-- Membership characterization: `x ∈ balanced ↔ balancedTM accepts `x`. -/
private theorem balancedExpected_zero_iff_mem (x : List Bool) :
    balancedExpected .scanExcess0 0 x = .one ↔ x ∈ Language.balanced := by
  rw [balancedExpected_scan_eq_one_iff x .scanExcess0 0 (Or.inl rfl)]
  simp only [ite_true, Nat.cast_zero, neg_zero, Language.balanced,
             Set.mem_ofPred_eq]
  exact boolDiff_eq_zero_iff x

/-- The output of `balancedExpected` from any scan state is always `.zero`
    or `.one`. -/
private theorem balancedExpected_dichotomy (s : BalancedPhase) (h : ℕ) (rest : List Bool)
    (hs : s = .scanExcess0 ∨ s = .scanExcess1) :
    balancedExpected s h rest = .zero ∨ balancedExpected s h rest = .one := by
  induction rest generalizing s h with
  | nil =>
    rcases hs with hs | hs <;> subst hs <;> cases h <;> simp [balancedExpected]
  | cons b rest' ih =>
    rcases hs with hs | hs <;> subst hs <;> cases b
    · -- scanExcess0 + false → scanExcess0, h+1
      simp only [balancedExpected]
      exact ih .scanExcess0 (h + 1) (Or.inl rfl)
    · -- scanExcess0 + true
      cases h with
      | zero =>
        simp only [balancedExpected]
        exact ih .scanExcess1 1 (Or.inr rfl)
      | succ h' =>
        simp only [balancedExpected]
        exact ih .scanExcess0 h' (Or.inl rfl)
    · -- scanExcess1 + false
      cases h with
      | zero =>
        simp only [balancedExpected]
        exact ih .scanExcess0 1 (Or.inl rfl)
      | succ h' =>
        simp only [balancedExpected]
        exact ih .scanExcess1 h' (Or.inr rfl)
    · -- scanExcess1 + true
      simp only [balancedExpected]
      exact ih .scanExcess1 (h + 1) (Or.inr rfl)

-- ════════════════════════════════════════════════════════════════════════
-- DecidesInTime bridge
-- ════════════════════════════════════════════════════════════════════════

/-- `balancedTM` decides `Language.balanced` in time `|x| + 3`. -/
theorem balancedTM_decidesInTime :
    balancedTM.DecidesInTime Language.balanced (fun n => n + 3) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ := balancedTM_reachesIn x
  refine ⟨c', x.length + 3, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    rw [hout]
    have heq : balancedExpected .scanExcess0 0 x = .one :=
      (balancedExpected_zero_iff_mem x).mpr hxL
    rw [heq]; rfl
  · intro hxnL
    rw [hout]
    have hne : balancedExpected .scanExcess0 0 x ≠ .one := fun h =>
      hxnL ((balancedExpected_zero_iff_mem x).mp h)
    have heq : balancedExpected .scanExcess0 0 x = .zero :=
      (balancedExpected_dichotomy .scanExcess0 0 x (Or.inl rfl)).resolve_right hne
    rw [heq]; rfl

end TM

-- ════════════════════════════════════════════════════════════════════════
-- DTIME / P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`balanced ∈ DTIME(n + 3)`**. -/
theorem balanced_in_DTIME : Language.balanced ∈ DTIME (fun n => n + 3) :=
  ⟨1, TM.balancedTM, fun n => n + 3, TM.balancedTM_decidesInTime, BigO.refl _⟩

/-- **`balanced ∈ P`**. -/
theorem balanced_mem_P : Language.balanced ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ balanced_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 3 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
