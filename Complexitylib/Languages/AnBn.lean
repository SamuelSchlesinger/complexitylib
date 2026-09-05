/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Classes.Containments

/-!
# `{0ⁿ 1ⁿ : n ≥ 0}`: the canonical push-down language

The first non-regular language formalized here: the TM uses its single work
tape as a counter (push on `0`, pop on `1`). Demonstrates a textbook
push-down construction with an `O(n)` time bound.

The machine has six control states (`start`, `initWork`, `scanZeros`,
`scanOnes`, `reject`, `done`) and maintains the invariant that the work
head equals the current stack size. Emptiness is detected structurally
via the permanently-`▷` cell 0.

## Main definitions

- `TM.anbnTM` — 6-state 1-work-tape push-down machine.
- `Language.anbn` — `{0ⁿ 1ⁿ : n ≥ 0}`.

## Main results

- `anbnTM_reachesIn` — halts in `|x| + 3` steps on every input.
- `anbn_in_DTIME`, `anbn_mem_P`.
-/


@[expose] public section

namespace Complexity

open Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Control state
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `anbnTM`.

    - `start`   : initial state. Moves all heads from cell 0 (▷) to cell 1.
    - `initWork`: rewinds work head back to cell 0 (where ▷ marks emptiness).
    - `scanZeros`: scanning the `0`-prefix; pushes on `0`, transitions on `1`.
    - `scanOnes` : scanning the `1`-suffix; pops on `1`, rejects on `0`.
    - `reject`  : sink state; consumes remaining input then halts with `0`.
    - `done`    : halted. -/
inductive AnBnPhase where
  | start | initWork | scanZeros | scanOnes | reject | done
  deriving DecidableEq

instance : Fintype AnBnPhase where
  elems := {.start, .initWork, .scanZeros, .scanOnes, .reject, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- The push-down TM
-- ════════════════════════════════════════════════════════════════════════

/-- Push-down TM deciding `{0ⁿ 1ⁿ}`. One work tape used as a unary counter:
    the work head holds the current stack size (`0` means empty, detected by
    reading `▷` at cell 0). -/
def anbnTM : TM 1 where
  Q := AnBnPhase
  qstart := .start
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .start =>
      -- All heads at 0 reading ▷: must move right. Writes are no-ops at cell 0.
      (.initWork, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | .initWork =>
      -- Rewind work head from cell 1 back to cell 0. Input and output heads
      -- remain at cell 1. `moveLeftDir` handles the constraint if somehow
      -- wHeads reads ▷ (it doesn't, after `.start`).
      (.scanZeros, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => moveLeftDir (wHeads i), idleDir oHead)
    | .scanZeros =>
      if iHead = Γ.blank then
        -- End of input. Accept iff stack empty.
        if wHeads 0 = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), .one,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.done, fun i => readBackWrite (wHeads i), .zero,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.zero then
        -- Push: write 1 at work head, advance both.
        (.scanZeros, fun _ => .one, readBackWrite oHead,
         .right, fun _ => .right, idleDir oHead)
      else if iHead = Γ.one then
        if wHeads 0 = Γ.start then
          -- Empty stack, 1 seen first: reject. Work must move right (reads ▷).
          (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           .right, fun _ => .right, idleDir oHead)
        else
          -- Pop and transition to scanOnes.
          (.scanOnes, fun _ => .blank, readBackWrite oHead,
           .right, fun i => moveLeftDir (wHeads i), idleDir oHead)
      else
        -- iHead = Γ.start: vacuous in actual runs, but δ is total.
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanOnes =>
      if iHead = Γ.blank then
        if wHeads 0 = Γ.start then
          (.done, fun i => readBackWrite (wHeads i), .one,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.done, fun i => readBackWrite (wHeads i), .zero,
           idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.zero then
        -- 0 after 1: reject.
        (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.one then
        if wHeads 0 = Γ.start then
          -- Stack empty, more 1s left: reject.
          (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           .right, fun _ => .right, idleDir oHead)
        else
          (.scanOnes, fun _ => .blank, readBackWrite oHead,
           .right, fun i => moveLeftDir (wHeads i), idleDir oHead)
      else
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .reject =>
      if iHead = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
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
    | .scanZeros =>
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
    | .scanOnes =>
      dsimp only []
      split
      · split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
      split
      · exact ⟨fun h => by simp_all, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      split
      · split
        · exact ⟨fun _ => rfl, fun _ _ => rfl, idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ hi => by
            simp only [moveLeftDir, hi, ↓reduceIte],
            idleDir_right_of_start⟩
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .reject =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · exact ⟨fun h => by simp_all, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .done =>
      exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Step 1: `.start` → `.initWork`. All three heads advance from 0 to 1. -/
private theorem anbnTM_step_start
    (c : Cfg 1 anbnTM.Q) (hst : c.state = .start)
    (hih : c.input.head = 0) (hwh : ∀ i, (c.work i).head = 0)
    (hoh : c.output.head = 0) :
    ∃ c', anbnTM.step c = some c' ∧
      c'.state = AnBnPhase.initWork ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 1) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hih]
  · intro i
    simp [Tape.writeAndMove, Tape.move, Tape.write, hwh i]
  · intro i
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hwh i]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hoh]

/-- Step 2: `.initWork` → `.scanZeros`. Work rewinds from 1 to 0; input and
    output stay at 1. Requires input cell 1 ≠ ▷, output cell 1 ≠ ▷, and work
    cell 1 ≠ ▷ (all hold after `step_start`). -/
private theorem anbnTM_step_initWork
    (c : Cfg 1 anbnTM.Q) (hst : c.state = .initWork)
    (hih : c.input.head = 1) (hih_nb : c.input.cells 1 ≠ Γ.start)
    (hwh : ∀ i, (c.work i).head = 1)
    (hw_nb : ∀ i, (c.work i).cells 1 ≠ Γ.start)
    (hoh : c.output.head = 1) (hoh_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', anbnTM.step c = some c' ∧
      c'.state = AnBnPhase.scanZeros ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 0) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte]
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
-- Helpers
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

/-- `readBackWrite.toΓ` is either `Γ.blank` (if read was `▷`) or the read symbol. -/
private theorem readBackWrite_toΓ_cases (g : Γ) :
    (readBackWrite g).toΓ = Γ.blank ∨ (readBackWrite g).toΓ = g := by
  cases g <;> simp [readBackWrite, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Expected output function
-- ════════════════════════════════════════════════════════════════════════

/-- The output that `anbnTM` produces when run from scan state `s` with work
    head `h` (= stack size) and remaining input `rest`. Structurally
    recursive on `rest`. -/
def anbnExpected : AnBnPhase → ℕ → List Bool → Γw
  | .reject, _, [] => .zero
  | .reject, h, _ :: rest => anbnExpected .reject h rest
  | .scanZeros, 0, [] => .one
  | .scanZeros, _ + 1, [] => .zero
  | .scanZeros, h, false :: rest => anbnExpected .scanZeros (h + 1) rest
  | .scanZeros, 0, true :: rest => anbnExpected .reject 1 rest
  | .scanZeros, h + 1, true :: rest => anbnExpected .scanOnes h rest
  | .scanOnes, 0, [] => .one
  | .scanOnes, _ + 1, [] => .zero
  | .scanOnes, h, false :: rest => anbnExpected .reject h rest
  | .scanOnes, 0, true :: rest => anbnExpected .reject 1 rest
  | .scanOnes, h + 1, true :: rest => anbnExpected .scanOnes h rest
  | .start, _, _ => .blank
  | .initWork, _, _ => .blank
  | .done, _, _ => .blank

-- ════════════════════════════════════════════════════════════════════════
-- Scan invariants
-- ════════════════════════════════════════════════════════════════════════

/-- Common invariants for a configuration during the scan phase. -/
structure ScanInv (c : Cfg 1 anbnTM.Q) (x : List Bool) (k h : ℕ) : Prop where
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  wh : (c.work 0).head = h
  wstart : (c.work 0).cells 0 = Γ.start
  wns : ∀ j, j ≥ 1 → (c.work 0).cells j ≠ Γ.start
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace ScanInv
variable {c : Cfg 1 anbnTM.Q} {x : List Bool} {k h : ℕ}

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
private theorem read_bit (inv : ScanInv c x k h) (hk : k < x.length) :
    c.input.read = Γ.ofBool (x[k]'hk) := by
  have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
  simp only [Tape.read, inv.ih, inv.ic]
  show (Tape.init (x.map Γ.ofBool)).cells (k + 1) = _
  have hkmap : k < (x.map Γ.ofBool).length := by rw [hmap_len]; exact hk
  simp only [Tape.init, show k + 1 ≠ 0 from by omega, ↓reduceIte,
    Nat.add_sub_cancel, List.getElem?_eq_getElem hkmap, Option.getD_some,
    List.getElem_map]

/-- Input reads blank when `k = x.length`. -/
private theorem read_blank (inv : ScanInv c x x.length h) : c.input.read = Γ.blank := by
  simp only [Tape.read, inv.ih, inv.ic]
  show (Tape.init (x.map Γ.ofBool)).cells (x.length + 1) = Γ.blank
  simp [Tape.init]

/-- Input cells are never ▷ at positions ≥ 1. -/
private theorem input_ns (inv : ScanInv c x k h) :
    ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start := by
  intro j hj
  rw [inv.ic]
  exact Tape.init_ns _ (map_ofBool_ns x) j hj

/-- Work reads ▷ iff the work head is at 0. -/
private theorem work_read_start_iff (inv : ScanInv c x k h) :
    (c.work 0).read = Γ.start ↔ h = 0 := by
  simp only [Tape.read, inv.wh]
  constructor
  · intro hr
    by_contra hne
    have h1 : h ≥ 1 := by omega
    exact inv.wns h h1 hr
  · intro h0; rw [h0]; exact inv.wstart

private theorem output_read (inv : ScanInv c x k h) : c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : ScanInv c x k h) : idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read]

end ScanInv

-- ════════════════════════════════════════════════════════════════════════
-- Scan step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Push step: `scanZeros + iHead=.zero` → `scanZeros`, input and work heads +1. -/
private theorem anbnTM_step_scanZeros_push
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanZeros) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : ScanInv c x k h) :
    ∃ c', anbnTM.step c = some c' ∧
      c'.state = AnBnPhase.scanZeros ∧ ScanInv c' x (k + 1) (h + 1) := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_one : c.input.read ≠ Γ.one := by rw [hir]; decide
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_left hir, ite_eq_right hir_ne_one]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- input.cells unchanged
    show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · -- input.head = k + 2
    show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · -- work.head = h + 1
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).head = h + 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, inv.wh]
  · -- work.cells 0 = ▷ (cell 0 immutable)
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.one.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · -- work.cells j ≠ ▷ for j ≥ 1
    intro j hj
    show ((c.work 0).writeAndMove Γw.one.toΓ Dir3.right).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · -- output.head = 1
    show (c.output.writeAndMove (readBackWrite c.output.read).toΓ (idleDir c.output.read)).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · -- output.cells 1 ≠ ▷
    show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Simpler invariant for the `.reject` state. Work head is not tracked. -/
structure RejectInv (c : Cfg 1 anbnTM.Q) (x : List Bool) (k : ℕ) : Prop where
  st : c.state = .reject
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace RejectInv
variable {c : Cfg 1 anbnTM.Q} {x : List Bool} {k : ℕ}

private theorem read_bit (inv : RejectInv c x k) (hk : k < x.length) :
    c.input.read = Γ.ofBool (x[k]'hk) := by
  have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
  simp only [Tape.read, inv.ih, inv.ic]
  show (Tape.init (x.map Γ.ofBool)).cells (k + 1) = _
  have hkmap : k < (x.map Γ.ofBool).length := by rw [hmap_len]; exact hk
  simp only [Tape.init, show k + 1 ≠ 0 from by omega, ↓reduceIte,
    Nat.add_sub_cancel, List.getElem?_eq_getElem hkmap, Option.getD_some,
    List.getElem_map]

private theorem read_blank (inv : RejectInv c x x.length) : c.input.read = Γ.blank := by
  simp only [Tape.read, inv.ih, inv.ic]
  show (Tape.init (x.map Γ.ofBool)).cells (x.length + 1) = Γ.blank
  simp [Tape.init]

private theorem output_read (inv : RejectInv c x k) : c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : RejectInv c x k) : idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read]

end RejectInv

/-- Halt step: `scanZeros` + iHead=blank + h=0 → done, output cell 1 = 1. -/
private theorem anbnTM_step_scanZeros_halt_empty
    (c : Cfg 1 anbnTM.Q) (x : List Bool)
    (hst : c.state = .scanZeros) (inv : ScanInv c x x.length 0) :
    ∃ c', anbnTM.step c = some c' ∧ anbnTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ (idleDir c.output.read)).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- Halt step: `scanZeros` + iHead=blank + h≥1 → done, output cell 1 = 0. -/
private theorem anbnTM_step_scanZeros_halt_nonempty
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (h : ℕ) (hh : h ≥ 1)
    (hst : c.state = .scanZeros) (inv : ScanInv c x x.length h) :
    ∃ c', anbnTM.step c = some c' ∧ anbnTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_right hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ (idleDir c.output.read)).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- scanZeros + iHead=1 + h=0 → reject, work 0→1, input+1. -/
private theorem anbnTM_step_scanZeros_reject_at_empty
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .scanZeros) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k 0) :
    ∃ c', anbnTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- scanZeros + iHead=1 + h≥1 → scanOnes, work h→h-1, input+1. -/
private theorem anbnTM_step_scanZeros_pop
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanZeros) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k (h + 1)) :
    ∃ c', anbnTM.step c = some c' ∧
      c'.state = AnBnPhase.scanOnes ∧ ScanInv c' x (k + 1) h := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr_ne : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_right hwr_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · -- work.head = h  (was h+1, moved left)
    have hmv : moveLeftDir (c.work 0).read = Dir3.left := by
      simp [moveLeftDir, hwr_ne]
    show ((c.work 0).writeAndMove Γw.blank.toΓ (moveLeftDir (c.work 0).read)).head = h
    simp only [Tape.writeAndMove, hmv, Tape.move, Tape.write_head, inv.wh]
    omega
  · -- work.cells 0 = ▷
    show ((c.work 0).writeAndMove Γw.blank.toΓ (moveLeftDir (c.work 0).read)).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head Γw.blank.toΓ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · -- work.cells j ≠ ▷ for j ≥ 1
    intro j hj
    show ((c.work 0).writeAndMove Γw.blank.toΓ _).cells j ≠ Γ.start
    exact writeAndMove_preserves_nonStart _ _ _ inv.wns j hj
  · -- output.head = 1
    show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · -- output.cells 1 ≠ ▷
    show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- scanOnes + iHead=blank + h=0 → done, output 1. -/
private theorem anbnTM_step_scanOnes_halt_empty
    (c : Cfg 1 anbnTM.Q) (x : List Bool)
    (hst : c.state = .scanOnes) (inv : ScanInv c x x.length 0) :
    ∃ c', anbnTM.step c = some c' ∧ anbnTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ _).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- scanOnes + iHead=blank + h≥1 → done, output 0. -/
private theorem anbnTM_step_scanOnes_halt_nonempty
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (h : ℕ) (hh : h ≥ 1)
    (hst : c.state = .scanOnes) (inv : ScanInv c x x.length h) :
    ∃ c', anbnTM.step c = some c' ∧ anbnTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  have hwr : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir, ite_eq_right hwr]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ _).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- scanOnes + iHead=0 → reject. -/
private theorem anbnTM_step_scanOnes_reject_zero
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanOnes) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : ScanInv c x k h) :
    ∃ c', anbnTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_left hir]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- scanOnes + iHead=1 + h=0 → reject. -/
private theorem anbnTM_step_scanOnes_reject_at_empty
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .scanOnes) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k 0) :
    ∃ c', anbnTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_left hwr]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- scanOnes + iHead=1 + h≥1 → scanOnes, work pop. -/
private theorem anbnTM_step_scanOnes_pop
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanOnes) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k (h + 1)) :
    ∃ c', anbnTM.step c = some c' ∧
      c'.state = AnBnPhase.scanOnes ∧ ScanInv c' x (k + 1) h := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr_ne : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_right hwr_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- reject + iHead=blank → done, output 0. -/
private theorem anbnTM_step_reject_halt
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (inv : RejectInv c x x.length) :
    ∃ c', anbnTM.step c = some c' ∧ anbnTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  simp only [TM.step, inv.st, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ _).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- reject + iHead≠blank → reject, input advances. -/
private theorem anbnTM_step_reject_consume
    (c : Cfg 1 anbnTM.Q) (x : List Bool) (k : ℕ)
    (hk : k < x.length) (inv : RejectInv c x k) :
    ∃ c', anbnTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir_bit : c.input.read = Γ.ofBool (x[k]'hk) := inv.read_bit hk
  have hir_ne_blank : c.input.read ≠ Γ.blank := by
    rw [hir_bit]; cases x[k] <;> decide
  simp only [TM.step, inv.st, anbnTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

-- ════════════════════════════════════════════════════════════════════════
-- Scan and reject induction lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- From `.reject` state, the TM consumes remaining input and halts with output 0.
    Parameterized by `m` = number of remaining input bits. -/
private theorem anbnTM_reject_to_halt (x : List Bool) :
    ∀ (m k : ℕ) (c : Cfg 1 anbnTM.Q),
      RejectInv c x k → k + m = x.length →
      ∃ c', anbnTM.reachesIn (m + 1) c c' ∧ anbnTM.halted c' ∧
        c'.output.cells 1 = Γ.zero := by
  intro m
  induction m with
  | zero =>
    intro k c inv hlen
    have hk : k = x.length := by omega
    subst hk
    obtain ⟨c', hstep, hhalt, hout⟩ := anbnTM_step_reject_halt c x inv
    exact ⟨c', .step hstep .zero, hhalt, hout⟩
  | succ m' ih =>
    intro k c inv hlen
    have hk : k < x.length := by omega
    obtain ⟨c', hstep, inv'⟩ := anbnTM_step_reject_consume c x k hk inv
    have hlen' : (k + 1) + m' = x.length := by omega
    obtain ⟨c'', hreach, hhalt, hout⟩ := ih (k + 1) c' inv' hlen'
    exact ⟨c'', .step hstep hreach, hhalt, hout⟩

/-- `anbnExpected` in state `.reject` always yields `.zero`. -/
private theorem anbnExpected_reject (h : ℕ) (rest : List Bool) :
    anbnExpected .reject h rest = .zero := by
  induction rest generalizing h with
  | nil => rfl
  | cons _ rest' ih => simp [anbnExpected, ih]

/-- After pop transition from `scanZeros` or `scanOnes` + `true`-bit + `h+1` → `scanOnes`. -/
private theorem anbnExpected_pop_scanZeros (h : ℕ) (rest : List Bool) :
    anbnExpected .scanZeros (h + 1) (true :: rest) = anbnExpected .scanOnes h rest := rfl

/-- **Main scan invariant**: from state `s ∈ {scanZeros, scanOnes}` with
    remaining input `rest` and work head `h`, the TM halts in `rest.length + 1`
    steps with output cell 1 matching `anbnExpected s h rest`. -/
private theorem anbnTM_scan_to_halt (x : List Bool) :
    ∀ (rest : List Bool) (s : AnBnPhase) (k h : ℕ) (c : Cfg 1 anbnTM.Q),
      (s = .scanZeros ∨ s = .scanOnes) →
      c.state = s → k + rest.length = x.length → rest = x.drop k →
      ScanInv c x k h →
      ∃ c', anbnTM.reachesIn (rest.length + 1) c c' ∧
        anbnTM.halted c' ∧
        c'.output.cells 1 = (anbnExpected s h rest).toΓ := by
  intro rest
  induction rest with
  | nil =>
    intro s k h c hs hst hlen _ inv
    have hk : k = x.length := by simpa using hlen
    subst hk
    rcases hs with hs | hs <;> rcases h with _ | h' <;> subst hs
    · -- scanZeros + h=0: halt with output 1
      obtain ⟨c', hstep, hhalt, hout⟩ := anbnTM_step_scanZeros_halt_empty c x hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [anbnExpected, hout, Γw.toΓ]⟩
    · -- scanZeros + h≥1: halt with output 0
      obtain ⟨c', hstep, hhalt, hout⟩ :=
        anbnTM_step_scanZeros_halt_nonempty c x (h' + 1) (by omega) hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [anbnExpected, hout, Γw.toΓ]⟩
    · -- scanOnes + h=0
      obtain ⟨c', hstep, hhalt, hout⟩ := anbnTM_step_scanOnes_halt_empty c x hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [anbnExpected, hout, Γw.toΓ]⟩
    · -- scanOnes + h≥1
      obtain ⟨c', hstep, hhalt, hout⟩ :=
        anbnTM_step_scanOnes_halt_nonempty c x (h' + 1) (by omega) hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [anbnExpected, hout, Γw.toΓ]⟩
  | cons b rest' ih =>
    intro s k h c hs hst hlen hrest inv
    have hcons_len : (b :: rest').length = rest'.length + 1 := rfl
    have hk : k < x.length := by
      rw [hcons_len] at hlen; omega
    have hbit : x[k]'hk = b := by
      have hsymm : x.drop k = b :: rest' := hrest.symm
      have h1 : (x.drop k)[0]? = some b := by rw [hsymm]; rfl
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hk] at h1
      exact Option.some.inj h1
    have hlen' : (k + 1) + rest'.length = x.length := by
      rw [hcons_len] at hlen; omega
    have hrest' : rest' = x.drop (k + 1) := by
      rw [← List.drop_drop, ← hrest]
      simp
    rcases hs with hs | hs <;> subst hs <;> cases b
    · -- scanZeros + false bit = push
      obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
        anbnTM_step_scanZeros_push c x k h hst hk hbit inv
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        ih .scanZeros (k + 1) (h + 1) c₁ (Or.inl rfl) hst₁ hlen' hrest' inv₁
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]; simp [anbnExpected]
    · -- scanZeros + true bit
      cases h with
      | zero =>
        -- reject at empty
        obtain ⟨c₁, hstep, inv₁⟩ :=
          anbnTM_step_scanZeros_reject_at_empty c x k hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          anbnTM_reject_to_halt x rest'.length (k + 1) c₁ inv₁ (by omega)
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [anbnExpected, anbnExpected_reject, Γw.toΓ]
      | succ h' =>
        -- pop to scanOnes
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          anbnTM_step_scanZeros_pop c x k h' hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanOnes (k + 1) h' c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [anbnExpected]
    · -- scanOnes + false bit = reject
      obtain ⟨c₁, hstep, inv₁⟩ :=
        anbnTM_step_scanOnes_reject_zero c x k h hst hk hbit inv
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        anbnTM_reject_to_halt x rest'.length (k + 1) c₁ inv₁ (by omega)
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]; simp [anbnExpected, anbnExpected_reject, Γw.toΓ]
    · -- scanOnes + true bit
      cases h with
      | zero =>
        obtain ⟨c₁, hstep, inv₁⟩ :=
          anbnTM_step_scanOnes_reject_at_empty c x k hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          anbnTM_reject_to_halt x rest'.length (k + 1) c₁ inv₁ (by omega)
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [anbnExpected, anbnExpected_reject, Γw.toΓ]
      | succ h' =>
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          anbnTM_step_scanOnes_pop c x k h' hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanOnes (k + 1) h' c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [anbnExpected]

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `anbnTM` halts in `|x| + 3` steps on every input, writing the correct
    answer (`Γ.one` if `x = 0ⁿ 1ⁿ`, else `Γ.zero`) to output cell 1. -/
theorem anbnTM_reachesIn (x : List Bool) :
    ∃ c', anbnTM.reachesIn (x.length + 3) (anbnTM.initCfg x) c' ∧
      anbnTM.halted c' ∧
      c'.output.cells 1 = (anbnExpected .scanZeros 0 x).toΓ := by
  -- Step 1: .start → .initWork
  obtain ⟨c₁, hstep1, hst1, hih1, hic1, hwh1, hwc1, hoh1, hoc1⟩ :=
    anbnTM_step_start (anbnTM.initCfg x) rfl rfl (by intro _; rfl) rfl
  -- Step 2: .initWork → .scanZeros (needs that cell 1 ≠ ▷ on all tapes)
  have hi_nb : c₁.input.cells 1 ≠ Γ.start := by
    rw [hic1]
    show (Tape.init (x.map Γ.ofBool)).cells 1 ≠ Γ.start
    exact ScanInv.Tape.init_ns _ (ScanInv.map_ofBool_ns x) 1 (by omega)
  have hw_nb : ∀ i, (c₁.work i).cells 1 ≠ Γ.start := by
    intro i
    rw [hwc1 i]
    have : (anbnTM.initCfg x).work i = Tape.init [] := by rfl
    rw [this]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  have ho_nb : c₁.output.cells 1 ≠ Γ.start := by
    rw [hoc1]
    have : (anbnTM.initCfg x).output = Tape.init [] := by rfl
    rw [this]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  obtain ⟨c₂, hstep2, hst2, hih2, hic2, hwh2, hwc2, hoh2, hoc2⟩ :=
    anbnTM_step_initWork c₁ hst1 hih1 hi_nb hwh1 hw_nb hoh1 ho_nb
  -- Apply scan invariant from k = 0, h = 0
  have hinv : ScanInv c₂ x 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- input.cells
      rw [hic2, hic1]
    · -- input.head = 0 + 1
      simp [hih2]
    · -- work.head = 0
      exact hwh2 0
    · -- work.cells 0 = ▷
      rw [hwc2 0, hwc1 0]
      have : (anbnTM.initCfg x).work 0 = Tape.init [] := by rfl
      rw [this]
      show (Tape.init []).cells 0 = Γ.start
      simp [Tape.init]
    · -- work.cells j ≠ ▷ for j ≥ 1
      intro j hj
      rw [hwc2 0, hwc1 0]
      have : (anbnTM.initCfg x).work 0 = Tape.init [] := by rfl
      rw [this]
      show (Tape.init []).cells j ≠ Γ.start
      have hj' : j ≠ 0 := by omega
      simp [Tape.init, hj']
    · -- output.head = 1
      exact hoh2
    · -- output.cells 1 ≠ ▷
      rw [hoc2]; exact ho_nb
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    anbnTM_scan_to_halt x x .scanZeros 0 0 c₂ (Or.inl rfl) hst2 (by simp) (by simp) hinv
  refine ⟨c', ?_, hhalt, hout⟩
  -- Assemble: 1 (start) + 1 (initWork) + (x.length + 1) (scan) = x.length + 3
  have hsteps : x.length + 3 = x.length + 1 + 1 + 1 := by ring
  rw [hsteps]
  exact .step hstep1 (.step hstep2 hreach)

end TM

namespace Language

/-- **The language `{0ⁿ 1ⁿ : n ≥ 0}`** — the canonical context-free
    but non-regular language. A string `x` is in `anbn` iff it consists of
    some `n` copies of `false` followed by the same number of copies of
    `true`. -/
def anbn : Language :=
  {x : List Bool | ∃ n, x = List.replicate n false ++ List.replicate n true}

end Language

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Characterization of `anbnExpected` in terms of string shape
-- ════════════════════════════════════════════════════════════════════════

/-- `List.replicate h true = false :: rest` is impossible. -/
private theorem not_replicate_true_eq_cons_false (h : ℕ) (rest : List Bool) :
    List.replicate h true ≠ false :: rest := by
  cases h with
  | zero => simp [List.replicate]
  | succ h' =>
    rw [List.replicate_succ]; intro heq
    exact absurd (List.cons_eq_cons.mp heq).1 (by decide)

/-- `List.replicate 0 true = true :: rest` is impossible. -/
private theorem not_replicate_zero_true_eq_cons_true (rest : List Bool) :
    List.replicate 0 true ≠ true :: rest := by
  simp [List.replicate]

/-- From `scanOnes h`, the output is `.one` iff the remaining input is
    exactly `h` copies of `true`. -/
private theorem anbnExpected_scanOnes_eq_one_iff (h : ℕ) (rest : List Bool) :
    anbnExpected .scanOnes h rest = .one ↔ rest = List.replicate h true := by
  induction rest generalizing h with
  | nil =>
    cases h with
    | zero => simp [anbnExpected, List.replicate]
    | succ h' => simp [anbnExpected, List.replicate]
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [anbnExpected, anbnExpected_reject]
      refine ⟨fun h1 => absurd h1 (by decide), fun hrep => ?_⟩
      exact absurd hrep.symm (not_replicate_true_eq_cons_false h rest')
    | true =>
      cases h with
      | zero =>
        simp only [anbnExpected, anbnExpected_reject]
        refine ⟨fun h1 => absurd h1 (by decide), fun hrep => ?_⟩
        exact absurd hrep.symm (not_replicate_zero_true_eq_cons_true rest')
      | succ h' =>
        simp only [anbnExpected]
        rw [ih h', List.replicate_succ]
        exact ⟨fun hrest => by rw [hrest], fun hrep => (List.cons_eq_cons.mp hrep).2⟩

/-- From `scanZeros h`, the output is `.one` iff the remaining input has
    the form `0ᵐ 1ʰ⁺ᵐ` for some `m ≥ 0`. -/
private theorem anbnExpected_scanZeros_eq_one_iff (h : ℕ) (x : List Bool) :
    anbnExpected .scanZeros h x = .one ↔
      ∃ m, x = List.replicate m false ++ List.replicate (h + m) true := by
  induction x generalizing h with
  | nil =>
    cases h with
    | zero =>
      simp only [anbnExpected]
      refine ⟨fun _ => ⟨0, by simp [List.replicate]⟩, fun _ => ?_⟩
      trivial
    | succ h' =>
      simp only [anbnExpected]
      refine ⟨fun h1 => absurd h1 (by decide), ?_⟩
      rintro ⟨m, hm⟩
      cases m with
      | zero => simp [List.replicate] at hm
      | succ m' =>
        rw [List.replicate_succ, List.cons_append] at hm
        exact absurd hm (by simp)
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [anbnExpected]
      rw [ih (h + 1)]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        rw [List.replicate_succ, List.cons_append, hm]
        congr 3
        omega
      · rintro ⟨m, hm⟩
        cases m with
        | zero =>
          exfalso
          simp only [List.replicate, List.nil_append] at hm
          exact not_replicate_true_eq_cons_false (h + 0) rest' hm.symm
        | succ m' =>
          refine ⟨m', ?_⟩
          rw [List.replicate_succ, List.cons_append] at hm
          have hrest : rest' = List.replicate m' false ++ List.replicate (h + (m' + 1)) true :=
            (List.cons_eq_cons.mp hm).2
          rw [hrest]
          congr 2
          omega
    | true =>
      cases h with
      | zero =>
        simp only [anbnExpected, anbnExpected_reject]
        refine ⟨fun h1 => absurd h1 (by decide), ?_⟩
        rintro ⟨m, hm⟩
        cases m with
        | zero => simp [List.replicate] at hm
        | succ m' =>
          rw [List.replicate_succ, List.cons_append] at hm
          exact absurd (List.cons_eq_cons.mp hm).1 (by decide)
      | succ h' =>
        simp only [anbnExpected]
        rw [anbnExpected_scanOnes_eq_one_iff]
        constructor
        · intro hrest
          refine ⟨0, ?_⟩
          simp only [List.replicate, List.nil_append]
          rw [hrest]
        · rintro ⟨m, hm⟩
          cases m with
          | zero =>
            simp only [List.replicate, List.nil_append] at hm
            exact (List.cons_eq_cons.mp hm).2
          | succ m' =>
            rw [List.replicate_succ, List.cons_append] at hm
            exact absurd (List.cons_eq_cons.mp hm).1 (by decide)

/-- **Membership characterization**: `x ∈ anbn` iff the TM accepts. -/
private theorem anbnExpected_scanZeros_zero_iff_mem (x : List Bool) :
    anbnExpected .scanZeros 0 x = .one ↔ x ∈ Language.anbn := by
  rw [anbnExpected_scanZeros_eq_one_iff]
  simp only [Language.anbn, Set.mem_ofPred_eq, Nat.zero_add]

/-- From `scanOnes`, output is always `.zero` or `.one`. -/
private theorem anbnExpected_scanOnes_dichotomy (h : ℕ) (rest : List Bool) :
    anbnExpected .scanOnes h rest = .zero ∨ anbnExpected .scanOnes h rest = .one := by
  induction rest generalizing h with
  | nil => cases h <;> simp [anbnExpected]
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [anbnExpected]
      exact Or.inl (anbnExpected_reject h rest')
    | true =>
      cases h with
      | zero =>
        simp only [anbnExpected]
        exact Or.inl (anbnExpected_reject 1 rest')
      | succ h' =>
        simp only [anbnExpected]
        exact ih h'

/-- From `scanZeros`, output is always `.zero` or `.one`. -/
private theorem anbnExpected_scanZeros_dichotomy (h : ℕ) (x : List Bool) :
    anbnExpected .scanZeros h x = .zero ∨ anbnExpected .scanZeros h x = .one := by
  induction x generalizing h with
  | nil => cases h <;> simp [anbnExpected]
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [anbnExpected]
      exact ih (h + 1)
    | true =>
      cases h with
      | zero =>
        simp only [anbnExpected]
        exact Or.inl (anbnExpected_reject 1 rest')
      | succ h' =>
        simp only [anbnExpected]
        exact anbnExpected_scanOnes_dichotomy h' rest'

-- ════════════════════════════════════════════════════════════════════════
-- DecidesInTime bridge
-- ════════════════════════════════════════════════════════════════════════

/-- `anbnTM` decides `Language.anbn` in time `|x| + 3`. -/
theorem anbnTM_decidesInTime :
    anbnTM.DecidesInTime Language.anbn (fun n => n + 3) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ := anbnTM_reachesIn x
  refine ⟨c', x.length + 3, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    rw [hout]
    have heq : anbnExpected .scanZeros 0 x = .one :=
      (anbnExpected_scanZeros_zero_iff_mem x).mpr hxL
    rw [heq]; rfl
  · intro hxnL
    rw [hout]
    have hne : anbnExpected .scanZeros 0 x ≠ .one := fun h =>
      hxnL ((anbnExpected_scanZeros_zero_iff_mem x).mp h)
    have heq : anbnExpected .scanZeros 0 x = .zero :=
      (anbnExpected_scanZeros_dichotomy 0 x).resolve_right hne
    rw [heq]; rfl

end TM

-- ════════════════════════════════════════════════════════════════════════
-- DTIME / P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`anbn ∈ DTIME(n + 3)`**. -/
theorem anbn_in_DTIME : Language.anbn ∈ DTIME (fun n => n + 3) :=
  ⟨1, TM.anbnTM, fun n => n + 3, TM.anbnTM_decidesInTime, BigO.refl _⟩

/-- **`anbn ∈ P`**. -/
theorem anbn_mem_P : Language.anbn ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ anbn_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 3 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
