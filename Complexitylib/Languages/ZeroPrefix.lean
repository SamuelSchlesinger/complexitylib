/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Classes.Containments

/-!
# `{0ⁿ 1ᵐ : n ≥ m}`: a push-down language with inequality counter

A small variant of `AnBn`: the input is `0ⁿ 1ᵐ` with the extra condition
`n ≥ m`. The machine structurally mirrors `anbnTM` — a single work tape is
used as a unary counter (push on `0`, pop on `1`) — but the end-of-input
branches accept unconditionally: after scanning the full input without
hitting a mismatch, the remaining stack height is exactly `n − m ≥ 0`,
which we accept.

The machine has six control states (`start`, `initWork`, `scanZeros`,
`scanOnes`, `reject`, `done`) and maintains the invariant that the work
head equals the current stack size. Emptiness is detected structurally
via the permanently-`▷` cell 0.

## Main definitions

- `TM.zeroPrefixTM` — 6-state 1-work-tape push-down machine.
- `Language.zeroPrefix` — `{0ⁿ 1ᵐ : n ≥ m}`.

## Main results

- `zeroPrefixTM_reachesIn` — halts in `|x| + 3` steps on every input.
- `zeroPrefix_in_DTIME`, `zeroPrefix_mem_P`.
-/


public section

namespace Complexity

open Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Control state
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `zeroPrefixTM`.

    - `start`   : initial state. Moves all heads from cell 0 (▷) to cell 1.
    - `initWork`: rewinds work head back to cell 0 (where ▷ marks emptiness).
    - `scanZeros`: scanning the `0`-prefix; pushes on `0`, transitions on `1`.
    - `scanOnes` : scanning the `1`-suffix; pops on `1`, rejects on `0`.
    - `reject`  : sink state; consumes remaining input then halts with `0`.
    - `done`    : halted. -/
inductive ZeroPrefixPhase where
  | start | initWork | scanZeros | scanOnes | reject | done
  deriving DecidableEq

instance : Fintype ZeroPrefixPhase where
  elems := {.start, .initWork, .scanZeros, .scanOnes, .reject, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- The push-down TM
-- ════════════════════════════════════════════════════════════════════════

/-- Push-down TM deciding `{0ⁿ 1ᵐ : n ≥ m}`. One work tape used as a unary
    counter: the work head holds the current stack size (`0` means empty,
    detected by reading `▷` at cell 0). End-of-input is accepted in both
    scan states — reaching a blank means we consumed the input without a
    mismatch, so `n ≥ m`. -/
@[expose] def zeroPrefixTM : TM 1 where
  Q := ZeroPrefixPhase
  qstart := .start
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .start =>
      -- All heads at 0 reading ▷: must move right. Writes are no-ops at cell 0.
      (.initWork, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | .initWork =>
      -- Rewind work head from cell 1 back to cell 0. Input and output heads
      -- remain at cell 1.
      (.scanZeros, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => moveLeftDir (wHeads i), idleDir oHead)
    | .scanZeros =>
      if iHead = Γ.blank then
        -- End of input: input was `0ⁿ` with n ≥ 0 = m. Accept.
        (.done, fun i => readBackWrite (wHeads i), .one,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.zero then
        -- Push: write 1 at work head, advance both.
        (.scanZeros, fun _ => .one, readBackWrite oHead,
         .right, fun _ => .right, idleDir oHead)
      else if iHead = Γ.one then
        if wHeads 0 = Γ.start then
          -- Empty stack, 1 seen first: reject (n = 0, m ≥ 1).
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
        -- End of input after popping m-many: stack holds n − m ≥ 0. Accept.
        (.done, fun i => readBackWrite (wHeads i), .one,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.zero then
        -- 0 after 1: not of form 0ⁿ 1ᵐ. Reject.
        (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.one then
        if wHeads 0 = Γ.start then
          -- Stack empty, more 1s left: reject (too many 1s vs 0s).
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
private theorem zeroPrefixTM_step_start
    (c : Cfg 1 zeroPrefixTM.Q) (hst : c.state = .start)
    (hih : c.input.head = 0) (hwh : ∀ i, (c.work i).head = 0)
    (hoh : c.output.head = 0) :
    ∃ c', zeroPrefixTM.step c = some c' ∧
      c'.state = ZeroPrefixPhase.initWork ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 1) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hih]
  · intro i
    simp [Tape.writeAndMove, Tape.move, Tape.write, hwh i]
  · intro i
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hwh i]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hoh]

/-- Step 2: `.initWork` → `.scanZeros`. -/
private theorem zeroPrefixTM_step_initWork
    (c : Cfg 1 zeroPrefixTM.Q) (hst : c.state = .initWork)
    (hih : c.input.head = 1) (hih_nb : c.input.cells 1 ≠ Γ.start)
    (hwh : ∀ i, (c.work i).head = 1)
    (hw_nb : ∀ i, (c.work i).cells 1 ≠ Γ.start)
    (hoh : c.output.head = 1) (hoh_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', zeroPrefixTM.step c = some c' ∧
      c'.state = ZeroPrefixPhase.scanZeros ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 0) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte]
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

-- ════════════════════════════════════════════════════════════════════════
-- Expected output function
-- ════════════════════════════════════════════════════════════════════════

/-- The output that `zeroPrefixTM` produces when run from scan state `s`
    with work head `h` (= stack size) and remaining input `rest`.

    Differs from `anbnExpected` only in end-of-input branches: scanZeros
    and scanOnes at end of input always accept (output `.one`). -/
def zeroPrefixExpected : ZeroPrefixPhase → ℕ → List Bool → Γw
  | .reject, _, [] => .zero
  | .reject, h, _ :: rest => zeroPrefixExpected .reject h rest
  | .scanZeros, _, [] => .one
  | .scanZeros, h, false :: rest => zeroPrefixExpected .scanZeros (h + 1) rest
  | .scanZeros, 0, true :: rest => zeroPrefixExpected .reject 1 rest
  | .scanZeros, h + 1, true :: rest => zeroPrefixExpected .scanOnes h rest
  | .scanOnes, _, [] => .one
  | .scanOnes, h, false :: rest => zeroPrefixExpected .reject h rest
  | .scanOnes, 0, true :: rest => zeroPrefixExpected .reject 1 rest
  | .scanOnes, h + 1, true :: rest => zeroPrefixExpected .scanOnes h rest
  | .start, _, _ => .blank
  | .initWork, _, _ => .blank
  | .done, _, _ => .blank

-- ════════════════════════════════════════════════════════════════════════
-- Scan invariants
-- ════════════════════════════════════════════════════════════════════════

/-- Common invariants for a configuration during the scan phase. -/
private structure ScanInv (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k h : ℕ) : Prop where
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  wh : (c.work 0).head = h
  wstart : (c.work 0).cells 0 = Γ.start
  wns : ∀ j, j ≥ 1 → (c.work 0).cells j ≠ Γ.start
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace ScanInv
variable {c : Cfg 1 zeroPrefixTM.Q} {x : List Bool} {k h : ℕ}

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
private theorem zeroPrefixTM_step_scanZeros_push
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanZeros) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : ScanInv c x k h) :
    ∃ c', zeroPrefixTM.step c = some c' ∧
      c'.state = ZeroPrefixPhase.scanZeros ∧ ScanInv c' x (k + 1) (h + 1) := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_one : c.input.read ≠ Γ.one := by rw [hir]; decide
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
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
  · show (c.output.writeAndMove (readBackWrite c.output.read).toΓ (idleDir c.output.read)).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read)]
    exact inv.ons

/-- Simpler invariant for the `.reject` state. Work head is not tracked. -/
private structure RejectInv (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k : ℕ) : Prop where
  st : c.state = .reject
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace RejectInv
variable {c : Cfg 1 zeroPrefixTM.Q} {x : List Bool} {k : ℕ}

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

/-- Halt step: `scanZeros` + iHead=blank → done, output cell 1 = 1 (always accept). -/
private theorem zeroPrefixTM_step_scanZeros_halt
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (h : ℕ)
    (hst : c.state = .scanZeros) (inv : ScanInv c x x.length h) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ zeroPrefixTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ (idleDir c.output.read)).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- scanZeros + iHead=1 + h=0 → reject, work 0→1, input+1. -/
private theorem zeroPrefixTM_step_scanZeros_reject_at_empty
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .scanZeros) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k 0) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
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
private theorem zeroPrefixTM_step_scanZeros_pop
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanZeros) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k (h + 1)) :
    ∃ c', zeroPrefixTM.step c = some c' ∧
      c'.state = ZeroPrefixPhase.scanOnes ∧ ScanInv c' x (k + 1) h := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr_ne : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
             ite_eq_right hir_ne_zero, ite_eq_left hir, ite_eq_right hwr_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- Halt step: `scanOnes` + iHead=blank → done, output 1 (always accept). -/
private theorem zeroPrefixTM_step_scanOnes_halt
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (h : ℕ)
    (hst : c.state = .scanOnes) (inv : ScanInv c x x.length h) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ zeroPrefixTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ _).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- scanOnes + iHead=0 → reject. -/
private theorem zeroPrefixTM_step_scanOnes_reject_zero
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanOnes) (hk : k < x.length)
    (hbit : x[k]'hk = false) (inv : ScanInv c x k h) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.zero := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
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
private theorem zeroPrefixTM_step_scanOnes_reject_at_empty
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .scanOnes) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k 0) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr : (c.work 0).read = Γ.start := inv.work_read_start_iff.mpr rfl
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
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
private theorem zeroPrefixTM_step_scanOnes_pop
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k h : ℕ)
    (hst : c.state = .scanOnes) (hk : k < x.length)
    (hbit : x[k]'hk = true) (inv : ScanInv c x k (h + 1)) :
    ∃ c', zeroPrefixTM.step c = some c' ∧
      c'.state = ZeroPrefixPhase.scanOnes ∧ ScanInv c' x (k + 1) h := by
  have hir : c.input.read = Γ.one := by rw [inv.read_bit hk, hbit]; rfl
  have hir_ne_blank : c.input.read ≠ Γ.blank := by rw [hir]; decide
  have hir_ne_zero : c.input.read ≠ Γ.zero := by rw [hir]; decide
  have hwr_ne : (c.work 0).read ≠ Γ.start := by
    simp only [ne_eq, inv.work_read_start_iff]; omega
  simp only [TM.step, hst, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank,
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
private theorem zeroPrefixTM_step_reject_halt
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (inv : RejectInv c x x.length) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ zeroPrefixTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  simp only [TM.step, inv.st, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ _).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hstay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- reject + iHead≠blank → reject, input advances. -/
private theorem zeroPrefixTM_step_reject_consume
    (c : Cfg 1 zeroPrefixTM.Q) (x : List Bool) (k : ℕ)
    (hk : k < x.length) (inv : RejectInv c x k) :
    ∃ c', zeroPrefixTM.step c = some c' ∧ RejectInv c' x (k + 1) := by
  have hir_bit : c.input.read = Γ.ofBool (x[k]'hk) := inv.read_bit hk
  have hir_ne_blank : c.input.read ≠ Γ.blank := by
    rw [hir_bit]; cases x[k] <;> decide
  simp only [TM.step, inv.st, zeroPrefixTM, reduceCtorEq, ↓reduceIte, ite_eq_right hir_ne_blank]
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

/-- From `.reject` state, the TM consumes remaining input and halts with output 0. -/
private theorem zeroPrefixTM_reject_to_halt (x : List Bool) :
    ∀ (m k : ℕ) (c : Cfg 1 zeroPrefixTM.Q),
      RejectInv c x k → k + m = x.length →
      ∃ c', zeroPrefixTM.reachesIn (m + 1) c c' ∧ zeroPrefixTM.halted c' ∧
        c'.output.cells 1 = Γ.zero := by
  intro m
  induction m with
  | zero =>
    intro k c inv hlen
    have hk : k = x.length := by omega
    subst hk
    obtain ⟨c', hstep, hhalt, hout⟩ := zeroPrefixTM_step_reject_halt c x inv
    exact ⟨c', .step hstep .zero, hhalt, hout⟩
  | succ m' ih =>
    intro k c inv hlen
    have hk : k < x.length := by omega
    obtain ⟨c', hstep, inv'⟩ := zeroPrefixTM_step_reject_consume c x k hk inv
    have hlen' : (k + 1) + m' = x.length := by omega
    obtain ⟨c'', hreach, hhalt, hout⟩ := ih (k + 1) c' inv' hlen'
    exact ⟨c'', .step hstep hreach, hhalt, hout⟩

/-- `zeroPrefixExpected` in state `.reject` always yields `.zero`. -/
private theorem zeroPrefixExpected_reject (h : ℕ) (rest : List Bool) :
    zeroPrefixExpected .reject h rest = .zero := by
  induction rest generalizing h with
  | nil => rfl
  | cons _ rest' ih => simp [zeroPrefixExpected, ih]

/-- **Main scan invariant**: from state `s ∈ {scanZeros, scanOnes}` with
    remaining input `rest` and work head `h`, the TM halts in `rest.length + 1`
    steps with output cell 1 matching `zeroPrefixExpected s h rest`. -/
private theorem zeroPrefixTM_scan_to_halt (x : List Bool) :
    ∀ (rest : List Bool) (s : ZeroPrefixPhase) (k h : ℕ) (c : Cfg 1 zeroPrefixTM.Q),
      (s = .scanZeros ∨ s = .scanOnes) →
      c.state = s → k + rest.length = x.length → rest = x.drop k →
      ScanInv c x k h →
      ∃ c', zeroPrefixTM.reachesIn (rest.length + 1) c c' ∧
        zeroPrefixTM.halted c' ∧
        c'.output.cells 1 = (zeroPrefixExpected s h rest).toΓ := by
  intro rest
  induction rest with
  | nil =>
    intro s k h c hs hst hlen _ inv
    have hk : k = x.length := by simpa using hlen
    subst hk
    rcases hs with hs | hs <;> subst hs
    · -- scanZeros at end of input: always accept
      obtain ⟨c', hstep, hhalt, hout⟩ := zeroPrefixTM_step_scanZeros_halt c x h hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [zeroPrefixExpected, hout, Γw.toΓ]⟩
    · -- scanOnes at end of input: always accept
      obtain ⟨c', hstep, hhalt, hout⟩ := zeroPrefixTM_step_scanOnes_halt c x h hst inv
      exact ⟨c', .step hstep .zero, hhalt, by simp [zeroPrefixExpected, hout, Γw.toΓ]⟩
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
        zeroPrefixTM_step_scanZeros_push c x k h hst hk hbit inv
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        ih .scanZeros (k + 1) (h + 1) c₁ (Or.inl rfl) hst₁ hlen' hrest' inv₁
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]; simp [zeroPrefixExpected]
    · -- scanZeros + true bit
      cases h with
      | zero =>
        obtain ⟨c₁, hstep, inv₁⟩ :=
          zeroPrefixTM_step_scanZeros_reject_at_empty c x k hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          zeroPrefixTM_reject_to_halt x rest'.length (k + 1) c₁ inv₁ (by omega)
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [zeroPrefixExpected, zeroPrefixExpected_reject, Γw.toΓ]
      | succ h' =>
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          zeroPrefixTM_step_scanZeros_pop c x k h' hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanOnes (k + 1) h' c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [zeroPrefixExpected]
    · -- scanOnes + false bit = reject
      obtain ⟨c₁, hstep, inv₁⟩ :=
        zeroPrefixTM_step_scanOnes_reject_zero c x k h hst hk hbit inv
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        zeroPrefixTM_reject_to_halt x rest'.length (k + 1) c₁ inv₁ (by omega)
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]; simp [zeroPrefixExpected, zeroPrefixExpected_reject, Γw.toΓ]
    · -- scanOnes + true bit
      cases h with
      | zero =>
        obtain ⟨c₁, hstep, inv₁⟩ :=
          zeroPrefixTM_step_scanOnes_reject_at_empty c x k hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          zeroPrefixTM_reject_to_halt x rest'.length (k + 1) c₁ inv₁ (by omega)
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [zeroPrefixExpected, zeroPrefixExpected_reject, Γw.toΓ]
      | succ h' =>
        obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
          zeroPrefixTM_step_scanOnes_pop c x k h' hst hk hbit inv
        obtain ⟨c', hreach, hhalt, hout⟩ :=
          ih .scanOnes (k + 1) h' c₁ (Or.inr rfl) hst₁ hlen' hrest' inv₁
        refine ⟨c', .step hstep hreach, hhalt, ?_⟩
        rw [hout]; simp [zeroPrefixExpected]

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `zeroPrefixTM` halts in `|x| + 3` steps on every input, writing the
    correct answer to output cell 1. -/
theorem zeroPrefixTM_reachesIn (x : List Bool) :
    ∃ c', zeroPrefixTM.reachesIn (x.length + 3) (zeroPrefixTM.initCfg x) c' ∧
      zeroPrefixTM.halted c' ∧
      c'.output.cells 1 = (zeroPrefixExpected .scanZeros 0 x).toΓ := by
  obtain ⟨c₁, hstep1, hst1, hih1, hic1, hwh1, hwc1, hoh1, hoc1⟩ :=
    zeroPrefixTM_step_start (zeroPrefixTM.initCfg x) rfl rfl (by intro _; rfl) rfl
  have hi_nb : c₁.input.cells 1 ≠ Γ.start := by
    rw [hic1]
    show (Tape.init (x.map Γ.ofBool)).cells 1 ≠ Γ.start
    exact ScanInv.Tape.init_ns _ (ScanInv.map_ofBool_ns x) 1 (by omega)
  have hw_nb : ∀ i, (c₁.work i).cells 1 ≠ Γ.start := by
    intro i
    rw [hwc1 i]
    have : (zeroPrefixTM.initCfg x).work i = Tape.init [] := by rfl
    rw [this]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  have ho_nb : c₁.output.cells 1 ≠ Γ.start := by
    rw [hoc1]
    have : (zeroPrefixTM.initCfg x).output = Tape.init [] := by rfl
    rw [this]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  obtain ⟨c₂, hstep2, hst2, hih2, hic2, hwh2, hwc2, hoh2, hoc2⟩ :=
    zeroPrefixTM_step_initWork c₁ hst1 hih1 hi_nb hwh1 hw_nb hoh1 ho_nb
  have hinv : ScanInv c₂ x 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hic2, hic1]
    · simp [hih2]
    · exact hwh2 0
    · rw [hwc2 0, hwc1 0]
      have : (zeroPrefixTM.initCfg x).work 0 = Tape.init [] := by rfl
      rw [this]
      show (Tape.init []).cells 0 = Γ.start
      simp [Tape.init]
    · intro j hj
      rw [hwc2 0, hwc1 0]
      have : (zeroPrefixTM.initCfg x).work 0 = Tape.init [] := by rfl
      rw [this]
      show (Tape.init []).cells j ≠ Γ.start
      have hj' : j ≠ 0 := by omega
      simp [Tape.init, hj']
    · exact hoh2
    · rw [hoc2]; exact ho_nb
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    zeroPrefixTM_scan_to_halt x x .scanZeros 0 0 c₂ (Or.inl rfl) hst2 (by simp) (by simp) hinv
  refine ⟨c', ?_, hhalt, hout⟩
  have hsteps : x.length + 3 = x.length + 1 + 1 + 1 := by ring
  rw [hsteps]
  exact .step hstep1 (.step hstep2 hreach)

end TM

namespace Language

/-- **The language `{0ⁿ 1ᵐ : n ≥ m}`** — strings of some zeros followed by
    at most that many ones. -/
def zeroPrefix : Language :=
  {x : List Bool | ∃ n m, n ≥ m ∧ x = List.replicate n false ++ List.replicate m true}

end Language

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Characterization of `zeroPrefixExpected` in terms of string shape
-- ════════════════════════════════════════════════════════════════════════

/-- `List.replicate h true = false :: rest` is impossible. -/
private theorem not_replicate_true_eq_cons_false (h : ℕ) (rest : List Bool) :
    List.replicate h true ≠ false :: rest := by
  cases h with
  | zero => simp [List.replicate]
  | succ h' =>
    rw [List.replicate_succ]
    intro heq; exact absurd (List.cons_eq_cons.mp heq).1 (by decide)

/-- `List.replicate 0 true = true :: rest` is impossible. -/
private theorem not_replicate_zero_true_eq_cons_true (rest : List Bool) :
    List.replicate 0 true ≠ true :: rest := by
  simp [List.replicate]

/-- From `scanOnes h`, the output is `.one` iff the remaining input is a
    prefix of `List.replicate h true` (there are at most `h` trailing ones
    left before we exhaust the stack). Equivalently, `rest = replicate m true`
    for some `m ≤ h`. -/
private theorem zeroPrefixExpected_scanOnes_eq_one_iff (h : ℕ) (rest : List Bool) :
    zeroPrefixExpected .scanOnes h rest = .one ↔
      ∃ m, m ≤ h ∧ rest = List.replicate m true := by
  induction rest generalizing h with
  | nil =>
    refine ⟨fun _ => ⟨0, Nat.zero_le _, rfl⟩, fun _ => ?_⟩
    rfl
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [zeroPrefixExpected, zeroPrefixExpected_reject]
      refine ⟨fun h1 => absurd h1 (by decide), ?_⟩
      rintro ⟨m, _, hm⟩
      exact absurd hm.symm (not_replicate_true_eq_cons_false m rest')
    | true =>
      cases h with
      | zero =>
        simp only [zeroPrefixExpected, zeroPrefixExpected_reject]
        refine ⟨fun h1 => absurd h1 (by decide), ?_⟩
        rintro ⟨m, hle, hm⟩
        have hm0 : m = 0 := by omega
        subst hm0
        exact absurd hm.symm (not_replicate_zero_true_eq_cons_true rest')
      | succ h' =>
        simp only [zeroPrefixExpected]
        rw [ih h']
        constructor
        · rintro ⟨m, hle, hm⟩
          refine ⟨m + 1, by omega, ?_⟩
          rw [List.replicate_succ, hm]
        · rintro ⟨m, hle, hm⟩
          cases m with
          | zero =>
            simp [List.replicate] at hm
          | succ m' =>
            refine ⟨m', by omega, ?_⟩
            rw [List.replicate_succ] at hm
            exact (List.cons_eq_cons.mp hm).2

/-- From `scanZeros h`, the output is `.one` iff the remaining input has
    the form `0ᵃ 1ᵇ` with `b ≤ h + a`. -/
private theorem zeroPrefixExpected_scanZeros_eq_one_iff (h : ℕ) (x : List Bool) :
    zeroPrefixExpected .scanZeros h x = .one ↔
      ∃ a b, b ≤ h + a ∧ x = List.replicate a false ++ List.replicate b true := by
  induction x generalizing h with
  | nil =>
    refine ⟨fun _ => ⟨0, 0, by omega, by simp [List.replicate]⟩, fun _ => ?_⟩
    rfl
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [zeroPrefixExpected]
      rw [ih (h + 1)]
      constructor
      · rintro ⟨a, b', hle, hm⟩
        refine ⟨a + 1, b', by omega, ?_⟩
        rw [List.replicate_succ, List.cons_append, hm]
      · rintro ⟨a, b', hle, hm⟩
        cases a with
        | zero =>
          exfalso
          simp only [List.replicate, List.nil_append] at hm
          exact not_replicate_true_eq_cons_false b' rest' hm.symm
        | succ a' =>
          refine ⟨a', b', by omega, ?_⟩
          rw [List.replicate_succ, List.cons_append] at hm
          exact (List.cons_eq_cons.mp hm).2
    | true =>
      cases h with
      | zero =>
        simp only [zeroPrefixExpected, zeroPrefixExpected_reject]
        refine ⟨fun h1 => absurd h1 (by decide), ?_⟩
        rintro ⟨a, b', hle, hm⟩
        cases a with
        | zero =>
          simp only [List.replicate, List.nil_append] at hm
          cases b' with
          | zero => simp [List.replicate] at hm
          | succ b'' => omega
        | succ a' =>
          rw [List.replicate_succ, List.cons_append] at hm
          exact absurd (List.cons_eq_cons.mp hm).1 (by decide)
      | succ h' =>
        simp only [zeroPrefixExpected]
        rw [zeroPrefixExpected_scanOnes_eq_one_iff]
        constructor
        · rintro ⟨m, hle, hm⟩
          refine ⟨0, m + 1, by omega, ?_⟩
          simp only [List.replicate, List.nil_append]
          rw [hm]
        · rintro ⟨a, b', hle, hm⟩
          cases a with
          | zero =>
            simp only [List.replicate, List.nil_append] at hm
            cases b' with
            | zero => simp [List.replicate] at hm
            | succ b'' =>
              refine ⟨b'', by omega, ?_⟩
              rw [List.replicate_succ] at hm
              exact (List.cons_eq_cons.mp hm).2
          | succ a' =>
            rw [List.replicate_succ, List.cons_append] at hm
            exact absurd (List.cons_eq_cons.mp hm).1 (by decide)

/-- **Membership characterization**: `x ∈ zeroPrefix` iff the TM accepts. -/
private theorem zeroPrefixExpected_scanZeros_zero_iff_mem (x : List Bool) :
    zeroPrefixExpected .scanZeros 0 x = .one ↔ x ∈ Language.zeroPrefix := by
  rw [zeroPrefixExpected_scanZeros_eq_one_iff]
  constructor
  · rintro ⟨a, b', hle, hm⟩
    exact ⟨a, b', by omega, hm⟩
  · rintro ⟨n, m, hnm, hx⟩
    exact ⟨n, m, by omega, hx⟩

/-- From `scanOnes`, output is always `.zero` or `.one`. -/
private theorem zeroPrefixExpected_scanOnes_dichotomy (h : ℕ) (rest : List Bool) :
    zeroPrefixExpected .scanOnes h rest = .zero ∨
      zeroPrefixExpected .scanOnes h rest = .one := by
  induction rest generalizing h with
  | nil => simp [zeroPrefixExpected]
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [zeroPrefixExpected]
      exact Or.inl (zeroPrefixExpected_reject h rest')
    | true =>
      cases h with
      | zero =>
        simp only [zeroPrefixExpected]
        exact Or.inl (zeroPrefixExpected_reject 1 rest')
      | succ h' =>
        simp only [zeroPrefixExpected]
        exact ih h'

/-- From `scanZeros`, output is always `.zero` or `.one`. -/
private theorem zeroPrefixExpected_scanZeros_dichotomy (h : ℕ) (x : List Bool) :
    zeroPrefixExpected .scanZeros h x = .zero ∨
      zeroPrefixExpected .scanZeros h x = .one := by
  induction x generalizing h with
  | nil => simp [zeroPrefixExpected]
  | cons b rest' ih =>
    cases b with
    | false =>
      simp only [zeroPrefixExpected]
      exact ih (h + 1)
    | true =>
      cases h with
      | zero =>
        simp only [zeroPrefixExpected]
        exact Or.inl (zeroPrefixExpected_reject 1 rest')
      | succ h' =>
        simp only [zeroPrefixExpected]
        exact zeroPrefixExpected_scanOnes_dichotomy h' rest'

-- ════════════════════════════════════════════════════════════════════════
-- DecidesInTime bridge
-- ════════════════════════════════════════════════════════════════════════

/-- `zeroPrefixTM` decides `Language.zeroPrefix` in time `|x| + 3`. -/
theorem zeroPrefixTM_decidesInTime :
    zeroPrefixTM.DecidesInTime Language.zeroPrefix (fun n => n + 3) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ := zeroPrefixTM_reachesIn x
  refine ⟨c', x.length + 3, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    rw [hout]
    have heq : zeroPrefixExpected .scanZeros 0 x = .one :=
      (zeroPrefixExpected_scanZeros_zero_iff_mem x).mpr hxL
    rw [heq]; rfl
  · intro hxnL
    rw [hout]
    have hne : zeroPrefixExpected .scanZeros 0 x ≠ .one := fun h =>
      hxnL ((zeroPrefixExpected_scanZeros_zero_iff_mem x).mp h)
    have heq : zeroPrefixExpected .scanZeros 0 x = .zero :=
      (zeroPrefixExpected_scanZeros_dichotomy 0 x).resolve_right hne
    rw [heq]; rfl

end TM

-- ════════════════════════════════════════════════════════════════════════
-- DTIME / P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`zeroPrefix ∈ DTIME(n + 3)`**. -/
theorem zeroPrefix_in_DTIME : Language.zeroPrefix ∈ DTIME (fun n => n + 3) :=
  ⟨1, TM.zeroPrefixTM, fun n => n + 3, TM.zeroPrefixTM_decidesInTime, BigO.refl _⟩

/-- **`zeroPrefix ∈ P`**. -/
theorem zeroPrefix_mem_P : Language.zeroPrefix ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ zeroPrefix_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 3 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Complexity
