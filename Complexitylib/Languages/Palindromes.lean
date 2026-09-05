/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Classes.Containments

/-!
# `palindromes`: strings equal to their reverse

A classical non-regular language decided in linear time by a 1-work-tape TM.
The machine copies the input to its work tape, rewinds the input head,
then scans the input forward and the work tape backward, comparing bits.

## Main definitions

- `TM.palindromesTM` — 6-state 1-work-tape palindrome decider.
- `Language.palindromes` — `{x : List Bool | x = x.reverse}`.

## Main results

- `palindromesTM_reachesIn` — halts in `3·|x| + 4` steps on every input.
- `palindromes_in_DTIME`, `palindromes_mem_P`.

## Design

Phases (see comments on `PalindromePhase`):

1. `start`: move all heads from cell 0 (▷) to cell 1.
2. `copy`: scan input forward, copying each bit to the work tape. When
   input reads `□`, move input head left and enter `rewindInput`.
3. `rewindInput`: move input head left until reading `▷`. On `▷`, move
   input head right to cell 1 and work head left by one, entering
   `compare`.
4. `compare`: compare input and work bits. On match, advance input right
   and work left. On `□`, halt with output `1`. On mismatch, enter
   `reject`.
5. `reject`: consume remaining input, then halt with output `0`.
-/


@[expose] public section

namespace Complexity

open Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Control state
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `palindromesTM`. -/
inductive PalindromePhase where
  | start | copy | rewindInput | compare | reject | done
  deriving DecidableEq

instance : Fintype PalindromePhase where
  elems := {.start, .copy, .rewindInput, .compare, .reject, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- The palindrome TM
-- ════════════════════════════════════════════════════════════════════════

/-- Palindrome-decider TM with one work tape. The work tape is used as a
    copy of the input, which is then scanned backward during the compare
    phase. -/
def palindromesTM : TM 1 where
  Q := PalindromePhase
  qstart := .start
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .start =>
      -- All heads at 0 reading ▷: must move right. Writes are no-ops at cell 0.
      (.copy, fun _ => .blank, .blank, .right, fun _ => .right, .right)
    | .copy =>
      if iHead = Γ.blank then
        -- End of input. Move input left (to position |x|), work stays,
        -- transition to rewindInput.
        (.rewindInput, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         moveLeftDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.start then
        -- Vacuous branch (input cell > 0 never reads ▷), but δ must be total.
        -- Halt harmlessly with output 0.
        (.done, fun i => readBackWrite (wHeads i), .zero,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
      else
        -- iHead ∈ {0, 1}. Copy it to the work tape; both heads advance.
        (.copy, fun _ => readBackWrite iHead, readBackWrite oHead,
         .right, fun _ => .right, idleDir oHead)
    | .rewindInput =>
      if iHead = Γ.start then
        -- Done rewinding. Move input right to cell 1, move work head left
        -- by one (from |x|+1 to |x|), transition to compare.
        (.compare, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => moveLeftDir (wHeads i), idleDir oHead)
      else
        -- Keep moving input head left; work stays.
        (.rewindInput, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         moveLeftDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .compare =>
      if iHead = Γ.blank then
        -- Palindrome confirmed (input exhausted); halt with 1.
        (.done, fun i => readBackWrite (wHeads i), .one,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.start then
        -- Vacuous: input at position > 0 can't read ▷. Halt safely with 0.
        (.done, fun i => readBackWrite (wHeads i), .zero,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = wHeads 0 then
        -- Match. Advance input right, move work left.
        (.compare, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => moveLeftDir (wHeads i), idleDir oHead)
      else
        -- Mismatch. Transition to reject; advance input, work stays.
        (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
    | .reject =>
      if iHead = Γ.blank then
        -- Consumed all input; halt writing 0.
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        -- Keep consuming input.
        (.reject, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
    | .done =>
      allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .start =>
      exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    | .copy =>
      dsimp only []
      split
      · -- iHead = blank
        exact ⟨fun h => by simp_all, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      split
      · -- iHead = start
        exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · -- else
        exact ⟨fun _ => rfl, fun _ _ => rfl, idleDir_right_of_start⟩
    | .rewindInput =>
      dsimp only []
      split
      · -- iHead = start
        exact ⟨fun _ => rfl, fun _ hi => by
                 simp only [moveLeftDir, hi, ↓reduceIte],
               idleDir_right_of_start⟩
      · -- iHead ≠ start
        refine ⟨fun h => by simp_all, fun _ => idleDir_right_of_start,
                idleDir_right_of_start⟩
    | .compare =>
      dsimp only []
      split
      · -- iHead = blank
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      split
      · -- iHead = start
        exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      split
      · -- iHead = wHeads 0
        exact ⟨fun _ => rfl, fun _ hi => by
                 simp only [moveLeftDir, hi, ↓reduceIte],
               idleDir_right_of_start⟩
      · -- mismatch
        exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .reject =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
    | .done =>
      exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- Step 1: `.start` → `.copy`. All three heads advance from 0 to 1. -/
private theorem palindromesTM_step_start
    (c : Cfg 1 palindromesTM.Q) (hst : c.state = .start)
    (hih : c.input.head = 0) (hwh : ∀ i, (c.work i).head = 0)
    (hoh : c.output.head = 0) :
    ∃ c', palindromesTM.step c = some c' ∧
      c'.state = PalindromePhase.copy ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      (∀ i, (c'.work i).head = 1) ∧ (∀ i, (c'.work i).cells = (c.work i).cells) ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hih]
  · intro i
    simp [Tape.writeAndMove, Tape.move, Tape.write, hwh i]
  · intro i
    simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hwh i]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hoh]

-- ════════════════════════════════════════════════════════════════════════
-- Small helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Writing any symbol from `Γw` preserves the "no ▷ at cells ≥ 1" invariant. -/
private theorem palindromes_writeAndMove_preserves_nonStart
    (t : Tape) (s : Γw) (d : Dir3)
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

/-- `Tape.init` at a position ≥ 1 is never `Γ.start`. -/
private theorem palindromes_initTape_ns (l : List Γ)
    (hl : ∀ b ∈ l, b ≠ Γ.start) (j : ℕ) (hj : j ≥ 1) :
    (Tape.init l).cells j ≠ Γ.start := by
  have hj' : j ≠ 0 := by omega
  simp only [Tape.init, hj', ↓reduceIte]
  rcases hget : l[j - 1]? with _ | v
  · simp
  · have hmem := List.mem_of_getElem? hget
    have := hl v hmem
    simp [this]

private theorem palindromes_map_ofBool_ns (x : List Bool) (b : Γ) :
    b ∈ x.map Γ.ofBool → b ≠ Γ.start := by
  intro hb
  rw [List.mem_map] at hb
  obtain ⟨b', _, hb'⟩ := hb
  cases b' <;> (simp [Γ.ofBool] at hb'; subst hb'; decide)

/-- Reading `Tape.init (x.map Γ.ofBool)` at cell `i+1` for `i < x.length` gives
    bit `x[i]`. -/
private theorem Tape.init_read_bit (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (Tape.init (x.map Γ.ofBool)).cells (i + 1) = Γ.ofBool (x[i]'hi) := by
  have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
  have himap : i < (x.map Γ.ofBool).length := by rw [hmap_len]; exact hi
  simp only [Tape.init, show i + 1 ≠ 0 from by omega, ↓reduceIte,
    Nat.add_sub_cancel, List.getElem?_eq_getElem himap, Option.getD_some,
    List.getElem_map]

/-- Reading `Tape.init (x.map Γ.ofBool)` at cell `x.length + 1` gives `□`. -/
private theorem Tape.init_read_past_end (x : List Bool) :
    (Tape.init (x.map Γ.ofBool)).cells (x.length + 1) = Γ.blank := by
  simp [Tape.init]

/-- Reading `Tape.init (x.map Γ.ofBool)` at cell `i+1` for `i ≥ x.length` gives `□`. -/
private theorem Tape.init_read_past (x : List Bool) (i : ℕ) (hi : x.length ≤ i) :
    (Tape.init (x.map Γ.ofBool)).cells (i + 1) = Γ.blank := by
  have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
  have hi' : (x.map Γ.ofBool).length ≤ i := by rw [hmap_len]; exact hi
  have hnone : (x.map Γ.ofBool)[i]? = none := List.getElem?_eq_none hi'
  simp only [Tape.init, show i + 1 ≠ 0 from by omega, ↓reduceIte,
    Nat.add_sub_cancel, hnone, Option.getD_none]

-- ════════════════════════════════════════════════════════════════════════
-- Copy phase: invariants
-- ════════════════════════════════════════════════════════════════════════

/-- Invariant during the copy phase: work tape holds the first `k` bits of
    `x`, heads are at cell `k+1`. We use `List.get?` via `getD` rather than a
    sized `getElem` to avoid embedding proofs in the structure fields. -/
structure CopyInv (c : Cfg 1 palindromesTM.Q) (x : List Bool) (k : ℕ) : Prop where
  kle : k ≤ x.length
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  wh : (c.work 0).head = k + 1
  wstart : (c.work 0).cells 0 = Γ.start
  -- Cells 1..k match the first k bits of x, stated via Tape.init.
  wcopy : ∀ i : ℕ, 1 ≤ i → i ≤ k →
    (c.work 0).cells i = (Tape.init (x.map Γ.ofBool)).cells i
  -- Cells > k have never been written (still `□`).
  wblank : ∀ i : ℕ, i > k → (c.work 0).cells i = Γ.blank
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace CopyInv
variable {c : Cfg 1 palindromesTM.Q} {x : List Bool} {k : ℕ}

private theorem input_ns (inv : CopyInv c x k) :
    ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start := by
  intro j hj; rw [inv.ic]
  exact palindromes_initTape_ns _ (palindromes_map_ofBool_ns x) j hj

/-- Work cells 1.. are never ▷. -/
private theorem work_ns (inv : CopyInv c x k) :
    ∀ j, j ≥ 1 → (c.work 0).cells j ≠ Γ.start := by
  intro j hj
  by_cases hjk : j ≤ k
  · rw [inv.wcopy j hj hjk]
    exact palindromes_initTape_ns _ (palindromes_map_ofBool_ns x) j hj
  · push Not at hjk
    rw [inv.wblank j hjk]; decide

private theorem read_bit (inv : CopyInv c x k) (hk : k < x.length) :
    c.input.read = Γ.ofBool (x[k]'hk) := by
  simp only [Tape.read, inv.ih, inv.ic]
  exact Tape.init_read_bit x k hk

private theorem read_blank (inv : CopyInv c x x.length) :
    c.input.read = Γ.blank := by
  simp only [Tape.read, inv.ih, inv.ic]
  exact Tape.init_read_past_end x

private theorem work_read (inv : CopyInv c x k) :
    (c.work 0).read = Γ.blank := by
  simp only [Tape.read, inv.wh]
  exact inv.wblank _ (by omega)

private theorem output_read_ne_start (inv : CopyInv c x k) :
    c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : CopyInv c x k) :
    idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read_ne_start]

end CopyInv

-- ════════════════════════════════════════════════════════════════════════
-- Rewind invariants
-- ════════════════════════════════════════════════════════════════════════

/-- Invariant during the `rewindInput` phase: work tape holds all of `x`,
    input head is somewhere in `[0 .. x.length]`. -/
structure RewindInv (c : Cfg 1 palindromesTM.Q) (x : List Bool) (j : ℕ) : Prop where
  jle : j ≤ x.length
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = j
  wh : (c.work 0).head = x.length + 1
  wstart : (c.work 0).cells 0 = Γ.start
  wcopy : ∀ i : ℕ, 1 ≤ i → i ≤ x.length →
    (c.work 0).cells i = (Tape.init (x.map Γ.ofBool)).cells i
  wblank : ∀ i : ℕ, i > x.length → (c.work 0).cells i = Γ.blank
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace RewindInv
variable {c : Cfg 1 palindromesTM.Q} {x : List Bool} {j : ℕ}

private theorem input_ns (inv : RewindInv c x j) :
    ∀ i, i ≥ 1 → c.input.cells i ≠ Γ.start := by
  intro i hi; rw [inv.ic]
  exact palindromes_initTape_ns _ (palindromes_map_ofBool_ns x) i hi

private theorem work_ns (inv : RewindInv c x j) :
    ∀ i, i ≥ 1 → (c.work 0).cells i ≠ Γ.start := by
  intro i hi
  by_cases hix : i ≤ x.length
  · rw [inv.wcopy i hi hix]
    exact palindromes_initTape_ns _ (palindromes_map_ofBool_ns x) i hi
  · push Not at hix
    rw [inv.wblank i hix]; decide

private theorem work_read (inv : RewindInv c x j) :
    (c.work 0).read = Γ.blank := by
  simp only [Tape.read, inv.wh]
  exact inv.wblank _ (by omega)

private theorem output_read_ne_start (inv : RewindInv c x j) :
    c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : RewindInv c x j) :
    idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read_ne_start]

end RewindInv

-- ════════════════════════════════════════════════════════════════════════
-- Compare invariants
-- ════════════════════════════════════════════════════════════════════════

/-- Invariant during the `compare` phase after `k` matches: input head at
    `k+1`, work head at `|x|-k`. -/
structure CompareInv (c : Cfg 1 palindromesTM.Q) (x : List Bool) (k : ℕ) : Prop where
  kle : k ≤ x.length
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = k + 1
  wh : (c.work 0).head = x.length - k
  wstart : (c.work 0).cells 0 = Γ.start
  wcopy : ∀ i : ℕ, 1 ≤ i → i ≤ x.length →
    (c.work 0).cells i = (Tape.init (x.map Γ.ofBool)).cells i
  wblank : ∀ i : ℕ, i > x.length → (c.work 0).cells i = Γ.blank
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace CompareInv
variable {c : Cfg 1 palindromesTM.Q} {x : List Bool} {k : ℕ}

private theorem input_ns (inv : CompareInv c x k) :
    ∀ i, i ≥ 1 → c.input.cells i ≠ Γ.start := by
  intro i hi; rw [inv.ic]
  exact palindromes_initTape_ns _ (palindromes_map_ofBool_ns x) i hi

private theorem work_ns (inv : CompareInv c x k) :
    ∀ i, i ≥ 1 → (c.work 0).cells i ≠ Γ.start := by
  intro i hi
  by_cases hix : i ≤ x.length
  · rw [inv.wcopy i hi hix]
    exact palindromes_initTape_ns _ (palindromes_map_ofBool_ns x) i hi
  · push Not at hix
    rw [inv.wblank i hix]; decide

private theorem output_read_ne_start (inv : CompareInv c x k) :
    c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : CompareInv c x k) :
    idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read_ne_start]

/-- Input reads bit k when k < x.length. -/
private theorem read_input_bit (inv : CompareInv c x k) (hk : k < x.length) :
    c.input.read = Γ.ofBool (x[k]'hk) := by
  simp only [Tape.read, inv.ih, inv.ic]
  exact Tape.init_read_bit x k hk

/-- When k = x.length, input reads blank. -/
private theorem read_input_blank (inv : CompareInv c x x.length) :
    c.input.read = Γ.blank := by
  simp only [Tape.read, inv.ih, inv.ic]
  exact Tape.init_read_past_end x

/-- Work reads the `(|x|-k-1)`-th bit when k < x.length. -/
private theorem read_work_bit (inv : CompareInv c x k) (hk : k < x.length) :
    (c.work 0).read = Γ.ofBool (x[x.length - k - 1]'(by omega)) := by
  simp only [Tape.read, inv.wh]
  have hxk : x.length - k - 1 < x.length := by omega
  have hwcopy := inv.wcopy (x.length - k) (by omega) (by omega)
  have hinit := Tape.init_read_bit x (x.length - k - 1) hxk
  have heq : x.length - k - 1 + 1 = x.length - k := by omega
  rw [heq] at hinit
  rw [hwcopy, hinit]

/-- When k = x.length, work reads `▷`. -/
private theorem read_work_start (inv : CompareInv c x x.length) :
    (c.work 0).read = Γ.start := by
  simp only [Tape.read, inv.wh]
  have : x.length - x.length = 0 := by omega
  rw [this]; exact inv.wstart

end CompareInv

-- ════════════════════════════════════════════════════════════════════════
-- Reject invariant
-- ════════════════════════════════════════════════════════════════════════

/-- Invariant during the `reject` phase: input head somewhere in
    `[1 .. x.length+1]`; work doesn't matter. -/
structure PalRejectInv (c : Cfg 1 palindromesTM.Q) (x : List Bool) (j : ℕ) : Prop where
  st : c.state = .reject
  ic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells
  ih : c.input.head = j + 1
  oh : c.output.head = 1
  ons : c.output.cells 1 ≠ Γ.start

namespace PalRejectInv
variable {c : Cfg 1 palindromesTM.Q} {x : List Bool} {j : ℕ}

private theorem read_bit (inv : PalRejectInv c x j) (hj : j < x.length) :
    c.input.read = Γ.ofBool (x[j]'hj) := by
  simp only [Tape.read, inv.ih, inv.ic]
  exact Tape.init_read_bit x j hj

private theorem read_blank (inv : PalRejectInv c x x.length) :
    c.input.read = Γ.blank := by
  simp only [Tape.read, inv.ih, inv.ic]
  exact Tape.init_read_past_end x

private theorem output_read_ne_start (inv : PalRejectInv c x j) :
    c.output.read ≠ Γ.start := by
  simp only [Tape.read, inv.oh]; exact inv.ons

private theorem output_stay (inv : PalRejectInv c x j) :
    idleDir c.output.read = Dir3.stay := by
  simp [idleDir, inv.output_read_ne_start]

end PalRejectInv

/-- Copy step: `.copy` + iHead ∈ {0,1} → `.copy`, both heads advance, work
    tape records the bit. -/
private theorem palindromesTM_step_copy_push
    (c : Cfg 1 palindromesTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .copy) (hk : k < x.length) (inv : CopyInv c x k) :
    ∃ c', palindromesTM.step c = some c' ∧
      c'.state = PalindromePhase.copy ∧ CopyInv c' x (k + 1) := by
  have hib : c.input.read = Γ.ofBool (x[k]'hk) := inv.read_bit hk
  have hir_ne_blank : c.input.read ≠ Γ.blank := by
    rw [hib]; cases x[k] <;> decide
  have hir_ne_start : c.input.read ≠ Γ.start := by
    rw [hib]; cases x[k] <;> decide
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte,
             ite_eq_right hir_ne_blank, ite_eq_right hir_ne_start]
  refine ⟨_, rfl, rfl, ?_⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _
    rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · -- work.head = k + 2
    show ((c.work 0).writeAndMove (readBackWrite c.input.read).toΓ Dir3.right).head = k + 1 + 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, inv.wh]
  · -- work.cells 0 = ▷
    show ((c.work 0).writeAndMove (readBackWrite c.input.read).toΓ Dir3.right).cells 0 = Γ.start
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · exact inv.wstart
    · rename_i hne
      show Function.update (c.work 0).cells (c.work 0).head _ 0 = Γ.start
      rw [Function.update_of_ne (Ne.symm hne)]
      exact inv.wstart
  · -- wcopy at k+1: the newly written cell holds x[k]; earlier cells unchanged
    intro i hi1 hik1
    show ((c.work 0).writeAndMove (readBackWrite c.input.read).toΓ Dir3.right).cells i
      = (Tape.init (x.map Γ.ofBool)).cells i
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · -- head = 0 case: vacuous since work.head = k+1 ≠ 0
      rename_i hhead
      rw [inv.wh] at hhead; omega
    · rename_i hhead
      -- Need to show: Function.update (c.work 0).cells (c.work 0).head _ i = Tape.init.cells i
      by_cases hik : i = k + 1
      · -- This is the new cell
        show Function.update (c.work 0).cells (c.work 0).head
              (readBackWrite c.input.read).toΓ i
          = (Tape.init (x.map Γ.ofBool)).cells i
        rw [inv.wh, ← hik, Function.update_self]
        rw [toΓ_readBackWrite_of_ne_start hir_ne_start, hib, hik, Tape.init_read_bit x k hk]
      · -- Old cell, unchanged
        show Function.update (c.work 0).cells (c.work 0).head _ i
          = (Tape.init (x.map Γ.ofBool)).cells i
        have hine : i ≠ (c.work 0).head := by rw [inv.wh]; omega
        rw [Function.update_of_ne hine]
        have : i ≤ k := by omega
        exact inv.wcopy i hi1 this
  · -- wblank at > k+1
    intro i hi
    show ((c.work 0).writeAndMove (readBackWrite c.input.read).toΓ Dir3.right).cells i = Γ.blank
    simp only [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · rename_i hhead; rw [inv.wh] at hhead; omega
    · show Function.update (c.work 0).cells (c.work 0).head _ i = Γ.blank
      have hine : i ≠ (c.work 0).head := by rw [inv.wh]; omega
      rw [Function.update_of_ne hine]
      exact inv.wblank i (by omega)
  · -- output.head = 1
    show (c.output.writeAndMove _ _).head = 1
    have hstay := inv.output_stay
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · -- output.cells 1 ≠ ▷
    show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Copy-end step: `.copy` + iHead=□ → `.rewindInput`. Input head moves left
    by one (from `|x|+1` to `|x|`); work stays. -/
private theorem palindromesTM_step_copy_end
    (c : Cfg 1 palindromesTM.Q) (x : List Bool)
    (hst : c.state = .copy) (inv : CopyInv c x x.length) :
    ∃ c', palindromesTM.step c = some c' ∧
      c'.state = PalindromePhase.rewindInput ∧ RewindInv c' x x.length := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hstay := inv.output_stay
  have hwread : (c.work 0).read = Γ.blank := inv.work_read
  have hwread_ne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
  have hw_stay : idleDir (c.work 0).read = Dir3.stay := by simp [idleDir, hwread_ne]
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- input cells unchanged (moveLeft preserves cells)
    show (c.input.move (moveLeftDir c.input.read)).cells = _
    rw [Tape.move_cells]; exact inv.ic
  · -- input head = x.length (moved from x.length+1 left by 1)
    show (c.input.move (moveLeftDir c.input.read)).head = x.length
    have hml : moveLeftDir c.input.read = Dir3.left := by
      simp [moveLeftDir, hir]
    simp only [hml, Tape.move, inv.ih]; omega
  · -- work head = x.length + 1 (unchanged since work idle)
    show ((c.work 0).writeAndMove _ _).head = x.length + 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hw_stay, inv.wh]
  · -- work cells 0 = ▷ (unchanged)
    show ((c.work 0).writeAndMove _ _).cells 0 = Γ.start
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wstart
  · -- wcopy unchanged
    intro i hi1 hix
    show ((c.work 0).writeAndMove _ _).cells i = (Tape.init (x.map Γ.ofBool)).cells i
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wcopy i hi1 hix
  · -- wblank unchanged
    intro i hi
    show ((c.work 0).writeAndMove _ _).cells i = Γ.blank
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wblank i hi
  · -- output head = 1
    show (c.output.writeAndMove _ _).head = 1
    simp [Tape.writeAndMove, hstay, Tape.move, Tape.write_head, inv.oh]
  · -- output cell 1 ≠ ▷
    show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Rewind-step (non-▷): `.rewindInput` + iHead ≠ ▷ → `.rewindInput`.
    Input head moves left; work stays. -/
private theorem palindromesTM_step_rewindInput_consume
    (c : Cfg 1 palindromesTM.Q) (x : List Bool) (j : ℕ) (hj : j ≥ 1)
    (hst : c.state = .rewindInput) (inv : RewindInv c x j) :
    ∃ c', palindromesTM.step c = some c' ∧
      c'.state = PalindromePhase.rewindInput ∧ RewindInv c' x (j - 1) := by
  have hir_ne_start : c.input.read ≠ Γ.start := by
    simp only [Tape.read, inv.ih]
    have : c.input.cells j ≠ Γ.start := inv.input_ns j hj
    exact this
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte,
             ite_eq_right hir_ne_start]
  refine ⟨_, rfl, rfl, ?_⟩
  have hml : moveLeftDir c.input.read = Dir3.left := by
    simp [moveLeftDir, hir_ne_start]
  have hwread_ne : (c.work 0).read ≠ Γ.start := by
    rw [inv.work_read]; decide
  have hw_stay : idleDir (c.work 0).read = Dir3.stay := by simp [idleDir, hwread_ne]
  have hostay := inv.output_stay
  have hjle := inv.jle
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move _).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move (moveLeftDir c.input.read)).head = j - 1
    simp only [hml, Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove _ _).head = x.length + 1
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hw_stay, inv.wh]
  · show ((c.work 0).writeAndMove _ _).cells 0 = Γ.start
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wstart
  · intro i hi1 hix
    show ((c.work 0).writeAndMove _ _).cells i = (Tape.init (x.map Γ.ofBool)).cells i
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wcopy i hi1 hix
  · intro i hi
    show ((c.work 0).writeAndMove _ _).cells i = Γ.blank
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wblank i hi
  · show (c.output.writeAndMove _ _).head = 1
    simp [Tape.writeAndMove, hostay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Rewind-finish step: `.rewindInput` + iHead=▷ → `.compare`. Input moves
    right (from 0 to 1); work moves left (from `|x|+1` to `|x|`). -/
private theorem palindromesTM_step_rewindInput_finish
    (c : Cfg 1 palindromesTM.Q) (x : List Bool)
    (hst : c.state = .rewindInput) (inv : RewindInv c x 0) :
    ∃ c', palindromesTM.step c = some c' ∧
      c'.state = PalindromePhase.compare ∧ CompareInv c' x 0 := by
  have hir : c.input.read = Γ.start := by
    simp only [Tape.read, inv.ih, inv.ic]
    simp [Tape.init]
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hwread : (c.work 0).read = Γ.blank := inv.work_read
  have hwread_ne : (c.work 0).read ≠ Γ.start := by rw [hwread]; decide
  have hwml : moveLeftDir (c.work 0).read = Dir3.left := by
    simp [moveLeftDir, hwread_ne]
  have hostay := inv.output_stay
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = 0 + 1
    simp [Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove _ _).head = x.length - 0
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hwml, inv.wh]
    omega
  · show ((c.work 0).writeAndMove _ _).cells 0 = Γ.start
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wstart
  · intro i hi1 hix
    show ((c.work 0).writeAndMove _ _).cells i = (Tape.init (x.map Γ.ofBool)).cells i
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wcopy i hi1 hix
  · intro i hi
    show ((c.work 0).writeAndMove _ _).cells i = Γ.blank
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwread_ne)]
    exact inv.wblank i hi
  · show (c.output.writeAndMove _ _).head = 1
    simp [Tape.writeAndMove, hostay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Compare-match step: `.compare` + input bit = work bit → `.compare`,
    input head +1, work head -1, `k` → `k+1`. -/
private theorem palindromesTM_step_compare_match
    (c : Cfg 1 palindromesTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .compare) (hk : k < x.length)
    (hmatch : (x[k]'hk) = (x[x.length - k - 1]'(by omega)))
    (inv : CompareInv c x k) :
    ∃ c', palindromesTM.step c = some c' ∧
      c'.state = PalindromePhase.compare ∧ CompareInv c' x (k + 1) := by
  have hir : c.input.read = Γ.ofBool (x[k]'hk) := inv.read_input_bit hk
  have hwr : (c.work 0).read = Γ.ofBool (x[x.length - k - 1]'(by omega)) :=
    inv.read_work_bit hk
  have hir_eq_wr : c.input.read = (c.work 0).read := by rw [hir, hwr, hmatch]
  have hir_ne_blank : c.input.read ≠ Γ.blank := by
    rw [hir]; cases x[k] <;> decide
  have hir_ne_start : c.input.read ≠ Γ.start := by
    rw [hir]; cases x[k] <;> decide
  -- The `compare` δ branch tests `iHead = wHeads 0`
  have hir_eq : c.input.read = (fun i : Fin 1 => (c.work i).read) 0 := by
    show c.input.read = (c.work 0).read
    exact hir_eq_wr
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte,
             ite_eq_right hir_ne_blank, ite_eq_right hir_ne_start, ite_eq_left hir_eq]
  refine ⟨_, rfl, rfl, ?_⟩
  have hwr_ne_start : (c.work 0).read ≠ Γ.start := by
    rw [hwr]; cases x[x.length-k-1] <;> decide
  have hwml : moveLeftDir (c.work 0).read = Dir3.left := by
    simp [moveLeftDir, hwr_ne_start]
  have hostay := inv.output_stay
  have hkle_succ : k + 1 ≤ x.length := by omega
  refine ⟨hkle_succ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show ((c.work 0).writeAndMove _ _).head = x.length - (k + 1)
    simp only [Tape.writeAndMove, Tape.move, Tape.write_head, hwml, inv.wh]
    omega
  · show ((c.work 0).writeAndMove _ _).cells 0 = Γ.start
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwr_ne_start)]
    exact inv.wstart
  · intro i hi1 hix
    show ((c.work 0).writeAndMove _ _).cells i = (Tape.init (x.map Γ.ofBool)).cells i
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwr_ne_start)]
    exact inv.wcopy i hi1 hix
  · intro i hi
    show ((c.work 0).writeAndMove _ _).cells i = Γ.blank
    rw [tape_readBackWrite_preserves (c.work 0) _ (Or.inr hwr_ne_start)]
    exact inv.wblank i hi
  · show (c.output.writeAndMove _ _).head = 1
    simp [Tape.writeAndMove, hostay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Compare-mismatch step: `.compare` + input bit ≠ work bit → `.reject`,
    input head +1, work stays. -/
private theorem palindromesTM_step_compare_mismatch
    (c : Cfg 1 palindromesTM.Q) (x : List Bool) (k : ℕ)
    (hst : c.state = .compare) (hk : k < x.length)
    (hmis : (x[k]'hk) ≠ (x[x.length - k - 1]'(by omega)))
    (inv : CompareInv c x k) :
    ∃ c', palindromesTM.step c = some c' ∧ PalRejectInv c' x (k + 1) := by
  have hir : c.input.read = Γ.ofBool (x[k]'hk) := inv.read_input_bit hk
  have hwr : (c.work 0).read = Γ.ofBool (x[x.length - k - 1]'(by omega)) :=
    inv.read_work_bit hk
  have hir_ne_blank : c.input.read ≠ Γ.blank := by
    rw [hir]; cases x[k] <;> decide
  have hir_ne_start : c.input.read ≠ Γ.start := by
    rw [hir]; cases x[k] <;> decide
  have hir_ne_wr : c.input.read ≠ (c.work 0).read := by
    rw [hir, hwr]; intro h
    apply hmis
    cases hb1 : x[k] <;> cases hb2 : x[x.length-k-1] <;>
      simp [hb1, hb2, Γ.ofBool] at h ⊢
  have hir_ne : c.input.read ≠ (fun i : Fin 1 => (c.work i).read) 0 := hir_ne_wr
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte,
             ite_eq_right hir_ne_blank, ite_eq_right hir_ne_start, ite_eq_right hir_ne]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = k + 1 + 1
    simp [Tape.move, inv.ih]
  · show (c.output.writeAndMove _ _).head = 1
    have hostay := inv.output_stay
    simp [Tape.writeAndMove, hostay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Compare-halt step: `.compare` + iHead=□ → halt, output 1. -/
private theorem palindromesTM_step_compare_halt
    (c : Cfg 1 palindromesTM.Q) (x : List Bool)
    (hst : c.state = .compare) (inv : CompareInv c x x.length) :
    ∃ c', palindromesTM.step c = some c' ∧ palindromesTM.halted c' ∧
      c'.output.cells 1 = Γ.one := by
  have hir : c.input.read = Γ.blank := inv.read_input_blank
  simp only [TM.step, hst, palindromesTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hostay := inv.output_stay
  show (c.output.writeAndMove Γw.one.toΓ _).cells 1 = Γ.one
  simp only [Tape.writeAndMove, hostay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

/-- Reject-consume step: `.reject` + iHead ≠ □ → `.reject`, input +1. -/
private theorem palindromesTM_step_reject_consume
    (c : Cfg 1 palindromesTM.Q) (x : List Bool) (j : ℕ)
    (hj : j < x.length) (inv : PalRejectInv c x j) :
    ∃ c', palindromesTM.step c = some c' ∧ PalRejectInv c' x (j + 1) := by
  have hir_bit : c.input.read = Γ.ofBool (x[j]'hj) := inv.read_bit hj
  have hir_ne_blank : c.input.read ≠ Γ.blank := by
    rw [hir_bit]; cases x[j] <;> decide
  simp only [TM.step, inv.st, palindromesTM, reduceCtorEq, ↓reduceIte,
             ite_eq_right hir_ne_blank]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · show (c.input.move Dir3.right).cells = _; rw [Tape.move_cells]; exact inv.ic
  · show (c.input.move Dir3.right).head = j + 1 + 1
    simp [Tape.move, inv.ih]
  · show (c.output.writeAndMove _ _).head = 1
    have hostay := inv.output_stay
    simp [Tape.writeAndMove, hostay, Tape.move, Tape.write_head, inv.oh]
  · show (c.output.writeAndMove _ _).cells 1 ≠ Γ.start
    rw [tape_readBackWrite_preserves c.output _ (Or.inr inv.output_read_ne_start)]
    exact inv.ons

/-- Reject-halt step: `.reject` + iHead=□ → halt, output 0. -/
private theorem palindromesTM_step_reject_halt
    (c : Cfg 1 palindromesTM.Q) (x : List Bool) (inv : PalRejectInv c x x.length) :
    ∃ c', palindromesTM.step c = some c' ∧ palindromesTM.halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  have hir : c.input.read = Γ.blank := inv.read_blank
  simp only [TM.step, inv.st, palindromesTM, reduceCtorEq, ↓reduceIte, ite_eq_left hir]
  refine ⟨_, rfl, rfl, ?_⟩
  have hostay := inv.output_stay
  show (c.output.writeAndMove Γw.zero.toΓ _).cells 1 = Γ.zero
  simp only [Tape.writeAndMove, hostay, Tape.move, Tape.write, inv.oh,
             show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte, Function.update_self, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Phase induction lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- From PalRejectInv at `j`, halt in `x.length - j + 1` steps with output 0.
    Parameterized by `m = x.length - j`. -/
private theorem palindromesTM_reject_to_halt (x : List Bool) :
    ∀ (m j : ℕ) (c : Cfg 1 palindromesTM.Q),
      PalRejectInv c x j → j + m = x.length →
      ∃ c', palindromesTM.reachesIn (m + 1) c c' ∧ palindromesTM.halted c' ∧
        c'.output.cells 1 = Γ.zero := by
  intro m
  induction m with
  | zero =>
    intro j c inv hlen
    have hj : j = x.length := by omega
    subst hj
    obtain ⟨c', hstep, hhalt, hout⟩ := palindromesTM_step_reject_halt c x inv
    exact ⟨c', .step hstep .zero, hhalt, hout⟩
  | succ m' ih =>
    intro j c inv hlen
    have hj : j < x.length := by omega
    obtain ⟨c', hstep, inv'⟩ := palindromesTM_step_reject_consume c x j hj inv
    have hlen' : (j + 1) + m' = x.length := by omega
    obtain ⟨c'', hreach, hhalt, hout⟩ := ih (j + 1) c' inv' hlen'
    exact ⟨c'', .step hstep hreach, hhalt, hout⟩

/-- Pointwise palindrome condition: `∀ i < |x|, x[i] = x[|x|-1-i]`. -/
def IsPalindrome (x : List Bool) : Prop :=
  ∀ i, (hi : i < x.length) → (x[i]'hi) = (x[x.length - 1 - i]'(by omega))

/-- Compare phase from k, case-split on whether the palindrome condition
    holds from `k` onwards. Returns the output cell value. -/
private theorem palindromesTM_compare_to_halt (x : List Bool) :
    ∀ (m k : ℕ) (c : Cfg 1 palindromesTM.Q),
      c.state = .compare → CompareInv c x k → k + m = x.length →
      ∃ c', palindromesTM.reachesIn (m + 1) c c' ∧ palindromesTM.halted c' ∧
        c'.output.cells 1 =
          (if ∀ i, (hi : i < x.length) → k ≤ i →
                    (x[i]'hi) = (x[x.length - 1 - i]'(by omega))
           then Γ.one else Γ.zero) := by
  intro m
  induction m with
  | zero =>
    intro k c hst inv hlen
    have hk : k = x.length := by omega
    subst hk
    obtain ⟨c', hstep, hhalt, hout⟩ := palindromesTM_step_compare_halt c x hst inv
    refine ⟨c', .step hstep .zero, hhalt, ?_⟩
    rw [hout]
    -- The "forall i < x.length, x.length ≤ i" is vacuous
    have htriv : ∀ i, (hi : i < x.length) → x.length ≤ i →
        (x[i]'hi) = (x[x.length - 1 - i]'(by omega)) := by
      intro i hi hle; exfalso; omega
    rw [ite_eq_left htriv]
  | succ m' ih =>
    intro k c hst inv hlen
    have hk : k < x.length := by omega
    -- Case split: palindrome condition at k matches or not
    by_cases hmatch : (x[k]'hk) = (x[x.length - k - 1]'(by omega))
    · -- Match: compare step then recurse
      have hmatch' : (x[k]'hk) = (x[x.length - 1 - k]'(by omega)) := by
        have : (x.length - 1 - k) = (x.length - k - 1) := by omega
        simp only [this]; exact hmatch
      obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
        palindromesTM_step_compare_match c x k hst hk hmatch inv
      have hlen' : (k + 1) + m' = x.length := by omega
      obtain ⟨c', hreach, hhalt, hout⟩ := ih (k + 1) c₁ hst₁ inv₁ hlen'
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]
      -- Show the if-condition at k+1 matches the if-condition at k
      by_cases hP : ∀ i, (hi : i < x.length) → k + 1 ≤ i →
                     (x[i]'hi) = (x[x.length - 1 - i]'(by omega))
      · -- Both hold
        have hPk : ∀ i, (hi : i < x.length) → k ≤ i →
                   (x[i]'hi) = (x[x.length - 1 - i]'(by omega)) := by
          intro i hi hle
          by_cases hik : i = k
          · subst hik; exact hmatch'
          · exact hP i hi (by omega)
        rw [ite_eq_left hP, ite_eq_left hPk]
      · -- Neither
        have hPk : ¬ ∀ i, (hi : i < x.length) → k ≤ i →
                   (x[i]'hi) = (x[x.length - 1 - i]'(by omega)) := by
          intro hP'; apply hP
          intro i hi hle; exact hP' i hi (by omega)
        rw [ite_eq_right hP, ite_eq_right hPk]
    · -- Mismatch: transition to reject, then reject-to-halt
      have hmis : (x[k]'hk) ≠ (x[x.length - k - 1]'(by omega)) := hmatch
      obtain ⟨c₁, hstep, inv₁⟩ :=
        palindromesTM_step_compare_mismatch c x k hst hk hmis inv
      have hlen' : (k + 1) + m' = x.length := by omega
      obtain ⟨c', hreach, hhalt, hout⟩ :=
        palindromesTM_reject_to_halt x m' (k + 1) c₁ inv₁ hlen'
      refine ⟨c', .step hstep hreach, hhalt, ?_⟩
      rw [hout]
      -- The palindrome condition fails since x[k] ≠ x[x.length-1-k]
      have hmis' : (x[k]'hk) ≠ (x[x.length - 1 - k]'(by omega)) := by
        have : (x.length - 1 - k) = (x.length - k - 1) := by omega
        simp only [this]; exact hmis
      have hPk : ¬ ∀ i, (hi : i < x.length) → k ≤ i →
                   (x[i]'hi) = (x[x.length - 1 - i]'(by omega)) := by
        intro hP
        exact hmis' (hP k hk le_rfl)
      rw [ite_eq_right hPk]

/-- Rewind input phase: from `RewindInv c x j`, reach `CompareInv c' x 0` in
    `j + 1` steps. -/
private theorem palindromesTM_rewind_to_compare (x : List Bool) :
    ∀ (j : ℕ) (c : Cfg 1 palindromesTM.Q),
      c.state = .rewindInput → RewindInv c x j →
      ∃ c', palindromesTM.reachesIn (j + 1) c c' ∧
        c'.state = PalindromePhase.compare ∧ CompareInv c' x 0 := by
  intro j
  induction j with
  | zero =>
    intro c hst inv
    obtain ⟨c', hstep, hst', inv'⟩ :=
      palindromesTM_step_rewindInput_finish c x hst inv
    exact ⟨c', .step hstep .zero, hst', inv'⟩
  | succ j' ih =>
    intro c hst inv
    have hj' : j' + 1 ≥ 1 := by omega
    obtain ⟨c₁, hstep, hst₁, inv₁⟩ :=
      palindromesTM_step_rewindInput_consume c x (j' + 1) hj' hst inv
    have hinv₁ : RewindInv c₁ x j' := by
      have : j' + 1 - 1 = j' := by omega
      rw [← this]; exact inv₁
    obtain ⟨c', hreach, hst', inv'⟩ := ih c₁ hst₁ hinv₁
    exact ⟨c', .step hstep hreach, hst', inv'⟩

/-- Copy phase: from `CopyInv c x k`, reach `RewindInv c' x x.length` via
    `(x.length - k)` copy steps and one copy-end step. Total: `x.length - k + 1` steps. -/
private theorem palindromesTM_copy_to_rewind (x : List Bool) :
    ∀ (m k : ℕ) (c : Cfg 1 palindromesTM.Q),
      c.state = .copy → CopyInv c x k → k + m = x.length →
      ∃ c', palindromesTM.reachesIn (m + 1) c c' ∧
        c'.state = PalindromePhase.rewindInput ∧ RewindInv c' x x.length := by
  intro m
  induction m with
  | zero =>
    intro k c hst inv hlen
    have hk : k = x.length := by omega
    subst hk
    obtain ⟨c', hstep, hst', inv'⟩ := palindromesTM_step_copy_end c x hst inv
    exact ⟨c', .step hstep .zero, hst', inv'⟩
  | succ m' ih =>
    intro k c hst inv hlen
    have hk : k < x.length := by omega
    obtain ⟨c₁, hstep, hst₁, inv₁⟩ := palindromesTM_step_copy_push c x k hst hk inv
    have hlen' : (k + 1) + m' = x.length := by omega
    obtain ⟨c', hreach, hst', inv'⟩ := ih (k + 1) c₁ hst₁ inv₁ hlen'
    exact ⟨c', .step hstep hreach, hst', inv'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `palindromesTM` halts in `3·|x| + 4` steps on every input, writing
    the correct answer to output cell 1. -/
theorem palindromesTM_reachesIn (x : List Bool) :
    ∃ c', palindromesTM.reachesIn (3 * x.length + 4) (palindromesTM.initCfg x) c' ∧
      palindromesTM.halted c' ∧
      c'.output.cells 1 =
        (if ∀ i, (hi : i < x.length) → (x[i]'hi) = (x[x.length - 1 - i]'(by omega))
         then Γ.one else Γ.zero) := by
  -- Step 1: start → copy
  obtain ⟨c₁, hstep1, hst1, hih1, hic1, hwh1, hwc1, hoh1, hoc1⟩ :=
    palindromesTM_step_start (palindromesTM.initCfg x) rfl rfl (by intro _; rfl) rfl
  -- Set up CopyInv at k = 0
  have hinv0 : CopyInv c₁ x 0 := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hic1]
    · simp [hih1]
    · exact hwh1 0
    · rw [hwc1 0]
      have : (palindromesTM.initCfg x).work 0 = Tape.init [] := rfl
      rw [this]; simp [Tape.init]
    · intro i hi1 hile
      omega
    · intro i hi
      rw [hwc1 0]
      have : (palindromesTM.initCfg x).work 0 = Tape.init [] := rfl
      rw [this]
      show (Tape.init []).cells i = Γ.blank
      have hi' : i ≠ 0 := by omega
      simp [Tape.init, hi']
    · exact hoh1
    · rw [hoc1]
      have : (palindromesTM.initCfg x).output = Tape.init [] := rfl
      rw [this]; show (Tape.init []).cells 1 ≠ Γ.start
      simp [Tape.init]
  -- Copy phase: x.length + 1 steps to reach rewindInput
  obtain ⟨c₂, hreach_copy, hst2, hinv_rewind⟩ :=
    palindromesTM_copy_to_rewind x x.length 0 c₁ hst1 hinv0 (by omega)
  -- Rewind phase: x.length + 1 steps to reach compare
  obtain ⟨c₃, hreach_rewind, hst3, hinv_cmp⟩ :=
    palindromesTM_rewind_to_compare x x.length c₂ hst2 hinv_rewind
  -- Compare phase: x.length + 1 steps to halt
  obtain ⟨c', hreach_cmp, hhalt, hout⟩ :=
    palindromesTM_compare_to_halt x x.length 0 c₃ hst3 hinv_cmp (by omega)
  refine ⟨c', ?_, hhalt, ?_⟩
  · -- Combine: (x.length+1) + (x.length+1) + (x.length+1) + 1 = 3*x.length + 4
    have h23 := TM.reachesIn_trans palindromesTM hreach_rewind hreach_cmp
    have h123 := TM.reachesIn_trans palindromesTM hreach_copy h23
    have hstep : palindromesTM.reachesIn
        (x.length + 1 + (x.length + 1 + (x.length + 1)) + 1)
        (palindromesTM.initCfg x) c' :=
      .step hstep1 h123
    have hcount : 3 * x.length + 4 =
        x.length + 1 + (x.length + 1 + (x.length + 1)) + 1 := by ring
    rw [hcount]; exact hstep
  · rw [hout]
    -- The compare-to-halt condition with k = 0 simplifies
    congr 1
    apply propext
    constructor
    · intro h i hi; exact h i hi (Nat.zero_le _)
    · intro h i hi _; exact h i hi

end TM

namespace Language

/-- **The palindromes language** — binary strings equal to their reverse. -/
def palindromes : Language := {x : List Bool | x = x.reverse}

end Language

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Equivalence: `IsPalindrome x ↔ x = x.reverse`
-- ════════════════════════════════════════════════════════════════════════

/-- Pointwise palindrome is equivalent to equality with the reverse. -/
private theorem isPalindrome_iff_reverse_eq (x : List Bool) :
    IsPalindrome x ↔ x = x.reverse := by
  constructor
  · intro h
    apply List.ext_getElem
    · simp
    · intro i hi hir
      rw [List.getElem_reverse]
      exact h i hi
  · intro hx i hi
    -- Reduce the goal to a fact about `x.reverse` via `hx : x = x.reverse`.
    have hx' : x.reverse = x := hx.symm
    have hir : i < x.reverse.length := by rw [hx']; exact hi
    have hrev : x.reverse[i]'hir = x[x.length - 1 - i]'(by
      simp at hir; omega) := List.getElem_reverse hir
    have hxi : x[i]'hi = x.reverse[i]'hir := by
      clear hrev
      -- Substitute `x.reverse = x` in place of `x.reverse`.
      revert hir
      rw [hx']
      intro _
      rfl
    rw [hxi, hrev]

-- ════════════════════════════════════════════════════════════════════════
-- DecidesInTime bridge
-- ════════════════════════════════════════════════════════════════════════

/-- `palindromesTM` decides `Language.palindromes` in time `3·|x| + 4`. -/
theorem palindromesTM_decidesInTime :
    palindromesTM.DecidesInTime Language.palindromes (fun n => 3 * n + 4) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ := palindromesTM_reachesIn x
  refine ⟨c', 3 * x.length + 4, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    rw [hout]
    have hpal : IsPalindrome x :=
      (isPalindrome_iff_reverse_eq x).mpr hxL
    exact ite_eq_left hpal
  · intro hxnL
    rw [hout]
    have hnot : ¬ IsPalindrome x := fun h =>
      hxnL ((isPalindrome_iff_reverse_eq x).mp h)
    exact ite_eq_right hnot

end TM

-- ════════════════════════════════════════════════════════════════════════
-- DTIME / P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`palindromes ∈ DTIME(3n + 4)`**. -/
theorem palindromes_in_DTIME : Language.palindromes ∈ DTIME (fun n => 3 * n + 4) :=
  ⟨1, TM.palindromesTM, fun n => 3 * n + 4, TM.palindromesTM_decidesInTime, BigO.refl _⟩

/-- **`palindromes ∈ P`**. -/
theorem palindromes_mem_P : Language.palindromes ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ palindromes_in_DTIME⟩
  refine BigO.add ?_ (BigO.const_le_pow 4 1)
  exact BigO.const_mul_left 3 (by simpa using BigO.refl (fun n : ℕ => n))

end Complexity
