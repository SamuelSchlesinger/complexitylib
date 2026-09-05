/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BitCodec
public import Complexitylib.Models.TuringMachine.Subroutines.Scan

/-!
# Checking one tape window against its successor

⚠️ Unreviewed by Bolton

A configuration of the simulated machine is held in registers, one per field, and the machine
checks a *guessed* successor rather than computing one — on a nondeterministic machine that is
free, and checking is a scan.

This file is the part of that check concerning one tape window. The window is a marked block: one
chunk per cell, each chunk three bits, the head marker first so that a rightward scan knows
whether the head is on a cell before it reads that cell's symbol. The checks are

- the marker is on exactly one chunk,
- the symbols agree everywhere except under the marker, where the new window carries the written
  symbol — except at cell zero, where a write is a no-op,
- the new marker sits where the direction says.

Each is a fold over chunks, and `Complexity.Scanner.cellFold_chunk` turns it into the cell-level
fold a `Complexity.Scanner` runs.

## Main definitions

- `Complexity.markOf`, `Complexity.symOf` — the marker and symbol of a chunk
- `Complexity.markCount` — how many chunks carry the marker
- `Complexity.markStep`, `Complexity.agreeStep` — the marker-count and symbol folds
- `Complexity.stayStep`, `Complexity.rightStep`, `Complexity.leftStep` — one fold per direction
- `Complexity.dirStep`, `Complexity.movedMark` — the three folded into one, and where the marker
  must land
- `Complexity.HoldsWindow`, `Complexity.HoldsBits` — a register whose cells spell out an encoded
  window, or any bitstring
- `Complexity.inHeadStep`, `Complexity.inHeadEmit` — the input-head check, all three directions
- `Complexity.blockStep`, `Complexity.blockEmit` — the four checks run together
- `Complexity.SuccParams`, `Complexity.succParamsCodec` — what the check is handed, and its
  layout

## Main results

- `Complexity.markStep_run` — the count fold reports whether there are none, one, or more
- `Complexity.agreeStep_run`, `Complexity.agreeOk_iff` — what the symbol check reports
- `Complexity.stayStep_run`, `Complexity.rightStep_run`, `Complexity.leftStep_state` — what each
  displacement check reports
- `Complexity.dirEmit_run` — and what the combined displacement check reports, whichever way the
  head moves
- `Complexity.blockEmit_run` — and what all four together report on one block
- `Complexity.markOf_of_holds`, `Complexity.symOf_of_holds` — what a scan reads off an encoded
  window
- `Complexity.markCount_eq` — an encoded window carries exactly one marker
- `Complexity.eq_run_of_holds`, `Complexity.eq_run_state` — the comparison scan decides equality
  of what two registers hold, and so decides the state field
- `Complexity.valUpTo_of_holds` — what a scan reads a register as, as a number
- `Complexity.tableSlice_eq`, `Complexity.ofTable_of_holdsBits`, `Complexity.ofTable_of_holds` —
  and through a codec, as a value: whatever bits a register holds, and when they are an
  encoding
- `Complexity.plusOne_of_holds`, `Complexity.plusOne_of_holds_fin` — the increment scan decides
  the input-head field
- `Complexity.inHeadEmit_of_holds` — and the input-head check, whichever way the head moves
- `Complexity.moved_of_holds`, `Complexity.sym_of_holds` — the displacement and symbol
  conditions, read as statements about the decoded windows
- `Complexity.blockEmit_holds` — and the whole check: the scan accepts exactly when the new
  window is the old one stepped
- `Complexity.mem_codeSucc_iff` — a successor code is the code of one step
- `Complexity.succCode_state`, `Complexity.succCode_inputHead`, `Complexity.succCode_work_head`,
  `Complexity.succCode_work_cells`, `Complexity.succCode_output_head`,
  `Complexity.succCode_output_cells` — a successor's fields, one by one
- `Complexity.eq_succCode_iff` — and all of them at once: under the space bound a code is a
  successor exactly when every field is what the transition makes it
- `Complexity.params_eq` — the guessed parameters are pinned by the checks themselves
- `Complexity.eq_succCode_of_checks` — so the conditions the checks establish say exactly that
  one code is the successor of another
- `Complexity.mem_codeSucc_of_checks` — and hence that it is a successor at all
-/

@[expose] public section

namespace Complexity

variable {j : ℕ}

/-- The head marker of chunk `p` of the block starting after cell `off`, on register `r`. -/
def markOf (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (r : Fin (j + 1)) (p : ℕ) : Bool :=
  decide (cols (off + 3 * p + 1) r = Γ.one)

/-- The two symbol bits of chunk `p`, on register `r`. -/
def symOf (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (r : Fin (j + 1)) (p : ℕ) : Bool × Bool :=
  (decide (cols (off + 3 * p + 2) r = Γ.one), decide (cols (off + 3 * p + 3) r = Γ.one))

/-- How many of the first `m` chunks carry the marker. -/
def markCount (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (r : Fin (j + 1)) : ℕ → ℕ
  | 0 => 0
  | p + 1 => markCount cols off r p + (if markOf cols off r p then 1 else 0)

/-- Count the markers, saturating at two: the first component says there is at least one, the
second that there are at least two. -/
-- The last two columns are the chunk's symbol bits, which this check ignores; the arity is
-- fixed by `Complexity.Scanner.chunkRun`.
@[nolint unusedArguments]
def markStep (r : Fin (j + 1)) (x : Bool × Bool)
    (c1 _c2 _c3 : Fin (j + 1) → Γ) : Bool × Bool :=
  if c1 r = Γ.one then (true, x.1 || x.2) else x

/-- **What the marker count reports.** -/
theorem markStep_run (r : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ, Scanner.chunkRun (markStep r) cols off (false, false) m
      = (decide (0 < markCount cols off r m), decide (1 < markCount cols off r m)) := by
  intro m
  induction m with
  | zero => simp [Scanner.chunkRun, markCount]
  | succ m ih =>
      rw [Scanner.chunkRun, ih, markStep, markCount]
      by_cases h : cols (off + 3 * m + 1) r = Γ.one
      · have hm : markOf cols off r m = true := by simp [markOf, h]
        rw [ite_eq_left h, hm]
        refine Prod.ext ?_ ?_
        · simp
        · show (decide (0 < markCount cols off r m) || decide (1 < markCount cols off r m))
            = decide (1 < markCount cols off r m + 1)
          rcases Nat.eq_zero_or_pos (markCount cols off r m) with h0 | h0
          · simp [h0]
          · have h1 : 0 < markCount cols off r m := h0
            simp [h1]
      · have hm : markOf cols off r m = false := by simp [markOf, h]
        rw [ite_eq_right h, hm]
        simp

/-! ## The symbols -/

/-- What the new window should carry at chunk `p`. -/
def wantSym (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a : Fin (j + 1)) (wrB : Bool × Bool)
    (p : ℕ) : Bool × Bool :=
  if markOf cols off a p && decide (0 < p) then wrB else symOf cols off a p

/-- The symbol conditions on the first `m` chunks. -/
def agreeOk (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a b : Fin (j + 1))
    (symB wrB : Bool × Bool) : ℕ → Bool
  | 0 => true
  | p + 1 =>
    agreeOk cols off a b symB wrB p &&
      decide (symOf cols off b p = wantSym cols off a wrB p) &&
      (!markOf cols off a p || decide (symOf cols off a p = symB))

/-- The symbol-agreement fold. Its second component remembers that chunk zero has gone by, which
is what suppresses the write there. -/
def agreeStep (a b : Fin (j + 1)) (symB wrB : Bool × Bool) (x : Bool × Bool)
    (c1 c2 c3 : Fin (j + 1) → Γ) : Bool × Bool :=
  let mA := decide (c1 a = Γ.one)
  let bA := (decide (c2 a = Γ.one), decide (c3 a = Γ.one))
  let bB := (decide (c2 b = Γ.one), decide (c3 b = Γ.one))
  (x.1 && decide (bB = (if mA && x.2 then wrB else bA)) && (!mA || decide (bA = symB)), true)

/-- **What the symbol check reports.** -/
theorem agreeStep_run (a b : Fin (j + 1)) (symB wrB : Bool × Bool)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ, Scanner.chunkRun (agreeStep a b symB wrB) cols off (true, false) m
      = (agreeOk cols off a b symB wrB m, decide (0 < m)) := by
  intro m
  induction m with
  | zero => simp [Scanner.chunkRun, agreeOk]
  | succ m ih =>
      rw [Scanner.chunkRun, ih, agreeStep, agreeOk]
      refine Prod.ext ?_ (by simp)
      show (agreeOk cols off a b symB wrB m &&
          decide ((decide (cols (off + 3 * m + 2) b = Γ.one),
              decide (cols (off + 3 * m + 3) b = Γ.one))
            = (if decide (cols (off + 3 * m + 1) a = Γ.one) && decide (0 < m) then wrB
              else (decide (cols (off + 3 * m + 2) a = Γ.one),
                decide (cols (off + 3 * m + 3) a = Γ.one)))) &&
          (!decide (cols (off + 3 * m + 1) a = Γ.one) ||
            decide ((decide (cols (off + 3 * m + 2) a = Γ.one),
              decide (cols (off + 3 * m + 3) a = Γ.one)) = symB))) = _
      rfl

/-- The fold's verdict spelled out. -/
theorem agreeOk_iff (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a b : Fin (j + 1))
    (symB wrB : Bool × Bool) :
    ∀ m : ℕ, agreeOk cols off a b symB wrB m = true ↔
      ∀ p < m, symOf cols off b p = wantSym cols off a wrB p ∧
        (markOf cols off a p = true → symOf cols off a p = symB) := by
  intro m
  induction m with
  | zero => simp [agreeOk]
  | succ m ih =>
      rw [agreeOk]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
      rw [ih]
      constructor
      · rintro ⟨⟨hall, hsym⟩, hmark⟩ p hp
        rcases Nat.lt_or_ge p m with hlt | hge
        · exact hall p hlt
        · have hpm : p = m := by omega
          subst hpm
          refine ⟨hsym, fun hm => ?_⟩
          rcases hmark with h | h
          · rw [h] at hm; exact absurd hm (by simp)
          · exact h
      · intro hall
        refine ⟨⟨fun p hp => hall p (by omega), (hall m (by omega)).1⟩, ?_⟩
        by_cases hm : markOf cols off a m = true
        · exact Or.inr ((hall m (by omega)).2 hm)
        · exact Or.inl (by simpa using hm)

/-! ## Where the marker moves -/

/-- The head stays: the markers must agree. -/
-- The last two columns are the chunk's symbol bits, which this check ignores; the arity is
-- fixed by `Complexity.Scanner.chunkRun`.
@[nolint unusedArguments]
def stayStep (a b : Fin (j + 1)) (x : Bool) (c1 _c2 _c3 : Fin (j + 1) → Γ) : Bool :=
  x && (decide (c1 a = Γ.one) == decide (c1 b = Γ.one))

theorem stayStep_run (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ, Scanner.chunkRun (stayStep a b) cols off true m = true ↔
      ∀ p < m, markOf cols off a p = markOf cols off b p := by
  intro m
  induction m with
  | zero => simp [Scanner.chunkRun]
  | succ m ih =>
      rw [Scanner.chunkRun, stayStep, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hall, hlast⟩ p hp
        rcases Nat.lt_or_ge p m with h | h
        · exact hall p h
        · have hpm : p = m := by omega
          subst hpm
          simpa [markOf] using hlast
      · intro hall
        exact ⟨fun p hp => hall p (by omega), by simpa [markOf] using hall m (by omega)⟩

/-- The marker the rightward rule expects at chunk `p`. -/
def prevMark (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a : Fin (j + 1)) (p : ℕ) : Bool :=
  if p = 0 then false else markOf cols off a (p - 1)

/-- The head moves right: the new marker is one chunk on. -/
-- The last two columns are the chunk's symbol bits, which this check ignores; the arity is
-- fixed by `Complexity.Scanner.chunkRun`.
@[nolint unusedArguments]
def rightStep (a b : Fin (j + 1)) (x : Bool × Bool) (c1 _c2 _c3 : Fin (j + 1) → Γ) :
    Bool × Bool :=
  (x.1 && (decide (c1 b = Γ.one) == x.2), decide (c1 a = Γ.one))

theorem rightStep_run (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ,
      (Scanner.chunkRun (rightStep a b) cols off (true, false) m).2
          = (if m = 0 then false else markOf cols off a (m - 1)) ∧
        ((Scanner.chunkRun (rightStep a b) cols off (true, false) m).1 = true ↔
          ∀ p < m, markOf cols off b p = prevMark cols off a p) := by
  intro m
  induction m with
  | zero => simp [Scanner.chunkRun]
  | succ m ih =>
      obtain ⟨ih2, ih1⟩ := ih
      rw [Scanner.chunkRun, rightStep]
      refine ⟨by simp [markOf], ?_⟩
      show (_ && (decide (cols (off + 3 * m + 1) b = Γ.one) ==
        (Scanner.chunkRun (rightStep a b) cols off (true, false) m).2)) = true ↔ _
      rw [Bool.and_eq_true, ih1, ih2]
      constructor
      · rintro ⟨hall, hlast⟩ p hp
        rcases Nat.lt_or_ge p m with h | h
        · exact hall p h
        · have hpm : p = m := by omega
          rw [hpm, markOf, prevMark]
          exact beq_iff_eq.mp hlast
      · intro hall
        refine ⟨fun p hp => hall p (by omega), ?_⟩
        have hm := hall m (by omega)
        rw [markOf, prevMark] at hm
        exact beq_iff_eq.mpr hm

/-- The head moves left: the new marker is one chunk back, except from chunk zero, where moving
left stays put. The fold carries the previous chunk's new marker, whether chunk zero has gone by,
and whether the old marker was on chunk zero. -/
-- The last two columns are the chunk's symbol bits, which this check ignores; the arity is
-- fixed by `Complexity.Scanner.chunkRun`.
@[nolint unusedArguments]
def leftStep (a b : Fin (j + 1)) (x : Bool × Bool × Bool × Bool)
    (c1 _c2 _c3 : Fin (j + 1) → Γ) : Bool × Bool × Bool × Bool :=
  let mA := decide (c1 a = Γ.one)
  let mB := decide (c1 b = Γ.one)
  if x.2.2.1 then
    ((if x.2.2.2 then x.1 && !mB else x.1 && (x.2.1 == mA)), mB, true, x.2.2.2)
  else ((if mA then mB else true), mB, true, mA)

/-- **The state of the leftward-move check.** -/
theorem leftStep_state (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ, 0 < m →
      (Scanner.chunkRun (leftStep a b) cols off (true, false, false, false) m).2.2.1 = true ∧
      (Scanner.chunkRun (leftStep a b) cols off (true, false, false, false) m).2.2.2
        = markOf cols off a 0 ∧
      (Scanner.chunkRun (leftStep a b) cols off (true, false, false, false) m).2.1
        = markOf cols off b (m - 1) ∧
      ((Scanner.chunkRun (leftStep a b) cols off (true, false, false, false) m).1 = true ↔
        (if markOf cols off a 0 then
            markOf cols off b 0 = true ∧ ∀ p, 1 ≤ p → p < m → markOf cols off b p = false
          else ∀ p, 1 ≤ p → p < m → markOf cols off b (p - 1) = markOf cols off a p)) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro _
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        rw [Scanner.chunkRun, Scanner.chunkRun, leftStep]
        refine ⟨rfl, rfl, rfl, ?_⟩
        by_cases hA : markOf cols off a 0 = true
        · have hA' : cols (off + 3 * 0 + 1) a = Γ.one := by simpa [markOf] using hA
          rw [ite_eq_left hA]
          simp only [hA', ite_true, decide_true]
          constructor
          · intro h
            exact ⟨by simpa [markOf] using h, by omega⟩
          · rintro ⟨h, -⟩
            simpa [markOf] using h
        · have hA' : ¬ (cols (off + 3 * 0 + 1) a = Γ.one) := by simpa [markOf] using hA
          rw [ite_eq_right hA]
          simp only [hA', decide_false]
          exact ⟨fun _ p h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
      · obtain ⟨h1, h2, h3, h4⟩ := ih hm0
        rw [Scanner.chunkRun, leftStep]
        simp only [h1, ite_true, h2, h3]
        refine ⟨by simp, by simp, by simp [markOf], ?_⟩
        by_cases hA : markOf cols off a 0 = true
        · rw [ite_eq_left hA] at h4 ⊢
          rw [ite_eq_left hA]
          rw [Bool.and_eq_true, h4]
          constructor
          · rintro ⟨⟨hb0, hall⟩, hlast⟩
            refine ⟨hb0, fun p hp1 hp2 => ?_⟩
            rcases Nat.lt_or_ge p m with h | h
            · exact hall p hp1 h
            · have hpm : p = m := by omega
              rw [hpm, markOf]
              simpa using hlast
          · rintro ⟨hb0, hall⟩
            refine ⟨⟨hb0, fun p hp1 hp2 => hall p hp1 (by omega)⟩, ?_⟩
            have := hall m hm0 (by omega)
            rw [markOf] at this
            simp [this]
        · rw [ite_eq_right hA] at h4 ⊢
          rw [ite_eq_right hA, Bool.and_eq_true, h4]
          constructor
          · rintro ⟨hall, hlast⟩ p hp1 hp2
            rcases Nat.lt_or_ge p m with h | h
            · exact hall p hp1 h
            · have hpm : p = m := by omega
              rw [hpm, markOf, markOf]
              exact beq_iff_eq.mp hlast
          · intro hall
            refine ⟨fun p hp1 hp2 => hall p hp1 (by omega), ?_⟩
            have hmm := hall m hm0 (by omega)
            rw [markOf, markOf] at hmm
            exact beq_iff_eq.mpr hmm

/-! ## One displacement check, whichever way the head moves -/

/-- The displacement check for one block, in the direction the transition dictates. The three
directions need different amounts of memory; this gives them all the widest state. -/
def dirStep (a b : Fin (j + 1)) (d : Dir3) (x : Bool × Bool × Bool × Bool)
    (c1 c2 c3 : Fin (j + 1) → Γ) : Bool × Bool × Bool × Bool :=
  match d with
  | .stay => (stayStep a b x.1 c1 c2 c3, x.2)
  | .right =>
    let y := rightStep a b (x.1, x.2.1) c1 c2 c3
    (y.1, y.2, x.2.2)
  | .left => leftStep a b x c1 c2 c3

/-- The verdict of the displacement check. -/
def dirEmit (d : Dir3) (x : Bool × Bool × Bool × Bool) : Bool :=
  match d with
  | .stay => x.1
  | .right => x.1
  | .left => if x.2.2.2 then x.1 else x.1 && !x.2.1

theorem dirStep_stay (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ)
    (y : Bool × Bool × Bool) :
    ∀ m : ℕ, (Scanner.chunkRun (dirStep a b Dir3.stay) cols off (true, y) m).1
      = Scanner.chunkRun (stayStep a b) cols off true m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Scanner.chunkRun, Scanner.chunkRun, ← ih]
      rfl

theorem dirStep_right (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (z : Bool × Bool) :
    ∀ m : ℕ, ((Scanner.chunkRun (dirStep a b Dir3.right) cols off (true, false, z) m).1,
        (Scanner.chunkRun (dirStep a b Dir3.right) cols off (true, false, z) m).2.1)
      = Scanner.chunkRun (rightStep a b) cols off (true, false) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Scanner.chunkRun, Scanner.chunkRun, ← ih]
      rfl

theorem dirStep_left (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ, Scanner.chunkRun (dirStep a b Dir3.left) cols off (true, false, false, false) m
      = Scanner.chunkRun (leftStep a b) cols off (true, false, false, false) m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [Scanner.chunkRun, Scanner.chunkRun, ih]; rfl

/-- Where the marker must sit in the new block, given the direction. -/
def movedMark (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a : Fin (j + 1)) (d : Dir3) (p : ℕ) :
    Bool :=
  match d with
  | .stay => markOf cols off a p
  | .right => prevMark cols off a p
  | .left => if markOf cols off a 0 then decide (p = 0) else markOf cols off a (p + 1)

/-- **What the displacement check reports.** -/
theorem dirEmit_run (a b : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (d : Dir3)
    (m : ℕ) (hm : 0 < m) (hend : markOf cols off a m = false) :
    dirEmit d (Scanner.chunkRun (dirStep a b d) cols off (true, false, false, false) m) = true ↔
      ∀ p < m, markOf cols off b p = movedMark cols off a d p := by
  cases d with
  | stay =>
      show (Scanner.chunkRun (dirStep a b Dir3.stay) cols off (true, false, false, false) m).1
        = true ↔ _
      rw [dirStep_stay a b cols off (false, false, false) m, stayStep_run]
      exact ⟨fun h p hp => (h p hp).symm, fun h p hp => (h p hp).symm⟩
  | right =>
      show (Scanner.chunkRun (dirStep a b Dir3.right) cols off (true, false, false, false) m).1
        = true ↔ _
      have hproj := dirStep_right a b cols off (false, false) m
      have h1 : (Scanner.chunkRun (dirStep a b Dir3.right) cols off (true, false, false, false) m).1
          = (Scanner.chunkRun (rightStep a b) cols off (true, false) m).1 := by
        rw [← hproj]
      rw [h1]
      exact (rightStep_run a b cols off m).2
  | left =>
      set y := Scanner.chunkRun (dirStep a b Dir3.left) cols off (true, false, false, false) m
        with hy
      show (if y.2.2.2 then y.1 else y.1 && !y.2.1) = true ↔ _
      rw [hy]
      rw [dirStep_left a b cols off m]
      obtain ⟨-, h2, h3, h4⟩ := leftStep_state a b cols off m hm
      rw [h2, h3]
      by_cases hA : markOf cols off a 0 = true
      · rw [ite_eq_left hA, h4, ite_eq_left hA]
        simp only [movedMark, hA, ite_true]
        constructor
        · rintro ⟨hb0, hall⟩ p hp
          rcases Nat.eq_zero_or_pos p with h0 | h0
          · rw [h0, hb0]; simp
          · rw [hall p h0 hp]; simp; omega
        · intro hall
          refine ⟨by simpa using hall 0 hm, fun p h1 h2 => ?_⟩
          have := hall p h2
          rw [this]
          simp
          omega
      · rw [ite_eq_right hA, Bool.and_eq_true, h4, ite_eq_right hA]
        have hA' : markOf cols off a 0 = false := by simpa using hA
        simp only [movedMark, hA', Bool.not_eq_true', Bool.false_eq_true, ite_false]
        constructor
        · rintro ⟨hall, hlast⟩ p hp
          rcases Nat.lt_or_ge p (m - 1) with h | h
          · have := hall (p + 1) (by omega) (by omega)
            simpa using this
          · have hpm : p = m - 1 := by omega
            rw [hpm, hlast, show m - 1 + 1 = m by omega, hend]
        · intro hall
          refine ⟨fun p h1 h2 => ?_, ?_⟩
          · have := hall (p - 1) (by omega)
            rw [this, show p - 1 + 1 = p by omega]
          · have := hall (m - 1) (by omega)
            rw [this, show m - 1 + 1 = m by omega, hend]

/-! ## A register that holds an encoded window -/

/-- The cells of register `r`, from `off + 1` on, spell out the encoding of the window
`(hd, cl)`. -/
def HoldsWindow {m : ℕ} [NeZero m] (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (r : Fin (j + 1))
    (hd : Fin m) (cl : Fin m → Γ) : Prop :=
  ∀ q, (hq : q < m * 3) → cols (off + q + 1) r
    = Γ.ofBool (((tapeCodec m).enc (hd, cl))[q]'(by rw [(tapeCodec m).enc_length]; exact hq))

private theorem enc_getElem {m : ℕ} [NeZero m] (hd : Fin m) (cl : Fin m → Γ) (p : Fin m)
    (i : ℕ) (hi : i < 3) (hb : p.val * 3 + i < ((tapeCodec m).enc (hd, cl)).length) :
    ((tapeCodec m).enc (hd, cl))[p.val * 3 + i]'hb
      = ([decide (p = hd), (gammaBits (cl p)).1, (gammaBits (cl p)).2])[i]'(by simpa using hi) := by
  have hchunk := tapeCodec_enc_chunk hd cl p
  have hlt : i < (((tapeCodec m).enc (hd, cl)).drop (p.val * 3)).length := by
    rw [List.length_drop]
    rw [(tapeCodec m).enc_length] at hb ⊢
    omega
  have h1 : (((tapeCodec m).enc (hd, cl)).drop (p.val * 3))[i]'hlt
      = ((tapeCodec m).enc (hd, cl))[p.val * 3 + i]'hb := by
    rw [List.getElem_drop]
  have h2 : ((((tapeCodec m).enc (hd, cl)).drop (p.val * 3)).take 3)[i]'(by
      rw [List.length_take]; omega)
      = (((tapeCodec m).enc (hd, cl)).drop (p.val * 3))[i]'hlt := by
    rw [List.getElem_take]
  rw [← h1, ← h2]
  congr 1

/-- The marker a scan reads off an encoded window. -/
theorem markOf_of_holds {m : ℕ} [NeZero m] {cols : ℕ → Fin (j + 1) → Γ} {off : ℕ}
    {r : Fin (j + 1)} {hd : Fin m} {cl : Fin m → Γ} (h : HoldsWindow cols off r hd cl)
    (p : Fin m) : markOf cols off r p.val = decide (p = hd) := by
  have hb : p.val * 3 + 0 < m * 3 := by have := p.isLt; omega
  have hc := h (p.val * 3 + 0) hb
  rw [markOf, show off + 3 * p.val + 1 = off + (p.val * 3 + 0) + 1 by omega, hc,
    enc_getElem hd cl p 0 (by omega)]
  cases hdec : decide (p = hd) <;> simp [Γ.ofBool]

/-- The symbol bits a scan reads off an encoded window. -/
theorem symOf_of_holds {m : ℕ} [NeZero m] {cols : ℕ → Fin (j + 1) → Γ} {off : ℕ}
    {r : Fin (j + 1)} {hd : Fin m} {cl : Fin m → Γ} (h : HoldsWindow cols off r hd cl)
    (p : Fin m) : symOf cols off r p.val = gammaBits (cl p) := by
  have hb1 : p.val * 3 + 1 < m * 3 := by have := p.isLt; omega
  have hb2 : p.val * 3 + 2 < m * 3 := by have := p.isLt; omega
  have hc1 := h (p.val * 3 + 1) hb1
  have hc2 := h (p.val * 3 + 2) hb2
  rw [symOf, show off + 3 * p.val + 2 = off + (p.val * 3 + 1) + 1 by omega,
    show off + 3 * p.val + 3 = off + (p.val * 3 + 2) + 1 by omega, hc1, hc2,
    enc_getElem hd cl p 1 (by omega), enc_getElem hd cl p 2 (by omega)]
  refine Prod.ext ?_ ?_ <;>
    [cases (gammaBits (cl p)).1; cases (gammaBits (cl p)).2] <;>
    simp [Γ.ofBool]

theorem gammaBits_injective : Function.Injective gammaBits := by
  intro g g' h
  cases g <;> cases g' <;> simp_all [gammaBits]

/-- Counting the markers of a register that holds an encoded window. -/
theorem markCount_eq (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a : Fin (j + 1)) (hd : ℕ) :
    ∀ m : ℕ, (∀ p < m, markOf cols off a p = decide (p = hd)) →
      markCount cols off a m = if hd < m then 1 else 0 := by
  intro m
  induction m with
  | zero => intro _; simp [markCount]
  | succ m ih =>
      intro h
      rw [markCount, ih (fun p hp => h p (by omega)), h m (by omega)]
      by_cases hlt : hd < m
      · simp [hlt, show ¬ (m = hd) by omega, show hd < m + 1 by omega]
      · by_cases heq : hd = m
        · simp [heq]
        · simp [hlt, show ¬ (m = hd) by omega, show ¬ (hd < m + 1) by omega]

/-- Where the head lands. -/
def movedIdx (d : Dir3) (h : ℕ) : ℕ :=
  match d with
  | .stay => h
  | .right => h + 1
  | .left => h - 1

/-- **What the displacement condition says about the decoded heads.** -/
theorem moved_of_holds {m : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a b : Fin (j + 1))
    (hd hd' : ℕ) (hdm : hd < m) (hdm' : hd' < m) (d : Dir3)
    (ha : ∀ p < m, markOf cols off a p = decide (p = hd))
    (hb : ∀ p < m, markOf cols off b p = decide (p = hd'))
    (hend : markOf cols off a m = false) :
    (∀ p < m, markOf cols off b p = movedMark cols off a d p) ↔ hd' = movedIdx d hd := by
  have hmark : ∀ p, p ≤ m → markOf cols off a p = decide (p = hd) := by
    intro p hp
    rcases Nat.lt_or_ge p m with h | h
    · exact ha p h
    · have hpm : p = m := by omega
      rw [hpm, hend, eq_comm, decide_eq_false_iff_not]
      omega
  cases d with
  | stay =>
      simp only [movedMark, movedIdx]
      constructor
      · intro h
        have := h hd' hdm'
        rw [hb hd' hdm', ha hd' hdm'] at this
        simpa using this.symm
      · intro h p hp
        rw [hb p hp, ha p hp, h]
  | right =>
      simp only [movedMark, movedIdx, prevMark]
      constructor
      · intro h
        have hh := h hd' hdm'
        rw [hb hd' hdm'] at hh
        simp only [decide_true] at hh
        by_cases h0 : hd' = 0
        · rw [h0, ite_eq_left rfl] at hh
          exact absurd hh.symm (by simp)
        · rw [ite_eq_right h0, hmark (hd' - 1) (by omega)] at hh
          have : hd' - 1 = hd := by simpa using hh.symm
          omega
      · intro h p hp
        rw [hb p hp, h]
        by_cases h0 : p = 0
        · rw [h0, ite_eq_left rfl]
          simp
        · rw [ite_eq_right h0, hmark (p - 1) (by omega)]
          congr 1
          simp only [eq_iff_iff]
          omega
  | left =>
      simp only [movedMark, movedIdx]
      rw [ha 0 (by omega)]
      by_cases h0 : hd = 0
      · rw [h0]
        simp only [decide_true, ite_true]
        constructor
        · intro h
          have hh := h hd' hdm'
          rw [hb hd' hdm'] at hh
          simpa using hh.symm
        · intro h p hp
          rw [hb p hp, h]
      · rw [decide_eq_false (by omega : ¬ (0 = hd))]
        constructor
        · intro h
          have hh := h hd' hdm'
          rw [hb hd' hdm', hmark (hd' + 1) (by omega)] at hh
          simp only [decide_true] at hh
          have : hd' + 1 = hd := by simpa using hh.symm
          omega
        · intro h p hp
          rw [hb p hp, hmark (p + 1) (by omega)]
          congr 1
          simp only [eq_iff_iff]
          omega

/-- **What the symbol condition says about the decoded windows.** -/
theorem sym_of_holds {m : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (a b : Fin (j + 1))
    (hd : Fin m) (cl cl' : Fin m → Γ) (sym wr : Γ)
    (ha : ∀ p : Fin m, markOf cols off a p.val = decide (p = hd))
    (hsa : ∀ p : Fin m, symOf cols off a p.val = gammaBits (cl p))
    (hsb : ∀ p : Fin m, symOf cols off b p.val = gammaBits (cl' p)) :
    (∀ p < m, symOf cols off b p = wantSym cols off a (gammaBits wr) p ∧
        (markOf cols off a p = true → symOf cols off a p = gammaBits sym)) ↔
      ((∀ p : Fin m, cl' p = if p = hd ∧ 0 < p.val then wr else cl p) ∧ cl hd = sym) := by
  have key : ∀ p : Fin m,
      (symOf cols off b p.val = wantSym cols off a (gammaBits wr) p.val ↔
        cl' p = if p = hd ∧ 0 < p.val then wr else cl p) := by
    intro p
    rw [wantSym, ha p, hsa p, hsb p]
    have hiff : ((decide (p = hd) && decide (0 < p.val)) = true) ↔ (p = hd ∧ 0 < p.val) := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
    by_cases hc : p = hd ∧ 0 < p.val
    · rw [ite_eq_left hc, ite_eq_left (hiff.mpr hc)]
      exact ⟨fun h => gammaBits_injective h, fun h => by rw [h]⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mp h))]
      exact ⟨fun h => gammaBits_injective h, fun h => by rw [h]⟩
  constructor
  · intro h
    refine ⟨fun p => (key p).mp (h p.val p.isLt).1, ?_⟩
    have hmark : markOf cols off a hd.val = true := by rw [ha hd]; simp
    have := (h hd.val hd.isLt).2 hmark
    rw [hsa hd] at this
    exact gammaBits_injective this
  · rintro ⟨h1, h2⟩ p hp
    refine ⟨(key ⟨p, hp⟩).mpr (h1 ⟨p, hp⟩), fun hm => ?_⟩
    rw [ha ⟨p, hp⟩] at hm
    have hpd : (⟨p, hp⟩ : Fin m) = hd := by simpa using hm
    rw [hsa ⟨p, hp⟩, hpd, h2]

/-! ## Registers that hold a bitstring -/

/-- The cells of register `r`, from `off + 1` on, spell out `bits`. -/
def HoldsBits (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (r : Fin (j + 1))
    (bits : List Bool) : Prop :=
  ∀ q, (hq : q < bits.length) → cols (off + q + 1) r = Γ.ofBool (bits[q]'hq)

theorem ofBool_injective : Function.Injective Γ.ofBool := by
  intro b b' h
  cases b <;> cases b' <;> simp_all [Γ.ofBool]

/-- A register determines the bits it holds. -/
theorem HoldsBits.inj {cols : ℕ → Fin (j + 1) → Γ} {off : ℕ} {r : Fin (j + 1)}
    {b₁ b₂ : List Bool} (h₁ : HoldsBits cols off r b₁) (h₂ : HoldsBits cols off r b₂)
    (hlen : b₁.length = b₂.length) : b₁ = b₂ := by
  refine List.ext_getElem hlen ?_
  intro i hi₁ hi₂
  have hc₁ := h₁ i hi₁
  have hc₂ := h₂ i hi₂
  exact ofBool_injective (hc₁.symm.trans hc₂)

/-- A list is a prefix of the enumeration of a stream that agrees with it. -/
theorem isPrefix_ofFn {L : List Bool} {n : ℕ} (b : ℕ → Bool) (hlen : L.length ≤ n)
    (hb : ∀ q, (hq : q < L.length) → b q = L[q]) :
    L <+: List.ofFn (fun q : Fin n => b q.val) := by
  have htake : (List.ofFn (fun q : Fin n => b q.val)).take L.length = L := by
    refine List.ext_getElem (by simp; omega) ?_
    intro q h1 h2
    rw [List.getElem_take, List.getElem_ofFn]
    exact hb q h2
  exact ⟨_, by rw [← htake]; exact List.take_append_drop _ _⟩

/-- Holding a list of bits means holding any prefix of it: a register guessed one bit wider than
a field still holds the field. -/
theorem HoldsBits.of_isPrefix {cols : ℕ → Fin (j + 1) → Γ} {off : ℕ} {r : Fin (j + 1)}
    {L L' : List Bool} (h : HoldsBits cols off r L) (hp : L' <+: L) :
    HoldsBits cols off r L' := by
  intro q hq
  obtain ⟨s, rfl⟩ := hp
  rw [h q (by rw [List.length_append]; omega), List.getElem_append_left hq]

/-- Holding a list means holding what follows a prefix of it, read from after that prefix. A
register whose field sits after a block of padding is read this way: the scan that checks the
field starts where the padding ends. -/
theorem HoldsBits.drop_prefix {cols : ℕ → Fin (j + 1) → Γ} {r : Fin (j + 1)}
    {L M : List Bool} (h : HoldsBits cols 0 r (L ++ M)) : HoldsBits cols L.length r M := by
  intro q hq
  have hlt : L.length + q < (L ++ M).length := by rw [List.length_append]; omega
  have := h (L.length + q) hlt
  rw [Nat.zero_add] at this
  have hidx : L.length + q - L.length = q := by omega
  rw [this, List.getElem_append_right (by omega)]
  simp only [hidx]

/-- Reading a register from an offset, as a scan that starts there. -/
theorem HoldsBits.shift {cols : ℕ → Fin (j + 1) → Γ} {off : ℕ} {r : Fin (j + 1)}
    {L : List Bool} (h : HoldsBits cols off r L) :
    HoldsBits (fun t => cols (off + t)) 0 r L := by
  intro q hq
  show cols (off + (0 + q + 1)) r = _
  rw [show off + (0 + q + 1) = off + q + 1 by omega]
  exact h q hq

/-- **The comparison scan decides equality of what two registers hold.** -/
theorem eq_run_of_holds (cols : ℕ → Fin (j + 1) → Γ) (r r' : Fin (j + 1))
    (bits bits' : List Bool) (hlen : bits.length = bits'.length)
    (h : HoldsBits cols 0 r bits) (h' : HoldsBits cols 0 r' bits') :
    (Scanner.eq j r r').run cols bits.length = true ↔ bits = bits' := by
  rw [Scanner.eq_run]
  constructor
  · intro hall
    refine List.ext_getElem hlen ?_
    intro i h1 h2
    have hc := hall (i + 1) (by omega) (by omega)
    rw [show (i + 1) = 0 + i + 1 by omega, h i h1, h' i h2] at hc
    exact ofBool_injective hc
  · rintro rfl q h1 h2
    obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
    rw [show (i + 1) = 0 + i + 1 by omega, h i (by omega), h' i (by omega)]

/-- **The state check.** Two registers holding encoded states agree exactly when the states do. -/
theorem eq_run_state {Q : Type} [Fintype Q] [Nonempty Q] (cols : ℕ → Fin (j + 1) → Γ)
    (r r' : Fin (j + 1)) (q q' : Q)
    (h : HoldsBits cols 0 r ((qCodec Q).enc q)) (h' : HoldsBits cols 0 r' ((qCodec Q).enc q')) :
    (Scanner.eq j r r').run cols (qCodec Q).width = true ↔ q = q' := by
  have hlen : ((qCodec Q).enc q).length = ((qCodec Q).enc q').length := by
    rw [(qCodec Q).enc_length, (qCodec Q).enc_length]
  rw [show (qCodec Q).width = ((qCodec Q).enc q).length from ((qCodec Q).enc_length q).symm,
    eq_run_of_holds cols r r' _ _ hlen h h']
  exact ⟨fun hb => (qCodec Q).enc_injective hb, fun hq => by rw [hq]⟩

/-! ## Reading a register as a number

`Complexity.Scanner.plusOne` speaks in `Complexity.Scanner.valUpTo`, the value of the bits a scan
has passed; `Complexity.finCodec` stores a number as `Complexity.bitsOfLenLE`, whose value is
`Complexity.binValLE`. Both are little-endian, so they agree. -/

theorem binValLE_concat (l : List Bool) (b : Bool) :
    binValLE (l ++ [b]) = binValLE l + (if b then 2 ^ l.length else 0) := by
  induction l with
  | nil => cases b <;> simp [binValLE]
  | cons c l ih =>
      have hp : (2 : ℕ) ^ (l.length + 1) = 2 * 2 ^ l.length := by rw [pow_succ]; ring
      simp only [List.cons_append, binValLE, ih, List.length_cons, hp]
      cases c <;> cases b <;> simp <;> omega

/-- **What a scan reads a register as.** -/
theorem valUpTo_of_holds (cols : ℕ → Fin (j + 1) → Γ) (r : Fin (j + 1)) (bits : List Bool)
    (h : HoldsBits cols 0 r bits) :
    ∀ p, p ≤ bits.length →
      Scanner.valUpTo (Scanner.bitAt cols r) p = binValLE (bits.take p) := by
  intro p
  induction p with
  | zero => intro _; simp [Scanner.valUpTo, binValLE]
  | succ p ih =>
      intro hp
      have hple : p < bits.length := by omega
      rw [Scanner.valUpTo, ih (by omega)]
      have hbit : Scanner.bitAt cols r (p + 1) = bits[p]'hple := by
        rw [Scanner.bitAt, show p + 1 = 0 + p + 1 by omega, h p hple]
        cases bits[p]'hple <;> simp [Γ.ofBool]
      have hsplit : bits.take (p + 1) = bits.take p ++ [bits[p]'hple] := by
        rw [List.take_add_one]
        simp [List.getElem?_eq_getElem hple]
      rw [hbit, hsplit, binValLE_concat, List.length_take, min_eq_left (by omega)]

/-- **The increment check decides the input-head condition.** -/
theorem plusOne_of_holds (cols : ℕ → Fin (j + 1) → Γ) (r r' : Fin (j + 1)) (w u v : ℕ)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (h : HoldsBits cols 0 r (bitsOfLenLE w u)) (h' : HoldsBits cols 0 r' (bitsOfLenLE w v)) :
    (Scanner.plusOne j r r').emit ((Scanner.plusOne j r r').run cols w) = true ↔ v = u + 1 := by
  have hlen : (bitsOfLenLE w u).length = w := bitsOfLenLE_length w u
  have hlen' : (bitsOfLenLE w v).length = w := bitsOfLenLE_length w v
  rw [Scanner.plusOne_run, valUpTo_of_holds cols r _ h w (by omega),
    valUpTo_of_holds cols r' _ h' w (by omega),
    List.take_of_length_le (le_of_eq hlen), List.take_of_length_le (le_of_eq hlen'),
    binValLE_bitsOfLenLE w u hu, binValLE_bitsOfLenLE w v hv]

/-- The same, for registers holding a bounded index. -/
theorem plusOne_of_holds_fin {m : ℕ} [NeZero m] (cols : ℕ → Fin (j + 1) → Γ)
    (r r' : Fin (j + 1)) (u v : Fin m)
    (h : HoldsBits cols 0 r ((finCodec m).enc u)) (h' : HoldsBits cols 0 r' ((finCodec m).enc v)) :
    (Scanner.plusOne j r r').emit ((Scanner.plusOne j r r').run cols (bitWidth m)) = true ↔
      v.val = u.val + 1 :=
  plusOne_of_holds cols r r' (bitWidth m) u.val v.val
    (lt_of_lt_of_le u.isLt (le_two_pow_bitWidth m))
    (lt_of_lt_of_le v.isLt (le_two_pow_bitWidth m)) h h'

/-! ## Reading a value off a register with a scan -/

/-- The leading `c` bits a scan has read from one register. -/
def tableSlice {s w : ℕ} (table : Fin s → Fin w → Bool) (t : Fin s) (c : ℕ) (hc : c ≤ w) :
    Fin c → Bool := fun i => table t ⟨i.val, lt_of_lt_of_le i.isLt hc⟩

/-- **What a scan has in its table**: the bits the register holds. -/
theorem tableSlice_eq (bits : List Bool) (c : ℕ) (hlen : bits.length = c)
    (cols : ℕ → Fin (j + 1) → Γ) (off s w : ℕ) (regs : Fin s → Fin (j + 1)) (t : Fin s)
    (hc : c ≤ w) (x₀ : Fin s → Fin w → Bool)
    (h : HoldsBits (fun q => cols (off + q)) 0 (regs t) bits) (i : Fin c) :
    tableSlice (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs)
        (fun q => cols (off + q)) w).2 t c hc i
      = bits[i.val]'(by rw [hlen]; exact i.isLt) := by
  have hread := (Scanner.bitsStep_run s w regs (fun q => cols (off + q)) x₀ w le_rfl).2 t
    ⟨i.val, lt_of_lt_of_le i.isLt hc⟩ (lt_of_lt_of_le i.isLt hc)
  have hh := h i.val (by rw [hlen]; exact i.isLt)
  simp only [Nat.zero_add] at hh
  rw [tableSlice, hread, Scanner.bitAt]
  simp only [hh]
  cases bits[i.val]'(by rw [hlen]; exact i.isLt) <;> simp [Γ.ofBool]

/-- **What a scan reads a register as, through a codec**, whatever bits it holds. -/
theorem ofTable_of_holdsBits {α : Type} (codec : BitCodec α) (bits : List Bool)
    (hlen : bits.length = codec.width) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (s w : ℕ)
    (regs : Fin s → Fin (j + 1)) (t : Fin s) (hc : codec.width ≤ w)
    (x₀ : Fin s → Fin w → Bool)
    (h : HoldsBits (fun q => cols (off + q)) 0 (regs t) bits) :
    codec.ofTable (tableSlice
        (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs)
          (fun q => cols (off + q)) w).2 t codec.width hc) = codec.dec bits := by
  rw [BitCodec.ofTable]
  congr 1
  refine List.ext_getElem (by simp [hlen]) ?_
  intro i h1 h2
  have hi : i < codec.width := by simpa using h1
  rw [List.getElem_ofFn]
  exact tableSlice_eq bits codec.width hlen cols off s w regs t hc x₀ h ⟨i, hi⟩

/-- The same, when the register holds an encoding. -/
theorem ofTable_of_holds {α : Type} (codec : BitCodec α) (val : α)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (s w : ℕ) (regs : Fin s → Fin (j + 1)) (t : Fin s)
    (hc : codec.width ≤ w) (x₀ : Fin s → Fin w → Bool)
    (h : HoldsBits (fun q => cols (off + q)) 0 (regs t) (codec.enc val)) :
    codec.ofTable (tableSlice
        (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs)
          (fun q => cols (off + q)) w).2 t codec.width hc) = val := by
  rw [ofTable_of_holdsBits codec (codec.enc val) (codec.enc_length val) cols off s w regs t hc
    x₀ h, codec.dec_enc]

/-- The same, for a scan that starts at the first cell. -/
theorem ofTable_of_holds_zero {α : Type} (codec : BitCodec α) (val : α)
    (cols : ℕ → Fin (j + 1) → Γ) (s w : ℕ) (regs : Fin s → Fin (j + 1)) (t : Fin s)
    (hc : codec.width ≤ w) (x₀ : Fin s → Fin w → Bool)
    (h : HoldsBits cols 0 (regs t) (codec.enc val)) :
    codec.ofTable (tableSlice
        (Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs) cols w).2
        t codec.width hc) = val := by
  have hshift : (fun q => cols (0 + q)) = cols := by
    funext q
    rw [Nat.zero_add]
  have hgen := ofTable_of_holds codec val cols 0 s w regs t hc x₀ (by rw [hshift]; exact h)
  rwa [hshift] at hgen

/-! ## The input head, whichever way it moves -/

/-- The input-head check, in the direction the transition dictates. The three directions share a
common state: `stay` compares, `right` checks an increment, and `left` checks one with the
registers swapped, since `v = u - 1` with `u > 0` is `u = v + 1`. -/
def inHeadStep (r r' : Fin (j + 1)) (d : Dir3) (x : Bool × Bool) (col : Fin (j + 1) → Γ) :
    Bool × Bool :=
  match d with
  | .stay => ((Scanner.eq j r r').stepR x.1 col, x.2)
  | .right => (Scanner.plusOne j r r').stepR x col
  | .left => (Scanner.plusOne j r' r).stepR x col

/-- The verdict of the input-head check. -/
def inHeadEmit (d : Dir3) (x : Bool × Bool) : Bool :=
  match d with
  | .stay => x.1
  | .right => !x.1 && x.2
  | .left => !x.1 && x.2

theorem inHeadStep_right_eq (r r' : Fin (j + 1)) :
    inHeadStep r r' Dir3.right = (Scanner.plusOne j r r').stepR := rfl

theorem inHeadStep_left_eq (r r' : Fin (j + 1)) :
    inHeadStep r r' Dir3.left = (Scanner.plusOne j r' r).stepR := rfl

theorem inHeadStep_stay_fst (r r' : Fin (j + 1)) (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ)
    (y : Bool) :
    ∀ p : ℕ, (Scanner.cellFold (inHeadStep r r' Dir3.stay) cols off (true, y) p).1
      = Scanner.cellFold (Scanner.eq j r r').stepR cols off true p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
      simp only [Scanner.cellFold]
      rw [← ih]
      rfl

theorem bitsOfLenLE_inj {w u v : ℕ} (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (h : bitsOfLenLE w u = bitsOfLenLE w v) : u = v := by
  rw [← binValLE_bitsOfLenLE w u hu, ← binValLE_bitsOfLenLE w v hv, h]

/-- **What the input-head check reports.** -/
theorem inHeadEmit_of_holds (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (r r' : Fin (j + 1))
    (d : Dir3) (w u v : ℕ) (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (h : HoldsBits (fun t => cols (off + t)) 0 r (bitsOfLenLE w u))
    (h' : HoldsBits (fun t => cols (off + t)) 0 r' (bitsOfLenLE w v))
    (hleft : d = Dir3.left → 0 < u) :
    inHeadEmit d (Scanner.cellFold (inHeadStep r r' d) cols off (true, true) w) = true ↔
      v = movedIdx d u := by
  have hlu : (bitsOfLenLE w u).length = w := bitsOfLenLE_length w u
  have hlv : (bitsOfLenLE w v).length = w := bitsOfLenLE_length w v
  cases d with
  | stay =>
      have hcf : (Scanner.eq j r r').runR (fun t => cols (off + t)) w
          = Scanner.cellFold (Scanner.eq j r r').stepR (fun t => cols (off + t)) 0 true w :=
        Scanner.runR_eq_cellFold (Scanner.eq j r r') _ w
      have hrun : (Scanner.eq j r r').run (fun t => cols (off + t)) w
          = (Scanner.eq j r r').runR (fun t => cols (off + t)) w := by
        erw [Scanner.run, Scanner.eq_runL]
      show (Scanner.cellFold (inHeadStep r r' Dir3.stay) cols off (true, true) w).1 = true ↔ _
      erw [inHeadStep_stay_fst, Scanner.cellFold_shift, ← hcf, ← hrun,
        show w = (bitsOfLenLE w u).length from hlu.symm]
      refine Iff.trans (eq_run_of_holds (fun t => cols (off + t)) r r' _ _ (by rw [hlu, hlv]) h h')
        ?_
      refine ⟨fun hb => (bitsOfLenLE_inj hu hv hb).symm, fun hb => ?_⟩
      rw [show movedIdx Dir3.stay u = u from rfl] at hb
      rw [hb]
  | right =>
      have hcf : (Scanner.plusOne j r r').runR (fun t => cols (off + t)) w
          = Scanner.cellFold (Scanner.plusOne j r r').stepR (fun t => cols (off + t)) 0
            (true, true) w := Scanner.runR_eq_cellFold (Scanner.plusOne j r r') _ w
      have hrun : (Scanner.plusOne j r r').run (fun t => cols (off + t)) w
          = (Scanner.plusOne j r r').runR (fun t => cols (off + t)) w := by
        rw [Scanner.run]
        exact Scanner.ofRight_runL (Bool × Bool) _ _ _ _ w _
      show (Scanner.plusOne j r r').emit
        (Scanner.cellFold (inHeadStep r r' Dir3.right) cols off (true, true) w) = true ↔ _
      erw [inHeadStep_right_eq, Scanner.cellFold_shift, ← hcf, ← hrun,
        plusOne_of_holds (fun t => cols (off + t)) r r' w u v hu hv h h']
      rfl
  | left =>
      have hpos := hleft rfl
      have hcf : (Scanner.plusOne j r' r).runR (fun t => cols (off + t)) w
          = Scanner.cellFold (Scanner.plusOne j r' r).stepR (fun t => cols (off + t)) 0
            (true, true) w := Scanner.runR_eq_cellFold (Scanner.plusOne j r' r) _ w
      have hrun : (Scanner.plusOne j r' r).run (fun t => cols (off + t)) w
          = (Scanner.plusOne j r' r).runR (fun t => cols (off + t)) w := by
        rw [Scanner.run]
        exact Scanner.ofRight_runL (Bool × Bool) _ _ _ _ w _
      show (Scanner.plusOne j r' r).emit
        (Scanner.cellFold (inHeadStep r r' Dir3.left) cols off (true, true) w) = true ↔ _
      erw [inHeadStep_left_eq, Scanner.cellFold_shift, ← hcf, ← hrun,
        plusOne_of_holds (fun t => cols (off + t)) r' r w v u hv hu h' h]
      show u = v + 1 ↔ v = movedIdx Dir3.left u
      show u = v + 1 ↔ v = u - 1
      omega

/-! ## The whole check on one block -/

/-- The four checks on one block, run together: the marker counts on each register, the symbols,
and the displacement. -/
def blockStep (a b : Fin (j + 1)) (symB wrB : Bool × Bool) (d : Dir3)
    (x : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool × Bool × Bool))
    (c1 c2 c3 : Fin (j + 1) → Γ) :
    (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool × Bool × Bool) :=
  (markStep a x.1 c1 c2 c3, markStep b x.2.1 c1 c2 c3,
    agreeStep a b symB wrB x.2.2.1 c1 c2 c3, dirStep a b d x.2.2.2 c1 c2 c3)

/-- Where the combined check starts. -/
def blockStart : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool × Bool × Bool) :=
  ((false, false), (false, false), (true, false), (true, false, false, false))

/-- The combined verdict: one marker on each register, the symbols right, the head moved right. -/
def blockEmit (d : Dir3)
    (x : (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × (Bool × Bool × Bool × Bool)) : Bool :=
  (x.1.1 && !x.1.2) && (x.2.1.1 && !x.2.1.2) && x.2.2.1.1 && dirEmit d x.2.2.2

theorem blockStep_run (a b : Fin (j + 1)) (symB wrB : Bool × Bool) (d : Dir3)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) :
    ∀ m : ℕ, Scanner.chunkRun (blockStep a b symB wrB d) cols off blockStart m
      = (Scanner.chunkRun (markStep a) cols off (false, false) m,
        Scanner.chunkRun (markStep b) cols off (false, false) m,
        Scanner.chunkRun (agreeStep a b symB wrB) cols off (true, false) m,
        Scanner.chunkRun (dirStep a b d) cols off (true, false, false, false) m) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Scanner.chunkRun, ih, Scanner.chunkRun, Scanner.chunkRun, Scanner.chunkRun,
        Scanner.chunkRun]
      rfl

/-- **What the whole block check reports.** -/
theorem blockEmit_run (a b : Fin (j + 1)) (symB wrB : Bool × Bool) (d : Dir3)
    (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ) (m : ℕ) (hm : 0 < m)
    (hend : markOf cols off a m = false) :
    blockEmit d (Scanner.chunkRun (blockStep a b symB wrB d) cols off blockStart m) = true ↔
      markCount cols off a m = 1 ∧ markCount cols off b m = 1 ∧
        (∀ p < m, symOf cols off b p = wantSym cols off a wrB p ∧
          (markOf cols off a p = true → symOf cols off a p = symB)) ∧
        (∀ p < m, markOf cols off b p = movedMark cols off a d p) := by
  rw [blockEmit, blockStep_run]
  simp only [markStep_run, agreeStep_run]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    agreeOk_iff, dirEmit_run a b cols off d m hm hend]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩
    exact ⟨by omega, by omega, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h3⟩, h4⟩

/-- **The block check, as a statement about decoded windows.** The scan accepts exactly when the
new window is the old one stepped: the symbol under the head is the one the transition was
computed from, the cells are unchanged except under the head, where the written symbol appears —
save at cell zero, where a write is a no-op — and the head has moved as the direction says. -/
theorem blockEmit_holds {m : ℕ} [NeZero m] (cols : ℕ → Fin (j + 1) → Γ) (off : ℕ)
    (a b : Fin (j + 1)) (hd hd' : Fin m) (cl cl' : Fin m → Γ)
    (ha : HoldsWindow cols off a hd cl) (hb : HoldsWindow cols off b hd' cl')
    (sym wr : Γ) (d : Dir3) (hm : 0 < m) (hend : markOf cols off a m = false) :
    blockEmit d (Scanner.chunkRun (blockStep a b (gammaBits sym) (gammaBits wr) d) cols off
        blockStart m) = true ↔
      (cl hd = sym ∧ (∀ p : Fin m, cl' p = if p = hd ∧ 0 < p.val then wr else cl p) ∧
        hd'.val = movedIdx d hd.val) := by
  have hA : ∀ p < m, markOf cols off a p = decide (p = hd.val) := by
    intro p hp
    rw [markOf_of_holds ha ⟨p, hp⟩]
    simp [Fin.ext_iff]
  have hB : ∀ p < m, markOf cols off b p = decide (p = hd'.val) := by
    intro p hp
    rw [markOf_of_holds hb ⟨p, hp⟩]
    simp [Fin.ext_iff]
  rw [blockEmit_run a b (gammaBits sym) (gammaBits wr) d cols off m hm hend,
    markCount_eq cols off a hd.val m hA, markCount_eq cols off b hd'.val m hB,
    ite_eq_left hd.isLt, ite_eq_left hd'.isLt,
    sym_of_holds cols off a b hd cl cl' sym wr (markOf_of_holds ha) (symOf_of_holds ha)
      (symOf_of_holds hb),
    moved_of_holds cols off a b hd.val hd'.val hd.isLt hd'.isLt d hA hB hend]
  constructor
  · rintro ⟨-, -, ⟨h1, h2⟩, h3⟩
    exact ⟨h2, h1, h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨rfl, rfl, ⟨h1, h2⟩, h3⟩

/-! ## The parameters a successor check is handed

The check does not guess what the simulated machine *does* — it guesses only what the machine
*sees*, and computes the transition itself. The state is verified against the old code's state
field, and each head symbol by the block check's own `symOk` conjunct, so nothing here is taken on
trust. -/

/-- What the simulated machine sees at one step: its choice bit, its state, and the symbol under
each of its heads. -/
structure SuccParams (Q : Type) (k : ℕ) where
  /-- The nondeterministic choice. -/
  beta : Bool
  /-- The state. -/
  q : Q
  /-- The symbol under the input head. -/
  inSym : Γ
  /-- The symbol under each work head. -/
  wSym : Fin k → Γ
  /-- The symbol under the output head. -/
  oSym : Γ

/-- `SuccParams` is a plain record, so it lays out as a product. The symbol under the input head
comes **first**: it is the one field a machine checks against its own input tape rather than by
scanning, and `TM.inMatchTM` reads the two cells at the start of the register. -/
def succParamsEquiv (Q : Type) (k : ℕ) :
    SuccParams Q k ≃ Γ × Bool × Q × (Fin k → Γ) × Γ where
  toFun p := (p.inSym, p.beta, p.q, p.wSym, p.oSym)
  invFun t := ⟨t.2.1, t.2.2.1, t.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The layout of a parameter block. -/
noncomputable def succParamsCodec (Q : Type) [Fintype Q] [Nonempty Q] (k : ℕ) :
    BitCodec (SuccParams Q k) :=
  BitCodec.equiv (succParamsEquiv Q k)
    (BitCodec.gamma.prod (BitCodec.bool.prod ((qCodec Q).prod
      ((BitCodec.fn k BitCodec.gamma).prod BitCodec.gamma))))

theorem succParamsCodec_width (Q : Type) [Fintype Q] [Nonempty Q] (k : ℕ) :
    (succParamsCodec Q k).width = 2 + (1 + (bitWidth (Fintype.card Q) + (k * 2 + 2))) := rfl

/-- What the simulated machine does, given what it sees. -/
def succTrans {k : ℕ} (tm : NTM k) (p : SuccParams tm.Q k) :
    tm.Q × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 :=
  tm.δ p.beta p.q p.inSym p.wSym p.oSym

/-- The symbol the simulated machine writes on work tape `i`. -/
def succWrite {k : ℕ} (tm : NTM k) (p : SuccParams tm.Q k) (i : Fin k) : Γ :=
  ((succTrans tm p).2.1 i).toΓ

/-- Which way work head `i` moves. -/
def succDir {k : ℕ} (tm : NTM k) (p : SuccParams tm.Q k) (i : Fin k) : Dir3 :=
  (succTrans tm p).2.2.2.2.1 i

/-- The state the simulated machine moves to. -/
def succState {k : ℕ} (tm : NTM k) (p : SuccParams tm.Q k) : tm.Q :=
  (succTrans tm p).1

/-! ## What the successor relation on codes says

`Complexity.NTM.codeSucc` is `cfgCode ∘ stepCfg ∘ decodeCfg`. Decoding reads the transition's
inputs straight off the code's fields, so a successor is determined by the code and the choice
bit — which is what lets the check guess only what the machine sees. -/

section Codes

variable {k : ℕ} (tm : NTM k) (x : List Bool) (S : ℕ)

/-- The symbol under the simulated input head. -/
def inSymOf (a : Code tm.Q k x.length S) : Γ :=
  (Tape.init (x.map Γ.ofBool)).cells a.2.1.val

/-- The symbol under simulated work head `i`. -/
def wSymOf (a : Code tm.Q k x.length S) (i : Fin k) : Γ :=
  (a.2.2.1 i).2 (a.2.2.1 i).1

/-- The symbol under the simulated output head. -/
def oSymOf (a : Code tm.Q k x.length S) : Γ :=
  a.2.2.2.2 a.2.2.2.1

/-- What the simulated machine sees, read off a code. -/
def paramsOf (a : Code tm.Q k x.length S) (β : Bool) : SuccParams tm.Q k :=
  { beta := β, q := a.1, inSym := inSymOf tm x S a, wSym := wSymOf tm x S a,
    oSym := oSymOf tm x S a }

@[simp] theorem decodeCfg_state (a : Code tm.Q k x.length S) :
    (decodeCfg x S a).state = a.1 := rfl

theorem decodeCfg_input_read (a : Code tm.Q k x.length S) :
    (decodeCfg x S a).input.read = inSymOf tm x S a := rfl

theorem decodeCfg_work_read (a : Code tm.Q k x.length S) (i : Fin k) :
    ((decodeCfg x S a).work i).read = wSymOf tm x S a i := by
  show (if h : (a.2.2.1 i).1.val < S + 1 then (a.2.2.1 i).2 ⟨_, h⟩ else Γ.blank) = _
  rw [dite_eq_left (a.2.2.1 i).1.isLt]
  rfl

theorem decodeCfg_output_read (a : Code tm.Q k x.length S) :
    (decodeCfg x S a).output.read = oSymOf tm x S a := by
  show (if h : a.2.2.2.1.val < S + 2 then a.2.2.2.2 ⟨_, h⟩ else Γ.blank) = _
  rw [dite_eq_left a.2.2.2.1.isLt]
  rfl

/-- The transition a code and a choice bit determine. -/
theorem stepCfg_decodeCfg_delta (a : Code tm.Q k x.length S) (β : Bool) :
    tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
        (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read
      = succTrans tm (paramsOf tm x S a β) := by
  rw [succTrans, decodeCfg_input_read, decodeCfg_output_read]
  congr 1
  funext i
  exact decodeCfg_work_read tm x S a i

/-- The successor of a code under one choice. -/
def succCode (β : Bool) (a : Code tm.Q k x.length S) : Code tm.Q k x.length S :=
  cfgCode x.length S (tm.stepCfg β (decodeCfg x S a))

/-- **Membership in `codeSucc`, unpacked.** -/
theorem mem_codeSucc_iff (a a' : Code tm.Q k x.length S) :
    a' ∈ NTM.codeSucc tm x S a ↔ a.1 ≠ tm.qhalt ∧ ∃ β : Bool, a' = succCode tm x S β a := by
  rw [NTM.codeSucc, decodeCfg_state]
  by_cases h : a.1 = tm.qhalt
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp only [Finset.mem_insert, Finset.mem_singleton, h, ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro (h1 | h1)
      · exact ⟨false, h1⟩
      · exact ⟨true, h1⟩
    · rintro ⟨β, hβ⟩
      cases β
      · exact Or.inl hβ
      · exact Or.inr hβ

theorem head_move (t : Tape) (d : Dir3) : (t.move d).head = movedIdx d t.head := by
  cases d <;> rfl

/-- The state of a successor. -/
theorem succCode_state (a : Code tm.Q k x.length S) (β : Bool) :
    (succCode tm x S β a).1 = succState tm (paramsOf tm x S a β) := by
  show ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
    (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).1) = _
  simp only [stepCfg_decodeCfg_delta]
  rfl

/-- The input head of a successor. -/
theorem succCode_inputHead (a : Code tm.Q k x.length S) (β : Bool) :
    (succCode tm x S β a).2.1.val
      = min (movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.1 a.2.1.val)
        (x.length + S + 1) := by
  show min ((decodeCfg x S a).input.move
    ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
      (fun i => ((decodeCfg x S a).work i).read)
      (decodeCfg x S a).output.read).2.2.2.1)).head (x.length + S + 1) = _
  rw [head_move]
  simp only [stepCfg_decodeCfg_delta]
  rfl

/-- The head of a successor's work window. -/
theorem succCode_work_head (a : Code tm.Q k x.length S) (β : Bool) (i : Fin k) :
    ((succCode tm x S β a).2.2.1 i).1.val
      = min (movedIdx (succDir tm (paramsOf tm x S a β) i) (a.2.2.1 i).1.val) S := by
  show min (((tm.stepCfg β (decodeCfg x S a)).work i).head) S = _
  congr 1
  show ((((decodeCfg x S a).work i).writeAndMove _ _).head) = _
  rw [show ((decodeCfg x S a).work i).writeAndMove
      ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
        (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.1 i)
      ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
        (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.2.2.2.1 i)
      = (((decodeCfg x S a).work i).write _).move
        ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
          (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.2.2.2.1 i)
      from rfl, head_move, Tape.write_head, stepCfg_decodeCfg_delta]
  rfl

/-- The cells of a successor's work window. -/
theorem succCode_work_cells (a : Code tm.Q k x.length S) (β : Bool) (i : Fin k)
    (p : Fin (S + 1)) :
    ((succCode tm x S β a).2.2.1 i).2 p
      = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm (paramsOf tm x S a β) i
        else (a.2.2.1 i).2 p := by
  have hcells : ((tm.stepCfg β (decodeCfg x S a)).work i).cells
      = ((((decodeCfg x S a).work i).write
          (((succTrans tm (paramsOf tm x S a β)).2.1 i) : Γ))).cells := by
    show ((((decodeCfg x S a).work i).writeAndMove _ _)).cells = _
    rw [Tape.move_cells]
    simp only [stepCfg_decodeCfg_delta]
  show ((tm.stepCfg β (decodeCfg x S a)).work i).cells p.val = _
  rw [hcells, Tape.write]
  have hbase : ∀ q : Fin (S + 1), ((decodeCfg x S a).work i).cells q.val = (a.2.2.1 i).2 q := by
    intro q
    show (if h : q.val < S + 1 then (a.2.2.1 i).2 ⟨q.val, h⟩ else Γ.blank) = _
    rw [dite_eq_left q.isLt]
  have hhead : ((decodeCfg x S a).work i).head = (a.2.2.1 i).1.val := rfl
  by_cases h0 : (a.2.2.1 i).1.val = 0
  · rw [ite_eq_left (by rw [hhead, h0])]
    rw [hbase p, ite_eq_right]
    rintro ⟨hp, hpos⟩
    rw [hp, h0] at hpos
    omega
  · rw [ite_eq_right (by rw [hhead]; exact h0)]
    show Function.update ((decodeCfg x S a).work i).cells
      ((decodeCfg x S a).work i).head _ p.val = _
    rw [hhead]
    by_cases hp : p.val = (a.2.2.1 i).1.val
    · rw [hp, Function.update_self, ite_eq_left ⟨Fin.ext hp, by omega⟩]
      rfl
    · rw [Function.update_of_ne hp, hbase p, ite_eq_right]
      rintro ⟨hq, -⟩
      exact hp (by rw [hq])

/-- The head of a successor's output window. -/
theorem succCode_output_head (a : Code tm.Q k x.length S) (β : Bool) :
    (succCode tm x S β a).2.2.2.1.val
      = min (movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.2.2 a.2.2.2.1.val) (S + 1) := by
  show min (((tm.stepCfg β (decodeCfg x S a)).output).head) (S + 1) = _
  congr 1
  show (((decodeCfg x S a).output.writeAndMove _ _).head) = _
  rw [show (decodeCfg x S a).output.writeAndMove
      ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
        (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.2.1)
      ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
        (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.2.2.2.2)
      = ((decodeCfg x S a).output.write _).move
        ((tm.δ β (decodeCfg x S a).state (decodeCfg x S a).input.read
          (fun i => ((decodeCfg x S a).work i).read) (decodeCfg x S a).output.read).2.2.2.2.2)
      from rfl, head_move, Tape.write_head]
  simp only [stepCfg_decodeCfg_delta]
  rfl

/-- The cells of a successor's output window. -/
theorem succCode_output_cells (a : Code tm.Q k x.length S) (β : Bool) (p : Fin (S + 2)) :
    (succCode tm x S β a).2.2.2.2 p
      = if p = a.2.2.2.1 ∧ 0 < p.val then
          (((succTrans tm (paramsOf tm x S a β)).2.2.1 : Γw) : Γ)
        else a.2.2.2.2 p := by
  have hcells : ((tm.stepCfg β (decodeCfg x S a)).output).cells
      = (((decodeCfg x S a).output.write
          (((succTrans tm (paramsOf tm x S a β)).2.2.1 : Γw) : Γ))).cells := by
    show (((decodeCfg x S a).output.writeAndMove _ _)).cells = _
    rw [Tape.move_cells]
    simp only [stepCfg_decodeCfg_delta]
  show ((tm.stepCfg β (decodeCfg x S a)).output).cells p.val = _
  rw [hcells, Tape.write]
  have hbase : ∀ q : Fin (S + 2), (decodeCfg x S a).output.cells q.val = a.2.2.2.2 q := by
    intro q
    show (if h : q.val < S + 2 then a.2.2.2.2 ⟨q.val, h⟩ else Γ.blank) = _
    rw [dite_eq_left q.isLt]
  have hhead : (decodeCfg x S a).output.head = a.2.2.2.1.val := rfl
  by_cases h0 : a.2.2.2.1.val = 0
  · rw [ite_eq_left (by rw [hhead, h0])]
    rw [hbase p, ite_eq_right]
    rintro ⟨hp, hpos⟩
    rw [hp, h0] at hpos
    omega
  · rw [ite_eq_right (by rw [hhead]; exact h0)]
    show Function.update (decodeCfg x S a).output.cells
      (decodeCfg x S a).output.head _ p.val = _
    rw [hhead]
    by_cases hp : p.val = a.2.2.2.1.val
    · rw [hp, Function.update_self, ite_eq_left ⟨Fin.ext hp, by omega⟩]
    · rw [Function.update_of_ne hp, hbase p, ite_eq_right]
      rintro ⟨hq, -⟩
      exact hp (by rw [hq])

/-- **A successor, field by field.** Under the space bound the clamps in `cfgCode` are inert, so a
code is the successor of another exactly when every field is what the transition makes it — which
is what the scans check. -/
theorem eq_succCode_iff (a a' : Code tm.Q k x.length S) (β : Bool)
    (hin : movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.1 a.2.1.val
      ≤ x.length + S + 1)
    (hw : ∀ i, movedIdx (succDir tm (paramsOf tm x S a β) i) (a.2.2.1 i).1.val ≤ S)
    (ho : movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.2.2 a.2.2.2.1.val ≤ S + 1) :
    a' = succCode tm x S β a ↔
      (a'.1 = succState tm (paramsOf tm x S a β) ∧
        a'.2.1.val = movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.1 a.2.1.val ∧
        (∀ i, (a'.2.2.1 i).1.val
            = movedIdx (succDir tm (paramsOf tm x S a β) i) (a.2.2.1 i).1.val ∧
          ∀ p, (a'.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val
            then succWrite tm (paramsOf tm x S a β) i else (a.2.2.1 i).2 p) ∧
        (a'.2.2.2.1.val
            = movedIdx (succTrans tm (paramsOf tm x S a β)).2.2.2.2.2 a.2.2.2.1.val ∧
          ∀ p, a'.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
            then (((succTrans tm (paramsOf tm x S a β)).2.2.1 : Γw) : Γ)
            else a.2.2.2.2 p)) := by
  constructor
  · rintro rfl
    refine ⟨succCode_state tm x S a β, ?_, fun i => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [succCode_inputHead, min_eq_left hin]
    · rw [succCode_work_head, min_eq_left (hw i)]
    · exact succCode_work_cells tm x S a β i
    · rw [succCode_output_head, min_eq_left ho]
    · exact succCode_output_cells tm x S a β
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine Prod.ext (by rw [h1, succCode_state]) (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · exact Fin.ext (by rw [h2, succCode_inputHead, min_eq_left hin])
    · funext i
      refine Prod.ext ?_ ?_
      · exact Fin.ext (by rw [(h3 i).1, succCode_work_head, min_eq_left (hw i)])
      · funext p
        rw [(h3 i).2 p, succCode_work_cells]
    · exact Fin.ext (by rw [h4, succCode_output_head, min_eq_left ho])
    · funext p
      rw [h5 p, succCode_output_cells]

/-- **The guessed parameters are forced.** Each field of what the check was handed is pinned by
one of the checks: the state by the comparison against the old code's state field, each head
symbol by that block's own `symOk` conjunct, and the input symbol by the machine reading its own
input head. -/
theorem params_eq (a : Code tm.Q k x.length S) (P : SuccParams tm.Q k)
    (hq : a.1 = P.q) (hin : P.inSym = inSymOf tm x S a)
    (hwk : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hot : a.2.2.2.2 a.2.2.2.1 = P.oSym) :
    P = paramsOf tm x S a P.beta := by
  cases P with
  | mk beta q inSym wSym oSym =>
      simp only [paramsOf, SuccParams.mk.injEq]
      refine ⟨trivial, hq.symm, hin, ?_, hot.symm⟩
      funext i
      exact (hwk i).symm

/-- **A successor, from the conditions the checks establish.** -/
theorem eq_succCode_of_checks (a b : Code tm.Q k x.length S) (P : SuccParams tm.Q k)
    (β : Bool) (hbeta : P.beta = β)
    (hq : a.1 = P.q) (hin : P.inSym = inSymOf tm x S a)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym)
    (hclampIn : movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hclampW : ∀ i, movedIdx (succDir tm P i) (a.2.2.1 i).1.val ≤ S)
    (hclampO : movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ≤ S + 1) :
    b = succCode tm x S β a ↔
      (b.1 = succState tm P ∧
        b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ∧
        (∀ i, (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val ∧
          ∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
            else (a.2.2.1 i).2 p) ∧
        (b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ∧
          ∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
            then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p)) := by
  have hP : P = paramsOf tm x S a β := by
    rw [params_eq tm x S a P hq hin hwsym hosym, hbeta]
  subst hP
  exact eq_succCode_iff tm x S a b β hclampIn hclampW hclampO

/-- **Membership in `codeSucc`, from the conditions the checks establish.** -/
theorem mem_codeSucc_of_checks (a b : Code tm.Q k x.length S) (P : SuccParams tm.Q k)
    (hne : a.1 ≠ tm.qhalt)
    (hq : a.1 = P.q) (hin : P.inSym = inSymOf tm x S a)
    (hwsym : ∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i)
    (hosym : a.2.2.2.2 a.2.2.2.1 = P.oSym)
    (hclampIn : movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hclampW : ∀ i, movedIdx (succDir tm P i) (a.2.2.1 i).1.val ≤ S)
    (hclampO : movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ≤ S + 1)
    (hstate : b.1 = succState tm P)
    (hhead : b.2.1.val = movedIdx (succTrans tm P).2.2.2.1 a.2.1.val)
    (hwork : ∀ i, (b.2.2.1 i).1.val = movedIdx (succDir tm P i) (a.2.2.1 i).1.val ∧
      ∀ p, (b.2.2.1 i).2 p = if p = (a.2.2.1 i).1 ∧ 0 < p.val then succWrite tm P i
        else (a.2.2.1 i).2 p)
    (hout : b.2.2.2.1.val = movedIdx (succTrans tm P).2.2.2.2.2 a.2.2.2.1.val ∧
      ∀ p, b.2.2.2.2 p = if p = a.2.2.2.1 ∧ 0 < p.val
        then (((succTrans tm P).2.2.1 : Γw) : Γ) else a.2.2.2.2 p) :
    b ∈ NTM.codeSucc tm x S a := by
  refine (mem_codeSucc_iff tm x S a b).mpr ⟨hne, P.beta, ?_⟩
  exact (eq_succCode_of_checks tm x S a b P P.beta rfl hq hin hwsym hosym hclampIn hclampW
    hclampO).mpr ⟨hstate, hhead, hwork, hout⟩

end Codes

end Complexity
