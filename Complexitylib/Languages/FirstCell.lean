/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Classes.Containments
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Languages determined by the first input cell

Non-trivial languages whose membership can be decided by reading just the
first cell after `▷` on the input tape. We build a single 3-state TM
`decideFirstCellTM` parameterized by a predicate `yesOn : Γ → Bool`, prove
it runs in exactly 2 steps, and specialize it to several concrete
languages.

## Main definitions

- `firstCell` — the first input cell after `▷` (a `Γ` symbol).
- `TM.decideFirstCellTM yesOn` — the 3-state parametric TM.

## Concrete languages

- `Language.singletonEmpty` — `{[]}` (empty string only).
- `Language.firstBitOne`    — strings beginning with `1`.
- `Language.firstBitZero`   — strings beginning with `0`.
- `Language.nonempty`       — nonempty strings.

## Main results

- `decideFirstCellTM_reachesIn` — the TM halts in 2 steps with the correct output.
- `singletonEmpty_in_DTIME`, `firstBitOne_in_DTIME`, `firstBitZero_in_DTIME`,
  `nonempty_in_DTIME` — all decidable in `DTIME(fun _ => 2)`.
- `singletonEmpty_mem_P`, `firstBitOne_mem_P`, `firstBitZero_mem_P`,
  `nonempty_mem_P` — all in `P` (and hence in every larger class).
- `nonempty_eq_compl_singletonEmpty` — the nonempty language is the
  complement of `{[]}`, giving a second derivation of its P-membership.
- `firstBitZero_union_firstBitOne_eq_nonempty` — explicit Boolean identity
  used to present `nonempty` as a union.
-/


@[expose] public section

namespace Complexity

open Complexity

-- ════════════════════════════════════════════════════════════════════════
-- The first-cell function
-- ════════════════════════════════════════════════════════════════════════

/-- The first cell after `▷` on the initial input tape, as a `Γ` symbol.
    This is the cell the machine reads on its second step. -/
def firstCell : List Bool → Γ
  | [] => Γ.blank
  | b :: _ => Γ.ofBool b

@[simp] theorem firstCell_nil : firstCell [] = Γ.blank := rfl

@[simp] theorem firstCell_cons (b : Bool) (xs : List Bool) :
    firstCell (b :: xs) = Γ.ofBool b := rfl

/-- `firstCell x` reads cell 1 of the initial input tape. -/
theorem firstCell_eq_initTape_cells_one (x : List Bool) :
    firstCell x = (Tape.init (x.map Γ.ofBool)).cells 1 := by
  cases x with
  | nil => simp [firstCell, Tape.init]
  | cons b xs => simp [firstCell, Tape.init]

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- The decideFirstCellTM construction
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `decideFirstCellTM`. -/
inductive FirstCellPhase where
  | advance | decide | done
  deriving DecidableEq

instance : Fintype FirstCellPhase where
  elems := {.advance, .decide, .done}
  complete := fun x => by cases x <;> simp

variable {n : ℕ}

/-- Parametric 3-state TM: advance past `▷` on input and output, then read
    input cell 1 and write `1` if `yesOn iHead`, else `0`. Always halts in
    exactly 2 steps. -/
def decideFirstCellTM (yesOn : Γ → Bool) : TM n where
  Q := FirstCellPhase
  qstart := .advance
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .advance =>
      (.decide, fun i => readBackWrite (wHeads i), .blank,
       .right, fun i => idleDir (wHeads i), .right)
    | .decide =>
      (.done, fun i => readBackWrite (wHeads i),
       (if yesOn iHead then Γw.one else Γw.zero),
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done =>
      allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .advance =>
      exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .decide =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done =>
      exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Step-by-step simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Step 1: from `.advance`, the machine moves input and output heads right,
    transitioning to `.decide`. Both heads go from position 0 (on `▷`) to
    position 1. Tape cell contents are preserved (write at cell 0 is a
    no-op; the work tape's `readBackWrite` also preserves cells). -/
private theorem decideFirstCellTM_step_advance (yesOn : Γ → Bool)
    (c : Cfg n (decideFirstCellTM yesOn).Q) (hst : c.state = FirstCellPhase.advance)
    (hi_head : c.input.head = 0) (ho_head : c.output.head = 0) :
    ∃ c', (decideFirstCellTM yesOn).step c = some c' ∧
      c'.state = FirstCellPhase.decide ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, decideFirstCellTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.move, hi_head]
  · rfl
  · simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, ho_head]

/-- Step 2: from `.decide` at input cell 1 and output cell 1, the machine
    writes `Γw.one` or `Γw.zero` depending on `yesOn iHead`, transitions to
    `.done`, and halts. -/
private theorem decideFirstCellTM_step_decide (yesOn : Γ → Bool)
    (c : Cfg n (decideFirstCellTM yesOn).Q) (hst : c.state = FirstCellPhase.decide)
    (ho_head : c.output.head = 1) (ho_ns : c.output.read ≠ Γ.start) :
    ∃ c', (decideFirstCellTM yesOn).step c = some c' ∧
      (decideFirstCellTM yesOn).halted c' ∧
      c'.output.cells 1 =
        (if yesOn c.input.read then Γ.one else Γ.zero) := by
  simp only [TM.step, hst, decideFirstCellTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_⟩
  -- Output tape: write the decision symbol, move (idleDir oHead = stay).
  have ho_move : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, ho_ns]
  have h1 : (1 : ℕ) ≠ 0 := by omega
  simp only [Tape.writeAndMove, ho_move, Tape.move, Tape.write, ho_head,
             ite_eq_right h1, Function.update_self, Γw.toΓ]
  split_ifs <;> rfl

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `decideFirstCellTM yesOn` halts in exactly 2 steps on every input, with
    output cell 1 set to `Γ.one` if `yesOn (firstCell x)` is true and
    `Γ.zero` otherwise. -/
theorem decideFirstCellTM_reachesIn (yesOn : Γ → Bool) (x : List Bool) :
    ∃ c', (decideFirstCellTM (n := n) yesOn).reachesIn 2
            ((decideFirstCellTM yesOn).initCfg x) c' ∧
      (decideFirstCellTM yesOn).halted c' ∧
      c'.output.cells 1 =
        (if yesOn (firstCell x) then Γ.one else Γ.zero) := by
  -- Step 1: advance → decide
  obtain ⟨c₁, hstep1, hst1, hi1h, hi1c, ho1h, ho1c⟩ :=
    decideFirstCellTM_step_advance (n := n) yesOn
      ((decideFirstCellTM yesOn).initCfg x) rfl rfl rfl
  -- Step 2: decide → done
  have hi1_read_eq : c₁.input.read = firstCell x := by
    simp only [Tape.read, hi1h, hi1c]
    exact (firstCell_eq_initTape_cells_one x).symm
  have ho1_read_ne : c₁.output.read ≠ Γ.start := by
    simp only [Tape.read, ho1h, ho1c]
    show (Tape.init []).cells 1 ≠ Γ.start
    simp [Tape.init]
  obtain ⟨c₂, hstep2, hhalt, hout⟩ :=
    decideFirstCellTM_step_decide (n := n) yesOn c₁ hst1 ho1h ho1_read_ne
  refine ⟨c₂, .step hstep1 (.step hstep2 .zero), hhalt, ?_⟩
  rw [hout, hi1_read_eq]

/-- Generic bridge from `decideFirstCellTM_reachesIn` to `DecidesInTime`.
    Whenever a language `L` is characterized by `x ∈ L ↔ yesOn (firstCell x)`,
    the 0-work-tape version of `decideFirstCellTM yesOn` decides `L` in 2 steps. -/
theorem decideFirstCellTM_decidesInTime {yesOn : Γ → Bool} {L : Language}
    (hL : ∀ x, x ∈ L ↔ yesOn (firstCell x) = true) :
    (decideFirstCellTM (n := 0) yesOn).DecidesInTime L (fun _ => 2) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ := decideFirstCellTM_reachesIn (n := 0) yesOn x
  refine ⟨c', 2, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    rw [hout, ite_eq_left ((hL x).mp hxL)]
  · intro hxnL
    rw [hout]
    have hy : yesOn (firstCell x) = false := by
      rcases h : yesOn (firstCell x) with _ | _
      · rfl
      · exact absurd ((hL x).mpr h) hxnL
    rw [ite_eq_right (by simp [hy])]

end TM

-- ════════════════════════════════════════════════════════════════════════
-- Concrete languages
-- ════════════════════════════════════════════════════════════════════════

namespace Language

/-- The language `{[]}`: the only accepted string is the empty one. -/
abbrev singletonEmpty : Language := {[]}

/-- Strings whose first bit is `1`. -/
def firstBitOne : Language := {x | ∃ xs, x = true :: xs}

/-- Strings whose first bit is `0`. -/
def firstBitZero : Language := {x | ∃ xs, x = false :: xs}

/-- Nonempty strings. -/
def nonempty : Language := {x | x ≠ []}

end Language

-- ════════════════════════════════════════════════════════════════════════
-- Membership characterizations via firstCell
-- ════════════════════════════════════════════════════════════════════════

theorem mem_singletonEmpty_iff (x : List Bool) :
    x ∈ Language.singletonEmpty ↔ decide (firstCell x = Γ.blank) = true := by
  cases x with
  | nil => simp [Language.singletonEmpty, firstCell]
  | cons b xs =>
    simp only [Language.singletonEmpty, Set.mem_singleton_iff, firstCell]
    cases b <;> simp [Γ.ofBool]

theorem mem_firstBitOne_iff (x : List Bool) :
    x ∈ Language.firstBitOne ↔ decide (firstCell x = Γ.one) = true := by
  cases x with
  | nil => simp [Language.firstBitOne, firstCell]
  | cons b xs =>
    cases b <;> simp [Language.firstBitOne, firstCell, Γ.ofBool]

theorem mem_firstBitZero_iff (x : List Bool) :
    x ∈ Language.firstBitZero ↔ decide (firstCell x = Γ.zero) = true := by
  cases x with
  | nil => simp [Language.firstBitZero, firstCell]
  | cons b xs =>
    cases b <;> simp [Language.firstBitZero, firstCell, Γ.ofBool]

theorem mem_nonempty_iff (x : List Bool) :
    x ∈ Language.nonempty ↔ decide (firstCell x ≠ Γ.blank) = true := by
  cases x with
  | nil => simp [Language.nonempty, firstCell]
  | cons b xs =>
    cases b <;> simp [Language.nonempty, firstCell, Γ.ofBool]

-- ════════════════════════════════════════════════════════════════════════
-- DTIME memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`{[]} ∈ DTIME(2)`**: decided in 2 steps by `decideFirstCellTM (· = Γ.blank)`. -/
theorem singletonEmpty_in_DTIME :
    Language.singletonEmpty ∈ DTIME (fun _ => 2) :=
  ⟨0, TM.decideFirstCellTM (fun g => decide (g = Γ.blank)), fun _ => 2,
    TM.decideFirstCellTM_decidesInTime mem_singletonEmpty_iff, BigO.refl _⟩

/-- **`firstBitOne ∈ DTIME(2)`**. -/
theorem firstBitOne_in_DTIME :
    Language.firstBitOne ∈ DTIME (fun _ => 2) :=
  ⟨0, TM.decideFirstCellTM (fun g => decide (g = Γ.one)), fun _ => 2,
    TM.decideFirstCellTM_decidesInTime mem_firstBitOne_iff, BigO.refl _⟩

/-- **`firstBitZero ∈ DTIME(2)`**. -/
theorem firstBitZero_in_DTIME :
    Language.firstBitZero ∈ DTIME (fun _ => 2) :=
  ⟨0, TM.decideFirstCellTM (fun g => decide (g = Γ.zero)), fun _ => 2,
    TM.decideFirstCellTM_decidesInTime mem_firstBitZero_iff, BigO.refl _⟩

/-- **`nonempty ∈ DTIME(2)`**. -/
theorem nonempty_in_DTIME :
    Language.nonempty ∈ DTIME (fun _ => 2) :=
  ⟨0, TM.decideFirstCellTM (fun g => decide (g ≠ Γ.blank)), fun _ => 2,
    TM.decideFirstCellTM_decidesInTime mem_nonempty_iff, BigO.refl _⟩

-- ════════════════════════════════════════════════════════════════════════
-- P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`{[]} ∈ P`**. -/
theorem singletonEmpty_mem_P : Language.singletonEmpty ∈ P :=
  Set.mem_iUnion.mpr ⟨0, DTIME_mono (BigO.const_le_pow 2 0) singletonEmpty_in_DTIME⟩

/-- **`firstBitOne ∈ P`**. -/
theorem firstBitOne_mem_P : Language.firstBitOne ∈ P :=
  Set.mem_iUnion.mpr ⟨0, DTIME_mono (BigO.const_le_pow 2 0) firstBitOne_in_DTIME⟩

/-- **`firstBitZero ∈ P`**. -/
theorem firstBitZero_mem_P : Language.firstBitZero ∈ P :=
  Set.mem_iUnion.mpr ⟨0, DTIME_mono (BigO.const_le_pow 2 0) firstBitZero_in_DTIME⟩

/-- **`nonempty ∈ P`**. -/
theorem nonempty_mem_P : Language.nonempty ∈ P :=
  Set.mem_iUnion.mpr ⟨0, DTIME_mono (BigO.const_le_pow 2 0) nonempty_in_DTIME⟩

-- ════════════════════════════════════════════════════════════════════════
-- Boolean combinations
-- ════════════════════════════════════════════════════════════════════════

/-- `nonempty` is the complement of `{[]}`. -/
theorem nonempty_eq_compl_singletonEmpty :
    Language.nonempty = Language.singletonEmptyᶜ := by
  ext x; simp [Language.nonempty, Language.singletonEmpty]

/-- `nonempty` is the union of "first bit 0" and "first bit 1". -/
theorem firstBitZero_union_firstBitOne_eq_nonempty :
    Language.firstBitZero ∪ Language.firstBitOne = Language.nonempty := by
  ext x
  cases x with
  | nil => simp [Language.firstBitZero, Language.firstBitOne, Language.nonempty]
  | cons b xs =>
    cases b <;>
      simp [Language.firstBitZero, Language.firstBitOne, Language.nonempty]

/-- **Alternative proof**: `nonempty ∈ P` via `P_compl` applied to `{[]} ∈ P`. -/
theorem nonempty_mem_P_via_compl : Language.nonempty ∈ P := by
  rw [nonempty_eq_compl_singletonEmpty]
  exact P_compl singletonEmpty_mem_P

/-- **Alternative proof**: `nonempty ∈ P` via `P_union`. -/
theorem nonempty_mem_P_via_union : Language.nonempty ∈ P := by
  rw [← firstBitZero_union_firstBitOne_eq_nonempty]
  exact P_union firstBitZero_mem_P firstBitOne_mem_P

end Complexity
