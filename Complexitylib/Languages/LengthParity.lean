/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Combinators
public import Complexitylib.Classes.Containments

/-!
# Languages determined by the parity of the input length

The first genuinely linear-time examples: scan the input, toggling a bit
each step, and write the answer once we hit a blank. Demonstrates a
textbook `scan`-style TM with an `O(n)` time bound, proved by induction on
the input.

## Main definitions

- `TM.evenLengthTM` — 4-state scanning TM (`start`, `even`, `odd`, `done`).
- `Language.evenLength` — strings of even length.
- `Language.oddLength` — strings of odd length.

## Main results

- `evenLengthTM_reachesIn` — halts in `|x| + 2` steps with `1` iff `|x|` is even.
- `evenLength_in_DTIME`, `oddLength_in_DTIME` — both in `DTIME(n + 2)`.
- `evenLength_mem_P`, `oddLength_mem_P` — derived via `DTIME_mono` / `P_compl`.
- `oddLength_eq_compl_evenLength` — explicit Boolean identity.
-/


public section

namespace Complexity

open Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- The 4-state parity scanner
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `evenLengthTM`. -/
inductive LengthParityPhase where
  | start | even | odd | done
  deriving DecidableEq

instance : Fintype LengthParityPhase where
  elems := {.start, .even, .odd, .done}
  complete := fun x => by cases x <;> simp

variable {n : ℕ}

/-- Scanning TM that writes `1` if the input length is even, `0` otherwise.
    Uses exactly 4 control states and halts in `|x| + 2` steps on every input. -/
def evenLengthTM : TM n where
  Q := LengthParityPhase
  qstart := .start
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .start =>
      -- Move both input and output heads from cell 0 (▷) to cell 1.
      -- The output write at cell 0 is a no-op, so ▷ is preserved.
      (.even, fun i => readBackWrite (wHeads i), .blank,
       .right, fun i => idleDir (wHeads i), .right)
    | .even =>
      if iHead = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), .one,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.odd, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
    | .odd =>
      if iHead = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), .zero,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.even, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         .right, fun i => idleDir (wHeads i), idleDir oHead)
    | .done =>
      allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .start =>
      exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .even =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
    | .odd =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
    | .done =>
      exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Step-by-step simulation
-- ════════════════════════════════════════════════════════════════════════

/-- Step 1: from `.start`, both heads advance from 0 to 1, entering `.even`. -/
private theorem evenLengthTM_step_start
    (c : Cfg n (evenLengthTM (n := n)).Q) (hst : c.state = .start)
    (hih : c.input.head = 0) (hoh : c.output.head = 0) :
    ∃ c', (evenLengthTM (n := n)).step c = some c' ∧
      c'.state = LengthParityPhase.even ∧
      c'.input.head = 1 ∧ c'.input.cells = c.input.cells ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  simp only [TM.step, hst, evenLengthTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp [Tape.move, hih]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hoh]

/-- Scan step: from `.even` or `.odd` with a non-blank non-start input symbol,
    the machine toggles state, advances input right by one, and leaves both
    input and output cells unchanged. -/
private theorem evenLengthTM_step_scan
    (c : Cfg n (evenLengthTM (n := n)).Q)
    (P : LengthParityPhase) (hP : P = .even ∨ P = .odd) (hst : c.state = P)
    (hi_nb : c.input.read ≠ Γ.blank)
    (ho_head : c.output.head = 1)
    (ho_cell1_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (evenLengthTM (n := n)).step c = some c' ∧
      c'.state = (if P = .even then LengthParityPhase.odd else LengthParityPhase.even) ∧
      c'.input.head = c.input.head + 1 ∧ c'.input.cells = c.input.cells ∧
      c'.output.head = 1 ∧ c'.output.cells = c.output.cells := by
  rcases hP with hP | hP <;> subst hP <;>
    simp only [TM.step, hst, evenLengthTM, reduceCtorEq, ↓reduceIte, ite_eq_right hi_nb]
  all_goals
    have ho_move : idleDir c.output.read = Dir3.stay := by
      simp [idleDir, Tape.read, ho_head, show c.output.cells 1 ≠ Γ.start from
        ho_cell1_nb]
    have hne : c.output.read ≠ Γ.start := by
      simp only [Tape.read, ho_head]; exact ho_cell1_nb
    refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_⟩
    · simp [Tape.move]
    · simp [Tape.writeAndMove, ho_move, Tape.move, Tape.write_head, ho_head]
    · exact tape_readBackWrite_preserves c.output _ (Or.inr hne)

/-- Halt step: from `.even` on blank input, writes `Γ.one` at output cell 1
    and enters `.done`. -/
private theorem evenLengthTM_step_halt_even
    (c : Cfg n (evenLengthTM (n := n)).Q) (hst : c.state = .even)
    (hi_blank : c.input.read = Γ.blank)
    (ho_head : c.output.head = 1)
    (ho_cell1_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (evenLengthTM (n := n)).step c = some c' ∧
      (evenLengthTM (n := n)).halted c' ∧
      c'.output.cells 1 = Γ.one := by
  simp only [TM.step, hst, evenLengthTM, reduceCtorEq, ↓reduceIte, ite_eq_left hi_blank]
  refine ⟨_, rfl, rfl, ?_⟩
  have ho_move : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, Tape.read, ho_head, show c.output.cells 1 ≠ Γ.start from ho_cell1_nb]
  have h1 : (1 : ℕ) ≠ 0 := by omega
  simp only [Tape.writeAndMove, ho_move, Tape.move, Tape.write, ho_head,
             ite_eq_right h1, Function.update_self, Γw.toΓ]

/-- Halt step: from `.odd` on blank input, writes `Γ.zero` at output cell 1. -/
private theorem evenLengthTM_step_halt_odd
    (c : Cfg n (evenLengthTM (n := n)).Q) (hst : c.state = .odd)
    (hi_blank : c.input.read = Γ.blank)
    (ho_head : c.output.head = 1)
    (ho_cell1_nb : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (evenLengthTM (n := n)).step c = some c' ∧
      (evenLengthTM (n := n)).halted c' ∧
      c'.output.cells 1 = Γ.zero := by
  simp only [TM.step, hst, evenLengthTM, reduceCtorEq, ↓reduceIte, ite_eq_left hi_blank]
  refine ⟨_, rfl, rfl, ?_⟩
  have ho_move : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, Tape.read, ho_head, show c.output.cells 1 ≠ Γ.start from ho_cell1_nb]
  have h1 : (1 : ℕ) ≠ 0 := by omega
  simp only [Tape.writeAndMove, ho_move, Tape.move, Tape.write, ho_head,
             ite_eq_right h1, Function.update_self, Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- Main scan lemma
-- ════════════════════════════════════════════════════════════════════════

/-- **Scan invariant**: given any configuration where input head is at cell
    `k + 1` with `m` input bits remaining (so `x.length = k + m`), the state
    matches the parity of `k`, and the output head is at cell 1 with a
    non-start value, the TM reaches a halted configuration in `m + 1` steps
    with output cell 1 set to `Γ.one` iff `|x|` is even. Proved by induction
    on `m`. -/
private theorem evenLengthTM_scan (x : List Bool) (m k : ℕ)
    (hlen : x.length = k + m)
    (c : Cfg n (evenLengthTM (n := n)).Q)
    (hst : c.state = if k % 2 = 0 then LengthParityPhase.even else LengthParityPhase.odd)
    (hic : c.input.cells = (Tape.init (x.map Γ.ofBool)).cells)
    (hih : c.input.head = k + 1)
    (hoh : c.output.head = 1)
    (hoc : c.output.cells 1 ≠ Γ.start) :
    ∃ c', (evenLengthTM (n := n)).reachesIn (m + 1) c c' ∧
      (evenLengthTM (n := n)).halted c' ∧
      c'.output.cells 1 = if x.length % 2 = 0 then Γ.one else Γ.zero := by
  induction m generalizing k c with
  | zero =>
    -- k = x.length: reading blank, halt step
    have hk : k = x.length := by omega
    have hi_blank : c.input.read = Γ.blank := by
      simp only [Tape.read, hih, hic]
      show (Tape.init (x.map Γ.ofBool)).cells (k + 1) = Γ.blank
      simp [Tape.init, hk]
    by_cases hpar : k % 2 = 0
    · have hst_even : c.state = LengthParityPhase.even := by rw [hst, ite_eq_left hpar]
      obtain ⟨c', hstep, hhalt, hout⟩ :=
        evenLengthTM_step_halt_even c hst_even hi_blank hoh hoc
      refine ⟨c', .step hstep .zero, hhalt, ?_⟩
      rw [hout, hk] at *
      simp [hpar]
    · have hst_odd : c.state = LengthParityPhase.odd := by rw [hst, ite_eq_right hpar]
      obtain ⟨c', hstep, hhalt, hout⟩ :=
        evenLengthTM_step_halt_odd c hst_odd hi_blank hoh hoc
      refine ⟨c', .step hstep .zero, hhalt, ?_⟩
      rw [hout, hk] at *
      have : x.length % 2 ≠ 0 := by rw [← hk]; exact hpar
      simp [this]
  | succ m ih =>
    -- k < x.length: reading bit, scan step then IH with k+1
    have hk_lt : k < x.length := by omega
    have hmap_len : (x.map Γ.ofBool).length = x.length := by simp
    have hi_nb : c.input.read ≠ Γ.blank := by
      simp only [Tape.read, hih, hic]
      show (Tape.init (x.map Γ.ofBool)).cells (k + 1) ≠ _
      have hkmap : k < (x.map Γ.ofBool).length := by rw [hmap_len]; exact hk_lt
      simp only [Tape.init, show k + 1 ≠ 0 from by omega, ↓reduceIte,
        Nat.add_sub_cancel, List.getElem?_eq_getElem hkmap, Option.getD_some,
        List.getElem_map]
      cases x[k]'hk_lt <;> simp [Γ.ofBool]
    -- Apply scan step (case split on parity to know the current state concretely)
    have hlen' : x.length = (k + 1) + m := by omega
    by_cases hpar : k % 2 = 0
    · -- state = .even, after scan = .odd
      have hst_eo : c.state = LengthParityPhase.even := by rw [hst, ite_eq_left hpar]
      obtain ⟨c₁, hstep, hst₁, hih₁, hic₁, hoh₁, hoc₁⟩ :=
        evenLengthTM_step_scan c LengthParityPhase.even (Or.inl rfl) hst_eo hi_nb hoh hoc
      have hst₁' : c₁.state =
          if (k + 1) % 2 = 0 then LengthParityPhase.even else LengthParityPhase.odd := by
        have h1 : (k + 1) % 2 ≠ 0 := by omega
        rw [hst₁, ite_eq_left rfl]; simp [h1]; rfl
      have hic₁' : c₁.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by rw [hic₁, hic]
      have hih₁' : c₁.input.head = (k + 1) + 1 := by rw [hih₁, hih]
      have hoc₁' : c₁.output.cells 1 ≠ Γ.start := by rw [hoc₁]; exact hoc
      obtain ⟨c', hreach', hhalt', hout'⟩ :=
        ih (k + 1) hlen' c₁ hst₁' hic₁' hih₁' hoh₁ hoc₁'
      exact ⟨c', .step hstep hreach', hhalt', hout'⟩
    · -- state = .odd, after scan = .even
      have hst_eo : c.state = LengthParityPhase.odd := by rw [hst, ite_eq_right hpar]
      obtain ⟨c₁, hstep, hst₁, hih₁, hic₁, hoh₁, hoc₁⟩ :=
        evenLengthTM_step_scan c LengthParityPhase.odd (Or.inr rfl) hst_eo hi_nb hoh hoc
      have hst₁' : c₁.state =
          if (k + 1) % 2 = 0 then LengthParityPhase.even else LengthParityPhase.odd := by
        have h1 : (k + 1) % 2 = 0 := by omega
        rw [hst₁, ite_eq_right (by decide : LengthParityPhase.odd ≠ LengthParityPhase.even)]
        simp [h1]
        rfl
      have hic₁' : c₁.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by rw [hic₁, hic]
      have hih₁' : c₁.input.head = (k + 1) + 1 := by rw [hih₁, hih]
      have hoc₁' : c₁.output.cells 1 ≠ Γ.start := by rw [hoc₁]; exact hoc
      obtain ⟨c', hreach', hhalt', hout'⟩ :=
        ih (k + 1) hlen' c₁ hst₁' hic₁' hih₁' hoh₁ hoc₁'
      exact ⟨c', .step hstep hreach', hhalt', hout'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main correctness theorem
-- ════════════════════════════════════════════════════════════════════════

/-- `evenLengthTM` halts in `|x| + 2` steps on every input, writing `Γ.one`
    to output cell 1 iff `|x|` is even. -/
theorem evenLengthTM_reachesIn (x : List Bool) :
    ∃ c', (evenLengthTM (n := n)).reachesIn (x.length + 2)
            ((evenLengthTM (n := n)).initCfg x) c' ∧
      (evenLengthTM (n := n)).halted c' ∧
      c'.output.cells 1 = if x.length % 2 = 0 then Γ.one else Γ.zero := by
  -- Step 1: start → even
  obtain ⟨c₁, hstep1, hst1, hih1, hic1, hoh1, hoc1⟩ :=
    evenLengthTM_step_start (n := n) ((evenLengthTM (n := n)).initCfg x) rfl rfl rfl
  -- Apply scan from k = 0 with m = x.length
  have hst1' : c₁.state =
      if (0 : ℕ) % 2 = 0 then LengthParityPhase.even else LengthParityPhase.odd := by
    simpa using hst1
  have hic1' : c₁.input.cells = (Tape.init (x.map Γ.ofBool)).cells := hic1
  have hih1' : c₁.input.head = 0 + 1 := by simpa using hih1
  have hoc1' : c₁.output.cells 1 ≠ Γ.start := by
    rw [hoc1]; simp [Tape.init]
  obtain ⟨c', hreach, hhalt, hout⟩ :=
    evenLengthTM_scan x x.length 0 (by omega) c₁ hst1' hic1' hih1' hoh1 hoc1'
  refine ⟨c', ?_, hhalt, hout⟩
  exact .step hstep1 hreach

end TM

-- ════════════════════════════════════════════════════════════════════════
-- Concrete languages
-- ════════════════════════════════════════════════════════════════════════

namespace Language

/-- Strings of even length (including the empty string). -/
def evenLength : Language := {x | x.length % 2 = 0}

/-- Strings of odd length. -/
def oddLength : Language := {x | x.length % 2 = 1}

end Language

theorem oddLength_eq_compl_evenLength :
    Language.oddLength = Language.evenLengthᶜ := by
  ext x
  simp only [Language.evenLength, Language.oddLength, Set.mem_ofPred_eq,
             Set.mem_compl_iff]
  omega

-- ════════════════════════════════════════════════════════════════════════
-- DecidesInTime bridge
-- ════════════════════════════════════════════════════════════════════════

/-- `evenLengthTM` decides `evenLength` in time `n + 2`. -/
theorem evenLengthTM_decidesInTime :
    (TM.evenLengthTM (n := 0)).DecidesInTime Language.evenLength (fun n => n + 2) := by
  intro x
  obtain ⟨c', hreach, hhalt, hout⟩ := TM.evenLengthTM_reachesIn (n := 0) x
  refine ⟨c', x.length + 2, le_refl _, hreach, hhalt, ?_, ?_⟩
  · intro hxL
    have : x.length % 2 = 0 := hxL
    rw [hout, ite_eq_left this]
  · intro hxnL
    have : x.length % 2 ≠ 0 := hxnL
    rw [hout, ite_eq_right this]

-- ════════════════════════════════════════════════════════════════════════
-- DTIME memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`evenLength ∈ DTIME(n + 2)`**. -/
theorem evenLength_in_DTIME :
    Language.evenLength ∈ DTIME (fun n => n + 2) :=
  ⟨0, TM.evenLengthTM, fun n => n + 2, evenLengthTM_decidesInTime, BigO.refl _⟩

-- ════════════════════════════════════════════════════════════════════════
-- P memberships
-- ════════════════════════════════════════════════════════════════════════

/-- **`evenLength ∈ P`**. -/
theorem evenLength_mem_P : Language.evenLength ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, DTIME_mono ?_ evenLength_in_DTIME⟩
  -- `n + 2 =O n^1` for large n
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

/-- **`oddLength ∈ P`** via `P_compl`. -/
theorem oddLength_mem_P : Language.oddLength ∈ P := by
  rw [oddLength_eq_compl_evenLength]
  exact P_compl evenLength_mem_P

end Complexity
