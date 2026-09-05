/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# UTM extraction phase: `extractTM`

The final phase of the universal machine copies the simulated output — stored
on work tape 2 (`vOut`) under the +1 shift, i.e. starting at cell 2 — onto the
real output tape starting at cell 1, up to and including the first `□`.

## Behavior

From `qstart`:

* **Phase A (rewind)**: move the work-tape-2 head left until it reads `▷`,
  then right once (to cell 1). All other tapes idle.
* **Phase B (step to cell 2)**: move the work-tape-2 head right once more,
  to cell 2 — the first simulated output cell under the +1 shift.
* **Phase C (copy)**: repeatedly copy the symbol under the work-2 head to the
  output tape; if the symbol is `□`, halt (after writing it); otherwise move
  both heads right and repeat.

All tapes other than work tape 2 and the output are *exactly* unchanged
(`readBackWrite` writes and `idleDir` moves); work tape 2's cells are
unchanged (only its head moves).

## Main definitions

- `TM.extractTM` — the extraction machine

## Main results

- `TM.extractTM_hoareTime` — full Hoare-time specification: if the first `m`
  cells starting at work-2 cell 2 are non-blank and cell `m + 2` is blank,
  the machine copies cells `2 .. m+2` of tape 2 onto output cells `1 .. m+1`
  within `B + m + 8` steps, where `B` bounds the initial work-2 head.
-/


public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `extractTM`. -/
inductive ExtractPhase where
  | rewind   -- Phase A: rewind work tape 2 to ▷, then step right to cell 1
  | toCell2  -- Phase B: one further right move, to cell 2
  | copy     -- Phase C: copy work-2 cells to the output until (and incl.) □
  | done
  deriving DecidableEq

instance : Fintype ExtractPhase where
  elems := {.rewind, .toCell2, .copy, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- Copy work tape 2 (`vOut`) cells `2, 3, …` verbatim to output cells
    `1, 2, …`, up to and including the first `□`. Work tape 2 is first
    rewound to cell 2; its cells are preserved (write-back), and all tapes
    other than work-2 and output are exactly unchanged. -/
def extractTM : TM 6 where
  Q := ExtractPhase
  qstart := .rewind
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewind =>
      if wHeads 2 = Γ.start then
        (.toCell2, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 2 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 2 then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .toCell2 =>
      (.copy, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 2 then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .copy =>
      if wHeads 2 = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), readBackWrite (wHeads 2),
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.copy, fun i => readBackWrite (wHeads i), readBackWrite (wHeads 2),
         idleDir iHead,
         fun i => if i = 2 then Dir3.right else idleDir (wHeads i),
         Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rewind =>
      dsimp only []; split
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
      · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro i hwi; simp only []; split
        · rename_i heq; subst heq; contradiction
        · exact idleDir_right_of_start hwi
    | .toCell2 =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; simp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .copy =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · refine ⟨idleDir_right_of_start, ?_, fun _ => rfl⟩
        intro i hwi; simp only []; split
        · rfl
        · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Writing back the read symbol preserves cells (for non-`▷` reads). -/
private theorem writeBack_cells (t : Tape) (d : Dir3) (h : t.read ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read) d).cells = t.cells :=
  tape_readBackWrite_preserves t d (Or.inr h)

-- ════════════════════════════════════════════════════════════════════════
-- Phase A: rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind loop: from state `rewind` with work-2 head at `h`, reach state
    `toCell2` with work-2 head at 1 in `h + 1` steps. Work-2 cells (ghost
    `W`) and all other tapes are exactly preserved. -/
private theorem extractTM_rewind_loop
    (inp₀ : Tape) (work₀ : Fin 6 → Tape) (out₀ : Tape) (W : ℕ → Γ)
    (hW0 : W 0 = Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hothers : ∀ i : Fin 6, i ≠ 2 → (work₀ i).read ≠ Γ.start) :
    ∀ (h : ℕ) (c : Cfg 6 extractTM.Q),
      c.state = ExtractPhase.rewind →
      (c.work 2).cells = W →
      (c.work 2).head = h →
      c.input = inp₀ → c.output = out₀ →
      (∀ i, i ≠ 2 → c.work i = work₀ i) →
      ∃ c',
        extractTM.reachesIn (h + 1) c c' ∧
        c'.state = ExtractPhase.toCell2 ∧
        (c'.work 2).head = 1 ∧
        (c'.work 2).cells = W ∧
        c'.input = inp₀ ∧ c'.output = out₀ ∧
        (∀ i, i ≠ 2 → c'.work i = work₀ i) := by
  intro h
  induction h with
  | zero =>
    intro c hst hcW hhead hin hout' hw
    have hread : (c.work 2).read = Γ.start := by
      simp [Tape.read, hhead, hcW, hW0]
    have hstep : ∃ c₁, extractTM.step c = some c₁ ∧
        c₁.state = ExtractPhase.toCell2 ∧
        (c₁.work 2).head = 1 ∧ (c₁.work 2).cells = W ∧
        c₁.input = inp₀ ∧ c₁.output = out₀ ∧
        (∀ i, i ≠ 2 → c₁.work i = work₀ i) := by
      simp only [TM.step, ↓reduceIte, hst, extractTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · dsimp only []; rw [hout']; exact transitionTape_eq_self hout
      · intro i hne; dsimp only []
        simp only [show ¬(i = 2) from hne, ↓reduceIte]
        rw [hw i hne]; exact transitionTape_eq_self (hothers i hne)
    obtain ⟨c₁, hstep', hst1, hh1, hc1, hin1, hout1, hw1⟩ := hstep
    exact ⟨c₁, .step hstep' .zero, hst1, hh1, hc1, hin1, hout1, hw1⟩
  | succ h ih =>
    intro c hst hcW hhead hin hout' hw
    have hread_ne : (c.work 2).read ≠ Γ.start := by
      simp only [Tape.read, hhead, hcW]
      exact hWns (h + 1) (by omega)
    have hstep : ∃ c₁, extractTM.step c = some c₁ ∧
        c₁.state = ExtractPhase.rewind ∧
        (c₁.work 2).head = h ∧ (c₁.work 2).cells = W ∧
        c₁.input = inp₀ ∧ c₁.output = out₀ ∧
        (∀ i, i ≠ 2 → c₁.work i = work₀ i) := by
      simp only [TM.step, ↓reduceIte, hst, extractTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      · dsimp only []
        rw [writeBack_cells _ _ hread_ne, hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · dsimp only []; rw [hout']; exact transitionTape_eq_self hout
      · intro i hne; dsimp only []
        simp only [show ¬(i = 2) from hne, ↓reduceIte]
        rw [hw i hne]; exact transitionTape_eq_self (hothers i hne)
    obtain ⟨c₁, hstep', hst1, hh1, hc1, hin1, hout1, hw1⟩ := hstep
    obtain ⟨c', hreach, hst', hh', hc', hin', hout'', hw'⟩ :=
      ih c₁ hst1 hc1 hh1 hin1 hout1 hw1
    exact ⟨c', .step hstep' hreach, hst', hh', hc', hin', hout'', hw'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase B: single step from cell 1 to cell 2
-- ════════════════════════════════════════════════════════════════════════

/-- Phase-B step: from state `toCell2` with work-2 head at 1, one step
    reaches state `copy` with work-2 head at 2, all cells preserved. -/
private theorem extractTM_toCell2_step
    (inp₀ : Tape) (work₀ : Fin 6 → Tape) (out₀ : Tape) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    (hothers : ∀ i : Fin 6, i ≠ 2 → (work₀ i).read ≠ Γ.start)
    (c : Cfg 6 extractTM.Q)
    (hst : c.state = ExtractPhase.toCell2)
    (hcW : (c.work 2).cells = W)
    (hhead : (c.work 2).head = 1)
    (hin : c.input = inp₀) (hout' : c.output = out₀)
    (hw : ∀ i, i ≠ 2 → c.work i = work₀ i) :
    ∃ c', extractTM.step c = some c' ∧
      c'.state = ExtractPhase.copy ∧
      (c'.work 2).head = 2 ∧
      (c'.work 2).cells = W ∧
      c'.input = inp₀ ∧ c'.output = out₀ ∧
      (∀ i, i ≠ 2 → c'.work i = work₀ i) := by
  have hread_ne : (c.work 2).read ≠ Γ.start := by
    simp only [Tape.read, hhead, hcW]
    exact hWns 1 le_rfl
  simp only [TM.step, hst, extractTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write_head]
    omega
  · dsimp only []
    rw [writeBack_cells _ _ hread_ne, hcW]
  · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
  · dsimp only []; rw [hout']; exact transitionTape_eq_self hout
  · intro i hne; dsimp only []
    simp only [show ¬(i = 2) from hne, ↓reduceIte]
    rw [hw i hne]; exact transitionTape_eq_self (hothers i hne)

-- ════════════════════════════════════════════════════════════════════════
-- Phase C: copy loop
-- ════════════════════════════════════════════════════════════════════════

/-- Copy loop: from state `copy` with work-2 head at `j + 2` and output head
    at `j + 1`, having copied cells `2 .. j+1` already, the machine copies the
    remaining `m - j` non-blank cells plus the terminating blank and halts in
    `(m - j) + 1` steps. -/
private theorem extractTM_copy_loop
    (inp₀ : Tape) (work₀ : Fin 6 → Tape) (W : ℕ → Γ) (m : ℕ)
    (hWblank : W (m + 2) = Γ.blank)
    (hWnb : ∀ j, j < m → W (j + 2) ≠ Γ.blank)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hothers : ∀ i : Fin 6, i ≠ 2 → (work₀ i).read ≠ Γ.start) :
    ∀ (rem j : ℕ) (c : Cfg 6 extractTM.Q),
      rem = m - j → j ≤ m →
      c.state = ExtractPhase.copy →
      (c.work 2).cells = W →
      (c.work 2).head = j + 2 →
      c.input = inp₀ →
      (∀ i, i ≠ 2 → c.work i = work₀ i) →
      c.output.head = j + 1 →
      (∀ j', j' < j → c.output.cells (j' + 1) = W (j' + 2)) →
      ∃ c',
        extractTM.reachesIn (rem + 1) c c' ∧
        extractTM.halted c' ∧
        (c'.work 2).cells = W ∧
        c'.input = inp₀ ∧
        (∀ i, i ≠ 2 → c'.work i = work₀ i) ∧
        (∀ j', j' ≤ m → c'.output.cells (j' + 1) = W (j' + 2)) := by
  intro rem
  induction rem with
  | zero =>
    intro j c hrem hjm hst hcW hhead hin hw hohead hocells
    have hj : j = m := by omega
    have hread : (c.work 2).read = Γ.blank := by
      simp [Tape.read, hhead, hcW, hj, hWblank]
    have hread_ne : (c.work 2).read ≠ Γ.start := by
      rw [hread]; simp
    have hstep : ∃ c₁, extractTM.step c = some c₁ ∧
        c₁.state = ExtractPhase.done ∧
        (c₁.work 2).cells = W ∧
        c₁.input = inp₀ ∧
        (∀ i, i ≠ 2 → c₁.work i = work₀ i) ∧
        c₁.output.cells = Function.update c.output.cells (j + 1) Γ.blank := by
      simp only [TM.step, ↓reduceIte, hst, extractTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        rw [writeBack_cells _ _ hread_ne, hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · intro i hne; dsimp only []
        rw [hw i hne]; exact transitionTape_eq_self (hothers i hne)
      · dsimp only []
        simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, hohead]
        rw [ite_eq_right (show ¬(j + 1 = 0) by omega)]
        dsimp only []
        simp [readBackWrite]
    obtain ⟨c₁, hstep', hst1, hc1, hin1, hw1, hout1⟩ := hstep
    refine ⟨c₁, .step hstep' .zero, hst1, hc1, hin1, hw1, ?_⟩
    intro j' hj'
    rw [hout1]
    rcases Nat.lt_or_ge j' j with hlt | hge
    · rw [Function.update_of_ne (show j' + 1 ≠ j + 1 by omega)]
      exact hocells j' hlt
    · have hj'j : j' = j := by omega
      subst hj'j
      rw [Function.update_self, hj, hWblank]
  | succ rem ih =>
    intro j c hrem hjm hst hcW hhead hin hw hohead hocells
    have hjlt : j < m := by omega
    have hread : (c.work 2).read = W (j + 2) := by
      simp [Tape.read, hhead, hcW]
    have hread_nb : (c.work 2).read ≠ Γ.blank := by
      rw [hread]; exact hWnb j hjlt
    have hread_ne : (c.work 2).read ≠ Γ.start := by
      rw [hread]; exact hWns (j + 2) (by omega)
    have hstep : ∃ c₁, extractTM.step c = some c₁ ∧
        c₁.state = ExtractPhase.copy ∧
        (c₁.work 2).cells = W ∧
        (c₁.work 2).head = (j + 1) + 2 ∧
        c₁.input = inp₀ ∧
        (∀ i, i ≠ 2 → c₁.work i = work₀ i) ∧
        c₁.output.head = (j + 1) + 1 ∧
        c₁.output.cells = Function.update c.output.cells (j + 1) (W (j + 2)) := by
      simp only [TM.step, ↓reduceIte, hst, extractTM, hread_nb]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        rw [writeBack_cells _ _ hread_ne, hcW]
      · dsimp only []
        simp only [↓reduceIte, Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · intro i hne; dsimp only []
        simp only [show ¬(i = 2) from hne, ↓reduceIte]
        rw [hw i hne]; exact transitionTape_eq_self (hothers i hne)
      · dsimp only []
        simp only [Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      · dsimp only []
        simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, hohead]
        rw [ite_eq_right (show ¬(j + 1 = 0) by omega)]
        dsimp only []
        rw [hread, toΓ_readBackWrite_of_ne_start (hWns (j + 2) (by omega))]
    obtain ⟨c₁, hstep', hst1, hc1, hh1, hin1, hw1, hoh1, hoc1⟩ := hstep
    obtain ⟨c', hreach, hhalt, hc', hin', hw', hoc'⟩ :=
      ih (j + 1) c₁ (by omega) (by omega) hst1 hc1 hh1 hin1 hw1 hoh1
        (by
          intro j' hj'
          rw [hoc1]
          rcases Nat.lt_or_ge j' j with hlt | hge
          · rw [Function.update_of_ne (show j' + 1 ≠ j + 1 by omega)]
            exact hocells j' hlt
          · have hj'j : j' = j := by omega
            subst hj'j
            rw [Function.update_self])
    exact ⟨c', .step hstep' hreach, hhalt, hc', hin', hw', hoc'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **`extractTM` specification.** Let `m` be the number of non-blank cells
    starting at work-2 cell 2 (cell `m + 2` is the first blank). Then
    `extractTM` copies work-2 cells `2 .. m+2` onto output cells `1 .. m+1`
    (the last one the terminating `□`), preserving the input tape, all work
    tapes other than 2 exactly, and work-2's cells, within `B + m + 8` steps
    where `B` bounds the initial work-2 head position. -/
theorem extractTM_hoareTime (m B : ℕ)
    (inp₀ : Tape) (work₀ : Fin 6 → Tape) (out₀ : Tape)
    (hblank : (work₀ 2).cells (m + 2) = Γ.blank)
    (hnb : ∀ j, j < m → (work₀ 2).cells (j + 2) ≠ Γ.blank)
    (hwf2 : (work₀ 2).StartInvariant) (hhead2 : (work₀ 2).head ≤ B) (hhead2' : 1 ≤ (work₀ 2).head)
    (hout0 : out₀.cells 0 = Γ.start) (houtns : ∀ j, 1 ≤ j → out₀.cells j ≠ Γ.start)
    (houth : out₀.head = 1)
    (hinp : inp₀.read ≠ Γ.start)
    (hothers : ∀ i : Fin 6, i ≠ 2 → (work₀ i).read ≠ Γ.start) :
    extractTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i : Fin 6, i ≠ 2 → work i = work₀ i) ∧
        (work 2).cells = (work₀ 2).cells ∧
        (∀ j, j ≤ m → out.cells (j + 1) = (work₀ 2).cells (j + 2)))
      (B + m + 8) := by
  intro inp work out ⟨hinp_eq, hwork_eq, hout_eq⟩
  subst inp; subst work; subst out
  -- `hout0` and `hhead2'` are part of the standard calling convention but are
  -- not needed: the rewind loop handles any initial head position, and the
  -- output tape is only ever written at cells ≥ 1.
  have _ := hout0
  have _ := hhead2'
  have hout_read : out₀.read ≠ Γ.start := by
    simp only [Tape.read, houth]
    exact houtns 1 le_rfl
  -- Phase A: rewind work tape 2 to cell 1
  obtain ⟨c₁, hr1, hst1, hh1, hc1, hin1, hout1, hw1⟩ :=
    extractTM_rewind_loop inp₀ work₀ out₀ (work₀ 2).cells hwf2.1 hwf2.2
      hinp hout_read hothers (work₀ 2).head
      { state := ExtractPhase.rewind, input := inp₀, work := work₀, output := out₀ }
      rfl rfl rfl rfl rfl (fun _ _ => rfl)
  -- Phase B: step to cell 2
  obtain ⟨c₂, hstepB, hst2, hh2, hc2, hin2, hout2, hw2⟩ :=
    extractTM_toCell2_step inp₀ work₀ out₀ (work₀ 2).cells hwf2.2
      hinp hout_read hothers c₁ hst1 hc1 hh1 hin1 hout1 hw1
  -- Phase C: copy cells 2 .. m+2 to output cells 1 .. m+1
  obtain ⟨c₃, hr3, hhalt, hc3, hin3, hw3, hoc3⟩ :=
    extractTM_copy_loop inp₀ work₀ (work₀ 2).cells m hblank hnb hwf2.2
      hinp hothers m 0 c₂ (by omega) (Nat.zero_le m) hst2 hc2 (by omega)
      hin2 hw2 (by rw [hout2]; omega)
      (fun j' hj' => absurd hj' (Nat.not_lt_zero j'))
  refine ⟨c₃, ((work₀ 2).head + 1) + 1 + (m + 1), by omega,
    reachesIn_trans _ (reachesIn_trans _ hr1 (.step hstepB .zero)) hr3,
    hhalt, hin3, hw3, hc3, hoc3⟩

end TM

end Complexity
