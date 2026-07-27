/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Output negation phase: `negOutTM`

The last phase of the time-hierarchy diagonalizer replaces output cell 1 with
the *binary* negation of "cell 1 = `1`": `1 ↦ 0`, and anything else (`0` or
`□`) `↦ 1`. (The `complementTM`/`flipBit` machinery maps `□ ↦ □`, which is
not binary — hence this machine.)

## Behavior

Mirrors `writeTM`: from `qstart`,

* **rewind**: move the output head left until it reads `▷`, then right once
  (to cell 1). All other tapes idle.
* **goRight**: one buffer step at cell 1, *preserving* its contents (unlike
  `writeTM`, which blanks it — here the next step must still read it).
* **write**: read output cell 1 and overwrite it with its binary negation.
* **done**: halt, parked at output cell 1.

The input tape and all work tapes are *exactly* unchanged (`readBackWrite`
writes and `idleDir` moves); the output cells are unchanged except cell 1.

## Main definitions

- `TM.negOutTM` — the output-negating machine

## Main results

- `TM.negOutTM_hoareTime` — ghost-style Hoare-time specification: with the
  initial tapes pinned as `inp₀`/`work₀`/`out₀`, the machine halts within
  `B + 3` steps (`B` bounding the initial output head) with
  `out.cells = Function.update out₀.cells 1
    (if out₀.cells 1 = Γ.one then Γ.zero else Γ.one)`,
  the output head parked at cell 1, and `inp = inp₀`, `work = work₀`.
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `negOutTM` (mirrors `WritePhase`). -/
inductive NegOutPhase where
  | rewind | goRight | write | done
  deriving DecidableEq

instance : Fintype NegOutPhase where
  elems := {.rewind, .goRight, .write, .done}
  complete := fun x => by cases x <;> simp

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- Replace output cell 1 with the binary negation of "cell 1 = `1`"
    (`1 ↦ 0`; anything else `↦ 1`) and halt with the output head parked at
    cell 1. Phases: rewind output to `▷` → right to cell 1 → read-and-negate
    → halt. The input tape and all work tapes are exactly unchanged. -/
def negOutTM : TM n where
  Q := NegOutPhase
  qstart := .rewind
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewind =>
      if oHead = Γ.start then
        (.goRight, fun i => readBackWrite (wHeads i), .blank,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
      else
        (.rewind, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.left)
    | .goRight =>
      (.write, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .write =>
      (.done, fun i => readBackWrite (wHeads i),
       if oHead = Γ.one then .zero else .one,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rewind =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
      · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
        intro h; next hn => exact absurd h hn
    | .goRight =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .write =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Tape helper
-- ════════════════════════════════════════════════════════════════════════

/-- Writing back the read symbol preserves cells (for non-`▷` reads). -/
private theorem negOut_writeBack_cells (t : Tape) (d : Dir3) (h : t.read ≠ Γ.start) :
    (t.writeAndMove (readBackWrite t.read) d).cells = t.cells :=
  tape_readBackWrite_preserves t d (Or.inr h)

-- ════════════════════════════════════════════════════════════════════════
-- Phase A: rewind loop (exact input/work frames)
-- ════════════════════════════════════════════════════════════════════════

/-- Rewind loop: from state `rewind` with output head at `h`, reach state
    `goRight` with output head at 1 in `h + 1` steps. Output cells (ghost `W`)
    are exactly preserved, as are the input tape and all work tapes. -/
private theorem negOutTM_rewind_loop
    (inp₀ : Tape) (work₀ : Fin n → Tape) (W : ℕ → Γ)
    (hW0 : W 0 = Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hw : ∀ i, (work₀ i).read ≠ Γ.start) :
    ∀ (h : ℕ) (c : Cfg n (negOutTM (n := n)).Q),
      c.state = NegOutPhase.rewind →
      c.output.cells = W →
      c.output.head = h →
      c.input = inp₀ → c.work = work₀ →
      ∃ c',
        (negOutTM (n := n)).reachesIn (h + 1) c c' ∧
        c'.state = NegOutPhase.goRight ∧
        c'.output.head = 1 ∧
        c'.output.cells = W ∧
        c'.input = inp₀ ∧ c'.work = work₀ := by
  intro h
  induction h with
  | zero =>
    intro c hst hcW hhead hin hwk
    have hread : c.output.read = Γ.start := by
      simp [Tape.read, hhead, hcW, hW0]
    have hstep : ∃ c₁, (negOutTM (n := n)).step c = some c₁ ∧
        c₁.state = NegOutPhase.goRight ∧
        c₁.output.head = 1 ∧ c₁.output.cells = W ∧
        c₁.input = inp₀ ∧ c₁.work = work₀ := by
      simp only [TM.step, ↓reduceIte, hst, negOutTM, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · dsimp only []
        simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead, hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)
    obtain ⟨c₁, hstep', hst1, hh1, hc1, hin1, hw1⟩ := hstep
    exact ⟨c₁, .step hstep' .zero, hst1, hh1, hc1, hin1, hw1⟩
  | succ h ih =>
    intro c hst hcW hhead hin hwk
    have hread_ne : c.output.read ≠ Γ.start := by
      simp only [Tape.read, hhead, hcW]
      exact hWns (h + 1) (by omega)
    have hstep : ∃ c₁, (negOutTM (n := n)).step c = some c₁ ∧
        c₁.state = NegOutPhase.rewind ∧
        c₁.output.head = h ∧ c₁.output.cells = W ∧
        c₁.input = inp₀ ∧ c₁.work = work₀ := by
      simp only [TM.step, ↓reduceIte, hst, negOutTM, hread_ne]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · dsimp only []
        simp only [Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
      · dsimp only []
        rw [negOut_writeBack_cells _ _ hread_ne, hcW]
      · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
      · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)
    obtain ⟨c₁, hstep', hst1, hh1, hc1, hin1, hw1⟩ := hstep
    obtain ⟨c', hreach, hst', hh', hc', hin', hw'⟩ := ih c₁ hst1 hc1 hh1 hin1 hw1
    exact ⟨c', .step hstep' hreach, hst', hh', hc', hin', hw'⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase B: buffer step at cell 1 (contents preserved)
-- ════════════════════════════════════════════════════════════════════════

/-- Buffer step: from state `goRight` with output head at 1, one step reaches
    state `write` with the output tape exactly unchanged. -/
private theorem negOutTM_goRight_step
    (inp₀ : Tape) (work₀ : Fin n → Tape) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hw : ∀ i, (work₀ i).read ≠ Γ.start)
    (c : Cfg n (negOutTM (n := n)).Q)
    (hst : c.state = NegOutPhase.goRight)
    (hcW : c.output.cells = W) (hhead : c.output.head = 1)
    (hin : c.input = inp₀) (hwk : c.work = work₀) :
    ∃ c', (negOutTM (n := n)).step c = some c' ∧
      c'.state = NegOutPhase.write ∧
      c'.output = c.output ∧
      c'.input = inp₀ ∧ c'.work = work₀ := by
  have hread_ne : c.output.read ≠ Γ.start := by
    simp only [Tape.read, hhead, hcW]
    exact hWns 1 le_rfl
  simp only [TM.step, hst, negOutTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
  · dsimp only []; exact transitionTape_eq_self hread_ne
  · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
  · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)

-- ════════════════════════════════════════════════════════════════════════
-- Phase C: the negating write step
-- ════════════════════════════════════════════════════════════════════════

/-- Write step: from state `write` with output head at 1, one step halts with
    output cell 1 replaced by the binary negation of `W 1 = Γ.one`, the head
    still at 1, and the input/work tapes exactly unchanged. -/
private theorem negOutTM_write_step
    (inp₀ : Tape) (work₀ : Fin n → Tape) (W : ℕ → Γ)
    (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hw : ∀ i, (work₀ i).read ≠ Γ.start)
    (c : Cfg n (negOutTM (n := n)).Q)
    (hst : c.state = NegOutPhase.write)
    (hcW : c.output.cells = W) (hhead : c.output.head = 1)
    (hin : c.input = inp₀) (hwk : c.work = work₀) :
    ∃ c', (negOutTM (n := n)).step c = some c' ∧
      (negOutTM (n := n)).halted c' ∧
      c'.output.head = 1 ∧
      c'.output.cells = Function.update W 1
        (if W 1 = Γ.one then Γ.zero else Γ.one) ∧
      c'.input = inp₀ ∧ c'.work = work₀ := by
  have hread : c.output.read = W 1 := by
    simp [Tape.read, hhead, hcW]
  have hread_ne : c.output.read ≠ Γ.start := by
    rw [hread]; exact hWns 1 le_rfl
  have hoDir : idleDir c.output.read = Dir3.stay := by
    simp [idleDir, hread_ne]
  simp only [TM.step, hst, negOutTM]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only []
    simp only [hoDir, Tape.writeAndMove, Tape.move, Tape.write_head, hhead]
  · dsimp only []
    rw [hread]
    by_cases hone : W 1 = Γ.one
    · simp [idleDir, Tape.writeAndMove, Tape.move, Tape.write, hhead, hcW, hone]
    · simp [idleDir, Tape.writeAndMove, Tape.move, Tape.write, hhead, hcW, hone,
            hWns 1 le_rfl]
  · dsimp only []; rw [hin]; exact transitionInput_eq_self hinp
  · dsimp only []; rw [hwk]; funext i; exact transitionTape_eq_self (hw i)

-- ════════════════════════════════════════════════════════════════════════
-- Main HoareTime theorem
-- ════════════════════════════════════════════════════════════════════════

/-- **`negOutTM` specification** (ghost form, exact frames). Starting from
    pinned tapes `inp₀`/`work₀`/`out₀` with a well-formed output tape (cell 0
    is `▷`, no `▷` at cells ≥ 1, head ≤ `B`) and no tape head resting on `▷`,
    `negOutTM` halts within `B + 3` steps having replaced output cell 1 with
    the binary negation of "cell 1 = `1`" (`1 ↦ 0`; `0`/`□ ↦ 1`), all other
    output cells unchanged, output head parked at cell 1, and the input and
    work tapes exactly unchanged. -/
theorem negOutTM_hoareTime (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (B : ℕ)
    (h0 : out₀.cells 0 = Γ.start) (hns : ∀ j, 1 ≤ j → out₀.cells j ≠ Γ.start)
    (hB : out₀.head ≤ B)
    (hinp : inp₀.read ≠ Γ.start) (hw : ∀ i, (work₀ i).read ≠ Γ.start) :
    (negOutTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧
        out.cells = Function.update out₀.cells 1
          (if out₀.cells 1 = Γ.one then Γ.zero else Γ.one) ∧
        out.head = 1)
      (B + 3) := by
  intro inp work out ⟨hinp_eq, hwork_eq, hout_eq⟩
  subst inp; subst work; subst out
  -- Phase A: rewind the output head to ▷, then step right to cell 1
  obtain ⟨c₁, hr1, hst1, hh1, hc1, hin1, hw1⟩ :=
    negOutTM_rewind_loop inp₀ work₀ out₀.cells h0 hns hinp hw out₀.head
      { state := NegOutPhase.rewind, input := inp₀, work := work₀, output := out₀ }
      rfl rfl rfl rfl rfl
  -- Phase B: buffer step at cell 1 (output preserved)
  obtain ⟨c₂, hs2, hst2, hout2, hin2, hw2⟩ :=
    negOutTM_goRight_step inp₀ work₀ out₀.cells hns hinp hw c₁ hst1 hc1 hh1 hin1 hw1
  -- Phase C: negating write step
  obtain ⟨c₃, hs3, hhalt, hh3, hc3, hin3, hw3⟩ :=
    negOutTM_write_step inp₀ work₀ out₀.cells hns hinp hw c₂ hst2
      (by rw [hout2, hc1]) (by rw [hout2, hh1]) hin2 hw2
  exact ⟨c₃, (out₀.head + 1) + 1 + 1, by omega,
    reachesIn_trans _ (reachesIn_trans _ hr1 (.step hs2 .zero)) (.step hs3 .zero),
    hhalt, hin3, hw3, hc3, hh3⟩

end TM

end Complexity
