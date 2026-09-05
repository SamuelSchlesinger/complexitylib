/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Clock

/-!
# Frontier-seeking clock machine for the time-bounded universal machine

Clock initialization delivers the canonical register tape
`regTape V = ⟨1, regCells V⟩` on the clock tape (`clkT` = work tape 6 of a
`TM 7`): head parked at cell 1. The clocked universal loop
(`clocked_loop_simulates` in `SimClocked.lean`) instead wants the
**frontier-parked** form of `ClockFrontier.lean`: cells `regCells V`, head
at `max V 1`. `seekFrontierTM` bridges the two: starting at cell 1, it
walks right over the unary `1` marks to the last mark (the frontier), or
halts immediately at cell 1 when the clock is zero (frontier read `□`).

Spec: `seekFrontierTM_hoareTime` (ghost-initial-tapes style), `V + 3`
steps, every other tape exactly preserved. Behavior from head 1 on
`regTape V`:

- `V = 0`: cell 1 reads `□`, halt in 1 step, head stays at `1 = max 0 1`.
- `V ≥ 1`: cell 1 reads `1`, step right into `walk`; walk right while
  reading `1`; at cell `V + 1` read `□` and step **left** onto the
  frontier `V = max V 1`, halting. Total `V + 1` steps.
-/


public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Tape helper: write-back plus an arbitrary move
-- ════════════════════════════════════════════════════════════════════════

/-- Writing back the currently read non-`▷` symbol and then moving is the
    same as just moving. The moving analogue of
    `Tape.writeAndMove_readBack_idle_of_ne_start`. -/
private theorem writeAndMove_readBack_move (t : Tape)
    (hread : t.read ≠ Γ.start) (d : Dir3) :
    t.writeAndMove (readBackWrite t.read) d = t.move d := by
  show (t.write (readBackWrite t.read).toΓ).move d = t.move d
  congr 1
  rw [toΓ_readBackWrite_of_ne_start hread, Tape.write]
  split
  · rfl
  · simp only [Tape.read, Function.update_eq_self]

-- ════════════════════════════════════════════════════════════════════════
-- seekFrontierTM: walk the clock head from cell 1 to the frontier
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `seekFrontierTM`. -/
inductive SeekFrontierPhase where
  | first | walk | done
  deriving DecidableEq

instance : Fintype SeekFrontierPhase where
  elems := {.first, .walk, .done}
  complete := fun x => by cases x <;> simp

/-- **Frontier seek**: with the clock head at cell 1 of the canonical
    register tape `regTape V`, reading `□` (`V = 0`) halts immediately;
    reading any mark (`V ≥ 1`) steps right into `walk`, which walks right
    over the `1` marks and, on the first `□` (cell `V + 1`), steps left
    onto the frontier mark at cell `V` and halts. All other tapes idle
    throughout. -/
def seekFrontierTM : TM 7 where
  Q := SeekFrontierPhase
  qstart := .first
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .first =>
      if wHeads clkT = Γ.blank then
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.walk, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .walk =>
      if wHeads clkT = Γ.one then
        (.walk, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then
             (if wHeads clkT = Γ.start then Dir3.right else Dir3.left)
           else idleDir (wHeads i),
         idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .first =>
      dsimp only []
      split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .walk =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir
          rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ── step lemmas ──

private theorem seekFrontier_ne_halt {s : SeekFrontierPhase} (h : s ≠ .done)
    {c : Cfg 7 seekFrontierTM.Q} (hst : c.state = s) :
    ¬ c.state = seekFrontierTM.qhalt := by
  rw [hst]
  show ¬ s = SeekFrontierPhase.done
  exact h

/-- `first` on a blank (zero clock): halt immediately; nothing changes. -/
private theorem seekFrontier_step_first_blank (c : Cfg 7 seekFrontierTM.Q)
    (hst : c.state = .first) (hblank : (c.work clkT).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    seekFrontierTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (seekFrontier_ne_halt (by decide) hst)]
  simp only [seekFrontierTM, hst, hblank, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (by rw [hblank]; decide)
    · exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `first` on a mark (`V ≥ 1`): step right into `walk`. -/
private theorem seekFrontier_step_first_one (c : Cfg 7 seekFrontierTM.Q)
    (hst : c.state = .first) (hone : (c.work clkT).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    seekFrontierTM.step c = some
      { state := .walk, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (seekFrontier_ne_halt (by decide) hst)]
  simp only [seekFrontierTM, hst, hone, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      exact writeAndMove_readBack_move _ (by rw [hone]; decide) _
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `walk` on a mark: keep walking right. -/
private theorem seekFrontier_step_walk_one (c : Cfg 7 seekFrontierTM.Q)
    (hst : c.state = .walk) (hone : (c.work clkT).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    seekFrontierTM.step c = some
      { state := .walk, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (seekFrontier_ne_halt (by decide) hst)]
  simp only [seekFrontierTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      exact writeAndMove_readBack_move _ (by rw [hone]; decide) _
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `walk` on the first blank (cell `V + 1`): step left onto the frontier
    and halt. -/
private theorem seekFrontier_step_walk_blank (c : Cfg 7 seekFrontierTM.Q)
    (hst : c.state = .walk) (hblank : (c.work clkT).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    seekFrontierTM.step c = some
      { state := .done, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (seekFrontier_ne_halt (by decide) hst)]
  simp only [seekFrontierTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      exact writeAndMove_readBack_move _ (by rw [hblank]; decide) _
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

-- ── walk loop ──

/-- **Walk loop**: in state `walk` with the clock tape holding `regCells V`
    and its head at cell `V + 1 - k` (so `k` marks-plus-blank remain, with
    `k ≤ V - 1` keeping the head ≥ 2), the machine reaches `done` in
    exactly `k + 1` steps with the clock head on the frontier `V` and every
    other tape exactly preserved. -/
private theorem seekFrontier_walk_loop (V : ℕ) :
    ∀ (k : ℕ) (c : Cfg 7 seekFrontierTM.Q),
      c.state = .walk →
      (c.work clkT).cells = regCells V →
      (c.work clkT).head = V + 1 - k →
      k ≤ V - 1 → 1 ≤ V →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      ∃ c', seekFrontierTM.reachesIn (k + 1) c c' ∧
        c'.state = .done ∧
        c'.input = c.input ∧
        (∀ i, i ≠ clkT → c'.work i = c.work i) ∧
        (c'.work clkT).cells = regCells V ∧
        (c'.work clkT).head = V ∧
        c'.output = c.output := by
  intro k
  induction k with
  | zero =>
    intro c hst hcells hhead hk hV hinp hoth hout
    -- head at `V + 1`: read `□`, one left step onto the frontier
    have hblank : (c.work clkT).read = Γ.blank := by
      rw [Tape.read, hhead, hcells]
      exact regCells_blank (by omega)
    have hstep := seekFrontier_step_walk_blank c hst hblank hinp hoth hout
    refine ⟨_, .step hstep .zero, rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      exact Function.update_of_ne hi _ _
    · show (Function.update c.work clkT ((c.work clkT).move .left) clkT).cells = _
      rw [Function.update_self, Tape.move_cells]
      exact hcells
    · show (Function.update c.work clkT ((c.work clkT).move .left) clkT).head = V
      rw [Function.update_self]
      show (c.work clkT).head - 1 = V
      omega
  | succ k ih =>
    intro c hst hcells hhead hk hV hinp hoth hout
    -- head at `V - k ∈ [2, V]`: read `1`, step right, recurse
    have hone : (c.work clkT).read = Γ.one := by
      rw [Tape.read, hhead, hcells]
      exact regCells_one (by omega) (by omega)
    have hstep := seekFrontier_step_walk_one c hst hone hinp hoth hout
    obtain ⟨c', hreach, hst', hin', hoth', hcl', hhd', hout'⟩ :=
      ih { state := .walk, input := c.input,
           work := Function.update c.work clkT ((c.work clkT).move .right),
           output := c.output }
        rfl
        (by show (Function.update c.work clkT ((c.work clkT).move .right) clkT).cells = _
            rw [Function.update_self, Tape.move_cells]
            exact hcells)
        (by show (Function.update c.work clkT ((c.work clkT).move .right) clkT).head = _
            rw [Function.update_self]
            show (c.work clkT).head + 1 = V + 1 - k
            omega)
        (by omega) hV hinp
        (fun i hi => by
          show (Function.update c.work clkT ((c.work clkT).move .right) i).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
    refine ⟨c', .step hstep hreach, hst', hin', ?_, hcl', hhd', hout'⟩
    intro i hi
    exact (hoth' i hi).trans (Function.update_of_ne hi _ _)

-- ── main theorem ──

/-- **`seekFrontierTM` specification** (ghost-initial-tapes style).
    Starting from `qstart` with the clock tape (`clkT` = work tape 6)
    holding the canonical register tape `regTape V` (cells `regCells V`, head
    at cell 1), and every other tape parked on a non-`▷` symbol,
    `seekFrontierTM` halts within `V + 3` steps having walked the clock
    head to the frontier (`max V 1`) with the cells untouched; the input
    tape, the output tape, and every other work tape are preserved
    **exactly**. -/
theorem seekFrontierTM_hoareTime (V : ℕ) (inp₀ : Tape) (work₀ : Fin 7 → Tape)
    (out₀ : Tape)
    (hclk : work₀ clkT = regTape V)
    (hinp : inp₀.read ≠ Γ.start)
    (hothers : ∀ i, i ≠ clkT → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    seekFrontierTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧
        (∀ i, i ≠ clkT → work i = work₀ i) ∧
        (work clkT).cells = regCells V ∧ (work clkT).head = max V 1 ∧
        out = out₀)
      (V + 3) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  rcases Nat.eq_zero_or_pos V with rfl | hV
  · -- ── zero clock: cell 1 reads `□`; one idle step into `done` ──
    have hblank : (work clkT).read = Γ.blank := by
      rw [hclk]
      show regCells 0 1 = Γ.blank
      exact regCells_blank le_rfl
    have hstep := seekFrontier_step_first_blank
      { state := seekFrontierTM.qstart, input := inp, work := work, output := out }
      rfl hblank hinp hothers hout
    exact ⟨_, 1, by omega, .step hstep .zero, rfl, rfl, fun i _ => rfl,
      by show (work clkT).cells = regCells 0; rw [hclk, regT_cells],
      by show (work clkT).head = max 0 1; rw [hclk, regT_head]; decide, rfl⟩
  · -- ── positive clock: step right into `walk`, walk to the frontier ──
    have hone : (work clkT).read = Γ.one := by
      rw [hclk]
      show regCells V 1 = Γ.one
      exact regCells_one le_rfl hV
    have hstep := seekFrontier_step_first_one
      { state := seekFrontierTM.qstart, input := inp, work := work, output := out }
      rfl hone hinp hothers hout
    obtain ⟨c', hreach, hst', hin', hoth', hcl', hhd', hout'⟩ :=
      seekFrontier_walk_loop V (V - 1)
        { state := .walk, input := inp,
          work := Function.update work clkT ((work clkT).move .right),
          output := out }
        rfl
        (by show (Function.update work clkT ((work clkT).move .right) clkT).cells = _
            rw [Function.update_self, Tape.move_cells, hclk, regT_cells])
        (by show (Function.update work clkT ((work clkT).move .right) clkT).head = _
            rw [Function.update_self]
            show (work clkT).head + 1 = V + 1 - (V - 1)
            rw [hclk, regT_head]
            omega)
        le_rfl hV hinp
        (fun i hi => by
          show (Function.update work clkT ((work clkT).move .right) i).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hothers i hi)
        hout
    refine ⟨c', V - 1 + 1 + 1, by omega, .step hstep hreach, hst', hin',
      ?_, hcl', ?_, hout'⟩
    · intro i hi
      exact (hoth' i hi).trans (Function.update_of_ne hi _ _)
    · rw [hhd']
      exact (max_eq_left hV).symm

end TM

end Complexity
