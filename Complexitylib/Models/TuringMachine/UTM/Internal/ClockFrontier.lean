/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.UTM.Clock

/-!
# Frontier-parked clock machines for the time-bounded universal machine

Frontier variants of `decClockTM` / `zeroTestTM` (see `Clock.lean`): to make
each clock tick O(1), the clock head stays parked **at the frontier** (the
last unary mark) between ticks, rather than rewinding to cell 1.

**Frontier representation**: clock value `v` ⟺ tape-6 (`clkT`) cells are
`regCells v` and the head is at `max v 1`. At `v = 0` the head sits at
cell 1 reading `□`; at `v ≥ 1` it sits at cell `v` reading `1`.

Two `TM 7` machines, both with ghost-initial-tapes `HoareTime` specs:

- `decFrontierTM` — one O(1) decrement: blank the mark under the head, move
  left, then settle (when the head lands on `▷`, i.e. `v = 1 → 0`, the
  settle step is forced right onto cell 1; otherwise it stays on the new
  frontier mark). The zero clock is left unchanged in one idle step.
  Spec: `decFrontierTM_hoareTime`, 3 steps, every other tape exactly
  preserved.
- `orZeroTM` — the combined loop-exit test, run right after the (lifted)
  halt test has left its verdict at output cell 1 with the output head at 1:
  overwrite output cell 1 with `1` if the verdict is `1` **or** the clock is
  zero (frontier read `□`), else `0`, keeping the output head at 1.
  Spec: `orZeroTM_hoareTime`, 2 steps. The verdict must be a non-`▷` symbol
  (`hverdns`): reading `▷` at the output head would force a right move via
  `δ_right_of_start`, making `out.head = 1` unachievable.
-/


public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- regCells frontier helpers
-- ════════════════════════════════════════════════════════════════════════

/-- Blanking the frontier mark turns `regCells v` into `regCells (v - 1)`. -/
private theorem regCells_update {v : ℕ} (hv : 1 ≤ v) :
    Function.update (regCells v) v Γ.blank = regCells (v - 1) := by
  funext j
  rw [Function.update_apply]
  split
  · next hj =>
    subst hj
    exact (regCells_blank (by omega)).symm
  · next hj =>
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rfl
    · rcases Nat.lt_or_ge (v - 1) j with hlt | hge
      · rw [regCells_blank (by omega), regCells_blank (by omega)]
      · rw [regCells_one (by omega) (by omega), regCells_one (by omega) (by omega)]

-- ════════════════════════════════════════════════════════════════════════
-- decFrontierTM: O(1) decrement of the frontier-parked clock on tape 6
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `decFrontierTM`. -/
inductive DecFrontierPhase where
  | dec | settle | done
  deriving DecidableEq

instance : Fintype DecFrontierPhase where
  elems := {.dec, .settle, .done}
  complete := fun x => by cases x <;> simp

/-- **Frontier decrement**: with the clock head parked at the frontier
    (`max v 1`), reading `1` (`v ≥ 1`) blanks the mark and moves left; the
    settle step then either steps right off `▷` (was at cell 1, `v = 1 → 0`)
    or stays on the new frontier mark (`v ≥ 2`). Reading `□` (`v = 0`) halts
    immediately — decrement of zero is a no-op. All other tapes idle
    throughout. -/
def decFrontierTM : TM 7 where
  Q := DecFrontierPhase
  qstart := .dec
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .dec =>
      if wHeads clkT = Γ.one then
        (.settle, fun i => if i = clkT then Γw.blank else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = clkT then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
      else
        (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .settle =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .dec =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
    | .settle =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ── step lemmas ──

private theorem decFrontier_ne_halt {s : DecFrontierPhase} (h : s ≠ .done)
    {c : Cfg 7 decFrontierTM.Q} (hst : c.state = s) :
    ¬ c.state = decFrontierTM.qhalt := by
  rw [hst]
  show ¬ s = DecFrontierPhase.done
  exact h

/-- `dec` on the frontier mark: blank it and move left into `settle`. -/
private theorem decFrontier_step_dec_one (c : Cfg 7 decFrontierTM.Q)
    (hst : c.state = .dec) (hone : (c.work clkT).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decFrontierTM.step c = some
      { state := .settle, input := c.input,
        work := Function.update c.work clkT
          (((c.work clkT).write Γw.blank).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decFrontier_ne_halt (by decide) hst)]
  simp only [decFrontierTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `dec` on a blank (zero clock): halt immediately; nothing changes. -/
private theorem decFrontier_step_dec_blank (c : Cfg 7 decFrontierTM.Q)
    (hst : c.state = .dec) (hblank : (c.work clkT).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decFrontierTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (decFrontier_ne_halt (by decide) hst)]
  simp only [decFrontierTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (by rw [hblank]; decide)
    · exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `settle` on the new frontier mark (`v ≥ 2`): stay and halt. -/
private theorem decFrontier_step_settle_stay (c : Cfg 7 decFrontierTM.Q)
    (hst : c.state = .settle)
    (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decFrontierTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (decFrontier_ne_halt (by decide) hst)]
  simp only [decFrontierTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `settle` on the sentinel (`v = 1 → 0`): forced right onto cell 1, halt. -/
private theorem decFrontier_step_settle_start (c : Cfg 7 decFrontierTM.Q)
    (hst : c.state = .settle) (hs : (c.work clkT).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work clkT).cells j ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decFrontierTM.step c = some
      { state := .done, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } := by
  have h0 : (c.work clkT).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (decFrontier_ne_halt (by decide) hst)]
  simp only [decFrontierTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      rw [Function.update_self]
      show (c.work clkT).writeAndMove (readBackWrite (c.work clkT).read)
        (idleDir (c.work clkT).read) = (c.work clkT).move .right
      rw [hs]
      show ((c.work clkT).write Γw.blank).move Dir3.right
        = (c.work clkT).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

-- ── main theorem ──

/-- **`decFrontierTM` specification** (ghost-initial-tapes style). Starting
    from `qstart` with the clock tape (`clkT` = work tape 6) holding
    `regCells v` with its head parked at the frontier (`max v 1`), and every
    other tape parked on a non-`▷` symbol, `decFrontierTM` halts within 3
    steps having decremented the clock to `regCells (v - 1)` with the head
    parked at the new frontier (`max (v - 1) 1`); the input tape, the output
    tape, and every other work tape are preserved **exactly**. The zero
    clock is left unchanged (`0 - 1 = 0`). -/
theorem decFrontierTM_hoareTime (v : ℕ) (inp₀ : Tape) (work₀ : Fin 7 → Tape)
    (out₀ : Tape)
    (hclk : (work₀ clkT).cells = regCells v) (hclkh : (work₀ clkT).head = max v 1)
    (hinp : inp₀.read ≠ Γ.start)
    (hwork : ∀ i : Fin 7, i ≠ clkT → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    decFrontierTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ (∀ i : Fin 7, i ≠ clkT → work i = work₀ i) ∧
        (work clkT).cells = regCells (v - 1) ∧ (work clkT).head = max (v - 1) 1 ∧
        out = out₀)
      3 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · -- ── zero clock: reading `□` at cell 1; one idle step into `done` ──
    have hblank : (work clkT).read = Γ.blank := by
      rw [Tape.read, hclkh, hclk]
      exact regCells_blank (le_max_right 0 1)
    have hstep := decFrontier_step_dec_blank
      { state := decFrontierTM.qstart, input := inp, work := work, output := out }
      rfl hblank hinp hwork hout
    exact ⟨_, 1, by omega, .step hstep .zero, rfl, rfl, fun i _ => rfl, hclk,
      hclkh, rfl⟩
  · -- ── positive clock: blank the frontier mark, move left, settle ──
    have hhead : (work clkT).head = v := by
      rw [hclkh]; exact max_eq_left hv
    have hone : (work clkT).read = Γ.one := by
      rw [Tape.read, hhead, hclk]
      exact regCells_one hv le_rfl
    have hstep₁ := decFrontier_step_dec_one
      { state := decFrontierTM.qstart, input := inp, work := work, output := out }
      rfl hone hinp hwork hout
    set t₁ : Tape := ((work clkT).write Γw.blank).move .left
    have ht₁cells : t₁.cells = regCells (v - 1) := by
      show ((work clkT).write Γw.blank).cells = _
      rw [Tape.write, ite_eq_right (show ¬ (work clkT).head = 0 by rw [hhead]; omega)]
      show Function.update (work clkT).cells (work clkT).head Γw.blank.toΓ = _
      rw [hclk, hhead]
      exact regCells_update hv
    have ht₁head : t₁.head = v - 1 := by
      show ((work clkT).write Γw.blank).head - 1 = _
      rw [Tape.write_head, hhead]
    have hoth₁ : ∀ i : Fin 7, i ≠ clkT →
        ((Function.update work clkT t₁) i).read ≠ Γ.start := fun i hi => by
      rw [Function.update_of_ne hi]; exact hwork i hi
    rcases Nat.lt_or_ge v 2 with hv2 | hv2
    · -- ── `v = 1`: settle sees the sentinel and is forced right to cell 1 ──
      have hs : (Function.update work clkT t₁ clkT).read = Γ.start := by
        rw [Tape.read, Function.update_self, ht₁head, ht₁cells,
          show v - 1 = 0 by omega]
        rfl
      have hcr : ∀ j, 1 ≤ j →
          ((Function.update work clkT t₁) clkT).cells j ≠ Γ.start := by
        intro j hj
        rw [Function.update_self, ht₁cells]
        exact regCells_ne_start hj
      have hstep₂ := decFrontier_step_settle_start
        { state := .settle, input := inp, work := Function.update work clkT t₁,
          output := out } rfl hs hcr hinp hoth₁ hout
      refine ⟨_, 2, by omega, .step hstep₁ (.step hstep₂ .zero), rfl, rfl,
        ?_, ?_, ?_, rfl⟩
      · intro i hi
        show Function.update (Function.update work clkT t₁) clkT
          ((Function.update work clkT t₁ clkT).move .right) i = work i
        rw [Function.update_of_ne hi, Function.update_of_ne hi]
      · show (Function.update (Function.update work clkT t₁) clkT
          ((Function.update work clkT t₁ clkT).move .right) clkT).cells = _
        rw [Function.update_self, Function.update_self]
        show t₁.cells = _
        exact ht₁cells
      · show (Function.update (Function.update work clkT t₁) clkT
          ((Function.update work clkT t₁ clkT).move .right) clkT).head = _
        rw [Function.update_self, Function.update_self]
        show t₁.head + 1 = max (v - 1) 1
        rw [ht₁head, max_eq_right (show v - 1 ≤ 1 by omega)]
        omega
    · -- ── `v ≥ 2`: settle stays on the new frontier mark ──
      have hone₁ : ((Function.update work clkT t₁) clkT).read = Γ.one := by
        rw [Tape.read, Function.update_self, ht₁head, ht₁cells]
        exact regCells_one (by omega) le_rfl
      have hall : ∀ i : Fin 7, ((Function.update work clkT t₁) i).read ≠ Γ.start := by
        intro i
        by_cases hir : i = clkT
        · subst hir
          rw [hone₁]
          decide
        · exact hoth₁ i hir
      have hstep₂ := decFrontier_step_settle_stay
        { state := .settle, input := inp, work := Function.update work clkT t₁,
          output := out } rfl hinp hall hout
      refine ⟨_, 2, by omega, .step hstep₁ (.step hstep₂ .zero), rfl, rfl,
        ?_, ?_, ?_, rfl⟩
      · intro i hi
        show Function.update work clkT t₁ i = work i
        rw [Function.update_of_ne hi]
      · show (Function.update work clkT t₁ clkT).cells = _
        rw [Function.update_self]
        exact ht₁cells
      · show (Function.update work clkT t₁ clkT).head = _
        rw [Function.update_self, ht₁head,
          max_eq_left (show 1 ≤ v - 1 by omega)]

-- ════════════════════════════════════════════════════════════════════════
-- orZeroTM: the combined loop-exit test (halt verdict OR clock zero)
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `orZeroTM`. -/
inductive OrZeroPhase where
  | test | done
  deriving DecidableEq

instance : Fintype OrZeroPhase where
  elems := {.test, .done}
  complete := fun x => by cases x <;> simp

/-- **Combined loop-exit test**: read output cell 1 (the halt-test verdict,
    head parked at 1) and the frontier-parked clock tape; overwrite output
    cell 1 with `1` if the verdict is `1` **or** the clock reads `□` (i.e.
    is zero), else `0`, keeping the output head at cell 1; then halt. Every
    work tape and the input tape idle. -/
def orZeroTM : TM 7 where
  Q := OrZeroPhase
  qstart := .test
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .test =>
      (.done, fun i => readBackWrite (wHeads i),
       (if oHead = Γ.one ∨ wHeads clkT = Γ.blank then Γw.one else Γw.zero),
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .test =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

private theorem orZero_ne_halt {c : Cfg 7 orZeroTM.Q}
    (hst : c.state = .test) : ¬ c.state = orZeroTM.qhalt := by
  rw [hst]
  show ¬ OrZeroPhase.test = OrZeroPhase.done
  decide

/-- The single working step of `orZeroTM`: write the combined verdict at the
    output head and halt; everything else is exactly preserved. -/
private theorem orZero_step (c : Cfg 7 orZeroTM.Q)
    (hst : c.state = .test)
    (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hh0 : ¬ c.output.head = 0)
    (hor : c.output.read ≠ Γ.start) :
    orZeroTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := { head := c.output.head,
                    cells := Function.update c.output.cells c.output.head
                      ((if c.output.read = Γ.one ∨ (c.work clkT).read = Γ.blank
                        then Γw.one else Γw.zero) : Γw).toΓ } } := by
  rw [TM.step, ite_eq_right (orZero_ne_halt hst)]
  simp only [orZeroTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · show c.output.writeAndMove _ (idleDir c.output.read) = _
    rw [idleDir, ite_eq_right hor]
    show c.output.write _ = _
    rw [Tape.write, ite_eq_right hh0]

/-- **`orZeroTM` specification** (ghost-initial-tapes style). Starting from
    `qstart` with the clock tape (`clkT` = work tape 6) holding `regCells v`
    with its head parked at the frontier (`max v 1`), the output head
    resting at cell 1 on the halt-test verdict (a non-`▷` symbol), and every
    other tape parked on a non-`▷` symbol, `orZeroTM` halts within 2 steps
    having

    * written the combined loop-exit verdict at output cell 1: `Γ.one` iff
      `verdict = Γ.one ∨ v = 0`, else `Γ.zero` (all other output cells
      unchanged, head still at cell 1);
    * left the input tape and **every** work tape exactly unchanged. -/
theorem orZeroTM_hoareTime (v : ℕ) (verdict : Γ) (inp₀ : Tape)
    (work₀ : Fin 7 → Tape) (out₀ : Tape)
    (hclk : (work₀ clkT).cells = regCells v) (hclkh : (work₀ clkT).head = max v 1)
    (hverd : out₀.cells 1 = verdict) (hverdns : verdict ≠ Γ.start)
    (houth : out₀.head = 1)
    (hout0 : out₀.cells 0 = Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hwork : ∀ i : Fin 7, i ≠ clkT → (work₀ i).read ≠ Γ.start) :
    orZeroTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧
        out.cells = Function.update out₀.cells 1
          (if verdict = Γ.one ∨ v = 0 then Γ.one else Γ.zero) ∧
        out.head = 1)
      2 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hclkread : (work clkT).read = (if v = 0 then Γ.blank else Γ.one) := by
    rw [Tape.read, hclkh, hclk]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [ite_eq_left rfl]
      exact regCells_blank (le_max_right 0 1)
    · rw [ite_eq_right (by omega), max_eq_left hv]
      exact regCells_one hv le_rfl
  have hclkns : (work clkT).read ≠ Γ.start := by
    rw [hclkread]; split <;> decide
  have hall : ∀ i : Fin 7, (work i).read ≠ Γ.start := by
    intro i
    by_cases hir : i = clkT
    · subst hir; exact hclkns
    · exact hwork i hir
  have houtread : out.read = verdict := by rw [Tape.read, houth, hverd]
  have hstep := orZero_step
    { state := orZeroTM.qstart, input := inp, work := work, output := out }
    rfl hinp hall (by rw [houth]; omega) (by rw [houtread]; exact hverdns)
  have hcells_eq : Function.update out.cells out.head
      ((if out.read = Γ.one ∨ (work clkT).read = Γ.blank then Γw.one
        else Γw.zero) : Γw).toΓ
      = Function.update out.cells 1
          (if verdict = Γ.one ∨ v = 0 then Γ.one else Γ.zero) := by
    rw [houth, houtread, hclkread]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · have hv' : v ≠ 0 := by omega
      by_cases hverd1 : verdict = Γ.one <;> simp [hverd1, hv']
  exact ⟨_, 1, by omega, .step hstep .zero, rfl, rfl, rfl, hcells_eq, houth⟩

end TM

end Complexity
