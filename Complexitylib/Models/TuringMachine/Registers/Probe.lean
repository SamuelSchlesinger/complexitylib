/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Mathlib.Tactic.FinCases
public import Complexitylib.Models.TuringMachine.Registers.Emit
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

/-!
# symProbeTM: read the input symbol at a register-indexed position

`symProbeTM f r q` walks the input head to the cell indexed by register
`r` (lockstep over `r`'s marks), reads the symbol `s` there, adds
`(f s).val ≤ 3` marks to register `q`, and restores everything: the input
head returns to cell 1, `r` is untouched, `q` becomes `regTape (d + (f s))`.

This is the reduction emitter's only input-reading machine: the start
clauses of the tableau pin the input cells, so their symbol digits are
read off the input tape position by position.
-/


public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Control states of `symProbeTM`: walk out to the probed cell (`pre`, `walk`),
    rewind the input and register `r` carrying the read digit `k` (`backI k`,
    `backR k`), scan to the end of `q` and append `k` marks (`scanQ k`), then
    rewind `q` and park (`backQ`, `park`, `done`). -/
inductive ProbePhase where
  | pre | walk
  | backI (k : Fin 4) | backR (k : Fin 4) | scanQ (k : Fin 4)
  | backQ | park | done
  deriving DecidableEq

/-- `ProbePhase` is a finite type (17 states), as required for TM state sets. -/
instance : Fintype ProbePhase where
  elems := {.pre, .walk,
    .backI 0, .backI 1, .backI 2, .backI 3,
    .backR 0, .backR 1, .backR 2, .backR 3,
    .scanQ 0, .scanQ 1, .scanQ 2, .scanQ 3,
    .backQ, .park, .done}
  complete := fun x => by
    cases x with
    | backI k => fin_cases k <;> simp
    | backR k => fin_cases k <;> simp
    | scanQ k => fin_cases k <;> simp
    | _ => simp

/-- **Probe the input at the position held by `r`** and add `f`-of-the-symbol
    to `q`. All tapes restored except `q`. -/
def symProbeTM (f : Γ → Fin 4) (r q : Fin n) : TM n where
  Q := ProbePhase
  qstart := .pre
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .pre =>
      (.walk, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       if iHead = Γ.start then Dir3.right else Dir3.left,
       fun i => idleDir (wHeads i), idleDir oHead)
    | .walk =>
      if wHeads r = Γ.one then
        (.walk, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right,
         fun i => if i = r then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.backI (f iHead), fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         if iHead = Γ.start then Dir3.right else Dir3.left,
         fun i => if i = r then (if wHeads r = Γ.start then Dir3.right
                                 else Dir3.stay)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .backI k =>
      if iHead = Γ.start then
        (.backR k, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.backI k, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.left, fun i => idleDir (wHeads i), idleDir oHead)
    | .backR k =>
      if wHeads r = Γ.start then
        (.scanQ k, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = r then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.backR k, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = r then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .scanQ k =>
      if wHeads q = Γ.one then
        (.scanQ k, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        if k = 0 then
          (.backQ, fun i => readBackWrite (wHeads i), readBackWrite oHead,
           idleDir iHead,
           fun i => if i = q then (if wHeads q = Γ.start then Dir3.right
                                   else Dir3.left)
                    else idleDir (wHeads i),
           idleDir oHead)
        else
          (.scanQ ⟨k.val - 1, by omega⟩,
           fun i => if i = q then Γw.one else readBackWrite (wHeads i),
           readBackWrite oHead, idleDir iHead,
           fun i => if i = q then Dir3.right else idleDir (wHeads i),
           idleDir oHead)
    | .backQ =>
      if wHeads q = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = q then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.backQ, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = q then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .pre =>
      refine ⟨fun h => by rw [ite_eq_left h], fun i hi => idleDir_right_of_start hi,
        idleDir_right_of_start⟩
    | .walk =>
      dsimp only []
      split
      · next hone =>
        refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨fun h => by rw [ite_eq_left h], fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .backI k =>
      dsimp only []
      split
      · exact ⟨fun _ => rfl, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
      · next hns =>
        exact ⟨fun h => absurd h hns, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
    | .backR k =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = r
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .scanQ k =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hiq : i = q
        · subst hiq; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hiq]; exact idleDir_right_of_start hi
      · split
        · refine ⟨idleDir_right_of_start, fun i hi => ?_,
            idleDir_right_of_start⟩
          dsimp only []
          by_cases hiq : i = q
          · subst hiq; rw [ite_eq_left rfl, ite_eq_left hi]
          · rw [ite_eq_right hiq]; exact idleDir_right_of_start hi
        · refine ⟨idleDir_right_of_start, fun i hi => ?_,
            idleDir_right_of_start⟩
          dsimp only []
          by_cases hiq : i = q
          · rw [ite_eq_left hiq]
          · rw [ite_eq_right hiq]; exact idleDir_right_of_start hi
    | .backQ =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hiq : i = q
        · rw [ite_eq_left hiq]
        · rw [ite_eq_right hiq]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_,
          idleDir_right_of_start⟩
        dsimp only []
        by_cases hiq : i = q
        · subst hiq; exact absurd hi hns
        · rw [ite_eq_right hiq]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section Probe

variable {f : Γ → Fin 4} {r q : Fin n}

private theorem symProbeTM_ne_halt {s : ProbePhase} (h : s ≠ .done)
    {c : Cfg n (symProbeTM f r q).Q} (hst : c.state = s) :
    ¬ c.state = (symProbeTM f r q).qhalt := by
  rw [hst]
  show ¬ s = ProbePhase.done
  exact h

/-- Well-formed cells: `▷` exactly at cell 0. -/
private def StartInvariant (t : Tape) : Prop :=
  t.cells 0 = Γ.start ∧ ∀ j, 1 ≤ j → t.cells j ≠ Γ.start

private theorem StartInvariant.read_start_iff {t : Tape} (h : StartInvariant t) :
    t.read = Γ.start ↔ t.head = 0 := by
  constructor
  · intro hr
    by_contra hc
    exact h.2 t.head (by omega) hr
  · intro h0
    rw [Tape.read, h0]
    exact h.1

/-- `pre`: step the input head left off cell 1. -/
private theorem symProbeTM_step_pre (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .pre) (hi : c.input.read ≠ Γ.start)
    (hwork : ∀ i, Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .walk, input := c.input.move .left, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hi, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `walk` over a mark: both heads advance. -/
private theorem symProbeTM_step_walk_one (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .walk) (hone : (c.work r).read = Γ.one)
    (hwork : ∀ i, i ≠ r → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .walk, input := c.input.move .right,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `walk` at the first blank: record the input symbol, start rewinding the
    input; the register head stays. -/
private theorem symProbeTM_step_walk_blank (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .walk) (hblank : (c.work r).read = Γ.blank)
    (hwork : ∀ i, i ≠ r → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .backI (f c.input.read),
        input := c.input.move
          (if c.input.read = Γ.start then .right else .left),
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [writeAndMove_readBack _ (by rw [hblank]; decide), ite_eq_left rfl]
      rfl
    · rw [ite_eq_right hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `backI` off the sentinel: keep rewinding the input. -/
private theorem symProbeTM_step_backI_left {k : Fin 4}
    (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .backI k) (hi : c.input.read ≠ Γ.start)
    (hwork : ∀ i, Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .backI k, input := c.input.move .left, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hi, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `backI` on the sentinel: step the input right to cell 1. -/
private theorem symProbeTM_step_backI_start {k : Fin 4}
    (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .backI k) (hi : c.input.read = Γ.start)
    (hwork : ∀ i, Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .backR k, input := c.input.move .right, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hi, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `backR` off the sentinel: keep rewinding the register. -/
private theorem symProbeTM_step_backR_left {k : Fin 4}
    (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .backR k) (hns : (c.work r).read ≠ Γ.start)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ r → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .backR k, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `backR` on the sentinel: park the register head at cell 1. -/
private theorem symProbeTM_step_backR_start {k : Fin 4}
    (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .backR k) (hs : (c.work r).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ r → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .scanQ k, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  have h0 : (c.work r).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact (hwork i hir).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scanQ` over a mark. -/
private theorem symProbeTM_step_scanQ_one {k : Fin 4}
    (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .scanQ k) (hone : (c.work q).read = Γ.one)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .scanQ k, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hiq : i = q
    · subst hiq
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hiq, Function.update_of_ne hiq]
      exact (hwork i hiq).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scanQ 0` at the first blank: turn onto the last mark. -/
private theorem symProbeTM_step_scanQ_blank_zero
    (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .scanQ 0) (hblank : (c.work q).read = Γ.blank)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .backQ, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hiq : i = q
    · subst hiq
      rw [Function.update_self,
        writeAndMove_readBack _ (by rw [hblank]; decide), ite_eq_left rfl]
    · rw [ite_eq_right hiq, Function.update_of_ne hiq]
      exact (hwork i hiq).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `scanQ (k+1)` at the first blank: write a mark and continue scanning. -/
private theorem symProbeTM_step_scanQ_blank_succ {k : Fin 4}
    (c : Cfg n (symProbeTM f r q).Q) (hk : k ≠ 0)
    (hst : c.state = .scanQ k) (hblank : (c.work q).read = Γ.blank)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .scanQ ⟨k.val - 1, by omega⟩, input := c.input,
        work := Function.update c.work q
          (((c.work q).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hblank, reduceCtorEq, ↓reduceIte, hk]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hiq : i = q
    · subst hiq
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hiq, ite_eq_right hiq, Function.update_of_ne hiq]
      exact (hwork i hiq).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `backQ` off the sentinel. -/
private theorem symProbeTM_step_backQ_left (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .backQ) (hns : (c.work q).read ≠ Γ.start)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .backQ, input := c.input,
        work := Function.update c.work q ((c.work q).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hiq : i = q
    · subst hiq
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [ite_eq_right hiq, Function.update_of_ne hiq]
      exact (hwork i hiq).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `backQ` on the sentinel: park. -/
private theorem symProbeTM_step_backQ_start (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .backQ) (hs : (c.work q).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start)
    (hinp : Parked c.input)
    (hwork : ∀ i, i ≠ q → Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } := by
  have h0 : (c.work q).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    by_cases hiq : i = q
    · subst hiq
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hiq, Function.update_of_ne hiq]
      exact (hwork i hiq).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- `park`: one idle step into `done`. -/
private theorem symProbeTM_step_park (c : Cfg n (symProbeTM f r q).Q)
    (hst : c.state = .park) (hinp : Parked c.input)
    (hwork : ∀ i, Parked (c.work i)) (hout : Parked c.output) :
    (symProbeTM f r q).step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (symProbeTM_ne_halt (by simp) hst)]
  simp only [symProbeTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle


/-- The lockstep walk: register head and input head advance together. -/
private theorem symProbeTM_walk_run (pos : ℕ) : ∀ (m k : ℕ), pos = k + m →
    ∀ c : Cfg n (symProbeTM f r q).Q, c.state = .walk →
    (∀ i, i ≠ r → Parked (c.work i)) → Parked c.output →
    (c.work r).cells = regCells pos → (c.work r).head = k + 1 →
    c.input.head = k →
    ∃ c', (symProbeTM f r q).reachesIn m c c' ∧ c'.state = .walk ∧
      c'.input.cells = c.input.cells ∧ c'.input.head = pos ∧
      (∀ i, i ≠ r → c'.work i = c.work i) ∧
      (c'.work r).cells = regCells pos ∧ (c'.work r).head = pos + 1 ∧
      c'.output = c.output := by
  intro m
  induction m with
  | zero =>
    intro k hk c hst hwork hout hcells hhead hihead
    exact ⟨c, .zero, hst, rfl, by rw [hihead]; omega, fun _ _ => rfl, hcells,
      by rw [hhead]; omega, rfl⟩
  | succ m ih =>
    intro k hk c hst hwork hout hcells hhead hihead
    have hone : (c.work r).read = Γ.one := by
      rw [Tape.read, hhead, hcells]
      exact regCells_one (by omega) (by omega)
    have hstep := symProbeTM_step_walk_one c hst hone hwork hout
    obtain ⟨c', hreach, hst', hicells', hihead', hwork', hcells', hhead',
      hout'⟩ :=
      ih (k + 1) (by omega)
        { state := .walk, input := c.input.move .right,
          work := Function.update c.work r ((c.work r).move .right),
          output := c.output } rfl
        (fun i hi => by
          show Parked (Function.update c.work r ((c.work r).move .right) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by
          show (Function.update c.work r ((c.work r).move .right) r).cells = _
          rw [Function.update_self]
          exact hcells)
        (by
          show (Function.update c.work r ((c.work r).move .right) r).head = _
          rw [Function.update_self]
          show (c.work r).head + 1 = _
          rw [hhead])
        (by show c.input.head + 1 = k + 1; rw [hihead])
    refine ⟨c', .step hstep hreach, hst', ?_, hihead', ?_, hcells', hhead',
      hout'⟩
    · rw [hicells']
      rfl
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work r ((c.work r).move .right) i = c.work i
      rw [Function.update_of_ne hi]

/-- The input rewind: from head `h` back to cell 1, entering `backR`. -/
private theorem symProbeTM_backI_run {k : Fin 4} : ∀ (h : ℕ),
    ∀ c : Cfg n (symProbeTM f r q).Q, c.state = .backI k →
    StartInvariant c.input → c.input.head = h →
    (∀ i, Parked (c.work i)) → Parked c.output →
    ∃ c', (symProbeTM f r q).reachesIn (h + 1) c c' ∧
      c'.state = .backR k ∧ c'.input.cells = c.input.cells ∧
      c'.input.head = 1 ∧ c'.work = c.work ∧ c'.output = c.output := by
  intro h
  induction h with
  | zero =>
    intro c hst hwf hhead hwork hout
    have hs : c.input.read = Γ.start := hwf.read_start_iff.mpr hhead
    have hstep := symProbeTM_step_backI_start c hst hs hwork hout
    refine ⟨_, .step hstep .zero, rfl, rfl, ?_, rfl, rfl⟩
    show c.input.head + 1 = 1
    rw [hhead]
  | succ h ih =>
    intro c hst hwf hhead hwork hout
    have hns : c.input.read ≠ Γ.start := by
      rw [Tape.read, hhead]
      exact hwf.2 (h + 1) (by omega)
    have hstep := symProbeTM_step_backI_left c hst hns hwork hout
    obtain ⟨c', hreach, hst', hicells', hihead', hwork', hout'⟩ :=
      ih { state := .backI k, input := c.input.move .left, work := c.work,
           output := c.output } rfl
        ⟨hwf.1, hwf.2⟩
        (by show c.input.head - 1 = h; rw [hhead]; omega)
        hwork hout
    exact ⟨c', .step hstep hreach, hst', by rw [hicells']; rfl, hihead',
      hwork', hout'⟩

/-- The register rewind: from head `h` back to cell 1, entering `scanQ`. -/
private theorem symProbeTM_backR_run {k : Fin 4} : ∀ (h : ℕ),
    ∀ c : Cfg n (symProbeTM f r q).Q, c.state = .backR k →
    Parked c.input → (∀ i, i ≠ r → Parked (c.work i)) → Parked c.output →
    (c.work r).cells 0 = Γ.start →
    (∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start) →
    (c.work r).head = h →
    ∃ c', (symProbeTM f r q).reachesIn (h + 1) c c' ∧
      c'.state = .scanQ k ∧ c'.input = c.input ∧
      (∀ i, i ≠ r → c'.work i = c.work i) ∧
      (c'.work r).cells = (c.work r).cells ∧ (c'.work r).head = 1 ∧
      c'.output = c.output := by
  intro h
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work r).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep := symProbeTM_step_backR_start c hst hs hcr hinp hwork hout
    refine ⟨_, .step hstep .zero, rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work r ((c.work r).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work r ((c.work r).move .right) r).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work r ((c.work r).move .right) r).head = 1
      rw [Function.update_self]
      show (c.work r).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work r).read ≠ Γ.start := by
      rw [Tape.read, hhead]
      exact hcr (h + 1) (by omega)
    have hstep := symProbeTM_step_backR_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work r ((c.work r).move .left) r).cells
        = (c.work r).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .backR k, input := c.input,
           work := Function.update c.work r ((c.work r).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work r ((c.work r).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work r ((c.work r).move .left) r).head = h
          rw [Function.update_self]
          show (c.work r).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work r ((c.work r).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

/-- The target scan: walk `q`'s head over its marks. -/
private theorem symProbeTM_scanQ_run {k : Fin 4} (d : ℕ) :
    ∀ (m j : ℕ), d = j + m →
    ∀ c : Cfg n (symProbeTM f r q).Q, c.state = .scanQ k →
    Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) → Parked c.output →
    (c.work q).cells = regCells d → (c.work q).head = j + 1 →
    ∃ c', (symProbeTM f r q).reachesIn m c c' ∧
      c'.state = .scanQ k ∧ c'.input = c.input ∧
      (∀ i, i ≠ q → c'.work i = c.work i) ∧
      (c'.work q).cells = regCells d ∧ (c'.work q).head = d + 1 ∧
      c'.output = c.output := by
  intro m
  induction m with
  | zero =>
    intro j hj c hst hinp hwork hout hcells hhead
    exact ⟨c, .zero, hst, rfl, fun _ _ => rfl, hcells, by rw [hhead, hj], rfl⟩
  | succ m ih =>
    intro j hj c hst hinp hwork hout hcells hhead
    have hone : (c.work q).read = Γ.one := by
      rw [Tape.read, hhead, hcells]
      exact regCells_one (by omega) (by omega)
    have hstep := symProbeTM_step_scanQ_one c hst hone hinp hwork hout
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih (j + 1) (by omega)
        { state := .scanQ k, input := c.input,
          work := Function.update c.work q ((c.work q).move .right),
          output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .right) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by
          show (Function.update c.work q ((c.work q).move .right) q).cells = _
          rw [Function.update_self]
          exact hcells)
        (by
          show (Function.update c.work q ((c.work q).move .right) q).head = _
          rw [Function.update_self]
          show (c.work q).head + 1 = _
          rw [hhead])
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, hcells', hhead', hout'⟩
    intro i hi
    rw [hwork' i hi]
    show Function.update c.work q ((c.work q).move .right) i = c.work i
    rw [Function.update_of_ne hi]

/-- The write run: append `k.val` marks to `q`, counting the state down. -/
private theorem symProbeTM_write_run : ∀ (kv : ℕ) (k : Fin 4), k.val = kv →
    ∀ (e : ℕ) (c : Cfg n (symProbeTM f r q).Q), c.state = .scanQ k →
    Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) → Parked c.output →
    (c.work q).cells = regCells e → (c.work q).head = e + 1 →
    ∃ c', (symProbeTM f r q).reachesIn kv c c' ∧
      c'.state = .scanQ 0 ∧ c'.input = c.input ∧
      (∀ i, i ≠ q → c'.work i = c.work i) ∧
      (c'.work q).cells = regCells (e + kv) ∧
      (c'.work q).head = e + kv + 1 ∧
      c'.output = c.output := by
  intro kv
  induction kv with
  | zero =>
    intro k hk e c hst hinp hwork hout hcells hhead
    have hk0 : k = 0 := Fin.ext hk
    subst hk0
    exact ⟨c, .zero, hst, rfl, fun _ _ => rfl, hcells, by rw [hhead], rfl⟩
  | succ kv ih =>
    intro k hk e c hst hinp hwork hout hcells hhead
    have hkne : k ≠ 0 := by
      intro hc
      rw [hc] at hk
      exact absurd hk.symm (by omega)
    have hblank : (c.work q).read = Γ.blank := by
      rw [Tape.read, hhead, hcells]
      exact regCells_blank (by omega)
    have hstep := symProbeTM_step_scanQ_blank_succ c hkne hst hblank hinp
      hwork hout
    have hwcells : ((((c.work q).write Γw.one)).move .right).cells
        = regCells (e + 1) := by
      show ((c.work q).write Γw.one).cells = _
      rw [Tape.write, ite_eq_right (by rw [hhead]; omega)]
      show Function.update (c.work q).cells (c.work q).head Γw.one.toΓ = _
      rw [hcells, hhead]
      exact regCells_update_succ e
    have hwhead : ((((c.work q).write Γw.one)).move .right).head = e + 2 := by
      show ((c.work q).write Γw.one).head + 1 = e + 2
      have hwh : ((c.work q).write Γw.one).head = (c.work q).head := by
        rw [Tape.write]
        split <;> rfl
      rw [hwh, hhead]
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih ⟨k.val - 1, by omega⟩ (by show k.val - 1 = kv; omega) (e + 1)
        { state := .scanQ ⟨k.val - 1, by omega⟩, input := c.input,
          work := Function.update c.work q
            (((c.work q).write Γw.one).move .right),
          output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q _ i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by
          show (Function.update c.work q _ q).cells = _
          rw [Function.update_self]
          exact hwcells)
        (by
          show (Function.update c.work q _ q).head = _
          rw [Function.update_self]
          exact hwhead)
    refine ⟨c', .step hstep hreach, hst', hinp', ?_,
      by rw [hcells']; congr 1; omega,
      by rw [hhead']; omega, hout'⟩
    intro i hi
    rw [hwork' i hi]
    show Function.update c.work q _ i = c.work i
    rw [Function.update_of_ne hi]

/-- The final rewind: `q` back to cell 1, park, halt. -/
private theorem symProbeTM_backQ_run : ∀ (h : ℕ),
    ∀ c : Cfg n (symProbeTM f r q).Q, c.state = .backQ →
    Parked c.input → (∀ i, i ≠ q → Parked (c.work i)) → Parked c.output →
    (c.work q).cells 0 = Γ.start →
    (∀ j, 1 ≤ j → (c.work q).cells j ≠ Γ.start) →
    (c.work q).head = h →
    ∃ c', (symProbeTM f r q).reachesIn (h + 2) c c' ∧
      c'.state = .done ∧ c'.input = c.input ∧
      (∀ i, i ≠ q → c'.work i = c.work i) ∧
      (c'.work q).cells = (c.work q).cells ∧ (c'.work q).head = 1 ∧
      c'.output = c.output := by
  intro h
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work q).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep₁ := symProbeTM_step_backQ_start c hst hs hcr hinp hwork hout
    have hworkP : ∀ i,
        Parked (Function.update c.work q ((c.work q).move .right) i) := by
      intro i
      by_cases hiq : i = q
      · subst hiq
        rw [Function.update_self]
        exact ⟨by show (c.work i).head + 1 ≥ 1; omega, fun j hj => hcr j hj⟩
      · rw [Function.update_of_ne hiq]
        exact hwork i hiq
    have hstep₂ := symProbeTM_step_park (f := f) (r := r) (q := q)
      { state := .park, input := c.input,
        work := Function.update c.work q ((c.work q).move .right),
        output := c.output } rfl hinp hworkP hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work q ((c.work q).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work q ((c.work q).move .right) q).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work q ((c.work q).move .right) q).head = 1
      rw [Function.update_self]
      show (c.work q).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work q).read ≠ Γ.start := by
      rw [Tape.read, hhead]
      exact hcr (h + 1) (by omega)
    have hstep₁ := symProbeTM_step_backQ_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work q ((c.work q).move .left) q).cells
        = (c.work q).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .backQ, input := c.input,
           work := Function.update c.work q ((c.work q).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show Parked (Function.update c.work q ((c.work q).move .left) i)
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work q ((c.work q).move .left) q).head = h
          rw [Function.update_self]
          show (c.work q).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep₁ hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work q ((c.work q).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

/-- **`symProbeTM` Hoare specification.** Reads the input symbol at the
    position held by register `r` and adds its `f`-index to register `q`;
    the input (parked at cell 1), the register `r`, and every other tape are
    restored exactly. -/
theorem symProbeTM_hoareTime (f : Γ → Fin 4) (r q : Fin n) (hrq : r ≠ q)
    (pos d : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp₀ : Parked inp₀) (hhead : inp₀.head = 1)
    (hwf : inp₀.cells 0 = Γ.start)
    (hwork₀ : ∀ i, Parked (work₀ i))
    (hr : work₀ r = regTape pos) (hq : work₀ q = regTape d) :
    (symProbeTM f r q).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ q (regTape (d + (f (inp₀.cells pos)).val))) ys)
      (3 * pos + 2 * d + 20) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have hWF : StartInvariant inp := ⟨hwf, hinp₀.2⟩
  have hqr : q ≠ r := fun h => hrq h.symm
  have hstep₀ := symProbeTM_step_pre (f := f) (r := r) (q := q)
    { state := .pre, input := inp, work := work, output := out } rfl
    hinp₀.read_ne_start hwork₀ hout.parked
  obtain ⟨c₂, hreach₂, hst₂, hicells₂, hihead₂, hwork₂, hcells₂, hhead₂,
    hout₂⟩ :=
    symProbeTM_walk_run (f := f) (r := r) (q := q) pos pos 0 (by omega)
      { state := .walk, input := inp.move .left, work := work, output := out }
      rfl (fun i _ => hwork₀ i) hout.parked
      (by show (work r).cells = _; rw [hr, regT_cells])
      (by show (work r).head = 0 + 1; rw [hr, regT_head])
      (by show inp.head - 1 = 0; rw [hhead])
  have hic₂ : c₂.input.cells = inp.cells := by
    rw [hicells₂]
    rfl
  have hworkP₂ : ∀ i, i ≠ r → Parked (c₂.work i) := fun i hi => by
    rw [hwork₂ i hi]
    exact hwork₀ i
  have houtP₂ : Parked c₂.output := by rw [hout₂]; exact hout.parked
  have hs₂ : c₂.input.read = inp.cells pos := by
    rw [Tape.read, hihead₂, hic₂]
  have hblank₂ : (c₂.work r).read = Γ.blank := by
    rw [Tape.read, hhead₂, hcells₂]
    exact regCells_blank (by omega)
  have hstep₂ := symProbeTM_step_walk_blank c₂ hst₂ hblank₂ hworkP₂ houtP₂
  set c₃ : Cfg n (symProbeTM f r q).Q :=
    { state := .backI (f c₂.input.read),
      input := c₂.input.move
        (if c₂.input.read = Γ.start then .right else .left),
      work := c₂.work, output := c₂.output } with hc₃
  have hc₃st : c₃.state = .backI (f (inp.cells pos)) := by
    show ProbePhase.backI (f c₂.input.read) = _
    rw [hs₂]
  have hmovecells : ∀ (t : Tape) (dd : Dir3), (t.move dd).cells = t.cells := by
    intro t dd
    cases dd <;> rfl
  have hc₃icells : c₃.input.cells = inp.cells := by
    show (c₂.input.move _).cells = _
    rw [hmovecells, hic₂]
  have hc₃ihead : c₃.input.head ≤ pos + 1 := by
    show (c₂.input.move _).head ≤ pos + 1
    split
    · show c₂.input.head + 1 ≤ pos + 1
      rw [hihead₂]
    · show c₂.input.head - 1 ≤ pos + 1
      rw [hihead₂]
      omega
  have hrparked : Parked (c₂.work r) :=
    ⟨by rw [hhead₂]; omega, fun j hj => by
      rw [hcells₂]
      show regCells pos j ≠ Γ.start
      rw [regCells, ite_eq_right (by omega)]
      split <;> decide⟩
  have hc₃workP : ∀ i, Parked (c₃.work i) := by
    intro i
    by_cases hi : i = r
    · subst hi
      exact hrparked
    · exact hworkP₂ i hi
  obtain ⟨c₄, hreach₄, hst₄, hicells₄, hihead₄, hwork₄, hout₄⟩ :=
    symProbeTM_backI_run c₃.input.head c₃ hc₃st
      ⟨by rw [hc₃icells]; exact hWF.1,
       fun j hj => by rw [hc₃icells]; exact hWF.2 j hj⟩
      rfl hc₃workP
      (by show Parked c₂.output; exact houtP₂)
  have hc₄r : (c₄.work r).cells = regCells pos := by
    rw [hwork₄]
    exact hcells₂
  have hc₄rhead : (c₄.work r).head = pos + 1 := by
    rw [hwork₄]
    exact hhead₂
  have hc₄inpP : Parked c₄.input :=
    ⟨by rw [hihead₄], fun j hj => by
      rw [hicells₄, hc₃icells]
      exact hWF.2 j hj⟩
  obtain ⟨c₅, hreach₅, hst₅, hinp₅, hwork₅, hcells₅, hhead₅, hout₅⟩ :=
    symProbeTM_backR_run (c₄.work r).head c₄ hst₄ hc₄inpP
      (fun i hi => by
        rw [hwork₄]
        exact hc₃workP i)
      (by rw [hout₄]; exact houtP₂)
      (by rw [hc₄r]; rfl)
      (fun j hj => by
        rw [hc₄r]
        show regCells pos j ≠ Γ.start
        rw [regCells, ite_eq_right (by omega)]
        split <;> decide)
      rfl
  have hc₅q : c₅.work q = work q := by
    rw [hwork₅ q hqr, hwork₄]
    show c₂.work q = work q
    exact hwork₂ q hqr
  have hc₅inpP : Parked c₅.input := by rw [hinp₅]; exact hc₄inpP
  have hc₅workPq : ∀ i, i ≠ q → Parked (c₅.work i) := by
    intro i hi
    by_cases hir : i = r
    · subst hir
      refine ⟨by rw [hhead₅], fun j hj => ?_⟩
      rw [hcells₅, hc₄r]
      show regCells pos j ≠ Γ.start
      rw [regCells, ite_eq_right (by omega)]
      split <;> decide
    · rw [hwork₅ i hir, hwork₄]
      exact hc₃workP i
  have houtP₅ : Parked c₅.output := by
    rw [hout₅, hout₄]
    exact houtP₂
  obtain ⟨c₆, hreach₆, hst₆, hinp₆, hwork₆, hcells₆, hhead₆, hout₆⟩ :=
    symProbeTM_scanQ_run (f := f) (r := r) (q := q) d d 0 (by omega) c₅ hst₅
      hc₅inpP hc₅workPq houtP₅
      (by rw [hc₅q, hq, regT_cells])
      (by rw [hc₅q, hq, regT_head])
  obtain ⟨c₇, hreach₇, hst₇, hinp₇, hwork₇, hcells₇, hhead₇, hout₇⟩ :=
    symProbeTM_write_run (f (inp.cells pos)).val (f (inp.cells pos)) rfl d
      c₆ hst₆ (by rw [hinp₆]; exact hc₅inpP)
      (fun i hi => by rw [hwork₆ i hi]; exact hc₅workPq i hi)
      (by rw [hout₆]; exact houtP₅) hcells₆ hhead₆
  set kv : ℕ := (f (inp.cells pos)).val with hkv
  have hblank₇ : (c₇.work q).read = Γ.blank := by
    rw [Tape.read, hhead₇, hcells₇]
    exact regCells_blank (by omega)
  have hc₇inpP : Parked c₇.input := by
    rw [hinp₇, hinp₆]
    exact hc₅inpP
  have hc₇workPq : ∀ i, i ≠ q → Parked (c₇.work i) := fun i hi => by
    rw [hwork₇ i hi, hwork₆ i hi]
    exact hc₅workPq i hi
  have houtP₇ : Parked c₇.output := by
    rw [hout₇, hout₆]
    exact houtP₅
  have hstep₇ := symProbeTM_step_scanQ_blank_zero c₇ hst₇ hblank₇ hc₇inpP
    hc₇workPq houtP₇
  set c₈ : Cfg n (symProbeTM f r q).Q :=
    { state := .backQ, input := c₇.input,
      work := Function.update c₇.work q ((c₇.work q).move .left),
      output := c₇.output } with hc₈
  have hc₈qcells : (c₈.work q).cells = regCells (d + kv) := by
    show (Function.update c₇.work q ((c₇.work q).move .left) q).cells = _
    rw [Function.update_self]
    show (c₇.work q).cells = _
    exact hcells₇
  have hc₈qhead : (c₈.work q).head = d + kv := by
    show (Function.update c₇.work q ((c₇.work q).move .left) q).head = _
    rw [Function.update_self]
    show (c₇.work q).head - 1 = _
    rw [hhead₇]
    omega
  obtain ⟨c₉, hreach₉, hst₉, hinp₉, hwork₉, hcells₉, hhead₉, hout₉⟩ :=
    symProbeTM_backQ_run (d + kv) c₈ rfl hc₇inpP
      (fun i hi => by
        show Parked (Function.update c₇.work q ((c₇.work q).move .left) i)
        rw [Function.update_of_ne hi]
        exact hc₇workPq i hi)
      houtP₇
      (by rw [hc₈qcells]; rfl)
      (fun j hj => by
        rw [hc₈qcells]
        show regCells (d + kv) j ≠ Γ.start
        rw [regCells, ite_eq_right (by omega)]
        split <;> decide)
      hc₈qhead
  refine ⟨c₉, _, ?_,
    .step hstep₀ (reachesIn_trans _ hreach₂ (.step hstep₂
      (reachesIn_trans _ hreach₄ (reachesIn_trans _ hreach₅
        (reachesIn_trans _ hreach₆ (reachesIn_trans _ hreach₇
          (.step hstep₇ hreach₉))))))),
    hst₉, ?_, ?_, ?_⟩
  · have hkv3 : kv ≤ 3 := by
      have := (f (inp.cells pos)).isLt
      omega
    omega
  · show c₉.input = inp
    rw [hinp₉, hinp₇, hinp₆, hinp₅]
    refine Tape.ext ?_ ?_
    · rw [hihead₄, hhead]
    · rw [hicells₄, hc₃icells]
  · funext i
    by_cases hiq : i = q
    · subst hiq
      rw [Function.update_self]
      refine Tape.ext ?_ ?_
      · rw [hhead₉, regT_head]
      · rw [hcells₉, hc₈qcells, regT_cells]
    · rw [Function.update_of_ne hiq, hwork₉ i hiq]
      show Function.update c₇.work q ((c₇.work q).move .left) i = work i
      rw [Function.update_of_ne hiq, hwork₇ i hiq, hwork₆ i hiq]
      by_cases hir : i = r
      · subst hir
        refine Tape.ext ?_ ?_
        · rw [hhead₅, hr, regT_head]
        · rw [hcells₅, hc₄r, hr, regT_cells]
      · rw [hwork₅ i hir, hwork₄]
        show c₂.work i = work i
        exact hwork₂ i hir
  · show OutAcc ys c₉.output
    rw [hout₉, hout₇, hout₆, hout₅, hout₄]
    show OutAcc ys c₂.output
    rw [hout₂]
    exact hout

end Probe

end TM

end Complexity
