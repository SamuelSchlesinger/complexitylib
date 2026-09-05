/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.Hoare.Defs
public import Complexitylib.Models.TuringMachine.Registers
public import Complexitylib.Models.TuringMachine.UTM.Internal.VTape

/-!
# Clock infrastructure for the time-bounded universal machine

Everything lives in `namespace TM` (the machines here are generic
`TM`-building blocks in the style of `Subroutines.lean` / `DecReg.lean`,
not `bodyTM` phase states, so they sit beside `liftTM` rather than in
`TM.UTMBody`). Two pieces:

1. **`HoareTime` lifting through `liftTM`**: a Hoare-style spec for
   `tm : TM n` transfers to `tm.liftTM m` with the same time bound, with
   the `m` extra work tapes *exactly* preserved.
   - `liftTM_hoareTime_frame` is the ghost-pinned frame version: the extras
     hold **arbitrary** parked content (head ≥ 1, reading a non-`▷`
     symbol) — needed to run lifted 6-tape UTM phases while tape 6 holds
     the clock.
   - `liftTM_hoareTime` is the special case where the extras hold the
     canonical parked blank tape `(Tape.init []).move Dir3.right` (the
     tape `liftCfg` pins them to).

   The key observation: `liftTM`'s extra-tape action is
   `readBackWrite`/`idleDir` — exactly `transitionTape`, which is the
   identity on any tape reading a non-`▷` symbol (`transitionTape_eq_self`).
   So the extras are preserved exactly at every step, for *any* parked
   content, not just the blank tape hard-wired into `liftCfg`. Since
   `Lift.lean`'s step commutation is specialized to blank extras (and its
   internals are private), we redo the small step lemma here against the
   generalized embedding `liftCfgWith`.

2. **The clock machines**, both `TM 7`, acting on work tape 6 (`clkT`),
   which holds a unary counter (`1`s on cells `1..v`, head parked at 1 —
   i.e. `HoldsExact (List.replicate v Γw.one)` with head 1):
   - `decClockTM` — scan right to the last mark, blank it, rewind to
     cell 1; a zero counter is left unchanged. Spec: `decClockTM_hoareTime`
     (ghost style: `2*v + 6` steps, every other tape exactly unchanged).
   - `zeroTestTM` — read clock cell 1 and write the verdict to the real
     output cell 1 (`1` iff the counter is zero), leaving the output head
     at cell 1 and every work tape exactly unchanged. Spec:
     `zeroTestTM_hoareTime` (4 steps).
-/


@[expose] public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Cross-arity simulation lifting
-- ════════════════════════════════════════════════════════════════════════

/-- Cross-arity generalization of `reachesIn_map`: the simulating
    machine may have a different number of work tapes. If `wrap` commutes
    with `step`, then `reachesIn` lifts through the embedding. -/
theorem reachesIn_map' {n n' : ℕ} {tm : TM n} {tm' : TM n'}
    (wrap : Cfg n tm.Q → Cfg n' tm'.Q)
    (h_step : ∀ c c' : Cfg n tm.Q, tm.step c = some c' →
      tm'.step (wrap c) = some (wrap c'))
    {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') :
    tm'.reachesIn t (wrap c) (wrap c') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih => exact .step (h_step _ _ hstep) ih

/-- Configuration extensionality (pointwise on the work tapes). -/
private theorem cfg_ext {k : ℕ} {Q : Type} {c c' : Cfg k Q}
    (hs : c.state = c'.state) (hi : c.input = c'.input)
    (hw : ∀ i, c.work i = c'.work i) (ho : c.output = c'.output) : c = c' := by
  obtain ⟨s, i, w, o⟩ := c
  obtain ⟨s', i', w', o'⟩ := c'
  cases hs; cases hi; cases ho
  exact congrArg (fun w => Cfg.mk s i w o) (funext hw)

-- ════════════════════════════════════════════════════════════════════════
-- liftCfgWith: the lifted embedding with arbitrary pinned extras
-- ════════════════════════════════════════════════════════════════════════

/-- The extra-tape index of a lifted tape index `i` with `n ≤ i.val`. -/
def extraIdx {n m : ℕ} (i : Fin (n + m)) (h : n ≤ i.val) : Fin m :=
  ⟨i.val - n, by have := i.isLt; omega⟩

variable {n : ℕ}

/-- Embed a configuration of `tm : TM n` into one of `tm.liftTM m` with the
    extra work tapes pinned to the fixed tapes `extras`. Generalizes
    `liftCfg`, which is the special case
    `extras = fun _ => (Tape.init []).move Dir3.right`. -/
def liftCfgWith (tm : TM n) (m : ℕ) (extras : Fin m → Tape) (c : Cfg n tm.Q) :
    Cfg (n + m) tm.Q where
  state := c.state
  input := c.input
  work := fun i =>
    if h : i.val < n then c.work ⟨i.val, h⟩
    else extras (extraIdx i (Nat.le_of_not_lt h))
  output := c.output

/-- `liftCfgWith` leaves the state unchanged. -/
@[simp] theorem liftCfgWith_state (tm : TM n) (m : ℕ) (extras : Fin m → Tape)
    (c : Cfg n tm.Q) : (liftCfgWith tm m extras c).state = c.state := rfl

/-- `liftCfgWith` leaves the input tape unchanged. -/
@[simp] theorem liftCfgWith_input (tm : TM n) (m : ℕ) (extras : Fin m → Tape)
    (c : Cfg n tm.Q) : (liftCfgWith tm m extras c).input = c.input := rfl

/-- `liftCfgWith` leaves the output tape unchanged. -/
@[simp] theorem liftCfgWith_output (tm : TM n) (m : ℕ) (extras : Fin m → Tape)
    (c : Cfg n tm.Q) : (liftCfgWith tm m extras c).output = c.output := rfl

/-- `liftCfgWith` maps the first `n` work tapes to `c`'s work tapes. -/
theorem liftCfgWith_work_lt (tm : TM n) (m : ℕ) (extras : Fin m → Tape)
    (c : Cfg n tm.Q) (i : Fin (n + m)) (h : i.val < n) :
    (liftCfgWith tm m extras c).work i = c.work ⟨i.val, h⟩ := dite_eq_left h

/-- `liftCfgWith` maps the extra work tapes to the pinned tapes. -/
theorem liftCfgWith_work_ge (tm : TM n) (m : ℕ) (extras : Fin m → Tape)
    (c : Cfg n tm.Q) (i : Fin (n + m)) (h : n ≤ i.val) :
    (liftCfgWith tm m extras c).work i = extras (extraIdx i h) :=
  dite_eq_right (Nat.not_lt.mpr h)

/-- **Unified step commutation** for `liftTM` with arbitrary parked extras.
    Mirror of `Lift.lean`'s (private) blank-extras step lemma: the extras'
    per-step action is `transitionTape`, the identity on any tape reading a
    non-`▷` symbol. -/
private theorem liftTM_step_of_parked (tm : TM n) (m : ℕ) {extras : Fin m → Tape}
    (hex : ∀ j : Fin m, (extras j).read ≠ Γ.start)
    {c : Cfg n tm.Q} {C : Cfg (n + m) tm.Q}
    (hs : C.state = c.state) (hi : C.input = c.input) (ho : C.output = c.output)
    (hw : ∀ (i : Fin (n + m)) (h : i.val < n), C.work i = c.work ⟨i.val, h⟩)
    (hd : ∀ (i : Fin (n + m)) (h : n ≤ i.val), C.work i = extras (extraIdx i h)) :
    (tm.liftTM m).step C = (tm.step c).map (liftCfgWith tm m extras) := by
  by_cases hh : c.state = tm.qhalt
  · -- both machines are halted
    have h1 : (tm.liftTM m).step C = none := by
      simp only [step]
      exact ite_eq_left (show C.state = (tm.liftTM m).qhalt from by rw [hs, hh]; rfl)
    have h2 : tm.step c = none := by
      simp only [step, hh, ↓reduceIte]
    rw [h1, h2]; rfl
  · cases hstep : tm.step c with
    | none => exact absurd hstep (by simp [step, hh])
    | some c' =>
      -- extract the explicit stepped configuration
      simp only [step, hh, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      have hinner : (fun i : Fin n => (C.work (Fin.castAdd m i)).read)
          = fun i => (c.work i).read :=
        funext fun i => by rw [hw (Fin.castAdd m i) i.isLt]; rfl
      simp only [step, Option.map_some]
      dsimp only [liftTM, liftCfgWith]
      rw [hs, hi, ho, hinner]
      erw [ite_eq_right hh]
      refine congrArg some (Cfg.mk.injEq _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, rfl, ?_, rfl⟩)
      funext i
      by_cases hik : i.val < n
      · rw [hw i hik, dite_eq_left hik, dite_eq_left hik, dite_eq_left hik]
      · have hge := Nat.le_of_not_lt hik
        rw [dite_eq_right hik, dite_eq_right hik, dite_eq_right hik, hd i hge]
        exact transitionTape_eq_self (hex _)

/-- **Step commutation** on embedded configurations with arbitrary parked
    extras: `tm.liftTM m` steps exactly as `tm` does through `liftCfgWith`. -/
private theorem liftTM_step_liftCfgWith (tm : TM n) (m : ℕ) {extras : Fin m → Tape}
    (hex : ∀ j : Fin m, (extras j).read ≠ Γ.start) (c : Cfg n tm.Q) :
    (tm.liftTM m).step (liftCfgWith tm m extras c)
      = (tm.step c).map (liftCfgWith tm m extras) :=
  liftTM_step_of_parked tm m hex rfl rfl rfl
    (fun _ h => dite_eq_left h) (fun _ h => dite_eq_right (Nat.not_lt.mpr h))

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime lifting
-- ════════════════════════════════════════════════════════════════════════

/-- **Frame rule for `liftTM` Hoare specs** (ghost-pinned extras). If
    `tm : TM n` satisfies `{pre} tm {post} [≤ b]`, then `tm.liftTM m`
    satisfies the same triple on its first `n` work tapes while the `m`
    extra tapes — holding *arbitrary* parked content `extras` (head ≥ 1,
    reading a non-`▷` symbol) — are preserved **exactly**, with the same
    time bound. This is what lets lifted 6-tape UTM phases run while tape
    6 holds the clock. -/
theorem liftTM_hoareTime_frame {n m : ℕ} (tm : TM n) {pre post : TapePred n}
    {b : ℕ} (extras : Fin m → Tape)
    (hex : ∀ j : Fin m, 1 ≤ (extras j).head ∧ (extras j).read ≠ Γ.start)
    (h : tm.HoareTime pre post b) :
    (tm.liftTM m).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = extras j)
      (fun inp work out => post inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = extras j)
      b := by
  have hex' : ∀ j : Fin m, (extras j).read ≠ Γ.start := fun j => (hex j).2
  rintro inp work out ⟨hpre, hpark⟩
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ :=
    h inp (fun i => work (Fin.castAdd m i)) out hpre
  -- the lifted start configuration is the embedded n-tape start configuration
  have hstart :
      ({ state := (tm.liftTM m).qstart, input := inp, work := work, output := out }
        : Cfg (n + m) (tm.liftTM m).Q)
      = liftCfgWith tm m extras
          { state := tm.qstart, input := inp,
            work := fun i => work (Fin.castAdd m i), output := out } := by
    refine cfg_ext rfl rfl (fun i => ?_) rfl
    by_cases hik : i.val < n
    · rw [liftCfgWith_work_lt tm m extras _ i hik]
      rfl
    · rw [liftCfgWith_work_ge tm m extras _ i (Nat.le_of_not_lt hik),
        ← hpark (extraIdx i (Nat.le_of_not_lt hik))]
      exact congrArg work (Fin.ext (show i.val = n + (i.val - n) by
        have := Nat.le_of_not_lt hik; omega))
  refine ⟨liftCfgWith tm m extras c', t, ht, ?_, ?_, ?_, ?_⟩
  · rw [hstart]
    exact reachesIn_map' (tm' := tm.liftTM m) (liftCfgWith tm m extras)
      (fun a a' ha => by rw [liftTM_step_liftCfgWith tm m hex', ha]; rfl) hreach
  · exact hhalt
  · have hwl : (fun i => (liftCfgWith tm m extras c').work (Fin.castAdd m i))
        = c'.work := by
      funext i
      rw [liftCfgWith_work_lt tm m extras c' (Fin.castAdd m i) i.isLt]
      rfl
    rw [liftCfgWith_input, liftCfgWith_output, hwl]
    exact hpost
  · intro j
    rw [liftCfgWith_work_ge tm m extras c' (Fin.natAdd n j)
      (Nat.le_add_right n j.val)]
    exact congrArg extras (Fin.ext (show n + j.val - n = j.val by omega))

/-- **`liftTM` preserves Hoare specs** (blank extras). Special case of
    `liftTM_hoareTime_frame`: the extra tapes start and end as the
    canonical parked blank tape `(Tape.init []).move Dir3.right`. -/
theorem liftTM_hoareTime {n m : ℕ} (tm : TM n) {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) :
    (tm.liftTM m).HoareTime
      (fun inp work out => pre inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = (Tape.init []).move Dir3.right)
      (fun inp work out => post inp (fun i => work (Fin.castAdd m i)) out ∧
        ∀ j : Fin m, work (Fin.natAdd n j) = (Tape.init []).move Dir3.right)
      b := by
  have hblank : ((Tape.init []).move Dir3.right).read ≠ Γ.start := by decide
  exact liftTM_hoareTime_frame tm (fun _ => (Tape.init []).move Dir3.right)
    (fun _ => ⟨Nat.le_refl 1, hblank⟩) h

-- ════════════════════════════════════════════════════════════════════════
-- The clock tape and its contents
-- ════════════════════════════════════════════════════════════════════════

/-- The clock tape: work tape 6 of the 7-tape layout (6 UTM body tapes
    plus the clock). -/
def clkT : Fin 7 := 6

/-- A tape whose cells are `regCells v` holds exactly `v` unary marks. -/
private theorem holdsExact_replicate_of_cells {t : Tape} {v : ℕ}
    (h : t.cells = regCells v) : t.HoldsExact (List.replicate v Γw.one) := by
  refine ⟨by rw [h]; rfl, fun i => ?_⟩
  rw [h]
  by_cases hi : i < v
  · rw [dite_eq_left (by rwa [List.length_replicate]), List.getElem_replicate]
    exact regCells_one (by omega) (by omega)
  · rw [dite_eq_right (by rw [List.length_replicate]; omega)]
    exact regCells_blank (by omega)

/-- A tape holding exactly `v` unary marks has cells `regCells v`. -/
private theorem cells_of_holdsExact_replicate {t : Tape} {v : ℕ}
    (h : t.HoldsExact (List.replicate v Γw.one)) : t.cells = regCells v := by
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [h.1]; rfl
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    by_cases hi : i < v
    · rw [Tape.HoldsExact.cells_lt h (by rwa [List.length_replicate]),
        List.getElem_replicate]
      exact (regCells_one (by omega) (by omega)).symm
    · rw [Tape.HoldsExact.cells_ge h (by rw [List.length_replicate]; omega)]
      exact (regCells_blank (by omega)).symm

-- ════════════════════════════════════════════════════════════════════════
-- decClockTM: decrement the unary clock on tape 6
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `decClockTM`. -/
inductive ClockPhase where
  | scan | erase | back | park | done
  deriving DecidableEq

instance : Fintype ClockPhase where
  elems := {.scan, .erase, .back, .park, .done}
  complete := fun x => by cases x <;> simp

/-- **Decrement the clock**: scan right over the marks on tape `clkT`,
    erase the last one, rewind to cell 1. From `v` marks to `v - 1` marks
    in at most `2v + 6` steps; every other tape idles throughout (and is
    exactly preserved while parked). The zero clock is left unchanged. -/
def decClockTM : TM 7 where
  Q := ClockPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if wHeads clkT = Γ.one then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.erase, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then
                    (if wHeads clkT = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .erase =>
      if wHeads clkT = Γ.one then
        (.back, fun i => if i = clkT then Γw.blank else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = clkT then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
      else
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then
                    (if wHeads clkT = Γ.start then Dir3.right else Dir3.stay)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads clkT = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = clkT then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .scan =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .erase =>
      dsimp only []
      split
      · next hone =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir; rw [hone] at hi; exact absurd hi (by decide)
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = clkT
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ── step lemmas ──

private theorem decClock_ne_halt {s : ClockPhase} (h : s ≠ .done)
    {c : Cfg 7 decClockTM.Q} (hst : c.state = s) :
    ¬ c.state = decClockTM.qhalt := by
  rw [hst]
  show ¬ s = ClockPhase.done
  exact h

/-- `scan` over a mark: the clock head advances; nothing else changes. -/
private theorem decClock_step_scan_one (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .scan) (hone : (c.work clkT).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .scan, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `scan` at the first blank: turn around onto the last mark. -/
private theorem decClock_step_scan_blank (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .scan) (hblank : (c.work clkT).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .erase, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hblank]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `erase` on the last mark: blank it and start rewinding. -/
private theorem decClock_step_erase_one (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .erase) (hone : (c.work clkT).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .back, input := c.input,
        work := Function.update c.work clkT
          (((c.work clkT).write Γw.blank).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `erase` on the sentinel (zero clock): step right and park. -/
private theorem decClock_step_erase_start (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .erase) (hs : (c.work clkT).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work clkT).cells j ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .park, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } := by
  have h0 : (c.work clkT).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst, hs, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work clkT).write _).move Dir3.right = (c.work clkT).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` off the sentinel: keep rewinding. -/
private theorem decClock_step_back_left (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .back) (hns : (c.work clkT).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .back, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` on the sentinel: step right to cell 1 and park. -/
private theorem decClock_step_back_start (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .back) (hs : (c.work clkT).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work clkT).cells j ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .park, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } := by
  have h0 : (c.work clkT).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = clkT
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work clkT).write _).move Dir3.right = (c.work clkT).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `park`: one idle step into `done`. -/
private theorem decClock_step_park (c : Cfg 7 decClockTM.Q)
    (hst : c.state = .park)
    (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    decClockTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (decClock_ne_halt (by decide) hst)]
  simp only [decClockTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

-- ── run lemmas ──

/-- The scan loop: from `scan` with the clock head at `k + 1` over
    `regCells d` cells (`d = k + m`), reach the first blank in `m` steps. -/
private theorem decClock_scan_run (d m : ℕ) :
    ∀ (k : ℕ), d = k + m →
      ∀ c : Cfg 7 decClockTM.Q,
      c.state = .scan →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work clkT).cells = regCells d → (c.work clkT).head = k + 1 →
      ∃ c', decClockTM.reachesIn m c c' ∧
        c'.state = .scan ∧ c'.input = c.input ∧
        (∀ i, i ≠ clkT → c'.work i = c.work i) ∧
        (c'.work clkT).cells = regCells d ∧ (c'.work clkT).head = d + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst _ _ _ hcells hhead
    exact ⟨c, .zero, hst, rfl, fun _ _ => rfl, hcells, by rw [hhead, hk], rfl⟩
  | succ m ih =>
    intro k hk c hst hinp hoth hout hcells hhead
    have hone : (c.work clkT).read = Γ.one := by
      rw [Tape.read, hhead, hcells]
      exact regCells_one (by omega) (by omega)
    have hstep := decClock_step_scan_one c hst hone hinp hoth hout
    obtain ⟨c', hreach, hst', hin', hw', hcells', hhead', hout'⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input,
          work := Function.update c.work clkT ((c.work clkT).move .right),
          output := c.output } rfl hinp
        (fun i hi => by
          show ((Function.update c.work clkT ((c.work clkT).move .right)) i).read
            ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by
          show (Function.update c.work clkT ((c.work clkT).move .right) clkT).cells
            = _
          rw [Function.update_self]
          show (c.work clkT).cells = _
          exact hcells)
        (by
          show (Function.update c.work clkT ((c.work clkT).move .right) clkT).head
            = _
          rw [Function.update_self]
          show (c.work clkT).head + 1 = _
          rw [hhead])
    refine ⟨c', .step hstep hreach, hst', hin', ?_, hcells', hhead', hout'⟩
    intro i hi
    rw [hw' i hi]
    show Function.update c.work clkT ((c.work clkT).move .right) i = c.work i
    rw [Function.update_of_ne hi]

/-- The rewind loop: from `back` at head `h` over `▷`-clean cells, reach
    `done` parked at cell 1 in `h + 2` steps. -/
private theorem decClock_back_run (h : ℕ) :
    ∀ c : Cfg 7 decClockTM.Q,
      c.state = .back →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ clkT → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work clkT).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work clkT).cells j ≠ Γ.start) →
      (c.work clkT).head = h →
      ∃ c', decClockTM.reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ clkT → c'.work i = c.work i) ∧
        (c'.work clkT).cells = (c.work clkT).cells ∧ (c'.work clkT).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hoth hout hc0 hcr hhead
    have hs : (c.work clkT).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep₁ := decClock_step_back_start c hst hs hcr hinp hoth hout
    have hall : ∀ i,
        ((Function.update c.work clkT ((c.work clkT).move .right)) i).read
          ≠ Γ.start := by
      intro i
      by_cases hir : i = clkT
      · subst hir
        rw [Function.update_self]
        show (c.work clkT).cells ((c.work clkT).head + 1) ≠ Γ.start
        exact hcr _ (by omega)
      · rw [Function.update_of_ne hir]
        exact hoth i hir
    have hstep₂ := decClock_step_park
      { state := .park, input := c.input,
        work := Function.update c.work clkT ((c.work clkT).move .right),
        output := c.output } rfl hinp hall hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work clkT ((c.work clkT).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work clkT ((c.work clkT).move .right) clkT).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work clkT ((c.work clkT).move .right) clkT).head = 1
      rw [Function.update_self]
      show (c.work clkT).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hoth hout hc0 hcr hhead
    have hns : (c.work clkT).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep₁ := decClock_step_back_left c hst hns hinp hoth hout
    have hupd : (Function.update c.work clkT ((c.work clkT).move .left) clkT).cells
        = (c.work clkT).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hin', hw', hcl', hhd', hout'⟩ :=
      ih { state := .back, input := c.input,
           work := Function.update c.work clkT ((c.work clkT).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show ((Function.update c.work clkT ((c.work clkT).move .left)) i).read
            ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work clkT ((c.work clkT).move .left) clkT).head = h
          rw [Function.update_self]
          show (c.work clkT).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep₁ hreach, hst', hin', ?_, ?_, hhd', hout'⟩
    · intro i hi
      rw [hw' i hi]
      show Function.update c.work clkT ((c.work clkT).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcl', hupd]

-- ── main theorem ──

/-- **`decClockTM` specification** (ghost-initial-tapes style). Starting
    from `qstart` with the clock tape (`clkT` = work tape 6) holding `v`
    unary marks with its head at cell 1, and every other tape parked on a
    non-`▷` symbol, `decClockTM` halts within `2v + 6` steps having
    decremented the clock to `v - 1` marks (head back at cell 1); the
    input tape, the output tape, and every other work tape are preserved
    **exactly**. The zero clock is left unchanged (`0 - 1 = 0`). -/
theorem decClockTM_hoareTime (v : ℕ) (inp₀ : Tape) (work₀ : Fin 7 → Tape)
    (out₀ : Tape)
    (hclk : (work₀ clkT).HoldsExact (List.replicate v Γw.one))
    (hclkh : (work₀ clkT).head = 1)
    (hinp : inp₀.read ≠ Γ.start)
    (hwork : ∀ i : Fin 7, i ≠ clkT → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    decClockTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i : Fin 7, i ≠ clkT → work i = work₀ i) ∧
        (work clkT).HoldsExact (List.replicate (v - 1) Γw.one) ∧
        (work clkT).head = 1 ∧
        out = out₀)
      (2 * v + 6) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hcells : (work clkT).cells = regCells v := cells_of_holdsExact_replicate hclk
  -- ── Phase A: scan right to the first blank ──
  obtain ⟨c₁, hr₁, hst₁, hin₁, hw₁, hcl₁, hhd₁, hout₁⟩ :=
    decClock_scan_run v v 0 (by omega)
      { state := decClockTM.qstart, input := inp, work := work, output := out }
      rfl hinp hwork hout hcells
      (by show (work clkT).head = 0 + 1; rw [hclkh])
  have hoth₁ : ∀ i, i ≠ clkT → (c₁.work i).read ≠ Γ.start := fun i hi => by
    rw [hw₁ i hi]; exact hwork i hi
  have hblank₁ : (c₁.work clkT).read = Γ.blank := by
    rw [Tape.read, hhd₁, hcl₁]
    exact regCells_blank (by omega)
  -- ── Phase B: turn around onto the last mark ──
  have hstep₂ := decClock_step_scan_blank c₁ hst₁ hblank₁
    (by rw [hin₁]; exact hinp) hoth₁ (by rw [hout₁]; exact hout)
  set c₂ : Cfg 7 decClockTM.Q :=
    { state := .erase, input := c₁.input,
      work := Function.update c₁.work clkT ((c₁.work clkT).move .left),
      output := c₁.output }
  have hc₂cells : (c₂.work clkT).cells = regCells v := by
    show (Function.update c₁.work clkT ((c₁.work clkT).move .left) clkT).cells = _
    rw [Function.update_self]
    show (c₁.work clkT).cells = _
    exact hcl₁
  have hc₂head : (c₂.work clkT).head = v := by
    show (Function.update c₁.work clkT ((c₁.work clkT).move .left) clkT).head = v
    rw [Function.update_self]
    show (c₁.work clkT).head - 1 = v
    rw [hhd₁]
    omega
  have hc₂w : ∀ i, i ≠ clkT → c₂.work i = work i := fun i hi => by
    show Function.update c₁.work clkT ((c₁.work clkT).move .left) i = work i
    rw [Function.update_of_ne hi]
    exact hw₁ i hi
  have hc₂oth : ∀ i, i ≠ clkT → (c₂.work i).read ≠ Γ.start := fun i hi => by
    rw [hc₂w i hi]; exact hwork i hi
  have hc₂in : c₂.input.read ≠ Γ.start := by
    show c₁.input.read ≠ Γ.start
    rw [hin₁]; exact hinp
  have hc₂out : c₂.output.read ≠ Γ.start := by
    show c₁.output.read ≠ Γ.start
    rw [hout₁]; exact hout
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · -- ── Zero clock: `erase` sees the sentinel; nothing changes ──
    have hs₂ : (c₂.work clkT).read = Γ.start := by
      rw [Tape.read, hc₂head, hc₂cells]
      rfl
    have hstep₃ := decClock_step_erase_start c₂ rfl hs₂
      (fun j hj => by rw [hc₂cells]; exact regCells_ne_start hj)
      hc₂in hc₂oth hc₂out
    set c₃ : Cfg 7 decClockTM.Q :=
      { state := .park, input := c₂.input,
        work := Function.update c₂.work clkT ((c₂.work clkT).move .right),
        output := c₂.output }
    have hc₃clk : c₃.work clkT = (c₂.work clkT).move .right := by
      show Function.update c₂.work clkT ((c₂.work clkT).move .right) clkT = _
      rw [Function.update_self]
    have hc₃w : ∀ i, i ≠ clkT → c₃.work i = work i := fun i hi => by
      show Function.update c₂.work clkT ((c₂.work clkT).move .right) i = work i
      rw [Function.update_of_ne hi]
      exact hc₂w i hi
    have hall₃ : ∀ i, (c₃.work i).read ≠ Γ.start := by
      intro i
      by_cases hir : i = clkT
      · subst hir
        rw [hc₃clk]
        show (c₂.work clkT).cells ((c₂.work clkT).head + 1) ≠ Γ.start
        rw [hc₂cells]
        exact regCells_ne_start (by omega)
      · rw [hc₃w i hir]
        exact hwork i hir
    have hstep₄ := decClock_step_park c₃ rfl hc₂in hall₃ hc₂out
    have hpost_clk : (c₃.work clkT).HoldsExact (List.replicate (0 - 1) Γw.one) := by
      rw [hc₃clk]
      exact holdsExact_replicate_of_cells hc₂cells
    have hpost_head : (c₃.work clkT).head = 1 := by
      rw [hc₃clk]
      show (c₂.work clkT).head + 1 = 1
      rw [hc₂head]
    refine ⟨_, _, ?_,
      reachesIn_trans _ hr₁ (.step hstep₂ (.step hstep₃ (.step hstep₄ .zero))),
      rfl, hin₁, ?_, hpost_clk, hpost_head, hout₁⟩
    · omega
    · intro i hi
      exact hc₃w i hi
  · -- ── Positive clock: erase the last mark, rewind ──
    obtain ⟨e, rfl⟩ : ∃ e, v = e + 1 := ⟨v - 1, by omega⟩
    have hone₂ : (c₂.work clkT).read = Γ.one := by
      rw [Tape.read, hc₂head, hc₂cells]
      exact regCells_one (by omega) (by omega)
    have hstep₃ := decClock_step_erase_one c₂ rfl hone₂ hc₂in hc₂oth hc₂out
    set c₃ : Cfg 7 decClockTM.Q :=
      { state := .back, input := c₂.input,
        work := Function.update c₂.work clkT
          (((c₂.work clkT).write Γw.blank).move .left),
        output := c₂.output }
    have hc₃cells : (c₃.work clkT).cells = regCells e := by
      show (Function.update c₂.work clkT
        (((c₂.work clkT).write Γw.blank).move .left) clkT).cells = _
      rw [Function.update_self]
      show (((c₂.work clkT).write Γw.blank).move .left).cells = _
      show ((c₂.work clkT).write Γw.blank).cells = _
      rw [Tape.write, ite_eq_right (by rw [hc₂head]; omega)]
      show Function.update (c₂.work clkT).cells (c₂.work clkT).head Γw.blank.toΓ = _
      rw [hc₂cells, hc₂head]
      exact regCells_update_blank_succ e
    have hc₃head : (c₃.work clkT).head = e := by
      show (Function.update c₂.work clkT
        (((c₂.work clkT).write Γw.blank).move .left) clkT).head = e
      rw [Function.update_self]
      show ((c₂.work clkT).write Γw.blank).head - 1 = e
      rw [Tape.write_head, hc₂head]
      omega
    have hc₃w : ∀ i, i ≠ clkT → c₃.work i = work i := fun i hi => by
      show Function.update c₂.work clkT
        (((c₂.work clkT).write Γw.blank).move .left) i = work i
      rw [Function.update_of_ne hi]
      exact hc₂w i hi
    obtain ⟨c₄, hr₄, hst₄, hin₄, hw₄, hcl₄, hhd₄, hout₄⟩ :=
      decClock_back_run e c₃ rfl hc₂in
        (fun i hi => by rw [hc₃w i hi]; exact hwork i hi)
        hc₂out
        (by rw [hc₃cells]; rfl)
        (fun j hj => by rw [hc₃cells]; exact regCells_ne_start hj)
        hc₃head
    refine ⟨c₄, _, ?_,
      reachesIn_trans _ hr₁ (.step hstep₂ (.step hstep₃ hr₄)),
      hst₄, ?_, ?_, ?_, hhd₄, ?_⟩
    · omega
    · rw [hin₄]; exact hin₁
    · intro i hi
      rw [hw₄ i hi]
      exact hc₃w i hi
    · exact holdsExact_replicate_of_cells (by rw [hcl₄, hc₃cells]; rfl)
    · rw [hout₄]; exact hout₁

-- ════════════════════════════════════════════════════════════════════════
-- zeroTestTM: write the clock's zero-test verdict to the output tape
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `zeroTestTM`. -/
inductive ZeroTestPhase where
  | test | done
  deriving DecidableEq

instance : Fintype ZeroTestPhase where
  elems := {.test, .done}
  complete := fun x => by cases x <;> simp

/-- **Clock zero test**: read clock cell 1 (head parked at 1) and write
    the verdict to the real output cell 1 — `1` if it is blank (the
    counter is zero), else `0` — leaving the output head at cell 1;
    then halt. Every work tape and the input tape idle. -/
def zeroTestTM : TM 7 where
  Q := ZeroTestPhase
  qstart := .test
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .test =>
      (.done, fun i => readBackWrite (wHeads i),
       (if wHeads clkT = Γ.blank then Γw.one else Γw.zero),
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .test =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

private theorem zeroTest_ne_halt {c : Cfg 7 zeroTestTM.Q}
    (hst : c.state = .test) : ¬ c.state = zeroTestTM.qhalt := by
  rw [hst]
  show ¬ ZeroTestPhase.test = ZeroTestPhase.done
  decide

/-- The single working step of `zeroTestTM`: write the verdict at the
    output head and halt; everything else is exactly preserved. -/
private theorem zeroTest_step (c : Cfg 7 zeroTestTM.Q)
    (hst : c.state = .test)
    (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hh0 : ¬ c.output.head = 0)
    (hor : c.output.read ≠ Γ.start) :
    zeroTestTM.step c = some
      { state := .done, input := c.input, work := c.work,
        output := { head := c.output.head,
                    cells := Function.update c.output.cells c.output.head
                      ((if (c.work clkT).read = Γ.blank then Γw.one
                        else Γw.zero) : Γw).toΓ } } := by
  rw [TM.step, ite_eq_right (zeroTest_ne_halt hst)]
  simp only [zeroTestTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · show c.output.writeAndMove _ (idleDir c.output.read) = _
    rw [idleDir, ite_eq_right hor]
    show c.output.write _ = _
    rw [Tape.write, ite_eq_right hh0]

/-- **`zeroTestTM` specification** (ghost-initial-tapes style). Starting
    from `qstart` with the clock tape (`clkT` = work tape 6) holding `v`
    unary marks with its head at cell 1, the output head resting at cell 1
    on a non-`▷` symbol, and every other tape parked on a non-`▷` symbol,
    `zeroTestTM` halts within 4 steps having

    * written the verdict at output cell 1: `Γ.one` iff `v = 0`, else
      `Γ.zero` (all other output cells unchanged, head back at cell 1);
    * left the input tape and **every** work tape exactly unchanged. -/
theorem zeroTestTM_hoareTime (v : ℕ) (inp₀ : Tape) (work₀ : Fin 7 → Tape)
    (out₀ : Tape)
    (hclk : (work₀ clkT).HoldsExact (List.replicate v Γw.one))
    (hclkh : (work₀ clkT).head = 1)
    (hinp : inp₀.read ≠ Γ.start)
    (hwork : ∀ i : Fin 7, i ≠ clkT → (work₀ i).read ≠ Γ.start)
    (houth : out₀.head = 1)
    (hout1 : out₀.cells 1 ≠ Γ.start) :
    zeroTestTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = work₀ ∧
        out.cells = Function.update out₀.cells 1
          (if v = 0 then Γ.one else Γ.zero) ∧
        out.head = 1)
      4 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  have hclkread : (work clkT).read = (if v = 0 then Γ.blank else Γ.one) := by
    rw [Tape.read, hclkh]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [ite_eq_left rfl]
      exact Tape.HoldsExact.cells_ge hclk (by simp)
    · rw [ite_eq_right (by omega)]
      have h1 := Tape.HoldsExact.cells_lt hclk (i := 0)
        (by rwa [List.length_replicate])
      rw [List.getElem_replicate] at h1
      exact h1
  have hclkns : (work clkT).read ≠ Γ.start := by
    rw [hclkread]; split <;> decide
  have hall : ∀ i : Fin 7, (work i).read ≠ Γ.start := by
    intro i
    by_cases hir : i = clkT
    · subst hir; exact hclkns
    · exact hwork i hir
  have houtread : out.read ≠ Γ.start := by
    rw [Tape.read, houth]; exact hout1
  have hverdict : ((if (work clkT).read = Γ.blank then Γw.one
      else Γw.zero) : Γw).toΓ = (if v = 0 then Γ.one else Γ.zero) := by
    rw [hclkread]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · simp
    · have hv' : v ≠ 0 := by omega
      simp [hv']
  have hstep := zeroTest_step
    { state := zeroTestTM.qstart, input := inp, work := work, output := out }
    rfl hinp hall (by rw [houth]; omega) houtread
  have hcells_eq : Function.update out.cells out.head
      ((if (work clkT).read = Γ.blank then Γw.one else Γw.zero) : Γw).toΓ
      = Function.update out.cells 1 (if v = 0 then Γ.one else Γ.zero) := by
    rw [houth, hverdict]
  exact ⟨_, 1, by omega, .step hstep .zero, rfl, rfl, rfl, hcells_eq, houth⟩

end TM

end Complexity
