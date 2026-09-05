/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring.RingNF

/-!
# Clock constructibility for the time hierarchy theorem

`TM.ClockConstructible g` is the constructibility hypothesis used by the
proved time hierarchy theorem in `Complexitylib.Classes.Hierarchy`: an
8-tape machine can write the unary clock `regTape (g n)` on work tape 6 in time
`O(g n + n)`, ghost-preserving the rest of the diagonalizer's tape layout.

Contents:

1. `TM.ClockConstructible` — the layout-pinned definition (see its
   docstring for the design tradeoffs), plus the congruence helper
   `ClockConstructible.congr`.
2. `TM.clockLenTM` and `TM.clockConstructible_succ` — the base instance
   `ClockConstructible (fun n => n + 1)` via a single input sweep.
3. `TM.moveClockTM`, `TM.clockMulTM` and `ClockConstructible.mul_succ` —
   closure under multiplication by `n + 1`: move the clock to the scratch
   tape, then append it to the clock tape's frontier once per input
   position.
4. `TM.clockConstructible_pow` — `ClockConstructible (fun n => (n + 1) ^ k)`
   for all `k ≥ 1`: the polynomial clocks of the hierarchy theorem.

All machines are hand-written in the UTM house style (small inductive
state, ghost-framed step/run lemmas as in `UTM/Clock.lean` and
`InputLen.lean`).
-/


@[expose] public section

namespace Complexity

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Small helpers: input-tape cells, blank tapes, register cells
-- ════════════════════════════════════════════════════════════════════════

/-- The canonical parked blank tape (`liftTM`'s pinned extra tape) is the
    zero register. -/
theorem Tape.init_move_right_eq_regT_zero :
    (Tape.init []).move Dir3.right = regTape 0 := by
  refine Tape.ext rfl ?_
  show (Tape.init []).cells = regCells 0
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · show (Tape.init []).cells j = regCells 0 j
    rw [regCells_blank (by omega)]
    simp only [Tape.init]
    rw [ite_eq_right (by omega : ¬ j = 0)]
    simp

/-- The output-tape frame carried through all clock-construction phases:
    head parked at cell 1, sentinel at cell 0, no spurious `▷`s. The clock
    machines never write the output tape, so this frame is preserved
    literally. -/
private def outF (out : Tape) : Prop :=
  out.head = 1 ∧ out.cells 0 = Γ.start ∧ ∀ j, 1 ≤ j → out.cells j ≠ Γ.start

private theorem outF_read_ne_start {out : Tape} (h : outF out) :
    out.read ≠ Γ.start := by
  rw [Tape.read, h.1]
  exact h.2.2 1 le_rfl

-- ════════════════════════════════════════════════════════════════════════
-- The definition
-- ════════════════════════════════════════════════════════════════════════

/-- **Clock constructibility** — the hypothesis of the time hierarchy
    theorem. `g` is clock-constructible if some 8-tape machine, started on
    input `x` in the diagonalizer's tape layout, writes the unary register
    `regTape (g |x|)` on work tape 6 within `C * (g |x| + |x| + 1)` steps,
    disturbing nothing else.

    The definition is deliberately **layout-pinned** rather than maximally
    general: the diagonalizer `D` is an 8-tape machine whose UTM phases run
    on tapes 0–5, whose encoded pair ⟨M, x⟩ lives on tape 7, and whose
    clock lives on tape 6. Instead of a lift-and-frame story, the
    hypothesis quantifies over the ghost frame `work₀` directly:

    * tapes 0–4 and 7 may hold **arbitrary parked content** (head ≥ 1,
      reading a non-`▷` symbol) and must be preserved **exactly**;
    * tape 6 (the clock) starts as the canonical parked blank tape
      `(Tape.init []).move Dir3.right` (the tape the `liftTM` combinators
      pin blank extras to; it equals `regTape 0`) and ends as `regTape (g |x|)`;
    * tape 5 is a **designated scratch tape**: it must also start blank,
      and it is restored blank — this is exactly the `work i = work₀ i`
      clause at `i = 5`, since `work₀ 5` is pinned blank. `D` runs
      clock-initialization before any UTM phase touches tapes 0–5, so
      granting the clock machine one blank scratch tape costs nothing,
      and it makes the closure constructions (multiplication, hence all
      polynomials) feasible;
    * the input tape is read-only, so only its cells are pinned; its head
      **starts at cell 1** — the started form the combinator seams produce
      (`transitionInput` forces the input head to ≥ 1 at every phase
      boundary, so a head-0 input can never reach a mid-sequence phase) —
      and is returned to cell 1 (needed to chain clock phases sequentially);
    * the output tape must be `▷`-clean with head parked at cell 1, and is
      returned in the same state (clock machines never write the output).
-/
def ClockConstructible (g : ℕ → ℕ) : Prop :=
  ∃ (tm : TM 8) (C : ℕ),
    ∀ (x : List Bool) (work₀ : Fin 8 → Tape),
      (∀ i, 1 ≤ (work₀ i).head ∧ (work₀ i).read ≠ Γ.start) →
      work₀ (5 : Fin 8) = (Tape.init []).move Dir3.right →
      work₀ (6 : Fin 8) = (Tape.init []).move Dir3.right →
      tm.HoareTime
        (fun inp work out =>
          inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
          work = work₀ ∧
          out.head = 1 ∧ out.cells 0 = Γ.start ∧
          (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
        (fun inp work out =>
          inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
          (∀ i, i ≠ (6 : Fin 8) → work i = work₀ i) ∧
          work (6 : Fin 8) = regTape (g x.length) ∧
          out.head = 1 ∧ out.cells 0 = Γ.start ∧
          (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
        (C * (g x.length + x.length + 1))

/-- `ClockConstructible` respects pointwise-equal clock bounds. -/
theorem ClockConstructible.congr {g g' : ℕ → ℕ} (h : ClockConstructible g)
    (hgg' : ∀ n, g n = g' n) : ClockConstructible g' :=
  funext hgg' ▸ h

-- ════════════════════════════════════════════════════════════════════════
-- clockLenTM: write |x| + 1 marks on the clock tape
-- ════════════════════════════════════════════════════════════════════════

/-- **Measure the input length plus one into the clock tape**: scan the
    input left to right writing one mark on tape 6 per bit, write one
    final mark at the input's first blank (the `+ 1`), then rewind both
    heads to cell 1 in lockstep. Every other tape idles throughout. -/
def clockLenTM : TM 8 where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if iHead = Γ.start then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.blank then
        (.back, fun i => if i = 6 then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.left,
         fun i => if i = 6 then (if wHeads 6 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.scan, fun i => if i = 6 then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.right,
         fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads 6 = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         (if iHead = Γ.start then Dir3.right else Dir3.left),
         fun i => if i = 6 then Dir3.left else idleDir (wHeads i),
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
      · exact ⟨fun _ => rfl, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
      · next hns =>
        split
        · refine ⟨fun hi => absurd hi hns, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = (6 : Fin 8)
          · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
          · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
        · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = (6 : Fin 8)
          · rw [ite_eq_left hir]
          · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (6 : Fin 8)
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨fun hi => by rw [ite_eq_left hi], fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (6 : Fin 8)
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section ClockLen

private theorem clockLen_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg 8 clockLenTM.Q} (hst : c.state = s) :
    ¬ c.state = clockLenTM.qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` over a bit: mark the clock, advance the input and clock heads. -/
private theorem clockLen_step_scan_bit (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .scan) (hns : c.input.read ≠ Γ.start)
    (hbl : c.input.read ≠ Γ.blank)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .scan, input := c.input.move .right,
        work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hns, hbl, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `scan` at the input's first blank: write the final mark and turn both
    heads around. -/
private theorem clockLen_step_scan_blank (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .scan) (hbl : c.input.read = Γ.blank)
    (hclk : (c.work 6).read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .back, input := c.input.move .left,
        work := Function.update c.work 6 (((c.work 6).write Γw.one).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hbl, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      rw [ite_eq_right hclk]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` off the sentinel: input and clock heads keep rewinding. -/
private theorem clockLen_step_back_left (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .back) (hclk : (c.work 6).read ≠ Γ.start)
    (hins : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .back, input := c.input.move .left,
        work := Function.update c.work 6 ((c.work 6).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hclk, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · rw [ite_eq_right hins]
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hclk]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` on the sentinel: input and clock heads step right to cell 1. -/
private theorem clockLen_step_back_start (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .back) (hs : (c.work 6).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .park, input := c.input.move .right,
        work := Function.update c.work 6 ((c.work 6).move .right),
        output := c.output } := by
  have h0 : (c.work 6).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work 6).write _).move Dir3.right = (c.work 6).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `park`: one idle step into `done`. -/
private theorem clockLen_step_park (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .park) (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- The lockstep scan: one clock mark per input bit. -/
private theorem clockLen_scan_run (x : List Bool) (m : ℕ) :
    ∀ (k : ℕ), x.length = k + m →
      ∀ (c : Cfg 8 clockLenTM.Q),
      c.state = .scan →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = k + 1 →
      (∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 6).cells = regCells k → (c.work 6).head = k + 1 →
      ∃ c', clockLenTM.reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 6).cells = regCells x.length ∧
        (c'.work 6).head = x.length + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hic hih hoth hout hcl hhd
    obtain rfl : x.length = k := by omega
    exact ⟨c, .zero, hst, hic, hih, fun _ _ => rfl, hcl, hhd, rfl⟩
  | succ m ih =>
    intro k hk c hst hic hih hoth hout hcl hhd
    have hread : c.input.read = Γ.ofBool (x[k]'(by omega)) := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_lt x k (by omega)
    have hns : c.input.read ≠ Γ.start := by
      rw [hread]; exact Γ.ofBool_ne_start _
    have hbl : c.input.read ≠ Γ.blank := by
      rw [hread]; exact Γ.ofBool_ne_blank _
    have hstep := clockLen_step_scan_bit c hst hns hbl hoth hout
    have hq₁cells : (((c.work 6).write Γw.one).move .right).cells
        = regCells (k + 1) := by
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhd]; omega)]
      show Function.update (c.work 6).cells (c.work 6).head Γw.one.toΓ = _
      rw [hhd, hcl]
      exact regCells_update_succ k
    have hq₁head : (((c.work 6).write Γw.one).move .right).head = (k + 1) + 1 := by
      show ((c.work 6).write Γw.one).head + 1 = _
      rw [Tape.write_head, hhd]
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input.move .right,
          work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
          output := c.output } rfl
        (by show (c.input.move .right).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head + 1 = (k + 1) + 1
            rw [hih])
        (fun i hi => by
          show ((Function.update c.work 6 _ i)).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by show (Function.update c.work 6 _ 6).cells = _
            rw [Function.update_self]
            exact hq₁cells)
        (by show (Function.update c.work 6 _ 6).head = _
            rw [Function.update_self]
            exact hq₁head)
    refine ⟨c', .step hstep hreach, h1, h2, h3, ?_, h5, h6, h7⟩
    intro i hi
    rw [h4 i hi]
    show Function.update c.work 6 _ i = c.work i
    rw [Function.update_of_ne hi]

/-- The lockstep rewind: input and clock heads return to cell 1. -/
private theorem clockLen_back_run (x : List Bool) (h : ℕ) :
    ∀ (c : Cfg 8 clockLenTM.Q),
      c.state = .back →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = h →
      (∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 6).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start) →
      (c.work 6).head = h →
      ∃ c', clockLenTM.reachesIn (h + 2) c c' ∧
        c'.state = .done ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ c'.input.head = 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 6).cells = (c.work 6).cells ∧ (c'.work 6).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hic hih hoth hout hc0 hcr hhd
    have hs : (c.work 6).read = Γ.start := by rw [Tape.read, hhd]; exact hc0
    have hstep₁ := clockLen_step_back_start c hst hs hcr hoth hout
    have hstep₂ := clockLen_step_park
      { state := .park, input := c.input.move .right,
        work := Function.update c.work 6 ((c.work 6).move .right),
        output := c.output } rfl
      (by show (c.input.move .right).read ≠ Γ.start
          rw [Tape.read, Tape.move_cells]
          show c.input.cells (c.input.head + 1) ≠ Γ.start
          rw [hih, hic]
          exact Tape.init_ofBool_cells_ne_start x _ (by omega))
      (fun i => by
        by_cases hir : i = (6 : Fin 8)
        · subst hir
          show (Function.update c.work 6 ((c.work 6).move .right) 6).read ≠ Γ.start
          rw [Function.update_self]
          show (c.work 6).cells ((c.work 6).head + 1) ≠ Γ.start
          exact hcr _ (by omega)
        · show (Function.update c.work 6 _ i).read ≠ Γ.start
          rw [Function.update_of_ne hir]
          exact hoth i hir)
      hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show (c.input.move .right).cells = _
      rw [Tape.move_cells]
      exact hic
    · show c.input.head + 1 = 1
      rw [hih]
    · intro i hi
      show Function.update c.work 6 ((c.work 6).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work 6 ((c.work 6).move .right) 6).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work 6 ((c.work 6).move .right) 6).head = 1
      rw [Function.update_self]
      show (c.work 6).head + 1 = 1
      rw [hhd]
  | succ h ih =>
    intro c hst hic hih hoth hout hc0 hcr hhd
    have hclk : (c.work 6).read ≠ Γ.start := by
      rw [Tape.read, hhd]
      exact hcr (h + 1) (by omega)
    have hins : c.input.read ≠ Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_ne_start x _ (by omega)
    have hstep₁ := clockLen_step_back_left c hst hclk hins hoth hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih { state := .back, input := c.input.move .left,
           work := Function.update c.work 6 ((c.work 6).move .left),
           output := c.output } rfl
        (by show (c.input.move .left).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head - 1 = h
            rw [hih]
            omega)
        (fun i hi => by
          show (Function.update c.work 6 _ i).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by show (Function.update c.work 6 _ 6).cells 0 = _
            rw [Function.update_self]
            exact hc0)
        (fun j hj => by
          show (Function.update c.work 6 _ 6).cells j ≠ _
          rw [Function.update_self]
          exact hcr j hj)
        (by show (Function.update c.work 6 _ 6).head = h
            rw [Function.update_self]
            show (c.work 6).head - 1 = h
            rw [hhd]
            omega)
    refine ⟨c', .step hstep₁ hreach, h1, h2, h3, ?_, ?_, h6, h7⟩
    · intro i hi
      rw [h4 i hi]
      show Function.update c.work 6 ((c.work 6).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [h5]
      show (Function.update c.work 6 ((c.work 6).move .left) 6).cells = _
      rw [Function.update_self]
      rfl

/-- **`clockLenTM` Hoare specification.** From the started input tape (head
    at cell 1, the form the combinator seams hand a mid-sequence phase) and
    a blank clock, write `regTape (|x| + 1)` on tape 6 in `2|x| + 3` steps,
    returning the input head to cell 1 and preserving everything else
    exactly. The machine's `.scan` arm dispatches on the read symbol, so
    from the started configuration the run is exactly the bounced core: the
    `▷`-bounce step of a head-0 start is skipped. -/
private theorem clockLenTM_hoareTime (x : List Bool) (work₀ : Fin 8 → Tape)
    (hoth : ∀ i : Fin 8, i ≠ 6 → (work₀ i).read ≠ Γ.start)
    (hclk : work₀ 6 = regTape 0) :
    clockLenTM.HoareTime
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        work = work₀ ∧ outF out)
      (fun inp work out =>
        inp = ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ ∧
        (∀ i, i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work 6 = regTape (x.length + 1) ∧ outF out)
      (2 * x.length + 3) := by
  rintro inp work out ⟨hic, hih, rfl, hout⟩
  obtain rfl : inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) :=
    Tape.ext hih hic
  have houtr : out.read ≠ Γ.start := outF_read_ne_start hout
  -- the scan sweep over the bits, straight from the started head
  obtain ⟨c₂, hr₂, hst₂, hic₂, hih₂, hw₂, hcl₂, hhd₂, ho₂⟩ :=
    clockLen_scan_run x x.length 0 (by omega)
      { state := clockLenTM.qstart,
        input := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩,
        work := work, output := out } rfl
      rfl
      rfl
      (fun i hi => hoth i hi)
      houtr
      (by show (work 6).cells = regCells 0
          rw [hclk]
          rfl)
      (by show (work 6).head = 0 + 1
          rw [hclk]
          rfl)
  have hoth₂ : ∀ i, i ≠ (6 : Fin 8) → (c₂.work i).read ≠ Γ.start := fun i hi => by
    rw [hw₂ i hi]
    exact hoth i hi
  have ho₂r : c₂.output.read ≠ Γ.start := by rw [ho₂]; exact houtr
  have hibl₂ : c₂.input.read = Γ.blank := by
    rw [Tape.read, hih₂, hic₂]
    exact Tape.init_ofBool_cells_ge x x.length le_rfl
  have hclk₂ : (c₂.work 6).read ≠ Γ.start := by
    rw [Tape.read, hhd₂, hcl₂, regCells_blank le_rfl]
    decide
  -- the final mark and the turn
  have hstep₃ := clockLen_step_scan_blank c₂ hst₂ hibl₂ hclk₂ hoth₂ ho₂r
  have hc₃cl : (Function.update c₂.work 6
      (((c₂.work 6).write Γw.one).move .left) 6).cells
      = regCells (x.length + 1) := by
    rw [Function.update_self, Tape.move_cells, Tape.write,
      ite_eq_right (by rw [hhd₂]; omega)]
    show Function.update (c₂.work 6).cells (c₂.work 6).head Γw.one.toΓ = _
    rw [hhd₂, hcl₂]
    exact regCells_update_succ x.length
  have hc₃hd : (Function.update c₂.work 6
      (((c₂.work 6).write Γw.one).move .left) 6).head = x.length := by
    rw [Function.update_self]
    show ((c₂.work 6).write Γw.one).head - 1 = x.length
    rw [Tape.write_head, hhd₂]
    omega
  -- the lockstep rewind
  obtain ⟨c₄, hr₄, hst₄, hic₄, hih₄, hw₄, hcl₄, hhd₄, ho₄⟩ :=
    clockLen_back_run x x.length
      { state := .back, input := c₂.input.move .left,
        work := Function.update c₂.work 6 (((c₂.work 6).write Γw.one).move .left),
        output := c₂.output } rfl
      (by show (c₂.input.move .left).cells = _
          rw [Tape.move_cells]
          exact hic₂)
      (by show c₂.input.head - 1 = x.length
          rw [hih₂]
          omega)
      (fun i hi => by
        show (Function.update c₂.work 6 _ i).read ≠ Γ.start
        rw [Function.update_of_ne hi]
        exact hoth₂ i hi)
      ho₂r
      (by rw [hc₃cl]; rfl)
      (fun j hj => by rw [hc₃cl]; exact regCells_ne_start hj)
      hc₃hd
  refine ⟨c₄, _, ?_,
    reachesIn_trans _ hr₂ (.step hstep₃ hr₄), hst₄, ?_, ?_, ?_, ?_⟩
  · omega
  · exact Tape.ext hih₄ hic₄
  · intro i hi
    rw [hw₄ i hi]
    show Function.update c₂.work 6 _ i = work i
    rw [Function.update_of_ne hi]
    exact hw₂ i hi
  · refine Tape.ext hhd₄ ?_
    rw [hcl₄, hc₃cl]
    rfl
  · rw [ho₄, ho₂]
    exact hout

end ClockLen

/-- **The successor function is clock-constructible**: `clockLenTM` writes
    `|x| + 1` clock marks in a single input sweep, well within the
    `2 * (g n + n + 1)` budget. -/
theorem clockConstructible_succ : ClockConstructible (fun n => n + 1) := by
  refine ⟨clockLenTM, 2, ?_⟩
  intro x work₀ hpark _ h6
  have hspec := clockLenTM_hoareTime x work₀ (fun i _ => (hpark i).2)
    (by rw [h6, Tape.init_move_right_eq_regT_zero])
  refine hspec.consequence ?_ ?_ ?_
  · rintro inp work out ⟨h1, h2, h3, h4, h5, h6'⟩
    exact ⟨h1, h2, h3, h4, h5, h6'⟩
  · rintro inp work out ⟨rfl, hw, h6', houtF⟩
    exact ⟨rfl, rfl, hw, h6', houtF.1, houtF.2.1, houtF.2.2⟩
  · show 2 * x.length + 3 ≤ 2 * ((x.length + 1) + x.length + 1)
    omega

-- ════════════════════════════════════════════════════════════════════════
-- moveClockTM: move the clock register to the scratch tape
-- ════════════════════════════════════════════════════════════════════════

/-- **Move the clock register to the scratch tape**: sweep right over tape
    6's marks, blanking each while writing a mark on tape 5 in lockstep,
    then rewind both heads to cell 1. From `(regTape 0, regTape v)` on tapes
    `(5, 6)` to `(regTape v, regTape 0)`; every other tape idles throughout. -/
def moveClockTM : TM 8 where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if wHeads 6 = Γ.one then
        (.scan,
         fun i => if i = 6 then Γw.blank else if i = 5 then Γw.one
                  else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = 6 then Dir3.right else if i = 5 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 6 then (if wHeads 6 = Γ.start then Dir3.right else Dir3.left)
                  else if i = 5 then (if wHeads 5 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads 6 = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 6 then Dir3.right else if i = 5 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 6 then Dir3.left
                  else if i = 5 then (if wHeads 5 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
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
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · rw [ite_eq_left hir6]
        · rw [ite_eq_right hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · rw [ite_eq_left hir5]
          · rw [ite_eq_right hir5]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · subst hir6; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · subst hir5; rw [ite_eq_left rfl, ite_eq_left hi]
          · rw [ite_eq_right hir5]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · rw [ite_eq_left hir6]
        · rw [ite_eq_right hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · rw [ite_eq_left hir5]
          · rw [ite_eq_right hir5]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · subst hir6; exact absurd hi hns
        · rw [ite_eq_right hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · subst hir5; rw [ite_eq_left rfl, ite_eq_left hi]
          · rw [ite_eq_right hir5]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section MoveClock

private theorem moveClock_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg 8 moveClockTM.Q} (hst : c.state = s) :
    ¬ c.state = moveClockTM.qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` over a clock mark: blank it, mark the scratch, both heads right. -/
private theorem moveClock_step_scan_one (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .scan) (hone : (c.work 6).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .scan, input := c.input,
        work := Function.update
          (Function.update c.work 6 (((c.work 6).write Γw.blank).move .right))
          5 (((c.work 5).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
      · rw [ite_eq_right hir6, ite_eq_right hir5, ite_eq_right hir6, ite_eq_right hir5,
          Function.update_of_ne hir5, Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `scan` at the clock's first blank: turn both heads around. -/
private theorem moveClock_step_scan_turn (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .scan) (hbl : (c.work 6).read = Γ.blank)
    (h5ns : (c.work 5).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .back, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .left))
          5 ((c.work 5).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, hbl, h5ns, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
      rw [writeAndMove_readBack _ (by rw [hbl]; decide)]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
        rw [writeAndMove_readBack _ h5ns]
      · rw [ite_eq_right hir6, ite_eq_right hir5, Function.update_of_ne hir5,
          Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` off the sentinel: both heads keep rewinding. -/
private theorem moveClock_step_back_left (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .back) (h6ns : (c.work 6).read ≠ Γ.start)
    (h5ns : (c.work 5).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .back, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .left))
          5 ((c.work 5).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, h6ns, h5ns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
      rw [writeAndMove_readBack _ h6ns]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
        rw [writeAndMove_readBack _ h5ns]
      · rw [ite_eq_right hir6, ite_eq_right hir5, Function.update_of_ne hir5,
          Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` on the sentinel: both heads step right to cell 1 and park. -/
private theorem moveClock_step_back_start (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .back) (hs : (c.work 6).read = Γ.start)
    (h60 : (c.work 6).head = 0) (h50 : (c.work 5).head = 0)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .park, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .right))
          5 ((c.work 5).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
      show ((c.work 6).write _).move Dir3.right = (c.work 6).move .right
      congr 1
      rw [Tape.write, ite_eq_left h60]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
        show ((c.work 5).write _).move Dir3.right = (c.work 5).move .right
        congr 1
        rw [Tape.write, ite_eq_left h50]
      · rw [ite_eq_right hir6, ite_eq_right hir5, Function.update_of_ne hir5,
          Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `park`: one idle step into `done`. -/
private theorem moveClock_step_park (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .park) (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- The lockstep sweep: blank the clock marks, mark the scratch. -/
private theorem moveClock_scan_run (v m : ℕ) :
    ∀ (k : ℕ), v = k + m →
      ∀ (c : Cfg 8 moveClockTM.Q),
      c.state = .scan →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 5).cells = regCells k → (c.work 5).head = k + 1 →
      (c.work 6).cells = clearRegCells v k → (c.work 6).head = k + 1 →
      ∃ c', moveClockTM.reachesIn m c c' ∧
        c'.state = .scan ∧ c'.input = c.input ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 5).cells = regCells v ∧ (c'.work 5).head = v + 1 ∧
        (c'.work 6).cells = clearRegCells v v ∧ (c'.work 6).head = v + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hinp hoth hout hcl5 hhd5 hcl6 hhd6
    obtain rfl : v = k := by omega
    exact ⟨c, .zero, hst, rfl, fun _ _ _ => rfl, hcl5, hhd5, hcl6, hhd6, rfl⟩
  | succ m ih =>
    intro k hk c hst hinp hoth hout hcl5 hhd5 hcl6 hhd6
    have hone : (c.work 6).read = Γ.one := by
      rw [Tape.read, hhd6, hcl6, clearRegCells, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega)]
    have hstep := moveClock_step_scan_one c hst hone hinp hoth hout
    have h6cl : (((c.work 6).write Γw.blank).move .right).cells
        = clearRegCells v (k + 1) := by
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhd6]; omega)]
      show Function.update (c.work 6).cells (c.work 6).head Γw.blank.toΓ = _
      rw [hhd6, hcl6]
      exact clearCells_update_succ v k
    have h6hd : (((c.work 6).write Γw.blank).move .right).head = (k + 1) + 1 := by
      show ((c.work 6).write Γw.blank).head + 1 = _
      rw [Tape.write_head, hhd6]
    have h5cl : (((c.work 5).write Γw.one).move .right).cells
        = regCells (k + 1) := by
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhd5]; omega)]
      show Function.update (c.work 5).cells (c.work 5).head Γw.one.toΓ = _
      rw [hhd5, hcl5]
      exact regCells_update_succ k
    have h5hd : (((c.work 5).write Γw.one).move .right).head = (k + 1) + 1 := by
      show ((c.work 5).write Γw.one).head + 1 = _
      rw [Tape.write_head, hhd5]
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input,
          work := Function.update
            (Function.update c.work 6 (((c.work 6).write Γw.blank).move .right))
            5 (((c.work 5).write Γw.one).move .right),
          output := c.output } rfl hinp
        (fun i hi5 hi6 => by
          dsimp only
          rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
          exact hoth i hi5 hi6)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact h5cl)
        (by dsimp only
            rw [Function.update_self]
            exact h5hd)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            exact h6cl)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            exact h6hd)
    refine ⟨c', .step hstep hreach, h1, h2, ?_, h4, h5, h6, h7, h8⟩
    intro i hi5 hi6
    rw [h3 i hi5 hi6]
    dsimp only
    rw [Function.update_of_ne hi5, Function.update_of_ne hi6]

/-- The lockstep rewind: both heads return to cell 1 and the machine parks. -/
private theorem moveClock_back_run (h : ℕ) :
    ∀ (c : Cfg 8 moveClockTM.Q),
      c.state = .back →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 5).cells 0 = Γ.start → (∀ j, 1 ≤ j → (c.work 5).cells j ≠ Γ.start) →
      (c.work 5).head = h →
      (c.work 6).cells 0 = Γ.start → (∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start) →
      (c.work 6).head = h →
      ∃ c', moveClockTM.reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 5).cells = (c.work 5).cells ∧ (c'.work 5).head = 1 ∧
        (c'.work 6).cells = (c.work 6).cells ∧ (c'.work 6).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hoth hout hc05 hcr5 hhd5 hc06 hcr6 hhd6
    have hs : (c.work 6).read = Γ.start := by rw [Tape.read, hhd6]; exact hc06
    have hstep₁ := moveClock_step_back_start c hst hs hhd6 hhd5 hinp hoth hout
    have hstep₂ := moveClock_step_park
      { state := .park, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .right))
          5 ((c.work 5).move .right),
        output := c.output } rfl hinp
      (fun i => by
        by_cases hir5 : i = (5 : Fin 8)
        · subst hir5
          dsimp only
          rw [Function.update_self]
          show (c.work 5).cells ((c.work 5).head + 1) ≠ Γ.start
          exact hcr5 _ (by omega)
        · by_cases hir6 : i = (6 : Fin 8)
          · subst hir6
            dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            show (c.work 6).cells ((c.work 6).head + 1) ≠ Γ.start
            exact hcr6 _ (by omega)
          · dsimp only
            rw [Function.update_of_ne hir5, Function.update_of_ne hir6]
            exact hoth i hir5 hir6)
      hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · intro i hi5 hi6
      dsimp only
      rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
    · dsimp only
      rw [Function.update_self]
      rfl
    · dsimp only
      rw [Function.update_self]
      show (c.work 5).head + 1 = 1
      rw [hhd5]
    · dsimp only
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      rfl
    · dsimp only
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      show (c.work 6).head + 1 = 1
      rw [hhd6]
  | succ h ih =>
    intro c hst hinp hoth hout hc05 hcr5 hhd5 hc06 hcr6 hhd6
    have h6ns : (c.work 6).read ≠ Γ.start := by
      rw [Tape.read, hhd6]; exact hcr6 (h + 1) (by omega)
    have h5ns : (c.work 5).read ≠ Γ.start := by
      rw [Tape.read, hhd5]; exact hcr5 (h + 1) (by omega)
    have hstep₁ := moveClock_step_back_left c hst h6ns h5ns hinp hoth hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      ih { state := .back, input := c.input,
           work := Function.update
             (Function.update c.work 6 ((c.work 6).move .left))
             5 ((c.work 5).move .left),
           output := c.output } rfl hinp
        (fun i hi5 hi6 => by
          dsimp only
          rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
          exact hoth i hi5 hi6)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact hc05)
        (fun j hj => by
          dsimp only
          rw [Function.update_self]
          exact hcr5 j hj)
        (by dsimp only
            rw [Function.update_self]
            show (c.work 5).head - 1 = h
            rw [hhd5]
            omega)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            exact hc06)
        (fun j hj => by
          dsimp only
          rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
            Function.update_self]
          exact hcr6 j hj)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            show (c.work 6).head - 1 = h
            rw [hhd6]
            omega)
    refine ⟨c', .step hstep₁ hreach, h1, h2, ?_, ?_, h5, ?_, h7, h8⟩
    · intro i hi5 hi6
      rw [h3 i hi5 hi6]
      dsimp only
      rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
    · rw [h4]
      dsimp only
      rw [Function.update_self]
      rfl
    · rw [h6]
      dsimp only
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      rfl

/-- **`moveClockTM` Hoare specification.** From `(regTape 0, regTape v)` on tapes
    `(5, 6)`, reach `(regTape v, regTape 0)` in `2v + 4` steps; the input, the
    output, and every other work tape are preserved exactly. -/
private theorem moveClockTM_hoareTime (v : ℕ) (inp₀ : Tape) (work₀ : Fin 8 → Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hoth : ∀ i : Fin 8, i ≠ 5 → i ≠ 6 → (work₀ i).read ≠ Γ.start)
    (h5 : work₀ 5 = regTape 0) (h6 : work₀ 6 = regTape v) :
    moveClockTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ outF out)
      (fun inp work out => inp = inp₀ ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work 5 = regTape v ∧ work 6 = regTape 0 ∧ outF out)
      (2 * v + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have houtr : out.read ≠ Γ.start := outF_read_ne_start hout
  obtain ⟨c₂, hr₂, hst₂, hin₂, hw₂, hcl5₂, hhd5₂, hcl6₂, hhd6₂, ho₂⟩ :=
    moveClock_scan_run v v 0 (by omega)
      { state := moveClockTM.qstart, input := inp, work := work, output := out }
      rfl hinp hoth houtr
      (by show (work 5).cells = regCells 0
          rw [h5]
          rfl)
      (by show (work 5).head = 0 + 1
          rw [h5]
          rfl)
      (by show (work 6).cells = clearRegCells v 0
          rw [h6, regT_cells, clearCells_zero])
      (by show (work 6).head = 0 + 1
          rw [h6]
          rfl)
  have hoth₂ : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c₂.work i).read ≠ Γ.start :=
    fun i hi5 hi6 => by
      rw [hw₂ i hi5 hi6]
      exact hoth i hi5 hi6
  have hin₂r : c₂.input.read ≠ Γ.start := by rw [hin₂]; exact hinp
  have ho₂r : c₂.output.read ≠ Γ.start := by rw [ho₂]; exact houtr
  have h6bl₂ : (c₂.work 6).read = Γ.blank := by
    rw [Tape.read, hhd6₂, hcl6₂, clearCells_last]
    exact regCells_blank (by omega)
  have h5ns₂ : (c₂.work 5).read ≠ Γ.start := by
    rw [Tape.read, hhd5₂, hcl5₂]
    exact regCells_ne_start (by omega)
  have hstep₃ := moveClock_step_scan_turn c₂ hst₂ h6bl₂ h5ns₂ hin₂r hoth₂ ho₂r
  obtain ⟨c₄, hr₄, hst₄, hin₄, hw₄, hcl5₄, hhd5₄, hcl6₄, hhd6₄, ho₄⟩ :=
    moveClock_back_run v
      { state := .back, input := c₂.input,
        work := Function.update
          (Function.update c₂.work 6 ((c₂.work 6).move .left))
          5 ((c₂.work 5).move .left),
        output := c₂.output } rfl hin₂r
      (fun i hi5 hi6 => by
        dsimp only
        rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
        exact hoth₂ i hi5 hi6)
      ho₂r
      (by dsimp only
          rw [Function.update_self]
          show (c₂.work 5).cells 0 = _
          rw [hcl5₂]
          rfl)
      (fun j hj => by
        dsimp only
        rw [Function.update_self]
        show (c₂.work 5).cells j ≠ _
        rw [hcl5₂]
        exact regCells_ne_start hj)
      (by dsimp only
          rw [Function.update_self]
          show (c₂.work 5).head - 1 = v
          rw [hhd5₂]
          omega)
      (by dsimp only
          rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
            Function.update_self]
          show (c₂.work 6).cells 0 = _
          rw [hcl6₂]
          rfl)
      (fun j hj => by
        dsimp only
        rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
          Function.update_self]
        show (c₂.work 6).cells j ≠ _
        rw [hcl6₂]
        exact clearCells_ne_start hj)
      (by dsimp only
          rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
            Function.update_self]
          show (c₂.work 6).head - 1 = v
          rw [hhd6₂]
          omega)
  refine ⟨c₄, _, ?_, reachesIn_trans _ hr₂ (.step hstep₃ hr₄), hst₄, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hin₄]
    exact hin₂
  · intro i hi5 hi6
    rw [hw₄ i hi5 hi6]
    dsimp only
    rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
    exact hw₂ i hi5 hi6
  · refine Tape.ext hhd5₄ ?_
    rw [hcl5₄]
    dsimp only
    rw [Function.update_self, Tape.move_cells, hcl5₂, regT_cells]
  · refine Tape.ext hhd6₄ ?_
    rw [hcl6₄]
    dsimp only
    rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self,
      Tape.move_cells, hcl6₂, clearCells_last, regT_cells]
  · rw [ho₄, ho₂]
    exact hout
end MoveClock

-- ════════════════════════════════════════════════════════════════════════
-- clockMulTM: multiply the moved clock by |x| + 1
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `clockMulTM`. -/
inductive MulPhase where
  | drive | inScan | inRew | rewC | rew6 | park | done
  deriving DecidableEq

instance : Fintype MulPhase where
  elems := {.drive, .inScan, .inRew, .rewC, .rew6, .park, .done}
  complete := fun x => by cases x <;> simp

/-- **Multiply the moved clock by `|x| + 1`**: with `regTape v` on the scratch
    tape 5 and an empty clock tape 6 (head at its frontier, cell 1), run one
    round per scratch mark (`drive` consumes it): each round scans the input
    left to right appending one clock mark per bit plus one at the first
    blank (`inScan`), then rewinds the input head to cell 1 (`inRew`). The
    clock head never leaves its frontier, so each round costs `2|x| + 3`
    steps. After the last round the scratch is blanked while rewinding
    (`rewC`), the clock rewinds to cell 1 (`rew6`), and the machine parks:
    tape 5 is `regTape 0` and tape 6 is `regTape (v * (|x| + 1))`. -/
def clockMulTM : TM 8 where
  Q := MulPhase
  qstart := .drive
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .drive =>
      if wHeads 5 = Γ.one then
        (.inScan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = 5 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewC, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 5 then (if wHeads 5 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .inScan =>
      if iHead = Γ.start then
        (.inScan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.blank then
        (.inRew, fun i => if i = 6 then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.left,
         fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.inScan, fun i => if i = 6 then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.right,
         fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .inRew =>
      if iHead = Γ.start then
        (.drive, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else
        (.inRew, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.left, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewC =>
      if wHeads 5 = Γ.start then
        (.rew6, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = 5 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rewC, fun i => if i = 5 then Γw.blank else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = 5 then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .rew6 =>
      if wHeads 6 = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.rew6, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => if i = 6 then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .drive =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (5 : Fin 8)
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (5 : Fin 8)
        · subst hir; rw [ite_eq_left rfl, ite_eq_left hi]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .inScan =>
      dsimp only []
      split
      · exact ⟨fun _ => rfl, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
      · next hns =>
        split
        · refine ⟨fun hi => absurd hi hns, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = (6 : Fin 8)
          · rw [ite_eq_left hir]
          · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
        · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = (6 : Fin 8)
          · rw [ite_eq_left hir]
          · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .inRew =>
      dsimp only []
      split
      · exact ⟨fun _ => rfl, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
      · next hns =>
        exact ⟨fun hi => absurd hi hns, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
    | .rewC =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (5 : Fin 8)
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (5 : Fin 8)
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .rew6 =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (6 : Fin 8)
        · rw [ite_eq_left hir]
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (6 : Fin 8)
        · subst hir; exact absurd hi hns
        · rw [ite_eq_right hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section ClockMul

private theorem clockMul_ne_halt {s : MulPhase} (h : s ≠ .done)
    {c : Cfg 8 clockMulTM.Q} (hst : c.state = s) :
    ¬ c.state = clockMulTM.qhalt := by
  rw [hst]
  show ¬ s = MulPhase.done
  exact h

/-- `drive` over a scratch mark: consume it and begin a round. -/
private theorem clockMul_step_drive_one (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .drive) (hone : (c.work 5).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .inScan, input := c.input,
        work := Function.update c.work 5 ((c.work 5).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = (5 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `drive` at the scratch's first blank: all rounds done, exit to cleanup. -/
private theorem clockMul_step_drive_blank (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .drive) (hbl : (c.work 5).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .rewC, input := c.input,
        work := Function.update c.work 5 ((c.work 5).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hbl, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = (5 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hbl]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `inScan` over a bit: append a clock mark, advance input and clock. -/
private theorem clockMul_step_inScan_bit (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .inScan) (hns : c.input.read ≠ Γ.start)
    (hbl : c.input.read ≠ Γ.blank)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .inScan, input := c.input.move .right,
        work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hns, hbl, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `inScan` at the input's first blank: append the final clock mark of the
    round and turn the input head around. -/
private theorem clockMul_step_inScan_blank (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .inScan) (hbl : c.input.read = Γ.blank)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .inRew, input := c.input.move .left,
        work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hbl, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `inRew` off the input sentinel: keep rewinding the input head. -/
private theorem clockMul_step_inRew_left (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .inRew) (hns : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .inRew, input := c.input.move .left,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `inRew` on the input sentinel: step right to cell 1, next round. -/
private theorem clockMul_step_inRew_start (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .inRew) (hi : c.input.read = Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .drive, input := c.input.move .right,
        work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hi, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `rewC` off the sentinel: blank the scratch mark under the head and keep
    rewinding. -/
private theorem clockMul_step_rewC_left (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .rewC) (h5ns : (c.work 5).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .rewC, input := c.input,
        work := Function.update c.work 5 (((c.work 5).write Γw.blank).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, h5ns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = (5 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [ite_eq_right hir, ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `rewC` on the sentinel: scratch head steps right to cell 1, clock next. -/
private theorem clockMul_step_rewC_start (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .rewC) (hs : (c.work 5).read = Γ.start)
    (h50 : (c.work 5).head = 0)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .rew6, input := c.input,
        work := Function.update c.work 5 ((c.work 5).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = (5 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work 5).write _).move Dir3.right = (c.work 5).move .right
      congr 1
      rw [Tape.write, ite_eq_left h50]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `rew6` off the sentinel: keep rewinding the clock head. -/
private theorem clockMul_step_rew6_left (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .rew6) (h6ns : (c.work 6).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .rew6, input := c.input,
        work := Function.update c.work 6 ((c.work 6).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, h6ns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ h6ns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `rew6` on the sentinel: clock head steps right to cell 1 and parks. -/
private theorem clockMul_step_rew6_start (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .rew6) (hs : (c.work 6).read = Γ.start)
    (h60 : (c.work 6).head = 0)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .park, input := c.input,
        work := Function.update c.work 6 ((c.work 6).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work 6).write _).move Dir3.right = (c.work 6).move .right
      congr 1
      rw [Tape.write, ite_eq_left h60]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `park`: one idle step into `done`. -/
private theorem clockMul_step_park (c : Cfg 8 clockMulTM.Q)
    (hst : c.state = .park) (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockMulTM.step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, ite_eq_right (clockMul_ne_halt (by decide) hst)]
  simp only [clockMulTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- The round's input sweep: one clock mark per input bit, appended at the
    clock's frontier. -/
private theorem clockMul_inScan_run (x : List Bool) (m : ℕ) :
    ∀ (k d : ℕ), x.length = k + m →
      ∀ (c : Cfg 8 clockMulTM.Q),
      c.state = .inScan →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = k + 1 →
      (∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 6).cells = regCells d → (c.work 6).head = d + 1 →
      ∃ c', clockMulTM.reachesIn m c c' ∧
        c'.state = .inScan ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 6).cells = regCells (d + m) ∧ (c'.work 6).head = (d + m) + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k d hk c hst hic hih hoth hout hcl hhd
    obtain rfl : x.length = k := by omega
    exact ⟨c, .zero, hst, hic, hih, fun _ _ => rfl, hcl, hhd, rfl⟩
  | succ m ih =>
    intro k d hk c hst hic hih hoth hout hcl hhd
    have hread : c.input.read = Γ.ofBool (x[k]'(by omega)) := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_lt x k (by omega)
    have hns : c.input.read ≠ Γ.start := by
      rw [hread]; exact Γ.ofBool_ne_start _
    have hbl : c.input.read ≠ Γ.blank := by
      rw [hread]; exact Γ.ofBool_ne_blank _
    have hstep := clockMul_step_inScan_bit c hst hns hbl hoth hout
    have hq₁cells : (((c.work 6).write Γw.one).move .right).cells
        = regCells (d + 1) := by
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhd]; omega)]
      show Function.update (c.work 6).cells (c.work 6).head Γw.one.toΓ = _
      rw [hhd, hcl]
      exact regCells_update_succ d
    have hq₁head : (((c.work 6).write Γw.one).move .right).head = (d + 1) + 1 := by
      show ((c.work 6).write Γw.one).head + 1 = _
      rw [Tape.write_head, hhd]
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (k + 1) (d + 1) (by omega)
        { state := .inScan, input := c.input.move .right,
          work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
          output := c.output } rfl
        (by show (c.input.move .right).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head + 1 = (k + 1) + 1
            rw [hih])
        (fun i hi => by
          dsimp only
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact hq₁cells)
        (by dsimp only
            rw [Function.update_self]
            exact hq₁head)
    refine ⟨c', .step hstep hreach, h1, h2, h3, ?_, ?_, ?_, h7⟩
    · intro i hi
      rw [h4 i hi]
      dsimp only
      rw [Function.update_of_ne hi]
    · rw [show d + (m + 1) = d + 1 + m from by omega]
      exact h5
    · rw [show d + (m + 1) = d + 1 + m from by omega]
      exact h6

/-- The round's input rewind: the input head returns to cell 1 and the
    driver takes over; no work tape is touched. -/
private theorem clockMul_inRew_run (x : List Bool) (h : ℕ) :
    ∀ (c : Cfg 8 clockMulTM.Q),
      c.state = .inRew →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = h →
      (∀ i, (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      ∃ c', clockMulTM.reachesIn (h + 1) c c' ∧
        c'.state = .drive ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ c'.input.head = 1 ∧
        c'.work = c.work ∧ c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hic hih hall hout
    have hi : c.input.read = Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_cells_zero _
    have hstep := clockMul_step_inRew_start c hst hi hall hout
    refine ⟨_, .step hstep .zero, rfl, ?_, ?_, rfl, rfl⟩
    · show (c.input.move .right).cells = _
      rw [Tape.move_cells]
      exact hic
    · show c.input.head + 1 = 1
      rw [hih]
  | succ h ih =>
    intro c hst hic hih hall hout
    have hns : c.input.read ≠ Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_ne_start x _ (by omega)
    have hstep := clockMul_step_inRew_left c hst hns hall hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5⟩ :=
      ih { state := .inRew, input := c.input.move .left,
           work := c.work, output := c.output } rfl
        (by show (c.input.move .left).cells = _
            rw [Tape.move_cells]
            exact hic)
        (by show c.input.head - 1 = h
            rw [hih]
            omega)
        hall hout
    exact ⟨c', .step hstep hreach, h1, h2, h3, h4, h5⟩

/-- The cleanup rewind of the scratch tape: blank every mark on the way
    down, ending in `regTape 0`. -/
private theorem clockMul_rewC_run (h : ℕ) :
    ∀ (c : Cfg 8 clockMulTM.Q),
      c.state = .rewC →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (5 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 5).cells = regCells h → (c.work 5).head = h →
      ∃ c', clockMulTM.reachesIn (h + 1) c c' ∧
        c'.state = .rew6 ∧ c'.input = c.input ∧
        (∀ i, i ≠ (5 : Fin 8) → c'.work i = c.work i) ∧
        c'.work 5 = regTape 0 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hoth hout hcl hhd
    have hs : (c.work 5).read = Γ.start := by
      rw [Tape.read, hhd, hcl]
      rfl
    have hstep := clockMul_step_rewC_start c hst hs hhd hinp hoth hout
    refine ⟨_, .step hstep .zero, rfl, rfl, ?_, ?_, rfl⟩
    · intro i hi
      dsimp only
      rw [Function.update_of_ne hi]
    · dsimp only
      rw [Function.update_self]
      refine Tape.ext ?_ ?_
      · show (c.work 5).head + 1 = 1
        rw [hhd]
      · show (c.work 5).cells = _
        rw [hcl, regT_cells]
  | succ h ih =>
    intro c hst hinp hoth hout hcl hhd
    have h5one : (c.work 5).read = Γ.one := by
      rw [Tape.read, hhd, hcl]
      exact regCells_one (by omega) (by omega)
    have hstep := clockMul_step_rewC_left c hst (by rw [h5one]; decide)
      hinp hoth hout
    have hq₁cells : ((((c.work 5).write Γw.blank)).move .left).cells
        = regCells h := by
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhd]; omega)]
      show Function.update (c.work 5).cells (c.work 5).head Γw.blank.toΓ = _
      rw [hhd, hcl]
      exact regCells_update_blank_succ h
    have hq₁head : ((((c.work 5).write Γw.blank)).move .left).head = h := by
      show ((c.work 5).write Γw.blank).head - 1 = h
      rw [Tape.write_head, hhd]
      omega
    obtain ⟨c', hreach, h1, h2, h3, h4, h5⟩ :=
      ih { state := .rewC, input := c.input,
           work := Function.update c.work 5 (((c.work 5).write Γw.blank).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          dsimp only
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact hq₁cells)
        (by dsimp only
            rw [Function.update_self]
            exact hq₁head)
    refine ⟨c', .step hstep hreach, h1, h2, ?_, h4, h5⟩
    intro i hi
    rw [h3 i hi]
    dsimp only
    rw [Function.update_of_ne hi]

/-- The final clock rewind: the clock head returns from its frontier to
    cell 1 and the machine parks. -/
private theorem clockMul_rew6_run (h : ℕ) :
    ∀ (c : Cfg 8 clockMulTM.Q),
      c.state = .rew6 →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 6).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start) →
      (c.work 6).head = h →
      ∃ c', clockMulTM.reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 6).cells = (c.work 6).cells ∧ (c'.work 6).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hoth hout hc0 hcr hhd
    have hs : (c.work 6).read = Γ.start := by rw [Tape.read, hhd]; exact hc0
    have hstep₁ := clockMul_step_rew6_start c hst hs hhd hinp hoth hout
    have hstep₂ := clockMul_step_park
      { state := .park, input := c.input,
        work := Function.update c.work 6 ((c.work 6).move .right),
        output := c.output } rfl hinp
      (fun i => by
        by_cases hir : i = (6 : Fin 8)
        · subst hir
          dsimp only
          rw [Function.update_self]
          show (c.work 6).cells ((c.work 6).head + 1) ≠ Γ.start
          exact hcr _ (by omega)
        · dsimp only
          rw [Function.update_of_ne hir]
          exact hoth i hir)
      hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      dsimp only
      rw [Function.update_of_ne hi]
    · dsimp only
      rw [Function.update_self]
      rfl
    · dsimp only
      rw [Function.update_self]
      show (c.work 6).head + 1 = 1
      rw [hhd]
  | succ h ih =>
    intro c hst hinp hoth hout hc0 hcr hhd
    have h6ns : (c.work 6).read ≠ Γ.start := by
      rw [Tape.read, hhd]
      exact hcr (h + 1) (by omega)
    have hstep₁ := clockMul_step_rew6_left c hst h6ns hinp hoth hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6⟩ :=
      ih { state := .rew6, input := c.input,
           work := Function.update c.work 6 ((c.work 6).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          dsimp only
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact hc0)
        (fun j hj => by
          dsimp only
          rw [Function.update_self]
          exact hcr j hj)
        (by dsimp only
            rw [Function.update_self]
            show (c.work 6).head - 1 = h
            rw [hhd]
            omega)
    refine ⟨c', .step hstep₁ hreach, h1, h2, ?_, ?_, h5, h6⟩
    · intro i hi
      rw [h3 i hi]
      dsimp only
      rw [Function.update_of_ne hi]
    · rw [h4]
      dsimp only
      rw [Function.update_self]
      rfl

/-- The round loop: one input sweep per scratch mark, each appending
    `|x| + 1` marks at the clock's frontier in `2|x| + 3` steps. -/
private theorem clockMul_drive_run (x : List Bool) (v : ℕ) (m : ℕ) :
    ∀ (r : ℕ), v = r + m →
      ∀ (c : Cfg 8 clockMulTM.Q),
      c.state = .drive →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells → c.input.head = 1 →
      (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 5).cells = regCells v → (c.work 5).head = r + 1 →
      (c.work 6).cells = regCells (r * (x.length + 1)) →
      (c.work 6).head = r * (x.length + 1) + 1 →
      ∃ c' t, t ≤ m * (2 * x.length + 3) ∧ clockMulTM.reachesIn t c c' ∧
        c'.state = .drive ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ c'.input.head = 1 ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 5).cells = regCells v ∧ (c'.work 5).head = v + 1 ∧
        (c'.work 6).cells = regCells (v * (x.length + 1)) ∧
        (c'.work 6).head = v * (x.length + 1) + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro r hr c hst hic hih hoth hout hcl5 hhd5 hcl6 hhd6
    obtain rfl : v = r := by omega
    exact ⟨c, 0, by omega, .zero, hst, hic, hih, fun _ _ _ => rfl, hcl5, hhd5,
      hcl6, hhd6, rfl⟩
  | succ m ih =>
    intro r hr c hst hic hih hoth hout hcl5 hhd5 hcl6 hhd6
    -- consume the r-th scratch mark
    have h5one : (c.work 5).read = Γ.one := by
      rw [Tape.read, hhd5, hcl5]
      exact regCells_one (by omega) (by omega)
    have hinpr : c.input.read ≠ Γ.start := by
      rw [Tape.read, hih, hic]
      exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
    have h6blank : (c.work 6).read = Γ.blank := by
      rw [Tape.read, hhd6, hcl6]
      exact regCells_blank le_rfl
    have hstep₁ := clockMul_step_drive_one c hst h5one hinpr
      (fun i hi => by
        by_cases hir : i = (6 : Fin 8)
        · subst hir
          rw [h6blank]
          decide
        · exact hoth i hi hir)
      hout
    -- the input sweep
    have h5read₁ : (((c.work 5).move .right)).read ≠ Γ.start := by
      show (c.work 5).cells ((c.work 5).head + 1) ≠ Γ.start
      rw [hhd5, hcl5]
      exact regCells_ne_start (by omega)
    obtain ⟨c₂, hr₂, hst₂, hic₂, hih₂, hw₂, hcl₂, hhd₂, ho₂⟩ :=
      clockMul_inScan_run x x.length 0 (r * (x.length + 1)) (by omega)
        { state := .inScan, input := c.input,
          work := Function.update c.work 5 ((c.work 5).move .right),
          output := c.output } rfl hic
        (by rw [hih])
        (fun i hi => by
          by_cases hir : i = (5 : Fin 8)
          · subst hir
            dsimp only
            rw [Function.update_self]
            exact h5read₁
          · dsimp only
            rw [Function.update_of_ne hir]
            exact hoth i hir hi)
        hout
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5)]
            exact hcl6)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5)]
            exact hhd6)
    -- the final mark of the round and the turn
    have hoth₂ : ∀ i, i ≠ (6 : Fin 8) → (c₂.work i).read ≠ Γ.start := fun i hi => by
      rw [hw₂ i hi]
      by_cases hir : i = (5 : Fin 8)
      · subst hir
        dsimp only
        rw [Function.update_self]
        exact h5read₁
      · dsimp only
        rw [Function.update_of_ne hir]
        exact hoth i hir hi
    have ho₂r : c₂.output.read ≠ Γ.start := by rw [ho₂]; exact hout
    have hibl₂ : c₂.input.read = Γ.blank := by
      rw [Tape.read, hih₂, hic₂]
      exact Tape.init_ofBool_cells_ge x x.length le_rfl
    have hstep₃ := clockMul_step_inScan_blank c₂ hst₂ hibl₂ hoth₂ ho₂r
    have hc₃cl : (((c₂.work 6).write Γw.one).move .right).cells
        = regCells (r * (x.length + 1) + x.length + 1) := by
      rw [Tape.move_cells, Tape.write, ite_eq_right (by rw [hhd₂]; omega)]
      show Function.update (c₂.work 6).cells (c₂.work 6).head Γw.one.toΓ = _
      rw [hhd₂, hcl₂]
      exact regCells_update_succ (r * (x.length + 1) + x.length)
    have hc₃hd : (((c₂.work 6).write Γw.one).move .right).head
        = r * (x.length + 1) + x.length + 1 + 1 := by
      show ((c₂.work 6).write Γw.one).head + 1 = _
      rw [Tape.write_head, hhd₂]
    -- the input rewind
    obtain ⟨c₄, hr₄, hst₄, hic₄, hih₄, hw₄, ho₄⟩ :=
      clockMul_inRew_run x x.length
        { state := .inRew, input := c₂.input.move .left,
          work := Function.update c₂.work 6 (((c₂.work 6).write Γw.one).move .right),
          output := c₂.output } rfl
        (by show (c₂.input.move .left).cells = _
            rw [Tape.move_cells]
            exact hic₂)
        (by show c₂.input.head - 1 = x.length
            rw [hih₂]
            omega)
        (fun i => by
          by_cases hir : i = (6 : Fin 8)
          · subst hir
            dsimp only
            rw [Function.update_self, Tape.read, hc₃cl, hc₃hd]
            rw [regCells_blank le_rfl]
            decide
          · dsimp only
            rw [Function.update_of_ne hir]
            exact hoth₂ i hir)
        ho₂r
    -- recurse on the remaining rounds
    have harith : (r + 1) * (x.length + 1) = r * (x.length + 1) + x.length + 1 := by
      have := Nat.succ_mul r (x.length + 1)
      omega
    obtain ⟨c', t', ht', hreach', g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
      ih (r + 1) (by omega) c₄ hst₄ hic₄ hih₄
        (fun i hi5 hi6 => by
          rw [hw₄]
          dsimp only
          rw [Function.update_of_ne hi6, hw₂ i hi6]
          dsimp only
          rw [Function.update_of_ne hi5]
          exact hoth i hi5 hi6)
        (by rw [ho₄, ho₂]; exact hout)
        (by rw [hw₄]
            dsimp only
            rw [Function.update_of_ne (by decide : (5 : Fin 8) ≠ 6),
              hw₂ 5 (by decide)]
            dsimp only
            rw [Function.update_self, Tape.move_cells]
            exact hcl5)
        (by rw [hw₄]
            dsimp only
            rw [Function.update_of_ne (by decide : (5 : Fin 8) ≠ 6),
              hw₂ 5 (by decide)]
            dsimp only
            rw [Function.update_self]
            show (c.work 5).head + 1 = (r + 1) + 1
            rw [hhd5])
        (by rw [hw₄]
            dsimp only
            rw [Function.update_self, hc₃cl, harith])
        (by rw [hw₄]
            dsimp only
            rw [Function.update_self, hc₃hd, harith])
    refine ⟨c', x.length + (x.length + 1 + t' + 1) + 1, ?_,
      .step hstep₁ (reachesIn_trans _ hr₂ (.step hstep₃ (reachesIn_trans _ hr₄ hreach'))),
      g1, g2, g3, ?_, g5, g6, g7, g8, ?_⟩
    · have hmul : (m + 1) * (2 * x.length + 3)
          = m * (2 * x.length + 3) + (2 * x.length + 3) :=
        Nat.succ_mul m (2 * x.length + 3)
      omega
    · intro i hi5 hi6
      rw [g4 i hi5 hi6, hw₄]
      dsimp only
      rw [Function.update_of_ne hi6, hw₂ i hi6]
      dsimp only
      rw [Function.update_of_ne hi5]
    · rw [g9, ho₄, ho₂]

/-- **`clockMulTM` Hoare specification.** From `regTape v` on the scratch tape
    and `regTape 0` on the clock tape, with the input head parked at cell 1,
    reach `regTape 0` on the scratch and `regTape (v * (|x| + 1))` on the clock;
    the input tape, the output tape, and every other work tape are preserved
    exactly. -/
private theorem clockMulTM_hoareTime (v : ℕ) (x : List Bool) (work₀ : Fin 8 → Tape)
    (hoth : ∀ i : Fin 8, i ≠ 5 → i ≠ 6 → (work₀ i).read ≠ Γ.start)
    (h5 : work₀ 5 = regTape v) (h6 : work₀ 6 = regTape 0) :
    clockMulTM.HoareTime
      (fun inp work out =>
        inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        work = work₀ ∧ outF out)
      (fun inp work out =>
        inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work 5 = regTape 0 ∧ work 6 = regTape (v * (x.length + 1)) ∧ outF out)
      (v * (2 * x.length + 3) + v * (x.length + 1) + v + 5) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have houtr : out.read ≠ Γ.start := outF_read_ne_start hout
  -- the round loop
  obtain ⟨c₁, t₁, ht₁, hr₁, hst₁, hic₁, hih₁, hw₁, hcl5₁, hhd5₁, hcl6₁, hhd6₁, ho₁⟩ :=
    clockMul_drive_run x v v 0 (by omega)
      { state := clockMulTM.qstart,
        input := ⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩,
        work := work, output := out } rfl rfl rfl
      (fun i hi5 hi6 => hoth i hi5 hi6)
      houtr
      (by show (work 5).cells = regCells v
          rw [h5]
          rfl)
      (by show (work 5).head = 0 + 1
          rw [h5]
          rfl)
      (by show (work 6).cells = regCells (0 * (x.length + 1))
          rw [Nat.zero_mul, h6]
          rfl)
      (by show (work 6).head = 0 * (x.length + 1) + 1
          rw [Nat.zero_mul, h6]
          rfl)
  -- exit the loop at the scratch's first blank
  have hinp₁r : c₁.input.read ≠ Γ.start := by
    rw [Tape.read, hih₁, hic₁]
    exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
  have ho₁r : c₁.output.read ≠ Γ.start := by rw [ho₁]; exact houtr
  have h5bl₁ : (c₁.work 5).read = Γ.blank := by
    rw [Tape.read, hhd5₁, hcl5₁]
    exact regCells_blank le_rfl
  have h6bl₁ : (c₁.work 6).read = Γ.blank := by
    rw [Tape.read, hhd6₁, hcl6₁]
    exact regCells_blank le_rfl
  have hoth₁ : ∀ i, i ≠ (5 : Fin 8) → (c₁.work i).read ≠ Γ.start := fun i hi => by
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [h6bl₁]
      decide
    · rw [hw₁ i hi hir]
      exact hoth i hi hir
  have hstep₂ := clockMul_step_drive_blank c₁ hst₁ h5bl₁ hinp₁r hoth₁ ho₁r
  -- blank the scratch on the way down
  obtain ⟨c₃, hr₃, hst₃, hin₃, hw₃, h5₃, ho₃⟩ :=
    clockMul_rewC_run v
      { state := .rewC, input := c₁.input,
        work := Function.update c₁.work 5 ((c₁.work 5).move .left),
        output := c₁.output } rfl hinp₁r
      (fun i hi => by
        dsimp only
        rw [Function.update_of_ne hi]
        exact hoth₁ i hi)
      ho₁r
      (by dsimp only
          rw [Function.update_self, Tape.move_cells]
          exact hcl5₁)
      (by dsimp only
          rw [Function.update_self]
          show (c₁.work 5).head - 1 = v
          rw [hhd5₁]
          omega)
  -- rewind the clock from its frontier
  have hw₃6 : c₃.work 6 = c₁.work 6 := by
    rw [hw₃ 6 (by decide)]
    dsimp only
    rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5)]
  obtain ⟨c₄, hr₄, hst₄, hin₄, hw₄, hcl₄, hhd₄, ho₄⟩ :=
    clockMul_rew6_run (v * (x.length + 1) + 1) c₃ hst₃
      (by rw [hin₃]; exact hinp₁r)
      (fun i hi => by
        by_cases hir : i = (5 : Fin 8)
        · subst hir
          rw [h5₃]
          exact (parked_regTape 0).read_ne_start
        · rw [hw₃ i hir]
          dsimp only
          rw [Function.update_of_ne hir]
          exact hoth₁ i hir)
      (by rw [ho₃]; exact ho₁r)
      (by rw [hw₃6, hcl6₁]; rfl)
      (fun j hj => by
        rw [hw₃6, hcl6₁]
        exact regCells_ne_start hj)
      (by rw [hw₃6]; exact hhd6₁)
  refine ⟨c₄, _, ?_,
    reachesIn_trans _ hr₁ (.step hstep₂ (reachesIn_trans _ hr₃ hr₄)),
    hst₄, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : v * (x.length + 1) + 1 + 2 = v * (x.length + 1) + 3 := by omega
    omega
  · rw [hin₄, hin₃]
    refine Tape.ext hih₁ hic₁
  · intro i hi5 hi6
    rw [hw₄ i hi6, hw₃ i hi5]
    dsimp only
    rw [Function.update_of_ne hi5]
    exact hw₁ i hi5 hi6
  · rw [hw₄ 5 (by decide)]
    exact h5₃
  · refine Tape.ext hhd₄ ?_
    rw [hcl₄, hw₃6, hcl6₁, regT_cells]
  · rw [ho₄, ho₃, ho₁]
    exact hout

end ClockMul

-- ════════════════════════════════════════════════════════════════════════
-- Closure under multiplication by n + 1, and polynomial clocks
-- ════════════════════════════════════════════════════════════════════════

/-- **Closure under multiplication by `n + 1`.** Run the `g`-clock, move
    its register to the scratch tape (`moveClockTM`), then append it to the
    clock tape's frontier once per input position (`clockMulTM`), producing
    `regTape (g n * (n + 1))` in time `O(g n * (n + 1) + n)`. This is where
    the designated scratch tape 5 earns its keep. -/
theorem ClockConstructible.mul_succ {g : ℕ → ℕ} (h : ClockConstructible g) :
    ClockConstructible (fun n => g n * (n + 1)) := by
  obtain ⟨tm, C, hspec⟩ := h
  refine ⟨seqTM tm (seqTM moveClockTM clockMulTM), C + 20, ?_⟩
  intro x work₀ hpark h5 h6
  have hb5 : work₀ (5 : Fin 8) = regTape 0 := by
    rw [h5, Tape.init_move_right_eq_regT_zero]
  have hinpX : ((⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape)).read ≠ Γ.start := by
    show (Tape.init (x.map Γ.ofBool)).cells 1 ≠ Γ.start
    exact Tape.init_ofBool_cells_ne_start x 1 le_rfl
  -- phase 1: the g-clock
  have h₁ := hspec x work₀ hpark h5 h6
  -- ghost frames after phases 1 and 2
  set W₁ : Fin 8 → Tape := Function.update work₀ 6 (regTape (g x.length)) with hW₁
  set W₂ : Fin 8 → Tape :=
    Function.update (Function.update W₁ 5 (regTape (g x.length))) 6 (regTape 0) with hW₂
  have hW₁5 : W₁ 5 = regTape 0 := by
    rw [hW₁, Function.update_of_ne (by decide : (5 : Fin 8) ≠ 6)]
    exact hb5
  have hW₁6 : W₁ 6 = regTape (g x.length) := by
    rw [hW₁, Function.update_self]
  have hW₁oth : ∀ i : Fin 8, i ≠ 5 → i ≠ 6 → (W₁ i).read ≠ Γ.start := by
    intro i hi5 hi6
    rw [hW₁, Function.update_of_ne hi6]
    exact (hpark i).2
  have hW₁all : ∀ i : Fin 8, (W₁ i).read ≠ Γ.start := by
    intro i
    by_cases hi6 : i = (6 : Fin 8)
    · subst hi6
      rw [hW₁6]
      exact (parked_regTape _).read_ne_start
    · rw [hW₁, Function.update_of_ne hi6]
      exact (hpark i).2
  have hW₂5 : W₂ 5 = regTape (g x.length) := by
    rw [hW₂, Function.update_of_ne (by decide : (5 : Fin 8) ≠ 6),
      Function.update_self]
  have hW₂6 : W₂ 6 = regTape 0 := by
    rw [hW₂, Function.update_self]
  have hW₂oth : ∀ i : Fin 8, i ≠ 5 → i ≠ 6 → (W₂ i).read ≠ Γ.start := by
    intro i hi5 hi6
    rw [hW₂, Function.update_of_ne hi6, Function.update_of_ne hi5]
    exact hW₁oth i hi5 hi6
  have hW₂all : ∀ i : Fin 8, (W₂ i).read ≠ Γ.start := by
    intro i
    by_cases hi5 : i = (5 : Fin 8)
    · subst hi5
      rw [hW₂5]
      exact (parked_regTape _).read_ne_start
    · by_cases hi6 : i = (6 : Fin 8)
      · subst hi6
        rw [hW₂6]
        exact (parked_regTape _).read_ne_start
      · exact hW₂oth i hi5 hi6
  -- phases 2 and 3
  have h₂ := moveClockTM_hoareTime (g x.length)
    (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) W₁ hinpX hW₁oth hW₁5 hW₁6
  have h₃ := clockMulTM_hoareTime (g x.length) x W₂ hW₂oth hW₂5 hW₂6
  -- phase 2 → phase 3 transition
  have htrans₂₃ : ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → work i = W₁ i) ∧
        work 5 = regTape (g x.length) ∧ work 6 = regTape 0 ∧ outF out) →
      (transitionInput inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        (fun i => transitionTape (work i)) = W₂ ∧ outF (transitionTape out)) := by
    rintro inp work out ⟨rfl, hw, hw5, hw6, hout⟩
    have hweq : work = W₂ := by
      funext i
      by_cases hi6 : i = (6 : Fin 8)
      · subst hi6
        rw [hw6, hW₂6]
      · by_cases hi5 : i = (5 : Fin 8)
        · subst hi5
          rw [hw5, hW₂5]
        · rw [hw i hi5 hi6, hW₂, Function.update_of_ne hi6,
            Function.update_of_ne hi5]
    subst hweq
    obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
      phaseTransition_eq_self_of_reads_ne_start hinpX hW₂all
        (outF_read_ne_start hout)
    rw [hinputEq, hworkEq, houtputEq]
    exact ⟨rfl, rfl, hout⟩
  have hseq₂₃ := seqTM_hoareTime moveClockTM clockMulTM h₂ htrans₂₃ h₃
  -- phase 1 → phase 2 transition
  have htrans₁₂ : ∀ (inp : Tape) (work : Fin 8 → Tape) (out : Tape),
      (inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work (6 : Fin 8) = regTape (g x.length) ∧
        out.head = 1 ∧ out.cells 0 = Γ.start ∧
        (∀ j, 1 ≤ j → out.cells j ≠ Γ.start)) →
      (transitionInput inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) ∧
        (fun i => transitionTape (work i)) = W₁ ∧ outF (transitionTape out)) := by
    rintro inp work out ⟨hic, hih, hw, hw6, ho1, ho2, ho3⟩
    have hinp_eq : inp = (⟨1, (Tape.init (x.map Γ.ofBool)).cells⟩ : Tape) :=
      Tape.ext hih hic
    subst hinp_eq
    have hweq : work = W₁ := by
      funext i
      by_cases hi6 : i = (6 : Fin 8)
      · subst hi6
        rw [hw6, hW₁6]
      · rw [hw i hi6, hW₁, Function.update_of_ne hi6]
    subst hweq
    have houtF : outF out := ⟨ho1, ho2, ho3⟩
    obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
      phaseTransition_eq_self_of_reads_ne_start hinpX hW₁all
        (outF_read_ne_start houtF)
    rw [hinputEq, hworkEq, houtputEq]
    exact ⟨rfl, rfl, houtF⟩
  have hseq := seqTM_hoareTime tm (seqTM moveClockTM clockMulTM) h₁ htrans₁₂ hseq₂₃
  -- massage into the ClockConstructible shape
  refine hseq.consequence (fun _ _ _ hp => hp) ?_ ?_
  · rintro inp work out ⟨rfl, hw, hw5, hw6, hout⟩
    refine ⟨rfl, rfl, ?_, hw6, hout.1, hout.2.1, hout.2.2⟩
    intro i hi6
    by_cases hi5 : i = (5 : Fin 8)
    · subst hi5
      rw [hw5, ← Tape.init_move_right_eq_regT_zero, ← h5]
    · rw [hw i hi5 hi6, hW₂, Function.update_of_ne hi6, Function.update_of_ne hi5,
        hW₁, Function.update_of_ne hi6]
  · show C * (g x.length + x.length + 1) + 1 +
        (2 * g x.length + 4 + 1 +
          (g x.length * (2 * x.length + 3) + g x.length * (x.length + 1) +
            g x.length + 5))
        ≤ (C + 20) * (g x.length * (x.length + 1) + x.length + 1)
    have e1 : g x.length * (2 * x.length + 3)
        = 2 * (g x.length * x.length) + 3 * g x.length := by ring
    have e2 : g x.length * (x.length + 1) = g x.length * x.length + g x.length := by
      ring
    have e3 : C * (g x.length + x.length + 1)
        = C * g x.length + C * x.length + C := by ring
    have e4 : (C + 20) * (g x.length * x.length + g x.length + x.length + 1)
        = C * (g x.length * x.length) + C * g x.length + C * x.length + C
          + 20 * (g x.length * x.length) + 20 * g x.length + 20 * x.length + 20 := by
      ring
    rw [e2]
    omega

/-- **Polynomial clocks**: every positive power of `n + 1` is
    clock-constructible — the clock family the time hierarchy theorem uses
    against polynomial time bounds. -/
theorem clockConstructible_pow : ∀ k, 1 ≤ k →
    ClockConstructible (fun n => (n + 1) ^ k) := by
  intro k
  induction k with
  | zero =>
    intro h
    exact absurd h (by omega)
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact clockConstructible_succ.congr fun n => by rw [Nat.pow_one]
    · exact ((ih hkpos).mul_succ).congr fun n => by rw [Nat.pow_succ]

end TM

end Complexity
