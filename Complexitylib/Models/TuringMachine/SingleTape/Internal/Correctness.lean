/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.SingleTape.Internal.Delta
public import Complexitylib.Models.TuringMachine.Internal
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Single-tape simulation — correctness internals

The config-level correspondence `Corr` between a `singleTapeSim N` configuration
and an `N` configuration at a macro-step boundary, and the **macro-step
correspondence** `corr_macroStep` (one `N`-step ↦ several simulator steps,
preserving `Corr`). The behavioural lemmas (`SingleTape.lean`) follow by
iterating `corr_macroStep` over `N`'s computation and translating acceptance.

See `docs/A4-SingleTapeSimulation.md`. Proof internals only.
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n : ℕ}

end NTM

namespace NTM.SingleTape

/-- **Config correspondence.** At a macro-step boundary, the `singleTapeSim N`
    configuration `c1` corresponds to the `N` configuration `c`: same simulated
    state, work head parked at cell 0/1, identical input and output tapes, and
    the single work tape encodes `N`'s `k` work tapes (materialized up to `M`). -/
structure Corr {k : ℕ} (N : NTM k) (M : ℕ)
    (c1 : Cfg 1 (SimQ k N.Q)) (c : Cfg k N.Q) : Prop where
  /-- `c1` is at the `run` phase for `N`'s current state. -/
  state : c1.state = SimQ.run c.state
  /-- The single work head is parked at cell 0 (initial) or cell 1 (post-commit). -/
  headLe : (c1.work 0).head ≤ 1
  /-- Input tapes coincide (input is read-only, carried over verbatim). -/
  inputEq : c1.input = c.input
  /-- Output tapes coincide (the simulator writes output exactly as `N` does). -/
  outputEq : c1.output = c.output
  /-- The single work tape encodes `N`'s `k` work tapes. -/
  inv : SimInvAt k (c1.work 0) c.work M
  /-- Each `N` work tape is blank beyond the materialized region (heads never
      reached there). Needed to materialize the fresh block at SCATTER. -/
  wbeyond : ∀ (j : Fin k) (p : ℕ), M < p → (c.work j).cells p = Γ.blank
  /-- The input tape has `▷` only at cell `0` (input is read-only; cells hold
      `{0,1,□}`). Lets the phases keep the input head off `▷` (the `▷`-dodge). -/
  inputWf : ∀ p : ℕ, 1 ≤ p → c.input.cells p ≠ Γ.start
  /-- The output tape has `▷` only at cell `0` (writes use `Γw`, never `▷`). -/
  outputWf : ∀ p : ℕ, 1 ≤ p → c.output.cells p ≠ Γ.start

/-- **Base case.** The initial `singleTapeSim N` configuration corresponds to
    `N`'s initial configuration, materialized to `M = 0` (empty used region). -/
theorem corr_init {k : ℕ} (N : NTM k) (x : List Bool) :
    Corr N 0 ((singleTapeSim N).initCfg x) (N.initCfg x) where
  state := rfl
  headLe := Nat.zero_le 1
  inputEq := rfl
  outputEq := rfl
  inv := simInvAt_init k
  wbeyond := fun _ p hp => by
    show (Tape.init []).cells p = Γ.blank
    simp only [Tape.init]
    rw [ite_eq_right (by omega : ¬ p = 0)]
    simp
  inputWf := fun p hp => by
    show (Tape.init (x.map Γ.ofBool)).cells p ≠ Γ.start
    simp only [Tape.init, ite_eq_right (show ¬ p = 0 by omega)]
    cases h : (List.map Γ.ofBool x)[p - 1]? with
    | none => decide
    | some g =>
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
      cases b <;> decide
  outputWf := fun p hp => by
    show (Tape.init []).cells p ≠ Γ.start
    simp only [Tape.init]
    rw [ite_eq_right (by omega : ¬ p = 0)]
    simp

/-- Writing back the read symbol preserves whether a cell holds the accept bit
    `1` (`readBackWrite` fixes `0/1/□` and maps `▷ ↦ □`, never producing a
    spurious `1`). -/
theorem readBackWrite_one_iff (g : Γ) :
    ((TM.readBackWrite g : Γw) : Γ) = Γ.one ↔ g = Γ.one := by
  cases g <;> decide

/-- The halt step's output action — `writeAndMove` writing back the read
    symbol — preserves the accept bit at cell 1. -/
theorem accept_bit_preserved (t : Tape) (d : Dir3) :
    (t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) d).cells 1 = Γ.one
      ↔ t.cells 1 = Γ.one := by
  have hcells : (t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) d).cells
              = (t.write ((TM.readBackWrite t.read : Γw) : Γ)).cells := by
    cases d <;> rfl
  rw [hcells, Tape.write]
  by_cases hh0 : t.head = 0
  · simp [hh0]
  · rw [ite_eq_right hh0]
    simp only [Function.update_apply]
    by_cases h1 : (1 : ℕ) = t.head
    · rw [ite_eq_left h1, Tape.read, ← h1, readBackWrite_one_iff]
    · rw [ite_eq_right h1]

/-- **Halt correspondence.** When `N` has halted, the simulator (parked at
    `run N.qhalt`) takes one step to `SimQ.halt`, preserving the accept bit. -/
theorem halted_of_corr {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hh : c.state = N.qhalt) :
    (singleTapeSim N).halted ((singleTapeSim N).trace 1 (fun _ => false) c1) ∧
    (((singleTapeSim N).trace 1 (fun _ => false) c1).output.cells 1 = Γ.one
      ↔ c.output.cells 1 = Γ.one) := by
  have hst : c1.state = SimQ.run N.qhalt := by rw [hcorr.state, hh]
  refine ⟨?_, ?_⟩
  · show ((singleTapeSim N).trace 1 (fun _ => false) c1).state = (singleTapeSim N).qhalt
    simp only [NTM.trace, singleTapeSim, simDelta, hst, SimQ.run, SimQ.halt, reduceCtorEq,
      ↓reduceIte]
  · have hout : ((singleTapeSim N).trace 1 (fun _ => false) c1).output
        = c1.output.writeAndMove ((TM.readBackWrite c1.output.read : Γw) : Γ)
            (TM.idleDir c1.output.read) := by
      simp only [NTM.trace, singleTapeSim, simDelta, hst, SimQ.run, SimQ.halt, reduceCtorEq,
        ↓reduceIte]
    rw [hout, accept_bit_preserved, hcorr.outputEq]

/-- Per-macro-step sim-step budget at materialization level `M`: a generous bound
    covering the four sweeps over an `≈ 3k·M`-cell region plus the `run`/`commit`
    steps. The `16·(k+1)` constant matches `singleTapeSimTime`. -/
def macroBound (k M : ℕ) : ℕ := 16 * (k + 1) * (M + 1)

/-- `macroBound k` is monotone in the materialization level `M`. -/
theorem macroBound_mono {k M M' : ℕ} (h : M ≤ M') : macroBound k M ≤ macroBound k M' := by
  unfold macroBound
  exact Nat.mul_le_mul_left _ (by omega)

/-! ### Per-phase config transitions (building blocks for `corr_macroStep`)

Each lemma reduces `trace`-of-a-phase to the explicit next configuration; the
full macro-step composes them via `trace_add_fun`. -/

/-- The **run** step (1 sim step): from a `run q` config with `q ≠ N.qhalt`, the
    simulator initialises GATHER (`acc = ▷`, reads `iSym`/`oSym`, sweep at the
    start) and repositions the work head to cell 1. Input/output are advanced by
    `idleDir` (the `▷`-dodge); the work tape's cells are preserved
    (`readBackWrite`). -/
theorem run_step {k : ℕ} (N : NTM k) (q : N.Q) (hq : q ≠ N.qhalt) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.run q) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := SimQ.gather (q, (fun _ => Γ.start), c1.input.read, c1.output.read,
          (0, 0), false, Γ.blank),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun i => (c1.work i).writeAndMove
          ((TM.readBackWrite ((c1.work 0).read) : Γw) : Γ) (TM.idleDir ((c1.work 0).read)),
        output := c1.output.writeAndMove
          ((TM.readBackWrite c1.output.read : Γw) : Γ) (TM.idleDir c1.output.read) } := by
  simp only [hst, singleTapeSim, simDelta, runStep, SimQ.run, SimQ.halt, SimQ.gather,
    hq, reduceCtorEq, ↓reduceIte, NTM.trace]

/-- The **commit** step (1 sim step): from a `commit (q', oW, oD, iD, iSym, oSym)`
    config, the simulator applies the deferred output write/move and input move
    (accounting for the `▷`-dodge via the `iSym`/`oSym` guards) and returns to
    `run q'`. The work tape is preserved. -/
theorem commit_step {k : ℕ} (N : NTM k) (q' : N.Q) (oW : Γw) (oD iD : Dir3)
    (iSym oSym : Γ) (b : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.commit (q', oW, oD, iD, iSym, oSym)) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := SimQ.run q',
        input := c1.input.move
          (if iSym = Γ.start then TM.idleDir c1.input.read else safeDir c1.input.read iD),
        work := fun i => (c1.work i).writeAndMove
          ((TM.readBackWrite ((c1.work 0).read) : Γw) : Γ) (TM.idleDir ((c1.work 0).read)),
        output := c1.output.writeAndMove
          ((if oSym = Γ.start then TM.readBackWrite c1.output.read else oW : Γw) : Γ)
          (if oSym = Γ.start then TM.idleDir c1.output.read else safeDir c1.output.read oD) } := by
  simp only [hst, singleTapeSim, simDelta, commitStep, SimQ.commit, SimQ.run, SimQ.halt,
    Sum.inr.injEq, reduceCtorEq, ↓reduceIte, NTM.trace]

/-- One **gather** step (`trace 1`): from a `gather d` config, the result is the
    configuration built from `gatherStep`'s output (the trace step applied to the
    `gather` branch of `simDelta`). The basis of the gather-sweep induction. -/
theorem gather_trace1 {k : ℕ} (N : NTM k) (d : GatherData k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.gather d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := gatherStep N b d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  simp only [hst, singleTapeSim, simDelta, SimQ.gather, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- A GATHER work step (`readBackWrite`, move right) on a tape reading a non-`▷`
    cell just advances the head by one, leaving contents intact. -/
private theorem work_gather_step (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ Dir3.right = { t with head := t.head + 1 } := by
  rw [TM.toΓ_readBackWrite_of_ne_start h]
  show (t.write t.read).move Dir3.right = { t with head := t.head + 1 }
  unfold Tape.write Tape.read
  split <;> simp [Tape.move, Function.update_eq_self]

/-- Writing a value to a cell (head ≥ 1) and moving right updates that cell and
    advances the head. Used for SCATTER cells that are overwritten. -/
private theorem work_write_right (t : Tape) (s : Γ) (h : 1 ≤ t.head) :
    t.writeAndMove s Dir3.right = ⟨t.head + 1, Function.update t.cells t.head s⟩ := by
  show (t.write s).move Dir3.right = _
  simp only [Tape.write, show ¬(t.head = 0) by omega, ↓reduceIte, Tape.move]

/-- Writing a value to a cell (head ≥ 1) and moving left updates that cell and
    retreats the head. Used for SCATTER sweep-2 cells (head-bits moved left). -/
private theorem work_write_left (t : Tape) (s : Γ) (h : 1 ≤ t.head) :
    t.writeAndMove s Dir3.left = ⟨t.head - 1, Function.update t.cells t.head s⟩ := by
  show (t.write s).move Dir3.left = _
  simp only [Tape.write, show ¬(t.head = 0) by omega, ↓reduceIte, Tape.move]

/-- Writing a cell its own current value and moving right just advances the head
    (the write is a no-op). Used for SCATTER cells that aren't overwritten. -/
private theorem work_write_eq (t : Tape) (s : Γ) (h : t.read = s) :
    t.writeAndMove s Dir3.right = { t with head := t.head + 1 } := by
  obtain rfl : s = t.cells t.head := h.symm
  show (t.write (t.cells t.head)).move Dir3.right = { t with head := t.head + 1 }
  unfold Tape.write
  split <;> simp [Tape.move, Function.update_eq_self]

/-- A REWIND work step (`readBackWrite`, move left) on a tape reading a non-`▷`
    cell just retreats the head by one, leaving contents intact. -/
private theorem work_rewind_step (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ Dir3.left = { t with head := t.head - 1 } := by
  rw [TM.toΓ_readBackWrite_of_ne_start h]
  show (t.write t.read).move Dir3.left = { t with head := t.head - 1 }
  unfold Tape.write Tape.read
  split <;> simp [Tape.move, Function.update_eq_self]

/-- A blank-write + move right on a tape at cell `0` lands at cell `1`, contents
    intact (the write at cell `0` is a no-op). The REWIND→SCATTER turn-around. -/
private theorem work_blank_right_at0 (t : Tape) (h : t.head = 0) :
    t.writeAndMove Γw.blank.toΓ Dir3.right = { t with head := 1 } := by
  show (t.write Γw.blank.toΓ).move Dir3.right = { t with head := 1 }
  simp only [Tape.write, h, ↓reduceIte, Tape.move]

/-- An idle (`stay`) move on a tape reading a non-`▷` cell is a no-op. -/
private theorem tape_idle_stay (t : Tape) (h : t.read ≠ Γ.start) :
    t.move (TM.idleDir t.read) = t := by
  simp [TM.idleDir, h, Tape.move]

/-- A `readBackWrite`+idle step on a tape reading a non-`▷` cell is a no-op. -/
private theorem tape_idle_writeMove (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read) = t := by
  rw [TM.toΓ_readBackWrite_of_ne_start h]
  simp only [TM.idleDir, h, ↓reduceIte]
  show (t.write t.read).move Dir3.stay = t
  unfold Tape.write Tape.read
  split <;> simp [Tape.move, Function.update_eq_self]

/-- The **run/commit work action** (`readBackWrite` + `idleDir`) leaves the work
    tape's cells intact and parks the head at cell `1`. At cell `0` the write is a
    no-op and `idleDir` (`▷ ↦ right`) advances to cell `1`; at cell `1` the read is a
    non-`▷` code cell, so writing it back is a no-op and `idleDir` stays. -/
private theorem run_work_eq (t : Tape) (h : t.head ≤ 1) (hcell0 : t.cells 0 = Γ.start)
    (hns1 : t.cells 1 ≠ Γ.start) :
    t.writeAndMove ((TM.readBackWrite t.read : Γw) : Γ) (TM.idleDir t.read)
      = { head := 1, cells := t.cells } := by
  by_cases h0 : t.head = 0
  · have hr : t.read = Γ.start := by rw [Tape.read, h0]; exact hcell0
    rw [hr]
    show t.writeAndMove Γw.blank.toΓ Dir3.right = { head := 1, cells := t.cells }
    rw [work_blank_right_at0 t h0]
  · have hh1 : t.head = 1 := by omega
    have hr : t.read ≠ Γ.start := by rw [Tape.read, hh1]; exact hns1
    rw [tape_idle_writeMove t hr, ← hh1]

/-- After an `idleDir` **move**, a tape whose cells `≥ 1` are non-`▷` reads a non-`▷`
    cell: reading `▷` (necessarily at cell `0`) dodges right to cell `1`; off `▷` it
    stays. The input head's `▷`-dodge invariant for the gather/rewind/scatter phases. -/
private theorem move_idle_read_ne (t : Tape) (hwf : ∀ p, 1 ≤ p → t.cells p ≠ Γ.start) :
    (t.move (TM.idleDir t.read)).read ≠ Γ.start := by
  by_cases hr : t.read = Γ.start
  · have h0 : t.head = 0 := by
      by_contra h0; exact hwf t.head (Nat.one_le_iff_ne_zero.mpr h0) hr
    rw [TM.idleDir_right_of_start hr]
    show (t.move Dir3.right).cells (t.move Dir3.right).head ≠ Γ.start
    simp only [Tape.move, h0]
    exact hwf 1 (le_refl 1)
  · rw [tape_idle_stay t hr]; exact hr

/-- After the `readBackWrite`/`idleDir` **write-move** (the run/commit output action),
    a tape whose cells `≥ 1` are non-`▷` reads a non-`▷` cell (same `▷`-dodge). -/
private theorem writeMove_idle_read_ne (t : Tape) (hwf : ∀ p, 1 ≤ p → t.cells p ≠ Γ.start) :
    (t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read)).read ≠ Γ.start := by
  by_cases hr : t.read = Γ.start
  · have h0 : t.head = 0 := by
      by_contra h0; exact hwf t.head (Nat.one_le_iff_ne_zero.mpr h0) hr
    rw [hr, TM.idleDir_start]
    show (t.writeAndMove Γw.blank.toΓ Dir3.right).read ≠ Γ.start
    rw [work_blank_right_at0 t h0]
    exact hwf 1 (le_refl 1)
  · rw [tape_idle_writeMove t hr]; exact hr

/-- **COMMIT input reconciliation.** The COMMIT input move (guarded by the recorded
    `iSym = t.read`) exactly undoes the RUN dodge: composed with the RUN move it equals
    `N`'s single input move `t.move iD`. At `▷` both nets to `right` (`δ_right_of_start`);
    off `▷` the RUN move is a no-op and COMMIT's `safeDir` yields `iD`. -/
private theorem commit_input_eq (t : Tape) (iD : Dir3)
    (hwf : ∀ p, 1 ≤ p → t.cells p ≠ Γ.start) (hright : t.read = Γ.start → iD = Dir3.right) :
    (t.move (TM.idleDir t.read)).move
        (if t.read = Γ.start then TM.idleDir (t.move (TM.idleDir t.read)).read
         else safeDir (t.move (TM.idleDir t.read)).read iD)
      = t.move iD := by
  by_cases hr : t.read = Γ.start
  · rw [ite_eq_left hr, tape_idle_stay _ (move_idle_read_ne t hwf), hright hr,
      TM.idleDir_right_of_start hr]
  · rw [ite_eq_right hr, tape_idle_stay t hr,
      show safeDir t.read iD = iD from by simp only [safeDir, hr, ↓reduceIte]]

/-- **COMMIT output reconciliation.** Same as `commit_input_eq` but for the output
    write-move: COMMIT's `oSym`-guarded write-move composed with the RUN write-move
    equals `N`'s single output write-move `t.writeAndMove oW.toΓ oD`. -/
private theorem commit_output_eq (t : Tape) (oW : Γw) (oD : Dir3)
    (hwf : ∀ p, 1 ≤ p → t.cells p ≠ Γ.start) (hright : t.read = Γ.start → oD = Dir3.right) :
    (t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read)).writeAndMove
        (if t.read = Γ.start then
            TM.readBackWrite (t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read)).read
          else oW).toΓ
        (if t.read = Γ.start then
            TM.idleDir (t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read)).read
          else safeDir (t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read)).read oD)
      = t.writeAndMove oW.toΓ oD := by
  by_cases hr : t.read = Γ.start
  · have h0 : t.head = 0 := by
      rw [Tape.read] at hr; by_contra h; exact hwf t.head (by omega) hr
    have hpr : t.writeAndMove (TM.readBackWrite t.read).toΓ (TM.idleDir t.read)
        = { t with head := 1 } := by
      rw [hr, TM.idleDir_start]
      show (t.write (TM.readBackWrite Γ.start).toΓ).move Dir3.right = { t with head := 1 }
      rw [Tape.write, ite_eq_left h0]; simp [Tape.move, h0]
    have hr1ne : ({ t with head := 1 } : Tape).read ≠ Γ.start := by
      rw [Tape.read]; exact hwf 1 (le_refl 1)
    rw [hpr]
    simp only [ite_eq_left hr]
    rw [tape_idle_writeMove _ hr1ne, hright hr]
    show ({ t with head := 1 } : Tape) = (t.write oW.toΓ).move Dir3.right
    rw [Tape.write, ite_eq_left h0]; simp [Tape.move, h0]
  · simp only [ite_eq_right hr]
    rw [tape_idle_writeMove t hr,
      show safeDir t.read oD = oD from by simp only [safeDir, hr, ↓reduceIte]]

/-- `trace 3` with a constant choice unfolds into three single steps. -/
private theorem trace_three {n : ℕ} (M : NTM n) (bb : Bool) (c : Cfg n M.Q) :
    M.trace 3 (fun _ => bb) c
      = M.trace 1 (fun _ => bb) (M.trace 1 (fun _ => bb) (M.trace 1 (fun _ => bb) c)) := by
  have h1 := M.trace_add_fun 1 2 (fun _ => bb) c
  have h2 := M.trace_add_fun 1 1 (fun _ => bb) (M.trace 1 (fun _ => bb) c)
  simp only [] at h1 h2
  rw [show (3 : ℕ) = 1 + 2 from rfl, h1, show (2 : ℕ) = 1 + 1 from rfl, h2]

/-- `trace_three'` specialised to `singleTapeSim`: the state type is stated as
    `SimQ k N.Q` so that `rw` can build a type-correct motive. -/
private theorem trace_three' {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg 1 (SimQ k N.Q)) :
    (singleTapeSim N).trace 3 (fun _ => bb) c
      = (singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb)
          ((singleTapeSim N).trace 1 (fun _ => bb) c)) :=
  trace_three _ _ _

/-- GATHER slot-`0` step (head-bit): records whether this tape's head marker is
    present (`rf := wH = one`), advances to slot `1`, leaves contents/heads put. -/
private theorem gather_slot0 {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (pt : Fin (k + 1)) (rf : Bool) (pending : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (pt, 0), rf, pending))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.gather (q, acc, iSym, oSym, (pt, 1),
          decide ((c1.work 0).read = Γ.one), pending),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 } } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, (pt, 0), rf, pending) bb c1 hst]
  simp only [gatherStep, advanceSweep, hwb, ↓reduceIte, Fin.reduceEq, Fin.reduceAdd,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- GATHER slot-`1` step (sym-hi): stashes the high code cell into `pending`,
    advances to slot `2`, leaves contents/heads put. -/
private theorem gather_slot1 {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (pt : Fin (k + 1)) (rf : Bool) (pending : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (pt, 1), rf, pending))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.gather (q, acc, iSym, oSym, (pt, 2), rf, (c1.work 0).read),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 } } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, (pt, 1), rf, pending) bb c1 hst]
  simp only [gatherStep, advanceSweep, hwb, ↓reduceIte, Fin.reduceEq,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- GATHER slot-`2` step (sym-lo): decodes the symbol and, if this tape's head
    marker was seen (`rf`), records it into `acc`; advances to the next tape's
    slot `0`, leaves contents/heads put. -/
private theorem gather_slot2 {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (pt : Fin (k + 1)) (rf : Bool) (pending : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (pt, 2), rf, pending))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.gather (q,
          (if rf = true then
             (if h : pt.val < k then
                Function.update acc ⟨pt.val, h⟩ (decSymΓ pending (c1.work 0).read) else acc)
           else acc),
          iSym, oSym, (⟨if pt.val + 1 < k then pt.val + 1 else 0, by split <;> omega⟩, 0),
          rf, pending),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 } } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, (pt, 2), rf, pending) bb c1 hst]
  simp only [gatherStep, advanceSweep, hwb, ↓reduceIte, Fin.reduceEq,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- Split a constant-choice trace: `trace (a + a') = trace a' ∘ trace a`. -/
private theorem trace_const_add {n : ℕ} (M : NTM n) (a a' : ℕ) (bb : Bool) (c : Cfg n M.Q) :
    M.trace (a + a') (fun _ => bb) c
      = M.trace a' (fun _ => bb) (M.trace a (fun _ => bb) c) := by
  have h := M.trace_add_fun a a' (fun _ => bb) c
  simpa using h

/-- `trace_const_add'` specialised to `singleTapeSim`: the state type is stated as
    `SimQ k N.Q` so that `rw` can build a type-correct motive. -/
private theorem trace_const_add' {k : ℕ} (N : NTM k) (a a' : ℕ) (bb : Bool)
    (c : Cfg 1 (SimQ k N.Q)) :
    (singleTapeSim N).trace (a + a') (fun _ => bb) c
      = (singleTapeSim N).trace a' (fun _ => bb) ((singleTapeSim N).trace a (fun _ => bb) c) :=
  trace_const_add _ _ _ _ _

/-- One gather **triple** (`trace 3`): starting at slot `0` of tape `j`'s triple
    in the encoded region (work head at `h`), three GATHER steps read the head-bit
    (`cells h`), sym-hi (`cells (h+1)`), and sym-lo (`cells (h+2)`) cells, advance
    the sweep to the next tape's slot `0`, leave the work tape contents unchanged
    (read-only sweep, head at `h+3`), and — if the head-bit is set — record this
    tape's decoded symbol into `acc`. Input/output stay put (off `▷`, so `idleDir`
    is `stay`). The block/sweep inductions iterate this over the `k` tapes and `M`
    blocks. Code-cell hypotheses (`≠ □`, `≠ ▷`) keep all three steps in the slot
    branch (no sentinel) and make `readBackWrite` cell-preserving. -/
theorem gather_triple {k : ℕ} (N : NTM k) (bb : Bool)
    (q : N.Q) (acc : Fin k → Γ) (iSym oSym : Γ) (rf₀ : Bool) (pending₀ : Γ)
    (j : ℕ) (hj : j < k) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, (⟨j, by omega⟩, 0), rf₀, pending₀))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (hb0 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.blank)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (hs0 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.start)
    (hs1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.start)
    (hs2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.gather (q,
          (if (c1.work 0).cells ((c1.work 0).head) = Γ.one then
             Function.update acc ⟨j, hj⟩ (decSymΓ ((c1.work 0).cells ((c1.work 0).head + 1))
               ((c1.work 0).cells ((c1.work 0).head + 2)))
           else acc),
          iSym, oSym, (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0),
          decide ((c1.work 0).cells ((c1.work 0).head) = Γ.one),
          (c1.work 0).cells ((c1.work 0).head + 1)),
        input := c1.input, output := c1.output,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 3 } } := by
  have e0 : (singleTapeSim N).trace 1 (fun _ => bb) c1 = _ :=
    gather_slot0 N bb q acc iSym oSym ⟨j, by omega⟩ rf₀ pending₀ c1 hst hb0 hs0 his hos
  have e1 : (singleTapeSim N).trace 1 (fun _ => bb)
      ((singleTapeSim N).trace 1 (fun _ => bb) c1) = _ :=
    gather_slot1 N bb q acc iSym oSym ⟨j, by omega⟩ (decide ((c1.work 0).read = Γ.one)) pending₀
      ((singleTapeSim N).trace 1 (fun _ => bb) c1)
      (by rw [e0]) (by rw [e0]; exact hb1) (by rw [e0]; exact hs1)
      (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 : (singleTapeSim N).trace 1 (fun _ => bb)
      ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1)) = _ :=
    gather_slot2 N bb q acc iSym oSym ⟨j, by omega⟩ (decide ((c1.work 0).read = Γ.one))
      (((singleTapeSim N).trace 1 (fun _ => bb) c1).work 0).read
      ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
      (by rw [e1]) (by rw [e1, e0]; exact hb2) (by rw [e1, e0]; exact hs2)
      (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  simp only [Tape.read, dite_eq_left hj]
  by_cases hone : (c1.work 0).cells (c1.work 0).head = Γ.one <;> simp [hone]

/-- **GATHER one block (`trace (3*m)`).** Sweeping the `k`-tape block `b` (`1 ≤ b
    ≤ M`) starting at tape `0`, slot `0` (work head at `blockStart k b`): after
    `m ≤ k` triples the work head is at `blockStart k b + 3*m`, the sweep is at
    tape `(if m < k then m else 0)` slot `0`, and `acc` has recorded the read
    symbol of every tape `j < m` whose head sits in block `b` (others untouched).
    The `rf`/`pending` leftovers from the last triple are existential — the next
    block's slot-`0`/`1` steps overwrite them. Proved by induction on `m`, each
    step one `gather_triple` with the cell facts from `SimInvAt`. -/
private theorem gather_block_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (q : N.Q) (iSym oSym : Γ) (acc₀ : Fin k → Γ)
    (c1 : Cfg 1 (SimQ k N.Q)) (rf₀ : Bool) (pending₀ : Γ)
    (hst : c1.state = SimQ.gather (q, acc₀, iSym, oSym, (⟨0, by omega⟩, 0), rf₀, pending₀))
    (hhead : (c1.work 0).head = blockStart k b)
    (hinv : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (m : ℕ) (hm : m ≤ k) :
    ∃ (rf' : Bool) (pending' : Γ),
      (singleTapeSim N).trace (3 * m) (fun _ => bb) c1 =
        { state := SimQ.gather (q,
            (fun j => if j.val < m ∧ (c.work j).head = b then (c.work j).read else acc₀ j),
            iSym, oSym, (⟨if m < k then m else 0, by split <;> omega⟩, 0), rf', pending'),
          input := c1.input, output := c1.output,
          work := fun _ => { c1.work 0 with head := blockStart k b + 3 * m } } := by
  induction m with
  | zero =>
    refine ⟨rf₀, pending₀, ?_⟩
    have h0 : (singleTapeSim N).trace (3 * 0) (fun _ => bb) c1 = c1 := by
      simp only [Nat.mul_zero]; rfl
    rw [h0]
    obtain ⟨cst, cin, cwk, cout⟩ := c1
    simp only [Nat.not_lt_zero, false_and, ↓reduceIte, ite_self, Nat.mul_zero,
      Nat.add_zero] at hst hhead ⊢
    subst hst
    refine Cfg.mk.injEq .. |>.mpr ⟨rfl, rfl, ?_, rfl⟩
    funext x
    obtain rfl : x = 0 := Subsingleton.elim x 0
    rw [← hhead]
  | succ m ih =>
    obtain ⟨rfm, pendingm, hmeq⟩ := ih (by omega)
    have hmk : m < k := by omega
    have hbit := hinv.headBit b hb1 hbM ⟨m, hmk⟩
    have hsym := hinv.sym b hb1 hbM ⟨m, hmk⟩
    have hc0 : (c1.work 0).cells (blockStart k b + 3 * m)
        = if (c.work ⟨m, hmk⟩).head = b then Γ.one else Γ.zero := by
      rw [show blockStart k b + 3 * m = headBitCell k b ⟨m, hmk⟩ from by simp [headBitCell]]
      exact hbit
    have hc1 : (c1.work 0).cells (blockStart k b + 3 * m + 1)
        = (encSymΓ ((c.work ⟨m, hmk⟩).cells b)).1 := by
      rw [show blockStart k b + 3 * m + 1 = symCell k b ⟨m, hmk⟩ from by simp [symCell]]
      exact hsym.1
    have hc2 : (c1.work 0).cells (blockStart k b + 3 * m + 2)
        = (encSymΓ ((c.work ⟨m, hmk⟩).cells b)).2 := by
      rw [show blockStart k b + 3 * m + 2 = symCell k b ⟨m, hmk⟩ + 1 from by simp [symCell]]
      exact hsym.2
    refine ⟨decide ((c1.work 0).cells (blockStart k b + 3 * m) = Γ.one),
            (c1.work 0).cells (blockStart k b + 3 * m + 1), ?_⟩
    erw [show 3 * (m + 1) = 3 * m + 3 from by omega, trace_const_add',
        gather_triple N bb q
          (fun j => if ↑j < m ∧ (c.work j).head = b then (c.work j).read else acc₀ j)
          iSym oSym rfm pendingm m hmk
          ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1)
          (by rw [hmeq]; simp only [ite_eq_left hmk])
          (by rw [hmeq]; exact his)
          (by rw [hmeq]; exact hos)
          (by
            rw [hmeq];
            show (c1.work 0).cells (blockStart k b + 3 * m) ≠ Γ.blank;
            rw [hc0];
            split <;> decide)
          (by
            rw [hmeq];
            show (c1.work 0).cells (blockStart k b + 3 * m + 1) ≠ Γ.blank;
            rw [hc1];
            exact (encSymΓ_ne_blank _).1)
          (by
            rw [hmeq];
            show (c1.work 0).cells (blockStart k b + 3 * m + 2) ≠ Γ.blank;
            rw [hc2];
            exact (encSymΓ_ne_blank _).2)
          (by
            rw [hmeq];
            show (c1.work 0).cells (blockStart k b + 3 * m) ≠ Γ.start;
            rw [hc0];
            split <;> decide)
          (by
            rw [hmeq];
            show (c1.work 0).cells (blockStart k b + 3 * m + 1) ≠ Γ.start;
            rw [hc1];
            exact (encSymΓ_ne_start _).1)
          (by
            rw [hmeq];
            show (c1.work 0).cells (blockStart k b + 3 * m + 2) ≠ Γ.start;
            rw [hc2];
            exact (encSymΓ_ne_start _).2)]
    rw [hmeq]
    dsimp only
    rw [hc0, hc1, hc2, decSymΓ_encSymΓ (hinv.noStart ⟨m, hmk⟩ b hb1)]
    refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
    congr 3
    funext j
    by_cases hjm : j = (⟨m, hmk⟩ : Fin k)
    · subst hjm
      by_cases hb : (c.work ⟨m, hmk⟩).head = b
      · simp only [hb, ↓reduceIte, Function.update_self, and_true]
        rw [ite_eq_left (Nat.lt_succ_self m), Tape.read, hb]
      · simp only [hb, ↓reduceIte, reduceCtorEq, Nat.lt_irrefl, and_false]
    · have hjv : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
      by_cases hjb : (c.work j).head = b
      · by_cases hlt : (↑j : ℕ) < m
        · by_cases hb : (c.work ⟨m, hmk⟩).head = b <;>
            simp [hb, hjb, hlt, Function.update_of_ne hjm, show (↑j : ℕ) < m + 1 from by omega]
        · by_cases hb : (c.work ⟨m, hmk⟩).head = b <;>
            simp [hb, hjb, hlt, Function.update_of_ne hjm, show ¬(↑j : ℕ) < m + 1 from by omega]
      · by_cases hb : (c.work ⟨m, hmk⟩).head = b <;>
          simp [hb, hjb, Function.update_of_ne hjm]

/-- **GATHER full sweep (`trace (3*k*B)`).** Sweeping the first `B ≤ M` blocks
    (starting at block `1`, tape `0`, slot `0`, work head `blockStart k 1`, `acc`
    all `▷`): after `B` blocks the work head is at `blockStart k (B+1)`, the sweep
    is back at tape `0` slot `0`, and `acc` records the read symbol of every tape
    whose head sits in blocks `[1, B]` (and `▷` otherwise). Proved by induction on
    `B`, each step one `gather_block_aux` at block `B+1`. At `B = M` (with
    `heads_le`) every head is covered, so `acc` is exactly the per-tape reads. -/
private theorem gather_sweep_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q : N.Q) (iSym oSym : Γ) (c1 : Cfg 1 (SimQ k N.Q)) (rf₀ : Bool) (pending₀ : Γ)
    (hst : c1.state =
      SimQ.gather (q, (fun _ => Γ.start), iSym, oSym, (⟨0, by omega⟩, 0), rf₀, pending₀))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hinv : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (B : ℕ) (hB : B ≤ M) :
    ∃ (rf' : Bool) (pending' : Γ),
      (singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1 =
        { state := SimQ.gather (q,
            (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B then (c.work j).read
                      else Γ.start),
            iSym, oSym, (⟨0, by omega⟩, 0), rf', pending'),
          input := c1.input, output := c1.output,
          work := fun _ => { c1.work 0 with head := blockStart k (B + 1) } } := by
  induction B with
  | zero =>
    refine ⟨rf₀, pending₀, ?_⟩
    have h0 : (singleTapeSim N).trace (3 * k * 0) (fun _ => bb) c1 = c1 := by
      simp only [Nat.mul_zero]; rfl
    rw [h0]
    obtain ⟨cst, cin, cwk, cout⟩ := c1
    subst hst
    refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
    · congr 3
      funext j
      rw [ite_eq_right (by omega)]
    · funext x
      obtain rfl : x = 0 := Subsingleton.elim x 0
      show cwk 0 = { cwk 0 with head := blockStart k 1 }
      rw [← hhead]
  | succ B ih =>
    obtain ⟨rfB, pendingB, hBeq⟩ := ih (by omega)
    obtain ⟨rf', pending', hstep⟩ := gather_block_aux N bb c (B + 1) M (by omega) hB q iSym oSym
      (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B then (c.work j).read else Γ.start)
      ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1) rfB pendingB
      (by rw [hBeq]) (by rw [hBeq]) (by rw [hBeq]; exact hinv.cells_congr rfl)
      (by rw [hBeq]; exact his) (by rw [hBeq]; exact hos) k (le_refl k)
    refine ⟨rf', pending', ?_⟩
    erw [show 3 * k * (B + 1) = 3 * k * B + 3 * k from Nat.mul_succ (3 * k) B,
        trace_const_add', hstep, hBeq]
    dsimp only
    simp only [lt_self_iff_false, ↓reduceIte]
    rw [blockStart_succ k (B + 1) (by omega), blockWidth]
    refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
    congr 3
    funext j
    simp only [j.isLt, true_and]
    by_cases hjb : (c.work j).head = B + 1
    · simp only [hjb, ↓reduceIte, le_refl, and_true]
      rw [ite_eq_left (by omega)]
    · rw [ite_eq_right hjb]
      by_cases hr : 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B
      · rw [ite_eq_left hr, ite_eq_left (by omega)]
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

/-- One **GATHER sentinel** step (`trace 1`): reading the `□` that ends the used
    region fires `N.δ` (the one meaningful use of the choice `bb`) and hands the
    write/move actions to REWIND, turning the work head leftward. -/
theorem gather_sentinel {k : ℕ} (N : NTM k) (bb : Bool) (q : N.Q) (acc : Fin k → Γ)
    (iSym oSym : Γ) (pos : SweepPos k) (rf : Bool) (pending : Γ) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.gather (q, acc, iSym, oSym, pos, rf, pending))
    (hblank : (c1.work 0).read = Γ.blank) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.rewind ((N.δ bb q iSym acc oSym).1,
          (fun i => ((N.δ bb q iSym acc oSym).2.1 i, (N.δ bb q iSym acc oSym).2.2.2.2.1 i)),
          ((N.δ bb q iSym acc oSym).2.2.1, (N.δ bb q iSym acc oSym).2.2.2.2.2),
          (N.δ bb q iSym acc oSym).2.2.2.1, iSym, oSym, (fun j => decide (acc j = Γ.start))),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun i => (c1.work i).writeAndMove Γw.blank.toΓ Dir3.left,
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
  rw [gather_trace1 N (q, acc, iSym, oSym, pos, rf, pending) bb c1 hst]
  simp only [gatherStep, hblank, ↓reduceIte]; rfl

/-- **One non-sentinel GATHER step.** Reading a non-`□`, non-`▷` work cell, one
    GATHER step stays in GATHER (some evolved data `d'`), advances the work head
    by one with contents intact, and leaves input/output put (idle off `▷`). The
    inductive step of the per-step sweep characterization. -/
theorem gather_sweep_step1 {k : ℕ} (N : NTM k) (bb : Bool) (d : GatherData k N.Q)
    (c : Cfg 1 (SimQ k N.Q)) (hst : c.state = SimQ.gather d)
    (hb : (c.work 0).read ≠ Γ.blank) (hs : (c.work 0).read ≠ Γ.start)
    (his : c.input.read ≠ Γ.start) (hos : c.output.read ≠ Γ.start) :
    ∃ d', (singleTapeSim N).trace 1 (fun _ => bb) c =
      { state := SimQ.gather d', input := c.input,
        work := fun _ => { (c.work 0) with head := (c.work 0).head + 1 },
        output := c.output } := by
  obtain ⟨d', hd'⟩ :=
    gatherStep_fst_eq_gather_of_ne_blank N bb d c.input.read ((c.work 0).read) c.output.read hb
  obtain ⟨hw, ho_w, hi_d, hw_d, ho_d⟩ :=
    gatherStep_snd_eq_of_ne_blank N bb d c.input.read ((c.work 0).read) c.output.read hb
  refine ⟨d', ?_⟩
  rw [gather_trace1 N d bb c hst]
  simp only []
  rw [hd', hi_d, hw_d, ho_w, ho_d, hw]
  refine (Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩
  · exact tape_idle_stay c.input his
  · funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
    exact work_gather_step (c.work 0) hs
  · exact tape_idle_writeMove c.output hos

/-- **No sentinel during the GATHER sweep.** Starting from the post-run GATHER
    config (work head at cell `1`, contents materialized at level `M`), every one
    of the first `3*k*M` sweep steps keeps the simulator in a GATHER state reading
    a non-`□` cell — the `□` sentinel is reached only at step `3*k*M`. This is the
    crux of the backward correspondence: within a macro-step, a GATHER-on-`□`
    configuration (the one choice-consuming step) occurs at exactly one position. -/
theorem gather_sweep_no_sentinel {k : ℕ} (N : NTM k) (bb : Bool) {M : ℕ} {w : Fin k → Tape}
    (c_g : Cfg 1 (SimQ k N.Q))
    (hg0 : ∃ d, c_g.state = SimQ.gather d)
    (hhead : (c_g.work 0).head = 1)
    (hinv : SimInvAt k (c_g.work 0) w M)
    (his : c_g.input.read ≠ Γ.start) (hos : c_g.output.read ≠ Γ.start) :
    ∀ i, i < 3 * k * M →
      (∃ d, ((singleTapeSim N).trace i (fun _ => bb) c_g).state = SimQ.gather d) ∧
      (((singleTapeSim N).trace i (fun _ => bb) c_g).work 0).read ≠ Γ.blank := by
  have hbs : blockStart k (M + 1) = 1 + 3 * k * M := by
    simp only [blockStart, blockWidth, Nat.add_sub_cancel]; rw [Nat.mul_comm M (3 * k)]
  suffices H : ∀ i, i ≤ 3 * k * M →
      (∃ d, ((singleTapeSim N).trace i (fun _ => bb) c_g).state = SimQ.gather d) ∧
      ((singleTapeSim N).trace i (fun _ => bb) c_g).work 0
        = { head := 1 + i, cells := (c_g.work 0).cells } ∧
      ((singleTapeSim N).trace i (fun _ => bb) c_g).input = c_g.input ∧
      ((singleTapeSim N).trace i (fun _ => bb) c_g).output = c_g.output by
    intro i hi
    obtain ⟨hg, hwk, _, _⟩ := H i (le_of_lt hi)
    refine ⟨hg, ?_⟩
    rw [show ((singleTapeSim N).trace i (fun _ => bb) c_g).work 0 = _ from hwk]
    show (c_g.work 0).cells (1 + i) ≠ Γ.blank
    exact hinv.materialized_ne_blank (by omega) (by rw [hbs]; omega)
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨d, hd⟩ := hg0
    refine ⟨⟨d, hd⟩, ?_, rfl, rfl⟩
    show (c_g.work 0) = { head := 1 + 0, cells := (c_g.work 0).cells }
    simp only [Nat.add_zero]
    exact congrArg (fun h => ({ head := h, cells := (c_g.work 0).cells } : Tape)) hhead
  | succ i ih =>
    intro hsucc
    obtain ⟨⟨d_i, hd_i⟩, hwk_i, hin_i, hout_i⟩ := ih (by omega)
    rw [trace_const_add (singleTapeSim N) i 1 bb c_g]
    set c_i := (singleTapeSim N).trace i (fun _ => bb) c_g with hci
    have hread_b : (c_i.work 0).read ≠ Γ.blank := by
      rw [show (c_i.work 0) = _ from hwk_i]
      show (c_g.work 0).cells (1 + i) ≠ Γ.blank
      exact hinv.materialized_ne_blank (by omega) (by rw [hbs]; omega)
    have hread_s : (c_i.work 0).read ≠ Γ.start := by
      rw [show (c_i.work 0) = _ from hwk_i]
      show (c_g.work 0).cells (1 + i) ≠ Γ.start
      exact hinv.materialized_ne_start (by omega) (by rw [hbs]; omega)
    obtain ⟨d', hstep⟩ := gather_sweep_step1 N bb d_i c_i hd_i hread_b hread_s
      (by rw [hin_i]; exact his) (by rw [hout_i]; exact hos)
    rw [hstep]
    refine ⟨⟨d', rfl⟩, ?_, hin_i, hout_i⟩
    show { (c_i.work 0) with head := (c_i.work 0).head + 1 }
      = { head := 1 + (i + 1), cells := (c_g.work 0).cells }
    rw [hwk_i]
    congr 1

/-- The sweep accumulator at `B = M` is exactly the per-tape reads: a head in
    `[1, M]` had its symbol recorded; a head at `0` reads `▷`, which is also the
    `▷` default the sweep leaves. Uses `heads_le` (every head `≤ M`) and
    `read_eq_start_of_head_eq_zero` (a head at `0` reads `▷`). -/
theorem gather_acc_eq {k : ℕ} {t : Tape} {w : Fin k → Tape} {M : ℕ}
    (hinv : SimInvAt k t w M) :
    (fun j => if 1 ≤ (w j).head ∧ (w j).head ≤ M then (w j).read else Γ.start)
      = (fun j : Fin k => (w j).read) := by
  funext j
  by_cases h1 : 1 ≤ (w j).head
  · rw [ite_eq_left ⟨h1, hinv.heads_le j⟩]
  · rw [ite_eq_right (fun h => h1 h.1), hinv.read_eq_start_of_head_eq_zero j (by omega)]

/-- One **rewind** step (`trace 1`): from a `rewind d` config, the result is the
    configuration built from `rewindStep`'s output. Basis of the rewind sweep. -/
theorem rewind_trace1 {k : ℕ} (N : NTM k) (d : RewindData k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.rewind d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := rewindStep d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  simp only [hst, singleTapeSim, simDelta, SimQ.rewind, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- **REWIND full sweep (`trace (p+1)`).** From a `rewind` config with the work
    head at cell `p` (every cell in `[1,p]` a non-`▷` code cell, cell `0` the `▷`),
    the leftward sweep carries the `δ` results untouched back to cell `0`, then
    turns around into SCATTER sweep-1 at cell `1` (empty stay/left carries). Proved
    by induction on `p` (one `rewindStep` per cell), contents preserved throughout. -/
theorem rewind_sweep {k : ℕ} (N : NTM k) (bb : Bool)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (initRC : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q)) (p : ℕ)
    (hst : c1.state = SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC))
    (hhead : (c1.work 0).head = p)
    (hcell0 : (c1.work 0).cells 0 = Γ.start)
    (hne : ∀ p', 1 ≤ p' → p' ≤ p → (c1.work 0).cells p' ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace (p + 1) (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (0, 0), initRC,
          (fun _ => false), false, false),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := 1 },
        output := c1.output } := by
  induction p generalizing c1 with
  | zero =>
    have hread : (c1.work 0).read = Γ.start := by rw [Tape.read, hhead]; exact hcell0
    rw [rewind_trace1 N (q', wact, oWoD, iD, iSym, oSym, initRC) bb c1 hst]
    simp only [rewindStep, hread, ↓reduceIte, tape_idle_stay c1.input his,
      tape_idle_writeMove c1.output hos]
    congr 1
    funext x
    obtain rfl : x = 0 := Subsingleton.elim x 0
    exact work_blank_right_at0 (c1.work 0) hhead
  | succ p ih =>
    have hread : (c1.work 0).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hne (p + 1) (by omega) (le_refl _)
    have e1 : (singleTapeSim N).trace 1 (fun _ => bb) c1 =
        { state := SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC),
          input := c1.input,
          work := fun _ => { c1.work 0 with head := (c1.work 0).head - 1 },
          output := c1.output } := by
      rw [rewind_trace1 N (q', wact, oWoD, iD, iSym, oSym, initRC) bb c1 hst]
      simp only [rewindStep, hread, ↓reduceIte, tape_idle_stay c1.input his,
        tape_idle_writeMove c1.output hos]
      congr 1
      funext x; obtain rfl : x = 0 := Subsingleton.elim x 0
      exact work_rewind_step (c1.work 0) hread
    erw [show p + 1 + 1 = 1 + (p + 1) from by omega, trace_const_add', e1]
    exact ih _ rfl (by simp [hhead]) hcell0
      (fun p' hp1 hp2 => hne p' hp1 (by omega)) his hos

/-- **REWIND stays in REWIND (per step).** Throughout the leftward sweep (head at
    `p - i ≥ 0`, every cell in `[1,p]` non-`▷`), each intermediate config keeps the
    `rewind` state (data unchanged — only the head moves). Since `rewind ≠ gather`,
    this supplies the back-phase `¬gather` needed by the backward correspondence. -/
theorem rewind_sweep_states {k : ℕ} (N : NTM k) (bb : Bool)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (initRC : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q)) (p : ℕ)
    (hst : c1.state = SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC))
    (hhead : (c1.work 0).head = p)
    (hne : ∀ p', 1 ≤ p' → p' ≤ p → (c1.work 0).cells p' ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∀ i, i ≤ p →
      (singleTapeSim N).trace i (fun _ => bb) c1
        = { state := SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC),
            input := c1.input,
            work := fun _ => { c1.work 0 with head := p - i },
            output := c1.output } := by
  intro i
  induction i with
  | zero =>
    intro _
    refine (Cfg.mk.injEq ..).mpr ⟨hst, rfl, ?_, rfl⟩
    funext x; obtain rfl : x = 0 := Subsingleton.elim x 0
    simp only [Nat.sub_zero]
    exact congrArg (fun h => ({ (c1.work 0) with head := h } : Tape)) hhead
  | succ i ih =>
    intro hsucc
    rw [trace_const_add (singleTapeSim N) i 1 bb c1]
    set ci := (singleTapeSim N).trace i (fun _ => bb) c1 with hci
    have hih : ci = { state := SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC),
                      input := c1.input, work := fun _ => { c1.work 0 with head := p - i },
                      output := c1.output } := ih (by omega)
    have hst_i : ci.state = SimQ.rewind (q', wact, oWoD, iD, iSym, oSym, initRC) := by rw [hih]
    have hread_i : (ci.work 0).read ≠ Γ.start := by
      rw [hih]; show (c1.work 0).cells (p - i) ≠ Γ.start
      exact hne (p - i) (by omega) (by omega)
    have hisi : ci.input.read ≠ Γ.start := by rw [hih]; exact his
    have hosi : ci.output.read ≠ Γ.start := by rw [hih]; exact hos
    rw [rewind_trace1 N (q', wact, oWoD, iD, iSym, oSym, initRC) bb ci hst_i]
    simp only [rewindStep, hread_i, ↓reduceIte, tape_idle_stay ci.input hisi,
      tape_idle_writeMove ci.output hosi]
    refine (Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩
    · rw [hih]
    · funext x; obtain rfl : x = 0 := Subsingleton.elim x 0
      rw [work_rewind_step (ci.work 0) hread_i, hih]
      show ({ c1.work 0 with head := p - i - 1 } : Tape) = { c1.work 0 with head := p - (i + 1) }
      congr 1
    · rw [hih]

/-- **Intermediate work tape after SCATTER sweep-1** (before sweep-2 relocates the
    left-movers). For tape `t` with old tape `ct` and `N.δ` action `(w, d)`: the
    new symbol `w` is written at the old head position; the head-bit is placed at
    the new position for `stay`/`right` movers, but is **left at the old position**
    for left-movers — SCATTER sweep-2 moves those one block left. A head reading
    `▷` (position 0) is forced `right` by `δ_right_of_start`, so it lands at
    position 1 (the `▷` symbol write is a no-op at cell 0). Thus `head` here is
    `ct.head + 1` for right-movers and `ct.head` for stay/left-movers. -/
def scatterInterWork (ct : Tape) (wd : Γw × Dir3) : Tape where
  head := if wd.2 = Dir3.right then ct.head + 1 else ct.head
  cells := (ct.write wd.1.toΓ).cells

/-- `scatterInterWork` only rewrites the old head cell: every other cell is
    unchanged. (The new symbol is written at the old head position.) -/
theorem scatterInterWork_cells_of_ne (ct : Tape) (wd : Γw × Dir3) {c : ℕ}
    (h : c ≠ ct.head) : (scatterInterWork ct wd).cells c = ct.cells c := by
  show (ct.write wd.1.toΓ).cells c = ct.cells c
  unfold Tape.write
  split
  · rfl
  · exact Function.update_of_ne h _ _

/-- `scatterInterWork` preserves cell `0` (the `▷` marker): writing at the head
    never touches cell `0` (it's either a no-op there, or the head is `≥ 1`). -/
theorem scatterInterWork_cells_zero (ct : Tape) (wd : Γw × Dir3) :
    (scatterInterWork ct wd).cells 0 = ct.cells 0 := by
  show (ct.write wd.1.toΓ).cells 0 = ct.cells 0
  unfold Tape.write
  split
  · rfl
  · exact Function.update_of_ne (by omega) _ _

/-- `scatterInterWork` keeps every cell `≥ 1` non-`▷`: untouched cells inherit it
    from `ct`, and the rewritten head cell holds a writable symbol (`Γw`, which
    excludes `▷`). The `noStart` precondition for the post-sweep `SimInvAt (M+1)`. -/
theorem scatterInterWork_cells_ne_start (ct : Tape) (wd : Γw × Dir3) {p : ℕ}
    (hp : 1 ≤ p) (hns : ct.cells p ≠ Γ.start) :
    (scatterInterWork ct wd).cells p ≠ Γ.start := by
  by_cases hph : p = ct.head
  · rw [hph]
    show (ct.write wd.1.toΓ).cells ct.head ≠ Γ.start
    unfold Tape.write
    rw [ite_eq_right (show ¬ ct.head = 0 by omega)]
    show Function.update ct.cells ct.head wd.1.toΓ ct.head ≠ Γ.start
    rw [Function.update_self]
    cases wd.1 <;> decide
  · rw [scatterInterWork_cells_of_ne ct wd hph]; exact hns

/-- `scatterInterWork`'s head stays within the materialized region after growth:
    a right-mover advances by one (to `≤ M+1`), others stay. The `heads_le`
    precondition for the post-sweep `SimInvAt (M+1)`. -/
theorem scatterInterWork_head_le (ct : Tape) (wd : Γw × Dir3) {M : ℕ}
    (h : ct.head ≤ M) : (scatterInterWork ct wd).head ≤ M + 1 := by
  show (if wd.2 = Dir3.right then ct.head + 1 else ct.head) ≤ M + 1
  split <;> omega

/-- `scatterInterWork`'s head value: a right-mover advances by one, every other
    move keeps the old head position. (The `head` half of the intermediate
    encoding's head-bit.) -/
theorem scatterInterWork_head (ct : Tape) (wd : Γw × Dir3) :
    (scatterInterWork ct wd).head = if wd.2 = Dir3.right then ct.head + 1 else ct.head :=
  rfl

/-- `scatterInterWork` writes the new symbol at the old head position (when the
    head is `≥ 1`, where `write` is not a no-op). The `sym` half of the
    intermediate encoding at the head's block. -/
theorem scatterInterWork_cells_at_head (ct : Tape) (wd : Γw × Dir3)
    (hh : 1 ≤ ct.head) : (scatterInterWork ct wd).cells ct.head = wd.1.toΓ := by
  show (ct.write wd.1.toΓ).cells ct.head = wd.1.toΓ
  unfold Tape.write
  rw [ite_eq_right (show ¬ ct.head = 0 by omega)]
  show Function.update ct.cells ct.head wd.1.toΓ ct.head = wd.1.toΓ
  rw [Function.update_self]

/-- The post-SCATTER-sweep-2 work tape: `scatterInterWork` with a **left**-mover's head
    decremented one cell. This is the actual `N.trace 1` image of `ct` under action `wd`
    — sweep-1 placed stay/right heads, sweep-2 finishes the left-movers. The cells are
    identical to `scatterInterWork` (only the head position changes). -/
def scatterFinalWork (ct : Tape) (wd : Γw × Dir3) : Tape :=
  { scatterInterWork ct wd with
    head := if wd.2 = Dir3.left then ct.head - 1 else (scatterInterWork ct wd).head }

/-- `scatterFinalWork` has the same cells as `scatterInterWork` (only the head moves). -/
theorem scatterFinalWork_cells (ct : Tape) (wd : Γw × Dir3) :
    (scatterFinalWork ct wd).cells = (scatterInterWork ct wd).cells := rfl

/-- `scatterFinalWork`'s head: a left-mover retreats one cell, everything else is as in
    `scatterInterWork`. -/
theorem scatterFinalWork_head (ct : Tape) (wd : Γw × Dir3) :
    (scatterFinalWork ct wd).head
      = if wd.2 = Dir3.left then ct.head - 1 else (scatterInterWork ct wd).head := rfl

/-- `scatterFinalWork`'s head stays within the grown region `[0, M+1]`. -/
theorem scatterFinalWork_head_le (ct : Tape) (wd : Γw × Dir3) {M : ℕ} (h : ct.head ≤ M) :
    (scatterFinalWork ct wd).head ≤ M + 1 := by
  rw [scatterFinalWork_head]; split
  · omega
  · exact scatterInterWork_head_le ct wd h

/-- `scatterFinalWork` preserves cell `0` (the `▷` marker). -/
theorem scatterFinalWork_cells_zero (ct : Tape) (wd : Γw × Dir3) :
    (scatterFinalWork ct wd).cells 0 = ct.cells 0 := by
  rw [scatterFinalWork_cells]; exact scatterInterWork_cells_zero ct wd

/-- `scatterFinalWork` keeps every cell `≥ 1` non-`▷`. -/
theorem scatterFinalWork_cells_ne_start (ct : Tape) (wd : Γw × Dir3) {p : ℕ}
    (hp : 1 ≤ p) (hns : ct.cells p ≠ Γ.start) :
    (scatterFinalWork ct wd).cells p ≠ Γ.start := by
  rw [scatterFinalWork_cells]; exact scatterInterWork_cells_ne_start ct wd hp hns

/-- **Mid-sweep invariant for SCATTER sweep-2**, at block boundary `b`: the work tape
    holds the **final** head-bit encoding (`scatterFinalWork` — left-movers retreated) on
    blocks `[b, M+1]` already swept (leftward), and the **intermediate** encoding
    (`scatterInterWork`) on blocks `[1, b)` not yet reached. Symbol cells are the same in
    both (sweep-2 only moves head-bits). The in-flight `leftCarry` lives in the state. At
    `b = M+2` it's the sweep-1 output (`SimInvAt (M+1)` for `scatterInterWork`); at `b = 1`
    the whole region is `scatterFinalWork`-encoded. -/
structure Scatter2MidInv {k : ℕ} (t : Tape) (w : Fin k → Tape)
    (wact : Fin k → Γw × Dir3) (M b : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Blocks `[b, M+1]` already swept: final (`scatterFinalWork`) head-bits. -/
  donePart : ∀ q, b ≤ q → q ≤ M + 1 → ∀ j : Fin k,
    t.cells (headBitCell k q j)
        = (if (scatterFinalWork (w j) (wact j)).head = q then Γ.one else Γ.zero) ∧
      t.cells (symCell k q j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).1 ∧
      t.cells (symCell k q j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).2
  /-- Blocks `[1, b)` not yet reached: intermediate (`scatterInterWork`) head-bits. -/
  oldPart : ∀ q, 1 ≤ q → q < b → ∀ j : Fin k,
    t.cells (headBitCell k q j)
        = (if (scatterInterWork (w j) (wact j)).head = q then Γ.one else Γ.zero) ∧
      t.cells (symCell k q j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).1 ∧
      t.cells (symCell k q j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).2
  /-- The sentinel region (block `M+2` onward) is blank. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 2) ≤ c → t.cells c = Γ.blank

/-- **`▷` uniquely marks cell 0 during SCATTER sweep-2.** Every cell `≥ 1` is a head-bit
    (`{0,1}`), a code cell (`encSymΓ`, `≠ ▷`), or a sentinel blank — so none is `▷`. The
    same shape as `SimInvAt.materialized_ne_start`, dispatched on `donePart`/`oldPart`/
    `sentinel`. The per-step `read ≠ ▷` precondition for the `scatter2` sweep lemmas. -/
theorem Scatter2MidInv.cells_ne_start {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b : ℕ} (h : Scatter2MidInv t w wact M b)
    {c : ℕ} (hc1 : 1 ≤ c) : t.cells c ≠ Γ.start := by
  rcases Nat.lt_or_ge c (blockStart k (M + 2)) with hclt | hcge
  swap
  · rw [h.sentinel c hcge]; decide
  -- `1 ≤ c < blockStart k (M+2)`: decompose into block `q+1` and intra-block offset
  have hbs : blockStart k (M + 2) = 1 + (M + 1) * blockWidth k := by
    simp only [blockStart, show M + 2 - 1 = M + 1 from rfl]
  rw [hbs] at hclt
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp only [blockWidth] at hclt; omega
  have hW : 0 < blockWidth k := by simp only [blockWidth]; omega
  have hr : c - 1 < blockWidth k * (M + 1) := by rw [Nat.mul_comm]; omega
  obtain ⟨q, ib, hqM, hibW, hdm⟩ :
      ∃ q ib, q < M + 1 ∧ ib < blockWidth k ∧ blockWidth k * q + ib = c - 1 :=
    ⟨(c - 1) / blockWidth k, (c - 1) % blockWidth k,
      Nat.div_lt_of_lt_mul hr, Nat.mod_lt _ hW, Nat.div_add_mod _ _⟩
  have hp1 : 1 ≤ q + 1 := by omega
  have hpM : q + 1 ≤ M + 1 := by omega
  have hbq : blockStart k (q + 1) = 1 + q * blockWidth k := by
    show 1 + (q + 1 - 1) * blockWidth k = 1 + q * blockWidth k
    rw [Nat.add_sub_cancel]
  have hdm' : q * blockWidth k + ib = c - 1 := by rw [Nat.mul_comm] at hdm; exact hdm
  have hceq : c = blockStart k (q + 1) + ib := by rw [hbq]; omega
  have hib3 : ib < 3 * k := by have h' := hibW; simp only [blockWidth] at h'; exact h'
  have hjk : ib / 3 < k := Nat.div_lt_of_lt_mul hib3
  have hibdm : 3 * (ib / 3) + ib % 3 = ib := Nat.div_add_mod _ _
  have hc_full : c = blockStart k (q + 1) + (3 * (ib / 3) + ib % 3) := by rw [hceq, hibdm]
  -- the head-bit/sym cell of block `q+1`, tape `ib/3`: `donePart` (if `b ≤ q+1`) or `oldPart`
  set j : Fin k := ⟨ib / 3, hjk⟩ with hjdef
  have hcell : (t.cells (headBitCell k (q + 1) j) ≠ Γ.start) ∧
      (t.cells (symCell k (q + 1) j) ≠ Γ.start) ∧
      (t.cells (symCell k (q + 1) j + 1) ≠ Γ.start) := by
    rcases Nat.lt_or_ge (q + 1) b with hqb | hqb
    · exact ⟨by rw [(h.oldPart (q + 1) hp1 hqb j).1]; split <;> decide,
        by rw [(h.oldPart (q + 1) hp1 hqb j).2.1]; exact (encSymΓ_ne_start _).1,
        by rw [(h.oldPart (q + 1) hp1 hqb j).2.2]; exact (encSymΓ_ne_start _).2⟩
    · exact ⟨by rw [(h.donePart (q + 1) hqb hpM j).1]; split <;> decide,
        by rw [(h.donePart (q + 1) hqb hpM j).2.1]; exact (encSymΓ_ne_start _).1,
        by rw [(h.donePart (q + 1) hqb hpM j).2.2]; exact (encSymΓ_ne_start _).2⟩
  have hcases : ib % 3 = 0 ∨ ib % 3 = 1 ∨ ib % 3 = 2 := by omega
  rcases hcases with h3 | h3 | h3 <;> rw [h3] at hc_full
  · have hcs : c = headBitCell k (q + 1) j := by simp only [headBitCell, hjdef]; omega
    rw [hcs]; exact hcell.1
  · have hcs : c = symCell k (q + 1) j := by simp only [symCell, hjdef]; omega
    rw [hcs]; exact hcell.2.1
  · have hcs : c = symCell k (q + 1) j + 1 := by simp only [symCell, hjdef]; omega
    rw [hcs]; exact hcell.2.2

/-- Entering SCATTER sweep-2: the sweep-1 output `SimInvAt (M+1)` for `scatterInterWork`
    is `Scatter2MidInv` at `b = M+2` (no blocks swept yet — `donePart` vacuous). -/
theorem Scatter2MidInv.ofSimInv {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M : ℕ}
    (h : SimInvAt k t (fun j => scatterInterWork (w j) (wact j)) (M + 1)) :
    Scatter2MidInv t w wact M (M + 2) where
  cell0 := h.cell0
  donePart := fun _ hq _ _ => absurd hq (by omega)
  oldPart := fun q hq1 hqb j =>
    ⟨h.headBit q hq1 (by omega) j, (h.sym q hq1 (by omega) j).1, (h.sym q hq1 (by omega) j).2⟩
  sentinel := h.sentinel

/-- Leaving SCATTER sweep-2 (all blocks swept, `b = 1`): `Scatter2MidInv` is `SimInvAt
    (M+1)` for the **final** config `scatterFinalWork`. The structural fields use the
    original work tapes' `wfStart`/`noStart`/`heads_le`. -/
theorem Scatter2MidInv.toSimInv {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M : ℕ}
    (hwf : ∀ j : Fin k, (w j).cells 0 = Γ.start)
    (hns : ∀ (j : Fin k) (p : ℕ), 1 ≤ p → (w j).cells p ≠ Γ.start)
    (hle : ∀ j : Fin k, (w j).head ≤ M)
    (h : Scatter2MidInv t w wact M 1) :
    SimInvAt k t (fun j => scatterFinalWork (w j) (wact j)) (M + 1) where
  cell0 := h.cell0
  wfStart := fun j => (scatterFinalWork_cells_zero (w j) (wact j)).trans (hwf j)
  noStart := fun j p hp => scatterFinalWork_cells_ne_start (w j) (wact j) hp (hns j p hp)
  heads_le := fun j => scatterFinalWork_head_le (w j) (wact j) (hle j)
  headBit := fun q hq1 hqM j => (h.donePart q hq1 hqM j).1
  sym := fun q hq1 hqM j => ⟨(h.donePart q hq1 hqM j).2.1, (h.donePart q hq1 hqM j).2.2⟩
  sentinel := h.sentinel

/-- **Within-block partial invariant** for the SCATTER sweep-2 block step: like
    `Scatter2MidInv` at boundary `p+1`, but block `p` itself is split — its top `m`
    tapes `[k-m, k-1]` (swept first, leftward) hold the final (`scatterFinalWork`)
    head-bits, the rest still intermediate. `… p 0` ⇔ `Scatter2MidInv … (p+1)`; `… p k`
    ⇔ `Scatter2MidInv … p` (see `ofMid`/`toMidPred`). -/
structure Scatter2BlockInv {k : ℕ} (t : Tape) (w : Fin k → Tape)
    (wact : Fin k → Γw × Dir3) (M p m : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Blocks `(p, M+1]`: final (`scatterFinalWork`) head-bits. -/
  donePart : ∀ q, p < q → q ≤ M + 1 → ∀ j : Fin k,
    t.cells (headBitCell k q j)
        = (if (scatterFinalWork (w j) (wact j)).head = q then Γ.one else Γ.zero) ∧
      t.cells (symCell k q j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).1 ∧
      t.cells (symCell k q j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).2
  /-- Block `p`, tapes `[k-m, k-1]`: already final-encoded. -/
  doneTape : ∀ j : Fin k, k - m ≤ (j : ℕ) →
    t.cells (headBitCell k p j)
        = (if (scatterFinalWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2
  /-- Block `p`, tapes `[0, k-m)`: still intermediate. -/
  oldTape : ∀ j : Fin k, (j : ℕ) < k - m →
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2
  /-- Blocks `[1, p)`: still intermediate. -/
  oldPart : ∀ q, 1 ≤ q → q < p → ∀ j : Fin k,
    t.cells (headBitCell k q j)
        = (if (scatterInterWork (w j) (wact j)).head = q then Γ.one else Γ.zero) ∧
      t.cells (symCell k q j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).1 ∧
      t.cells (symCell k q j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells q)).2
  /-- The sentinel region (block `M+2` onward) is blank. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 2) ≤ c → t.cells c = Γ.blank

/-- **`▷` uniquely marks cell 0 during a SCATTER sweep-2 block step.** Every cell `≥ 1` is a
    head-bit (`{0,1}`), a code cell (`encSymΓ`, `≠ ▷`), or a sentinel blank. Same shape as
    `Scatter2MidInv.cells_ne_start`, dispatching block `p` on `doneTape`/`oldTape` and the
    rest on `donePart`/`oldPart`/`sentinel`. -/
theorem Scatter2BlockInv.cells_ne_start {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M p m : ℕ} (h : Scatter2BlockInv t w wact M p m)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) {c : ℕ} (hc1 : 1 ≤ c) : t.cells c ≠ Γ.start := by
  rcases Nat.lt_or_ge c (blockStart k (M + 2)) with hclt | hcge
  swap
  · rw [h.sentinel c hcge]; decide
  have hbs : blockStart k (M + 2) = 1 + (M + 1) * blockWidth k := by
    simp only [blockStart, show M + 2 - 1 = M + 1 from rfl]
  rw [hbs] at hclt
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp only [blockWidth] at hclt; omega
  have hW : 0 < blockWidth k := by simp only [blockWidth]; omega
  have hr : c - 1 < blockWidth k * (M + 1) := by rw [Nat.mul_comm]; omega
  obtain ⟨q, ib, hqM, hibW, hdm⟩ :
      ∃ q ib, q < M + 1 ∧ ib < blockWidth k ∧ blockWidth k * q + ib = c - 1 :=
    ⟨(c - 1) / blockWidth k, (c - 1) % blockWidth k,
      Nat.div_lt_of_lt_mul hr, Nat.mod_lt _ hW, Nat.div_add_mod _ _⟩
  have hq1 : 1 ≤ q + 1 := by omega
  have hqM' : q + 1 ≤ M + 1 := by omega
  have hbq : blockStart k (q + 1) = 1 + q * blockWidth k := by
    show 1 + (q + 1 - 1) * blockWidth k = 1 + q * blockWidth k
    rw [Nat.add_sub_cancel]
  have hdm' : q * blockWidth k + ib = c - 1 := by rw [Nat.mul_comm] at hdm; exact hdm
  have hceq : c = blockStart k (q + 1) + ib := by rw [hbq]; omega
  have hib3 : ib < 3 * k := by have h' := hibW; simp only [blockWidth] at h'; exact h'
  have hjk : ib / 3 < k := Nat.div_lt_of_lt_mul hib3
  have hibdm : 3 * (ib / 3) + ib % 3 = ib := Nat.div_add_mod _ _
  have hc_full : c = blockStart k (q + 1) + (3 * (ib / 3) + ib % 3) := by rw [hceq, hibdm]
  set j : Fin k := ⟨ib / 3, hjk⟩ with hjdef
  -- the three cells of block `q+1`, tape `j`: choose the relevant invariant clause
  have hcell : (t.cells (headBitCell k (q + 1) j) ≠ Γ.start) ∧
      (t.cells (symCell k (q + 1) j) ≠ Γ.start) ∧
      (t.cells (symCell k (q + 1) j + 1) ≠ Γ.start) := by
    rcases lt_trichotomy (q + 1) p with hqp | hqp | hqp
    · -- block `q+1 < p`: still intermediate
      exact ⟨by rw [(h.oldPart (q + 1) hq1 hqp j).1]; split <;> decide,
        by rw [(h.oldPart (q + 1) hq1 hqp j).2.1]; exact (encSymΓ_ne_start _).1,
        by rw [(h.oldPart (q + 1) hq1 hqp j).2.2]; exact (encSymΓ_ne_start _).2⟩
    · -- block `q+1 = p`: split on the tape `j` (done vs old)
      subst hqp
      rcases Nat.lt_or_ge (j : ℕ) (k - m) with hjm | hjm
      · exact ⟨by rw [(h.oldTape j hjm).1]; split <;> decide,
          by rw [(h.oldTape j hjm).2.1]; exact (encSymΓ_ne_start _).1,
          by rw [(h.oldTape j hjm).2.2]; exact (encSymΓ_ne_start _).2⟩
      · exact ⟨by rw [(h.doneTape j hjm).1]; split <;> decide,
          by rw [(h.doneTape j hjm).2.1]; exact (encSymΓ_ne_start _).1,
          by rw [(h.doneTape j hjm).2.2]; exact (encSymΓ_ne_start _).2⟩
    · -- block `p < q+1`: final
      exact ⟨by rw [(h.donePart (q + 1) hqp hqM' j).1]; split <;> decide,
        by rw [(h.donePart (q + 1) hqp hqM' j).2.1]; exact (encSymΓ_ne_start _).1,
        by rw [(h.donePart (q + 1) hqp hqM' j).2.2]; exact (encSymΓ_ne_start _).2⟩
  have hcases : ib % 3 = 0 ∨ ib % 3 = 1 ∨ ib % 3 = 2 := by omega
  rcases hcases with h3 | h3 | h3 <;> rw [h3] at hc_full
  · have hcs : c = headBitCell k (q + 1) j := by simp only [headBitCell, hjdef]; omega
    rw [hcs]; exact hcell.1
  · have hcs : c = symCell k (q + 1) j := by simp only [symCell, hjdef]; omega
    rw [hcs]; exact hcell.2.1
  · have hcs : c = symCell k (q + 1) j + 1 := by simp only [symCell, hjdef]; omega
    rw [hcs]; exact hcell.2.2

/-- Entering block `p` (no tapes swept): `Scatter2MidInv … (p+1)` is `Scatter2BlockInv …
    p 0` (block `p` still all intermediate). -/
theorem Scatter2BlockInv.ofMid {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M p : ℕ} (hp1 : 1 ≤ p)
    (h : Scatter2MidInv t w wact M (p + 1)) : Scatter2BlockInv t w wact M p 0 where
  cell0 := h.cell0
  donePart := fun q hq hqM j => h.donePart q (by omega) hqM j
  doneTape := fun j hj => absurd hj (by have := j.isLt; omega)
  oldTape := fun j _ => h.oldPart p hp1 (by omega) j
  oldPart := fun q hq1 hqp j => h.oldPart q hq1 (by omega) j
  sentinel := h.sentinel

/-- Leaving block `p` (all `k` tapes swept): `Scatter2BlockInv … p k` is `Scatter2MidInv
    … p` (block `p` now all final). -/
theorem Scatter2BlockInv.toMidPred {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M p : ℕ}
    (h : Scatter2BlockInv t w wact M p k) : Scatter2MidInv t w wact M p where
  cell0 := h.cell0
  donePart := fun q hq hqM j => by
    rcases Nat.lt_or_ge p q with hlt | hge
    · exact h.donePart q hlt hqM j
    · obtain rfl : q = p := by omega
      exact h.doneTape j (by omega)
  oldPart := fun q hq1 hqp j => h.oldPart q hq1 hqp j
  sentinel := h.sentinel

/-- **Block-step cell bookkeeping (pure)** for SCATTER sweep-2: advancing the within-block
    invariant one tape. Sweep-2 only rewrites a head-bit cell, so if a new tape `t'` agrees
    with `t` everywhere except block `p` tape `k-1-m`'s head-bit (now the final value), and
    `t` satisfies `Scatter2BlockInv … p m`, then `t'` satisfies `Scatter2BlockInv … p (m+1)`.
    The changed cell `headBitCell p (k-1-m)` is disjoint from every other queried cell
    (same-block sym cells differ mod 3; other tapes by index; other blocks by layout). -/
theorem scatter2_blockinv_step {k : ℕ} {t t' : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M p m : ℕ} (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (hmk : m < k)
    (hbm : Scatter2BlockInv t w wact M p m)
    (hbit : t'.cells (headBitCell k p ⟨k - 1 - m, by omega⟩)
        = (if (scatterFinalWork (w ⟨k - 1 - m, by omega⟩) (wact ⟨k - 1 - m, by omega⟩)).head = p
            then Γ.one else Γ.zero))
    (hpres : ∀ c, c ≠ headBitCell k p ⟨k - 1 - m, by omega⟩ → t'.cells c = t.cells c) :
    Scatter2BlockInv t' w wact M p (m + 1) where
  cell0 := by
    rw [hpres 0 (by simp only [headBitCell]; have := one_le_blockStart k p; omega)]; exact hbm.cell0
  donePart := fun q hpq hqM j => by
    have key : blockStart k p + 3 * (k - 1 - m) < blockStart k q := by
      have hA := headBitCell_add_three_le_blockStart_succ k p ⟨k - 1 - m, by omega⟩ hp1
      have hB := blockStart_le k (show p + 1 ≤ q by omega)
      simp only [headBitCell] at hA; omega
    rw [hpres (headBitCell k q j) (by simp only [headBitCell]; have := j.isLt; omega),
        hpres (symCell k q j) (by simp only [headBitCell, symCell]; have := j.isLt; omega),
        hpres (symCell k q j + 1) (by simp only [headBitCell, symCell]; have := j.isLt; omega)]
    exact hbm.donePart q hpq hqM j
  doneTape := fun j hj => by
    rcases Nat.lt_or_ge (k - 1 - m) (j : ℕ) with hlt | hge
    · rw [hpres (headBitCell k p j) (by simp only [headBitCell]; omega),
          hpres (symCell k p j) (by simp only [headBitCell, symCell]; omega),
          hpres (symCell k p j + 1) (by simp only [headBitCell, symCell]; omega)]
      exact hbm.doneTape j (by omega)
    · have hjeq : (j : ℕ) = k - 1 - m := by omega
      rw [show j = (⟨k - 1 - m, by omega⟩ : Fin k) from Fin.ext hjeq]
      obtain ⟨_, hs1, hs2⟩ := hbm.oldTape ⟨k - 1 - m, by omega⟩ (by show k - 1 - m < k - m; omega)
      refine ⟨hbit, ?_, ?_⟩
      · rw [hpres (symCell k p ⟨k - 1 - m, by omega⟩) (by simp only [headBitCell, symCell]; omega)]
        exact hs1
      · rw [hpres (symCell k p ⟨k - 1 - m, by omega⟩ + 1)
          (by simp only [headBitCell, symCell]; omega)]
        exact hs2
  oldTape := fun j hj => by
    rw [hpres (headBitCell k p j) (by simp only [headBitCell]; omega),
        hpres (symCell k p j) (by simp only [headBitCell, symCell]; omega),
        hpres (symCell k p j + 1) (by simp only [headBitCell, symCell]; omega)]
    exact hbm.oldTape j (by omega)
  oldPart := fun q hq1 hqp j => by
    have key : blockStart k q + 3 * (k : ℕ) ≤ blockStart k p := by
      have hC := blockStart_le k (show q + 1 ≤ p by omega)
      have hD := blockStart_succ k q (by omega)
      have hbw : blockWidth k = 3 * k := rfl
      omega
    rw [hpres (headBitCell k q j) (by simp only [headBitCell]; have := j.isLt; omega),
        hpres (symCell k q j) (by simp only [headBitCell, symCell]; have := j.isLt; omega),
        hpres (symCell k q j + 1) (by simp only [headBitCell, symCell]; have := j.isLt; omega)]
    exact hbm.oldPart q hq1 hqp j
  sentinel := fun c hc => by
    have key : blockStart k p + 3 * k ≤ blockStart k (M + 2) := by
      have hE := blockStart_le k (show p + 1 ≤ M + 2 by omega)
      have hD := blockStart_succ k p (by omega)
      have hbw : blockWidth k = 3 * k := rfl
      omega
    rw [hpres c (by simp only [headBitCell]; have := one_le_blockStart k p; omega)]
    exact hbm.sentinel c hc

/-- The SCATTER head triples write the symbol via the **writable** codec
    (`encSymW s`), but the `scatterInterWork` target reads it via the
    full-alphabet codec applied to the written cell (`encSymΓ s.toΓ`). They
    agree (both route through `encSym`): this matches a head triple's two symbol
    writes to the intermediate encoding at the head's block. -/
theorem encSymW_toΓ_eq_encSymΓ (s : Γw) :
    (encSymW s).1.toΓ = (encSymΓ s.toΓ).1 ∧ (encSymW s).2.toΓ = (encSymΓ s.toΓ).2 := by
  cases s <;> exact ⟨rfl, rfl⟩

/-- **Mid-sweep invariant for SCATTER sweep-1**, at block boundary `b`: the work
    tape `t` holds the **intermediate** encoding (`scatterInterWork`) on blocks
    `[1, b)` already swept, and the **old** encoding (`w`) on blocks `[b, M]` not
    yet reached, with the `▷` at cell 0 and the sentinel region blank beyond block
    `M`. (The in-flight `rightCarry` lives in the SCATTER state, not the tape.) The
    block step advances this `b → b+1`; at `b = 1` it's the REWIND output (all old),
    at `b = M+1` the whole region is intermediate-encoded. -/
structure Scatter1MidInv {k : ℕ} (t : Tape) (w : Fin k → Tape)
    (wact : Fin k → Γw × Dir3) (M b : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Blocks `[1, b)` already swept: intermediate (`scatterInterWork`) encoding. -/
  donePart : ∀ p, 1 ≤ p → p < b → ∀ j : Fin k,
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2
  /-- Blocks `[b, M]` not yet reached: the old encoding (`SimInvAt M`). -/
  oldPart : ∀ p, b ≤ p → p ≤ M → ∀ j : Fin k,
    t.cells (headBitCell k p j) = (if (w j).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((w j).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((w j).cells p)).2
  /-- The sentinel region (block `M+1` onward) is blank. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 1) ≤ c → t.cells c = Γ.blank

/-- **Base case** of the mid-sweep invariant: the REWIND output (whole region
    still old-encoded, `SimInvAt M`) is `Scatter1MidInv` at `b = 1` (no swept
    blocks yet). -/
theorem scatter1MidInv_init {k : ℕ} {t : Tape} {w : Fin k → Tape}
    (wact : Fin k → Γw × Dir3) {M : ℕ} (h : SimInvAt k t w M) :
    Scatter1MidInv t w wact M 1 where
  cell0 := h.cell0
  donePart := fun _ _ hp2 _ => absurd hp2 (by omega)
  oldPart := fun p hp1 hpM j =>
    ⟨h.headBit p hp1 hpM j, (h.sym p hp1 hpM j).1, (h.sym p hp1 hpM j).2⟩
  sentinel := h.sentinel

/-- **Final case** of the mid-sweep invariant: once all `M` blocks are swept
    (`b = M+1`), the whole materialized region is intermediate-encoded — exactly
    the `SimInvAt M`-style facts for `scatterInterWork (w j) (wact j)` on `[1, M]`. -/
theorem Scatter1MidInv.done {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M : ℕ} (h : Scatter1MidInv t w wact M (M + 1))
    (p : ℕ) (hp1 : 1 ≤ p) (hpM : p ≤ M) (j : Fin k) :
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2 :=
  h.donePart p hp1 (by omega) j

/-- **Within-block partial invariant** for the SCATTER sweep-1 block step: like
    `Scatter1MidInv` at boundary `b`, but block `b` itself is split — its first
    `m` tapes are already intermediate-encoded (`scatterInterWork`), the rest still
    old. The tape-by-tape block step advances `m → m+1`; `… b 0` is `Scatter1MidInv
    … b` and `… b k` is `Scatter1MidInv … (b+1)` (see `ofMid`/`toMidSucc`). -/
structure Scatter1BlockInv {k : ℕ} (t : Tape) (w : Fin k → Tape)
    (wact : Fin k → Γw × Dir3) (M b m : ℕ) : Prop where
  /-- Cell 0 is the global start marker `▷`. -/
  cell0 : t.cells 0 = Γ.start
  /-- Blocks `[1, b)`: intermediate (`scatterInterWork`) encoding. -/
  donePart : ∀ p, 1 ≤ p → p < b → ∀ j : Fin k,
    t.cells (headBitCell k p j)
        = (if (scatterInterWork (w j) (wact j)).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells p)).2
  /-- Block `b`, tapes `[0, m)`: already intermediate-encoded. -/
  doneTape : ∀ j : Fin k, (j : ℕ) < m →
    t.cells (headBitCell k b j)
        = (if (scatterInterWork (w j) (wact j)).head = b then Γ.one else Γ.zero) ∧
      t.cells (symCell k b j) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells b)).1 ∧
      t.cells (symCell k b j + 1) = (encSymΓ ((scatterInterWork (w j) (wact j)).cells b)).2
  /-- Block `b`, tapes `[m, k)`: still old. -/
  oldTape : ∀ j : Fin k, m ≤ (j : ℕ) →
    t.cells (headBitCell k b j) = (if (w j).head = b then Γ.one else Γ.zero) ∧
      t.cells (symCell k b j) = (encSymΓ ((w j).cells b)).1 ∧
      t.cells (symCell k b j + 1) = (encSymΓ ((w j).cells b)).2
  /-- Blocks `(b, M]`: still old. -/
  oldPart : ∀ p, b < p → p ≤ M → ∀ j : Fin k,
    t.cells (headBitCell k p j) = (if (w j).head = p then Γ.one else Γ.zero) ∧
      t.cells (symCell k p j) = (encSymΓ ((w j).cells p)).1 ∧
      t.cells (symCell k p j + 1) = (encSymΓ ((w j).cells p)).2
  /-- The sentinel region (block `M+1` onward) is blank. -/
  sentinel : ∀ c : ℕ, blockStart k (M + 1) ≤ c → t.cells c = Γ.blank

/-- Entering block `b` (no tapes processed yet): `Scatter1MidInv … b` is the block
    invariant at `m = 0`. The block-`b` old facts come from `oldPart` at `p = b`. -/
theorem Scatter1BlockInv.ofMid {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b : ℕ} (hbM : b ≤ M)
    (h : Scatter1MidInv t w wact M b) : Scatter1BlockInv t w wact M b 0 where
  cell0 := h.cell0
  donePart := h.donePart
  doneTape := fun _ hj => absurd hj (by omega)
  oldTape := fun j _ => h.oldPart b (le_refl b) hbM j
  oldPart := fun p hp hpM j => h.oldPart p (by omega) hpM j
  sentinel := h.sentinel

/-- Leaving block `b` (all `k` tapes processed): `Scatter1BlockInv … b k` is
    `Scatter1MidInv … (b+1)`. The new `donePart` at `p = b` is the just-finished
    `doneTape` (every `j : Fin k` satisfies `j < k`). -/
theorem Scatter1BlockInv.toMidSucc {k : ℕ} {t : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b : ℕ}
    (h : Scatter1BlockInv t w wact M b k) : Scatter1MidInv t w wact M (b + 1) where
  cell0 := h.cell0
  donePart := fun p hp1 hpb j => by
    rcases Nat.lt_or_ge p b with hlt | hge
    · exact h.donePart p hp1 hlt j
    · obtain rfl : p = b := by omega
      exact h.doneTape j j.isLt
  oldPart := fun p hp hpM j => h.oldPart p (by omega) hpM j
  sentinel := h.sentinel

/-- **Block-step cell bookkeeping (pure).** Advancing the within-block invariant
    one tape: if a new tape `t'` agrees with `t` everywhere except block `b` tape
    `m`'s three cells, which now hold the **intermediate** (`scatterInterWork`)
    encoding, and `t` satisfies `Scatter1BlockInv … b m`, then `t'` satisfies
    `Scatter1BlockInv … b (m+1)`. All other queried cells are untouched (block `b`
    tape `m`'s triple sits at `[blockStart b + 3m, +2]`, disjoint from every other
    `(p,j)` triple, cell 0 and the sentinel region). The five SCATTER triples each
    discharge the three value hypotheses; this lemma does the disjointness once. -/
theorem scatter1_blockinv_step {k : ℕ} {t t' : Tape} {w : Fin k → Tape}
    {wact : Fin k → Γw × Dir3} {M b m : ℕ} (hb1 : 1 ≤ b) (hbM : b ≤ M) (hmk : m < k)
    (hbm : Scatter1BlockInv t w wact M b m)
    (hbit : t'.cells (headBitCell k b ⟨m, hmk⟩)
        = if (scatterInterWork (w ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b then Γ.one else Γ.zero)
    (hs1 : t'.cells (symCell k b ⟨m, hmk⟩)
        = (encSymΓ ((scatterInterWork (w ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b)).1)
    (hs2 : t'.cells (symCell k b ⟨m, hmk⟩ + 1)
        = (encSymΓ ((scatterInterWork (w ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b)).2)
    (hpres : ∀ c, c ≠ headBitCell k b ⟨m, hmk⟩ → c ≠ symCell k b ⟨m, hmk⟩ →
        c ≠ symCell k b ⟨m, hmk⟩ + 1 → t'.cells c = t.cells c) :
    Scatter1BlockInv t' w wact M b (m + 1) where
  cell0 := by
    rw [hpres 0 (by simp only [headBitCell]; have := one_le_blockStart k b; omega)
      (by simp only [symCell]; have := one_le_blockStart k b; omega)
      (by simp only [symCell]; have := one_le_blockStart k b; omega)]
    exact hbm.cell0
  donePart := fun p hp1 hpb j => by
    have key : blockStart k p + 3 * (j : ℕ) + 2 < blockStart k b + 3 * m := by
      have hA := headBitCell_add_three_le_blockStart_succ k p j hp1
      have hB := blockStart_le k (show p + 1 ≤ b by omega)
      simp only [headBitCell] at hA; omega
    rw [hpres (headBitCell k p j) (by simp only [headBitCell]; omega)
          (by simp only [headBitCell, symCell]; omega) (by simp only [headBitCell, symCell]; omega),
        hpres (symCell k p j) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega),
        hpres (symCell k p j + 1) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega)]
    exact hbm.donePart p hp1 hpb j
  doneTape := fun j hj => by
    rcases Nat.lt_or_ge (j : ℕ) m with hlt | hge
    · have key : blockStart k b + 3 * (j : ℕ) + 2 < blockStart k b + 3 * m := by omega
      rw [hpres (headBitCell k b j) (by simp only [headBitCell]; omega)
            (by simp only [headBitCell, symCell]; omega)
            (by simp only [headBitCell, symCell]; omega),
          hpres (symCell k b j) (by simp only [headBitCell, symCell]; omega)
            (by simp only [symCell]; omega) (by simp only [symCell]; omega),
          hpres (symCell k b j + 1) (by simp only [headBitCell, symCell]; omega)
            (by simp only [symCell]; omega) (by simp only [symCell]; omega)]
      exact hbm.doneTape j hlt
    · have hjm : (j : ℕ) = m := by omega
      obtain rfl : j = ⟨m, hmk⟩ := Fin.ext hjm
      exact ⟨hbit, hs1, hs2⟩
  oldTape := fun j hj => by
    have key : blockStart k b + 3 * m + 2 < blockStart k b + 3 * (j : ℕ) := by omega
    rw [hpres (headBitCell k b j) (by simp only [headBitCell]; omega)
          (by simp only [headBitCell, symCell]; omega) (by simp only [headBitCell, symCell]; omega),
        hpres (symCell k b j) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega),
        hpres (symCell k b j + 1) (by simp only [headBitCell, symCell]; omega)
          (by simp only [symCell]; omega) (by simp only [symCell]; omega)]
    exact hbm.oldTape j (by omega)
  oldPart := fun p hp hpM j => by
    have key : blockStart k b + 3 * m + 2 < blockStart k p := by
      have hC := blockStart_le k (show b + 1 ≤ p by omega)
      have hD := blockStart_succ k b hb1
      have hbw : blockWidth k = 3 * k := rfl
      omega
    rw [hpres (headBitCell k p j) (by simp only [headBitCell]; have := j.isLt; omega)
          (by simp only [headBitCell, symCell]; have := j.isLt; omega)
          (by simp only [headBitCell, symCell]; have := j.isLt; omega),
        hpres (symCell k p j) (by simp only [headBitCell, symCell]; have := j.isLt; omega)
          (by simp only [symCell]; have := j.isLt; omega)
          (by simp only [symCell]; have := j.isLt; omega),
        hpres (symCell k p j + 1) (by simp only [headBitCell, symCell]; have := j.isLt; omega)
          (by simp only [symCell]; have := j.isLt; omega)
          (by simp only [symCell]; have := j.isLt; omega)]
    exact hbm.oldPart p hp hpM j
  sentinel := fun c hc => by
    have key : blockStart k b + 3 * m + 2 < blockStart k (M + 1) := by
      have hE := blockStart_le k (show b + 1 ≤ M + 1 by omega)
      have hD := blockStart_succ k b hb1
      have hbw : blockWidth k = 3 * k := rfl
      omega
    rw [hpres c (by simp only [headBitCell]; omega) (by simp only [symCell]; omega)
          (by simp only [symCell]; omega)]
    exact hbm.sentinel c hc

/-- One **scatter sweep-1** step (`trace 1`): from a `scatter1 d` config, the
    result is the configuration built from `scatter1Step`'s output. Basis of the
    SCATTER sweep-1 correctness (the phase that writes `N`'s new configuration and
    materializes a fresh block). -/
theorem scatter1_trace1 {k : ℕ} (N : NTM k) (d : Scatter1Data k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter1 d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  simp only [hst, singleTapeSim, simDelta, SimQ.scatter1, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- A SCATTER sweep-1 **non-sentinel step** (`trace 1`): on any cell other than the
    `□` sentinel, the work head writes `scatter1Step`'s computed symbol and moves
    right (input/output idle), landing in `scatter1Step`'s next state. The case
    logic (head-bit handling, symbol writes, marker carries) stays packaged inside
    `scatter1Step` for the sweep induction to unfold per cell. -/
theorem scatter1_step_right {k : ℕ} (N : NTM k) (d : Scatter1Data k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter1 d)
    (hwb : (c1.work 0).read ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).1,
        input := c1.input,
        work := fun i => (c1.work i).writeAndMove
          ((scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.1 i).toΓ Dir3.right,
        output := c1.output } := by
  rw [scatter1_trace1 N d b c1 hst]
  have hwd : (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.1
      = fun _ => Dir3.right := by
    funext i
    show (if (c1.work 0).read = Γ.blank ∧ _ then Dir3.left else Dir3.right) = Dir3.right
    rw [ite_eq_right (fun h => hwb h.1)]
  simp only [show (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.1
      = TM.idleDir c1.input.read from rfl,
    show (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.1
      = TM.readBackWrite c1.output.read from rfl,
    show (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.2
      = TM.idleDir c1.output.read from rfl,
    hwd, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]; rfl

/-- A SCATTER sweep-1 **materialize step** (`trace 1`): at the `□` sentinel, before
    the new block is complete (`¬(mat ∧ pos = (0,0))`), the head writes the fresh
    cell's value (`scatter1Step`'s symbol — a head-bit per `rightCarry` at slot 0,
    `□` otherwise) and moves right, growing the region by one cell. Same shape as
    `scatter1_step_right`; the work direction is right because the turn-around
    guard is false. -/
theorem scatter1_materialize {k : ℕ} (N : NTM k) (b : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (pos : SweepPos k) (rightCarry isLeftMover : Fin k → Bool) (writeFlag mat : Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat))
    (hnt : ¬(mat = true ∧ pos = (0, 0)))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let d := (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
       { state := (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).1,
         input := c1.input,
         work := fun i => (c1.work i).writeAndMove
           ((scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).2.1 i).toΓ Dir3.right,
         output := c1.output } : Cfg 1 (SimQ k N.Q)) := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat) b c1 hst]
  have hwd : (scatter1Step
      (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
      c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.1 = fun _ => Dir3.right := by
    funext i
    show (if (c1.work 0).read = Γ.blank ∧ mat = true ∧ pos = (0, 0) then Dir3.left
          else Dir3.right) = Dir3.right
    rw [ite_eq_right (fun h => hnt h.2)]
  simp only [show (scatter1Step
        (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
        c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.1
      = TM.idleDir c1.input.read from rfl,
    show (scatter1Step
        (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
        c1.input.read ((c1.work 0).read) c1.output.read).2.2.1
      = TM.readBackWrite c1.output.read from rfl,
    show (scatter1Step
        (q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat)
        c1.input.read ((c1.work 0).read) c1.output.read).2.2.2.2.2
      = TM.idleDir c1.output.read from rfl,
    hwd, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  rfl

/-- SCATTER sweep-1 **materialize slot-0** step: at the `□` sentinel, slot `0` of
    a fresh block-tape, deposit the head-bit (`one` if `rightCarry t`, else `zero`),
    clear that carry, set `mat`, and advance to slot 1. The right-movers carried out
    of the last old block land here. -/
theorem scatter1_mat_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (t : ℕ) (ht : t < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), rc, ilm, false, mat))
    (hblank : (c1.work 0).read = Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (hnt : ¬(mat = true ∧ ((⟨t, by omega⟩, 0) : SweepPos k) = (0, 0)))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 1),
          Function.update rc ⟨t, ht⟩ false, ilm, false, true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1, Function.update (c1.work 0).cells (c1.work 0).head
          (if rc ⟨t, ht⟩ then Γw.one else Γw.zero).toΓ⟩,
        output := c1.output } := by
  rw [scatter1_materialize N bb q' wact oWoD iD iSym oSym (⟨t, by omega⟩, 0) rc ilm false mat c1 hst
    hnt his hos]
  simp only [scatter1Step, hblank, ↓reduceIte, ite_eq_right hnt, dite_eq_left ht, advanceSweep,
    Fin.reduceEq,
    Fin.isValue]
  congr 1
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact work_write_right (c1.work 0) _ hh

/-- SCATTER sweep-1 **materialize symbol** step: at the `□` sentinel, slot `1` or `2`
    of a fresh block-tape, write the blank-symbol code cell (`Γw.zero`) and advance.
    `rightCarry`/`isLeftMover` untouched; the new block's symbols are all `□`. -/
theorem scatter1_mat_sym {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (t : ℕ) (ht : t < k) (s : Fin 3) (hs : s ≠ 0) (rc ilm : Fin k → Bool) (wf : Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, s), rc, ilm, wf, true))
    (hblank : (c1.work 0).read = Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, advanceSweep k (⟨t, by omega⟩, s),
          rc, ilm, false, true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.zero.toΓ⟩,
        output := c1.output } := by
  have hpos : (((⟨t, by omega⟩, s) : SweepPos k) = (0, 0)) = False :=
    eq_false (fun h => hs (congrArg Prod.snd h))
  have hnt : ¬(true = true ∧ ((⟨t, by omega⟩, s) : SweepPos k) = (0, 0)) := by
    rintro ⟨-, h⟩; exact hs (congrArg Prod.snd h)
  rw [scatter1_materialize N bb q' wact oWoD iD iSym oSym (⟨t, by omega⟩, s) rc ilm wf true c1 hst
    hnt his hos]
  simp only [scatter1Step, hblank, hpos, and_false, hs, ↓reduceIte, Fin.isValue]
  congr 1
  funext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact work_write_right (c1.work 0) _ hh

/-- SCATTER sweep-1 **materialize triple** (`trace 3`): materialize one fresh
    block-tape (3 blank cells) — deposit the head-bit (`one` iff `rightCarry t`),
    then two blank-symbol cells (`□`), clearing `rightCarry t` and setting `mat`. The
    work head advances by 3 to the next tape's slot 0. -/
theorem scatter1_mat_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (t : ℕ) (ht : t < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), rc, ilm, false, mat))
    (hh : 1 ≤ (c1.work 0).head)
    (hb0 : (c1.work 0).cells ((c1.work 0).head) = Γ.blank)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) = Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) = Γ.blank)
    (hnt : ¬(mat = true ∧ ((⟨t, by omega⟩, 0) : SweepPos k) = (0, 0)))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if t + 1 < k then t + 1 else 0, by split <;> omega⟩, 0),
          Function.update rc ⟨t, ht⟩ false, ilm, false, true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (Function.update (c1.work 0).cells
            (c1.work 0).head (if rc ⟨t, ht⟩ then Γw.one else Γw.zero).toΓ)
            ((c1.work 0).head + 1) Γw.zero.toΓ)
            ((c1.work 0).head + 2) Γw.zero.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_mat_slot0 N bb q' wact oWoD iD iSym oSym t ht rc ilm mat c1 hst
    (by rw [Tape.read]; exact hb0) hh hnt his hos
  have e1 := scatter1_mat_sym N bb q' wact oWoD iD iSym oSym t ht 1 (by decide)
    (Function.update rc ⟨t, ht⟩ false) ilm false ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0])
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb1)
    (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_mat_sym N bb q' wact oWoD iD iSym oSym t ht 2 (by decide)
    (Function.update rc ⟨t, ht⟩ false) ilm false
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [advanceSweep, Fin.isValue, Fin.reduceEq, Fin.reduceAdd, ↓reduceIte])
    (by rw [e1, e0]; simp only [Tape.read];
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  simp only [advanceSweep, Fin.isValue, ↓reduceIte]

/-- SCATTER sweep-1 **materialize sweep** (`trace (3*m)`): materialize the first
    `m ≤ k` tapes of the fresh block `M+1` (all `□` sentinel cells). After `m` tapes
    the head is at `blockStart (M+1) + 3*m`, the first `m` tapes hold their head-bit
    (`one` iff the incoming `rc`) and `□` symbols, the rest are still blank, the
    carries `[0,m)` are cleared, and `mat` is set (once any cell is materialized).
    Cells below block `M+1` (blocks `[1,M]`, cell 0) are untouched. -/
private theorem scatter1_mat_aux {k : ℕ} (N : NTM k) (bb : Bool) (M : ℕ) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = blockStart k (M + 1))
    (hsent : ∀ cc, blockStart k (M + 1) ≤ cc → (c1.work 0).cells cc = Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (m : ℕ) (hm : m ≤ k) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * m) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m < k then m else 0, by split <;> omega⟩, 0),
            (fun j => if (j : ℕ) < m then false else rc j), ilm, false,
            if m = 0 then false else true),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k (M + 1) + 3 * m
      ∧ (∀ cc, cc < blockStart k (M + 1) → wt.cells cc = (c1.work 0).cells cc)
      ∧ (∀ j : Fin k, (j : ℕ) < m →
          wt.cells (headBitCell k (M + 1) j) = (if rc j then Γ.one else Γ.zero) ∧
          wt.cells (symCell k (M + 1) j) = Γ.zero ∧
          wt.cells (symCell k (M + 1) j + 1) = Γ.zero)
      ∧ (∀ cc, blockStart k (M + 1) + 3 * m ≤ cc → wt.cells cc = Γ.blank) := by
  induction m with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, ?_, ?_, ?_⟩
    · have h0 : (singleTapeSim N).trace (3 * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
      · simp only [↓reduceIte, ite_self, Nat.not_lt_zero]
      · funext x; obtain rfl : x = 0 := Subsingleton.elim x 0; rfl
    · simp only [Nat.mul_zero, Nat.add_zero]; exact hhead
    · intro cc _; rfl
    · intro j hj; omega
    · simp only [Nat.mul_zero, Nat.add_zero]; exact hsent
  | succ m ih =>
    obtain ⟨wtm, htm, hwhm, hpres, hmat, hblank⟩ := ih (by omega)
    have hmk : m < k := by omega
    have hh : 1 ≤ wtm.head := by
      rw [hwhm]; have := one_le_blockStart k (M + 1); omega
    have hb0 : wtm.cells wtm.head = Γ.blank := by rw [hwhm]; exact hblank _ (by omega)
    have hb1 : wtm.cells (wtm.head + 1) = Γ.blank := by rw [hwhm]; exact hblank _ (by omega)
    have hb2 : wtm.cells (wtm.head + 2) = Γ.blank := by rw [hwhm]; exact hblank _ (by omega)
    have hcs : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).state
        = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0),
            (fun j => if (j : ℕ) < m then false else rc j), ilm, false,
            if m = 0 then false else true) := by
      rw [htm]; simp only [ite_eq_left hmk]; rfl
    have hcw : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm := by rw [htm]
    have hcis : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm]]
      exact his
    have hcos : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output
            from by rw [htm]]
      exact hos
    have hrcm : (fun (j : Fin k) => if (j : ℕ) < m then false else rc j) ⟨m, hmk⟩
        = rc ⟨m, hmk⟩ := by
      simp only [lt_irrefl, ite_false]
    have hnt : ¬((if m = 0 then false else true) = true ∧
        ((⟨m, by omega⟩, 0) : SweepPos k) = (0, 0)) := by
      rintro ⟨hmat', hpos⟩
      have : m = 0 := by
        by_contra h; rw [ite_eq_right h] at hmat'
        exact absurd (congrArg (fun p => (Prod.fst p).val) hpos) (by simp [h])
      simp [this] at hmat'
    have htr := scatter1_mat_triple N bb q' wact oWoD iD iSym oSym m hmk
      (fun j => if (j : ℕ) < m then false else rc j) ilm (if m = 0 then false else true)
      ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1) hcs (by rw [hcw]; exact hh)
      (by rw [hcw]; exact hb0) (by rw [hcw]; exact hb1) (by rw [hcw]; exact hb2) hnt hcis hcos
    erw [hcw] at htr
    simp only [hrcm] at htr
    refine ⟨⟨wtm.head + 3, Function.update (Function.update (Function.update wtm.cells wtm.head
        (if rc ⟨m, hmk⟩ then Γw.one else Γw.zero).toΓ) (wtm.head + 1) Γw.zero.toΓ)
        (wtm.head + 2) Γw.zero.toΓ⟩, ?_, ?_, ?_, ?_, ?_⟩
    · erw [show 3 * (m + 1) = 3 * m + 3 from Nat.mul_succ 3 m, trace_const_add', htr,
        show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm],
        show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output from by rw [htm]]
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
      rw [show (if m + 1 = 0 then false else true) = true from ite_eq_right (by omega),
        show Function.update (fun (j : Fin k) => if (j : ℕ) < m then false else rc j) ⟨m, hmk⟩ false
            = (fun (j : Fin k) => if (j : ℕ) < m + 1 then false else rc j) from by
          funext j
          by_cases hj : j = ⟨m, hmk⟩
          · subst hj; rw [Function.update_self]; simp only [Nat.lt_succ_self, ite_true]
          · rw [Function.update_of_ne hj]
            have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
            by_cases hlt : (j : ℕ) < m
            · simp only [ite_eq_left hlt, ite_eq_left (show (j : ℕ) < m + 1 by omega)]
            · simp only [ite_eq_right hlt, ite_eq_right (show ¬ (j : ℕ) < m + 1 by omega)]]
    · show wtm.head + 3 = blockStart k (M + 1) + 3 * (m + 1)
      rw [hwhm]; omega
    · intro cc hcc
      have hlt : cc < wtm.head := by rw [hwhm]; have := one_le_blockStart k (M + 1); omega
      show Function.update (Function.update (Function.update wtm.cells _ _) _ _) _ _ cc = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hpres cc hcc
    · intro j hj
      by_cases hjm : (j : ℕ) < m
      · obtain ⟨ha, hb, hc⟩ := hmat j hjm
        have key : blockStart k (M + 1) + 3 * (j : ℕ) + 2 < wtm.head := by rw [hwhm]; omega
        refine ⟨?_, ?_, ?_⟩
        · show Function.update (Function.update (Function.update wtm.cells _ _) _ _) _ _
            (headBitCell k (M + 1) j) = _
          rw [Function.update_of_ne (by simp only [headBitCell]; omega),
            Function.update_of_ne (by simp only [headBitCell]; omega),
            Function.update_of_ne (by simp only [headBitCell]; omega)]
          exact ha
        · show Function.update (Function.update (Function.update wtm.cells _ _) _ _) _ _
            (symCell k (M + 1) j) = _
          rw [Function.update_of_ne (by simp only [symCell]; omega),
            Function.update_of_ne (by simp only [symCell]; omega),
            Function.update_of_ne (by simp only [symCell]; omega)]
          exact hb
        · show Function.update (Function.update (Function.update wtm.cells _ _) _ _) _ _
            (symCell k (M + 1) j + 1) = _
          rw [Function.update_of_ne (by simp only [symCell]; omega),
            Function.update_of_ne (by simp only [symCell]; omega),
            Function.update_of_ne (by simp only [symCell]; omega)]
          exact hc
      · have hjeq : (j : ℕ) = m := by omega
        obtain rfl : j = ⟨m, hmk⟩ := Fin.ext hjeq
        have hhb : headBitCell k (M + 1) ⟨m, hmk⟩ = wtm.head := by
          simp only [headBitCell]; rw [hwhm]
        have hsc : symCell k (M + 1) ⟨m, hmk⟩ = wtm.head + 1 := by
          simp only [symCell]; rw [hwhm]
        refine ⟨?_, ?_, ?_⟩
        · rw [hhb]
          show Function.update (Function.update (Function.update wtm.cells wtm.head _) _ _) _ _
            wtm.head = _
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
          split <;> rfl
        · rw [hsc]
          show Function.update
            (Function.update (Function.update wtm.cells _ _) (wtm.head + 1) _) _ _
            (wtm.head + 1) = _
          rw [Function.update_of_ne (by omega), Function.update_self]; rfl
        · rw [hsc]
          show Function.update
            (Function.update (Function.update wtm.cells _ _) _ _) (wtm.head + 2) _
            (wtm.head + 1 + 1) = _
          rw [Function.update_self]; rfl
    · intro cc hcc
      show Function.update (Function.update (Function.update wtm.cells _ _) _ _) _ _ cc = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hblank cc (by omega)

/-- SCATTER sweep-1 **no-head slot-0** step: at a head-bit cell with no head
    (`wH = zero`) and no incoming carry (`rc t = false`), write `zero` (preserving
    the cell) and advance to slot 1. The common case for tapes without a head in
    this block. -/
theorem scatter1_nohead_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hz : (c1.work 0).read = Γ.zero) (hrc : rc ⟨j, hj⟩ = false)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat) bb c1 hst]
  simp only [scatter1Step, hz, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq, Fin.reduceAdd,
    dite_eq_left hj, hrc, Bool.false_eq_true, false_and, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_eq (c1.work 0) Γw.zero.toΓ hz

/-- SCATTER sweep-1 **no-head symbol** step (slot 1 or 2 with `writeFlag = false`):
    the symbol cell is preserved (`readBackWrite`) and the sweep advances. -/
theorem scatter1_nohead_sym {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (pt : Fin (k + 1)) (s : Fin 3) (hs : s ≠ 0) (rc ilm : Fin k → Bool) (mat : Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (pt, s), rc, ilm, false, mat))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hws : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, advanceSweep k (pt, s), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N (q', wact, oWoD, iD, iSym, oSym, (pt, s), rc, ilm, false, mat) bb c1 hst]
  simp only [scatter1Step, hwb, hs, ↓reduceIte, Bool.false_eq_true, ite_self,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_gather_step (c1.work 0) hws

/-- SCATTER sweep-1 **no-head triple** (`trace 3`): a tape with no head in this
    block (head-bit `zero`) and no incoming carry (`rc = false`) is passed through
    untouched — its three cells are preserved and the sweep advances to the next
    tape, carries/markers unchanged. The common per-tape case in a block. -/
theorem scatter1_nohead_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hrc : rc ⟨j, hj⟩ = false)
    (hz0 : (c1.work 0).cells ((c1.work 0).head) = Γ.zero)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (hs1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.start)
    (hs2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 3 },
        output := c1.output } := by
  have e0 := scatter1_nohead_slot0 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat c1 hst
    (by rw [Tape.read]; exact hz0) hrc his hos
  have e1 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 1 (by decide)
    rc ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0]) (by rw [e0]; exact hb1) (by rw [e0]; exact hs1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 2 (by decide)
    rc ilm mat
      ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [advanceSweep, Fin.reduceEq, Fin.reduceAdd, ↓reduceIte])
    (by rw [e1, e0]; exact hb2) (by rw [e1, e0]; exact hs2)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  simp only [advanceSweep, ↓reduceIte]

/-- SCATTER sweep-1 **head slot-0, stay** step: at a head-bit cell with a head
    (`wH = one`) whose `δ` action is `stay`, keep the bit (`one`, preserving the
    cell), set `writeFlag` (so the symbol cells get the new symbol), advance. -/
theorem scatter1_head_slot0_stay {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (wf mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat))
    (hone : (c1.work 0).read = Γ.one) (hstay : (wact ⟨j, hj⟩).2 = Dir3.stay)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, true, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat) bb c1 hst]
  simp only [scatter1Step, hone, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dite_eq_left hj, hstay, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_eq (c1.work 0) Γw.one.toΓ hone

/-- SCATTER sweep-1 **head slot-0, left** step: a head whose `δ` action is `left`
    keeps its bit here for now (`one`, cell preserved) and is recorded in
    `isLeftMover` (sweep-2 moves it one block left); `writeFlag` is set, advance. -/
theorem scatter1_head_slot0_left {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (wf mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat))
    (hone : (c1.work 0).read = Γ.one) (hleft : (wact ⟨j, hj⟩).2 = Dir3.left)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc,
          Function.update ilm ⟨j, hj⟩ true, true, mat),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head + 1 },
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat) bb c1 hst]
  simp only [scatter1Step, hone, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dite_eq_left hj, hleft, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_eq (c1.work 0) Γw.one.toΓ hone

/-- SCATTER sweep-1 **head slot-0, right** step: a head whose `δ` action is `right`
    leaves this cell (`zero` — the bit is cleared, changing the cell), carries the
    head one block right via `rightCarry`, sets `writeFlag`, and advances. -/
theorem scatter1_head_slot0_right {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (wf mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat))
    (hone : (c1.work 0).read = Γ.one) (hright : (wact ⟨j, hj⟩).2 = Dir3.right)
    (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1),
          Function.update rc ⟨j, hj⟩ true, ilm, true, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.zero.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, wf, mat) bb c1 hst]
  simp only [scatter1Step, hone, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dite_eq_left hj, hright, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) Γw.zero.toΓ hh

/-- SCATTER sweep-1 **head sym-hi** step (slot 1, `writeFlag = true`): overwrite the
    high symbol cell with the new symbol's high bit; `writeFlag` stays set. -/
theorem scatter1_head_sym1 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, true, mat))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1
          (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 2), rc, ilm, true, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1, Function.update (c1.work 0).cells
          (c1.work 0).head (encSymW (wact ⟨j, hj⟩).1).1.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1), rc, ilm, true, mat) bb c1 hst]
  simp only [scatter1Step, hwb, ↓reduceIte, advanceSweep, Fin.reduceEq, Fin.reduceAdd,
    dite_eq_left hj, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) (encSymW (wact ⟨j, hj⟩).1).1.toΓ hh

/-- SCATTER sweep-1 **head sym-lo** step (slot 2, `writeFlag = true`): overwrite the
    low symbol cell with the new symbol's low bit; `writeFlag` is reset, advancing
    to the next tape. -/
theorem scatter1_head_sym2 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 2), rc, ilm, true, mat))
    (hwb : (c1.work 0).read ≠ Γ.blank) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1, Function.update (c1.work 0).cells
          (c1.work 0).head (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 2), rc, ilm, true, mat) bb c1 hst]
  simp only [scatter1Step, hwb, ↓reduceIte, advanceSweep, Fin.reduceEq,
    dite_eq_left hj, tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) (encSymW (wact ⟨j, hj⟩).1).2.toΓ hh

/-- SCATTER sweep-1 **head stay triple** (`trace 3`): a tape whose head is in this
    block (head-bit `one`) and stays put writes its new symbol into the two symbol
    cells, keeps its head-bit, and advances; carries/markers unchanged. -/
theorem scatter1_head_stay_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hone : (c1.work 0).cells ((c1.work 0).head) = Γ.one)
    (hstay : (wact ⟨j, hj⟩).2 = Dir3.stay) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (c1.work 0).cells
            ((c1.work 0).head + 1) (encSymW (wact ⟨j, hj⟩).1).1.toΓ)
            ((c1.work 0).head + 2) (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_head_slot0_stay N bb q' wact oWoD iD iSym oSym j hj rc ilm false mat c1 hst
    (by rw [Tape.read]; exact hone) hstay his hos
  have e1 := scatter1_head_sym1 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat
    ((singleTapeSim N).trace 1 (fun _ => bb) c1) (by rw [e0])
    (by rw [e0]; exact hb1) (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_head_sym2 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1])
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]

/-- SCATTER sweep-1 **head left triple** (`trace 3`): like the stay triple (writes
    the new symbol, keeps the head-bit here), but records the tape in `isLeftMover`
    so sweep-2 will move its bit one block left. -/
theorem scatter1_head_left_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hone : (c1.work 0).cells ((c1.work 0).head) = Γ.one)
    (hleft : (wact ⟨j, hj⟩).2 = Dir3.left) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0), rc,
          Function.update ilm ⟨j, hj⟩ true, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (c1.work 0).cells
            ((c1.work 0).head + 1) (encSymW (wact ⟨j, hj⟩).1).1.toΓ)
            ((c1.work 0).head + 2) (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_head_slot0_left N bb q' wact oWoD iD iSym oSym j hj rc ilm false mat c1 hst
    (by rw [Tape.read]; exact hone) hleft his hos
  have e1 := scatter1_head_sym1 N bb q' wact oWoD iD iSym oSym j hj rc
    (Function.update ilm ⟨j, hj⟩ true) mat ((singleTapeSim N).trace 1 (fun _ => bb) c1) (by rw [e0])
    (by rw [e0]; exact hb1) (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_head_sym2 N bb q' wact oWoD iD iSym oSym j hj rc
    (Function.update ilm ⟨j, hj⟩ true) mat
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1])
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]

/-- SCATTER sweep-1 **head right triple** (`trace 3`): a head moving right clears its
    head-bit here (`zero`), writes its new symbol into the two symbol cells, and
    carries the head one block right via `rightCarry`; three cell writes total. -/
theorem scatter1_head_right_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hone : (c1.work 0).cells ((c1.work 0).head) = Γ.one)
    (hright : (wact ⟨j, hj⟩).2 = Dir3.right) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0),
          Function.update rc ⟨j, hj⟩ true, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (Function.update (Function.update (c1.work 0).cells
            (c1.work 0).head Γw.zero.toΓ)
            ((c1.work 0).head + 1) (encSymW (wact ⟨j, hj⟩).1).1.toΓ)
            ((c1.work 0).head + 2) (encSymW (wact ⟨j, hj⟩).1).2.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_head_slot0_right N bb q' wact oWoD iD iSym oSym j hj rc ilm false mat c1 hst
    (by rw [Tape.read]; exact hone) hright hh his hos
  have e1 := scatter1_head_sym1 N bb q' wact oWoD iD iSym oSym j hj
    (Function.update rc ⟨j, hj⟩ true)
    ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) c1) (by rw [e0])
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb1)
    (by rw [e0]; show 1 ≤ (c1.work 0).head + 1; omega)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_head_sym2 N bb q' wact oWoD iD iSym oSym j hj
    (Function.update rc ⟨j, hj⟩ true)
    ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1])
    (by rw [e1, e0]; simp only [Tape.read];
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; show 1 ≤ (c1.work 0).head + 1 + 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]

/-- SCATTER sweep-1 **deposit slot-0** step: at a head-bit cell with no head
    (`wH = zero`) but an incoming carry (`rc t = true` — a head moved right into
    this block), deposit the head-bit (write `one`, clearing the carry); the symbol
    cells are not overwritten (`writeFlag` stays false). -/
theorem scatter1_deposit_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hz : (c1.work 0).read = Γ.zero) (hrc : rc ⟨j, hj⟩ = true) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 1),
          Function.update rc ⟨j, hj⟩ false, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩,
        output := c1.output } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat) bb c1 hst]
  simp only [scatter1Step, hz, reduceCtorEq, ↓reduceIte, advanceSweep, Fin.reduceEq,
    Fin.reduceAdd, dite_eq_left hj, hrc, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_right (c1.work 0) Γw.one.toΓ hh

/-- SCATTER sweep-1 **deposit triple** (`trace 3`): a no-head tape with an incoming
    carry gets its head-bit deposited (write `one`), symbols preserved, carry
    cleared, advance. The right-mover landing case. -/
theorem scatter1_deposit_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (j : ℕ) (hj : j < k) (rc ilm : Fin k → Bool) (mat : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨j, by omega⟩, 0), rc, ilm, false, mat))
    (hz0 : (c1.work 0).cells ((c1.work 0).head) = Γ.zero)
    (hrc : rc ⟨j, hj⟩ = true) (hh : 1 ≤ (c1.work 0).head)
    (hb1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.blank)
    (hb2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.blank)
    (hs1 : (c1.work 0).cells ((c1.work 0).head + 1) ≠ Γ.start)
    (hs2 : (c1.work 0).cells ((c1.work 0).head + 2) ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
          (⟨if j + 1 < k then j + 1 else 0, by split <;> omega⟩, 0),
          Function.update rc ⟨j, hj⟩ false, ilm, false, mat),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head + 3,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter1_deposit_slot0 N bb q' wact oWoD iD iSym oSym j hj rc ilm mat c1 hst
    (by rw [Tape.read]; exact hz0) hrc hh his hos
  have e1 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 1 (by decide)
    (Function.update rc ⟨j, hj⟩ false) ilm mat ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0])
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb1)
    (by rw [e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hs1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter1_nohead_sym N bb q' wact oWoD iD iSym oSym ⟨j, by omega⟩ 2 (by decide)
    (Function.update rc ⟨j, hj⟩ false) ilm mat
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [advanceSweep, Fin.reduceEq, Fin.reduceAdd, ↓reduceIte])
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hb2)
    (by rw [e1, e0]; simp only [Tape.read]; rw [Function.update_of_ne (by omega)]; exact hs2)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  simp only [advanceSweep, ↓reduceIte]

/-- The **SCATTER sweep-1 → sweep-2 turn-around** (`trace 1`): once the freshly
    materialized block is complete (`mat`, back at tape `0` slot `0`, reading the
    `□` past it), the sweep turns leftward into sweep-2 at the last block's last
    cell. -/
theorem scatter1_turnaround {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rightCarry isLeftMover : Fin k → Bool) (writeFlag : Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (0, 0), rightCarry, isLeftMover, writeFlag, true))
    (hblank : (c1.work 0).read = Γ.blank) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter2
          (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2), isLeftMover, fun _ => false),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun i => (c1.work i).writeAndMove Γw.blank.toΓ Dir3.left,
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
  rw [scatter1_trace1 N
    (q', wact, oWoD, iD, iSym, oSym, (0, 0), rightCarry, isLeftMover, writeFlag, true) bb c1 hst]
  simp only [scatter1Step, hblank, ↓reduceIte, and_self]; rfl

/-- **SCATTER block step — no-head tape.** Tape `m` has no head in block `b`
    (`(c.work m).head ≠ b`) and no incoming carry (`¬((c.work m).head = b-1 ∧ right)`,
    so `rc m = false`): its three cells are unchanged — which already IS the
    intermediate encoding, since the head neither sits at nor moves into `b`.
    Advances the within-block invariant `b m → b (m+1)` with `rc`/`ilm` unchanged. -/
theorem scatter1_tape_nohead {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhd : (c.work ⟨m, hmk⟩).head ≠ b)
    (hndep : ¬((c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right))
    (hrc : rc ⟨m, hmk⟩ = decide ((c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hrcf : rc ⟨m, hmk⟩ = false := by rw [hrc]; exact decide_eq_false hndep
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head ≠ b := by
    rw [scatterInterWork_head]
    split_ifs with hdir
    · intro hb; exact hndep ⟨by omega, hdir⟩
    · exact hhd
  have hcb : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (c.work ⟨m, hmk⟩).cells b :=
    scatterInterWork_cells_of_ne (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (Ne.symm hhd)
  have htriple := scatter1_nohead_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    hrcf
    (by rw [hhead]; exact hot.1.trans (ite_eq_right hhd))
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_start _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    his hos
  refine ⟨{ c1.work 0 with head := (c1.work 0).head + 3 }, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show (c1.work 0).cells (headBitCell k b ⟨m, hmk⟩) = _
      rw [hot.1, ite_eq_right hhd, ite_eq_right hscat]
    · show (c1.work 0).cells (symCell k b ⟨m, hmk⟩) = _
      rw [hcb]; exact hot.2.1
    · show (c1.work 0).cells (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [hcb]; exact hot.2.2
    · intro c _ _ _; rfl

/-- **SCATTER block step — deposit (right-mover landing).** Tape `m` has no head
    in block `b` but an incoming carry: its head moved right out of `b-1`
    (`(c.work m).head = b-1 ∧ dir = right`, so `rc m = true`). The deposit writes
    the head-bit `one` at `(b,m)` (clearing the carry); symbols stay (the new
    symbol was written back at `b-1`). The intermediate head IS at `b`
    (`scatterInterWork.head = (b-1)+1 = b`). Advances `b m → b (m+1)`, clearing
    `rc m`. -/
theorem scatter1_tape_deposit {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hdep : (c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
    (hrc : rc ⟨m, hmk⟩ = true)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0),
            Function.update rc ⟨m, hmk⟩ false, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  obtain ⟨hdh, hdr⟩ := hdep
  have hhd : (c.work ⟨m, hmk⟩).head ≠ b := by omega
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b := by
    rw [scatterInterWork_head, ite_eq_left hdr]; omega
  have hcb : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (c.work ⟨m, hmk⟩).cells b :=
    scatterInterWork_cells_of_ne (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (Ne.symm hhd)
  have htriple := scatter1_deposit_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (ite_eq_right hhd))
    hrc hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_start _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ
        (headBitCell k b ⟨m, hmk⟩) = _
      rw [← hhead, Function.update_self, ite_eq_left hscat]; rfl
    · show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ
        (symCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; simp only [symCell, headBitCell]; omega), hcb]
      exact hot.2.1
    · show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ
        (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [Function.update_of_ne (by rw [hhead]; simp only [symCell, headBitCell]; omega), hcb]
      exact hot.2.2
    · intro c hc _ _
      show Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ c = (c1.work 0).cells c
      rw [Function.update_of_ne (by rw [hhead]; exact hc)]

/-- **SCATTER block step — head, stay.** Tape `m` has its head at block `b`
    (`(c.work m).head = b`) with `δ`-action `stay`: keep the head-bit `one`, write
    the new symbol into the two symbol cells. The intermediate head stays at `b`
    (`scatterInterWork.head = b`, since `stay ≠ right`) and the intermediate symbol
    at `b` is the new write (`scatterInterWork.cells b = (wact m).1`, via
    `cells_at_head`), matched to the triple's `encSymW` writes by the codec bridge.
    Advances `b m → b (m+1)`, `rc`/`ilm` unchanged. -/
theorem scatter1_tape_head_stay {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhdb : (c.work ⟨m, hmk⟩).head = b) (hstay : (wact ⟨m, hmk⟩).2 = Dir3.stay)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b := by
    rw [scatterInterWork_head,
      ite_eq_right (show ¬ (wact ⟨m, hmk⟩).2 = Dir3.right by rw [hstay]; decide)]
    exact hhdb
  have hcbh : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (wact ⟨m, hmk⟩).1.toΓ := by
    rw [← hhdb]; exact scatterInterWork_cells_at_head (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (by omega)
  have htriple := scatter1_head_stay_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (ite_eq_left hhdb))
    hstay hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (Function.update (c1.work 0).cells
        ((c1.work 0).head + 1) (encSymW (wact ⟨m, hmk⟩).1).1.toΓ)
        ((c1.work 0).head + 2) (encSymW (wact ⟨m, hmk⟩).1).2.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _
        (headBitCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; omega),
          Function.update_of_ne (by rw [hhead]; omega),
          hot.1, ite_eq_left hhdb, ite_eq_left hscat]
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (symCell k b ⟨m, hmk⟩) = _
      rw [show symCell k b ⟨m, hmk⟩ = (c1.work 0).head + 1 by rw [hsym, hhead],
          Function.update_of_ne (by omega), Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).1
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _
        (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [show symCell k b ⟨m, hmk⟩ + 1 = (c1.work 0).head + 2 by rw [hsym2, hhead],
          Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).2
    · intro c _ hc2 hc3
      show Function.update (Function.update (c1.work 0).cells _ _) _ _ c = (c1.work 0).cells c
      rw [Function.update_of_ne (show c ≠ (c1.work 0).head + 2 by rw [hhead, ← hsym2]; exact hc3),
          Function.update_of_ne (show c ≠ (c1.work 0).head + 1 by rw [hhead, ← hsym]; exact hc2)]

/-- **SCATTER block step — head, left.** Like `head_stay` (head-bit kept `one`,
    new symbol written) but the `δ`-action is `left`: the tape is recorded in
    `isLeftMover` (sweep-2 moves its bit one block left later). The intermediate
    head still sits at `b` (`scatterInterWork.head = b`, since `left ≠ right`), so
    the SCATTER-1 target is unchanged from stay; only `ilm` advances. -/
theorem scatter1_tape_head_left {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhdb : (c.work ⟨m, hmk⟩).head = b) (hleft : (wact ⟨m, hmk⟩).2 = Dir3.left)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc,
            Function.update ilm ⟨m, hmk⟩ true, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head = b := by
    rw [scatterInterWork_head,
      ite_eq_right (show ¬ (wact ⟨m, hmk⟩).2 = Dir3.right by rw [hleft]; decide)]
    exact hhdb
  have hcbh : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (wact ⟨m, hmk⟩).1.toΓ := by
    rw [← hhdb]; exact scatterInterWork_cells_at_head (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (by omega)
  have htriple := scatter1_head_left_triple N bb q' wact oWoD iD iSym oSym m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (ite_eq_left hhdb))
    hleft hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (Function.update (c1.work 0).cells
        ((c1.work 0).head + 1) (encSymW (wact ⟨m, hmk⟩).1).1.toΓ)
        ((c1.work 0).head + 2) (encSymW (wact ⟨m, hmk⟩).1).2.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _
        (headBitCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; omega),
          Function.update_of_ne (by rw [hhead]; omega),
          hot.1, ite_eq_left hhdb, ite_eq_left hscat]
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _ (symCell k b ⟨m, hmk⟩) = _
      rw [show symCell k b ⟨m, hmk⟩ = (c1.work 0).head + 1 by rw [hsym, hhead],
          Function.update_of_ne (by omega), Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).1
    · show Function.update (Function.update (c1.work 0).cells _ _) _ _
        (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [show symCell k b ⟨m, hmk⟩ + 1 = (c1.work 0).head + 2 by rw [hsym2, hhead],
          Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).2
    · intro c _ hc2 hc3
      show Function.update (Function.update (c1.work 0).cells _ _) _ _ c = (c1.work 0).cells c
      rw [Function.update_of_ne (show c ≠ (c1.work 0).head + 2 by rw [hhead, ← hsym2]; exact hc3),
          Function.update_of_ne (show c ≠ (c1.work 0).head + 1 by rw [hhead, ← hsym]; exact hc2)]

/-- **SCATTER block step — head, right.** Tape `m`'s head at `b` moving right:
    clears the head-bit here (`zero`), writes the new symbol, carries the head one
    block right via `rc`. The intermediate head moves to `b+1`
    (`scatterInterWork.head = b+1 ≠ b`), so the cleared `zero` matches; the new
    symbol at `b` (the old head's cell) matches via the codec bridge. Advances
    `b m → b (m+1)`, setting `rc m`. -/
theorem scatter1_tape_head_right {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = headBitCell k b ⟨m, hmk⟩)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b m)
    (hhdb : (c.work ⟨m, hmk⟩).head = b) (hright : (wact ⟨m, hmk⟩).2 = Dir3.right)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0),
            Function.update rc ⟨m, hmk⟩ true, ilm, false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k b ⟨m, hmk⟩ + 3
      ∧ Scatter1BlockInv wt c.work wact M b (m + 1) := by
  have hot := hbm.oldTape ⟨m, hmk⟩ (le_refl m)
  have hsym : symCell k b ⟨m, hmk⟩ = headBitCell k b ⟨m, hmk⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k b ⟨m, hmk⟩ + 1 = headBitCell k b ⟨m, hmk⟩ + 2 := by
    simp only [symCell, headBitCell]
  have hh1 : 1 ≤ (c1.work 0).head := by
    rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k b; omega
  have hscat : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).head ≠ b := by
    rw [scatterInterWork_head, ite_eq_left hright]; omega
  have hcbh : (scatterInterWork (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩)).cells b
      = (wact ⟨m, hmk⟩).1.toΓ := by
    rw [← hhdb]; exact scatterInterWork_cells_at_head (c.work ⟨m, hmk⟩) (wact ⟨m, hmk⟩) (by omega)
  have htriple := scatter1_head_right_triple N bb q' wact oWoD iD iSym oSym
    m hmk rc ilm false c1 hst
    (by rw [hhead]; exact hot.1.trans (ite_eq_left hhdb))
    hright hh1
    (by rw [hhead, ← hsym, hot.2.1]; exact (encSymΓ_ne_blank _).1)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_blank _).2)
    his hos
  refine ⟨⟨(c1.work 0).head + 3,
      Function.update (Function.update (Function.update (c1.work 0).cells
        (c1.work 0).head Γw.zero.toΓ)
        ((c1.work 0).head + 1) (encSymW (wact ⟨m, hmk⟩).1).1.toΓ)
        ((c1.work 0).head + 2) (encSymW (wact ⟨m, hmk⟩).1).2.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head + 3 = headBitCell k b ⟨m, hmk⟩ + 3
    rw [hhead]
  · apply scatter1_blockinv_step hb1 hbM hmk hbm
    · show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _
        (headBitCell k b ⟨m, hmk⟩) = _
      rw [Function.update_of_ne (by rw [hhead]; omega),
          Function.update_of_ne (by rw [hhead]; omega),
          ← hhead, Function.update_self, ite_eq_right hscat]; rfl
    · show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _
        (symCell k b ⟨m, hmk⟩) = _
      rw [show symCell k b ⟨m, hmk⟩ = (c1.work 0).head + 1 by rw [hsym, hhead],
          Function.update_of_ne (by omega), Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).1
    · show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _
        (symCell k b ⟨m, hmk⟩ + 1) = _
      rw [show symCell k b ⟨m, hmk⟩ + 1 = (c1.work 0).head + 2 by rw [hsym2, hhead],
          Function.update_self, hcbh]
      exact (encSymW_toΓ_eq_encSymΓ _).2
    · intro c hc1 hc2 hc3
      show Function.update (Function.update (Function.update (c1.work 0).cells _ _) _ _) _ _ c
        = (c1.work 0).cells c
      rw [Function.update_of_ne (show c ≠ (c1.work 0).head + 2 by rw [hhead, ← hsym2]; exact hc3),
          Function.update_of_ne (show c ≠ (c1.work 0).head + 1 by rw [hhead, ← hsym]; exact hc2),
          Function.update_of_ne (show c ≠ (c1.work 0).head by rw [hhead]; exact hc1)]

/-- **SCATTER block sweep (`trace (3*m)`).** Sweeping the first `m ≤ k` tapes of
    block `b` (from tape `0`, slot `0`, work head `blockStart k b`, incoming carry
    `rc_in j = decide((c.work j).head = b-1 ∧ right)`): after `m` tapes the head is
    at `blockStart k b + 3*m`, the sweep is back at slot `0` (tape `m mod k`), the
    tape's first `m` tapes of block `b` are intermediate-encoded (`Scatter1BlockInv
    … b m`), and `rc`/`ilm` are threaded — `rc` records the right-movers of the
    first `m` tapes, `ilm` the left-movers. Proved by induction on `m`, each step
    one of the five per-tape block-step lemmas selected by the old head-bit and
    `rc`. -/
private theorem scatter1_block_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc_in ilm_in : Fin k → Bool)
    (hrc_in : ∀ j : Fin k, rc_in j = decide ((c.work j).head = b - 1 ∧ (wact j).2 = Dir3.right))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc_in, ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k b)
    (hbm : Scatter1BlockInv (c1.work 0) c.work wact M b 0)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (m : ℕ) (hm : m ≤ k) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * m) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
            (⟨if m < k then m else 0, by split <;> omega⟩, 0),
            (fun (j : Fin k) => if (j : ℕ) < m then
                decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j),
            (fun (j : Fin k) => if (j : ℕ) < m ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
                true else ilm_in j),
            false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k b + 3 * m
      ∧ Scatter1BlockInv wt c.work wact M b m := by
  induction m with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, hbm⟩
    · have h0 : (singleTapeSim N).trace (3 * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      simp only [Nat.not_lt_zero, ↓reduceIte, false_and] at hst ⊢
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
      · split <;> rfl
      · funext x
        obtain rfl : x = 0 := Subsingleton.elim x 0
        rfl
    · simp only [Nat.mul_zero, Nat.add_zero]; exact hhead
  | succ m ih =>
    obtain ⟨wtm, htm, hwhm, hbim⟩ := ih (by omega)
    have hmk : m < k := by omega
    -- the threaded rc/ilm at m (what the IH config carries)
    set RCm := (fun (j : Fin k) => if (j : ℕ) < m then
        decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j) with hRCm
    set ILMm := (fun (j : Fin k) =>
      if (j : ℕ) < m ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
        true else ilm_in j) with hILMm
    -- structural step: the m+1 closed forms are single-slot updates of the m forms
    have hstep_rc : (fun (j : Fin k) => if (j : ℕ) < m + 1 then
          decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j)
        = Function.update RCm ⟨m, hmk⟩
            (decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)) := by
      funext j
      by_cases hj : j = ⟨m, hmk⟩
      · subst hj; rw [Function.update_self]; simp only [Nat.lt_succ_self, ite_true]
      · rw [Function.update_of_ne hj, hRCm]
        have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
        by_cases hlt : (j : ℕ) < m
        · simp only [ite_eq_left hlt, ite_eq_left (show (j : ℕ) < m + 1 by omega)]
        · simp only [ite_eq_right hlt, ite_eq_right (show ¬ (j : ℕ) < m + 1 by omega)]
    have hstep_ilm : (fun (j : Fin k) =>
        if (j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
          true else ilm_in j)
        = Function.update ILMm ⟨m, hmk⟩
            (if (c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.left then
              true else ilm_in ⟨m, hmk⟩) := by
      funext j
      by_cases hj : j = ⟨m, hmk⟩
      · subst hj; rw [Function.update_self]; simp only [Nat.lt_succ_self, true_and]
      · rw [Function.update_of_ne hj, hILMm]
        have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
        have hiff : ((j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left)
            ↔ ((j : ℕ) < m ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left) :=
          ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
        simp only [hiff]
    -- ILMm at slot m collapses to the incoming ilm_in
    have hILMm_at : ILMm ⟨m, hmk⟩ = ilm_in ⟨m, hmk⟩ := by
      rw [hILMm]; simp only [lt_irrefl, false_and, ite_false]
    have hRCm_at : RCm ⟨m, hmk⟩ = rc_in ⟨m, hmk⟩ := by
      rw [hRCm]; simp only [lt_irrefl, ite_false]
    -- facts about the IH config cM = trace (3*m) c1
    have hcs : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).state
        = SimQ.scatter1
            (q', wact, oWoD, iD, iSym, oSym, (⟨m, by omega⟩, 0), RCm, ILMm, false, false) := by
      rw [htm]; simp only [ite_eq_left hmk]; rfl
    have hch : (((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0).head
        = headBitCell k b ⟨m, hmk⟩ := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm
            from by rw [htm], hwhm]
      simp only [headBitCell]
    have hcbi : Scatter1BlockInv (((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0)
        c.work wact M b m := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm from by rw [htm]]
      exact hbim
    have hcis : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm]]
      exact his
    have hcos : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output
            from by rw [htm]]
      exact hos
    -- assembly closure (the trace_const_add' + input/output reconciliation, done once)
    have key : ∀ (wt : Tape) (rc' ilm' : Fin k → Bool),
        (singleTapeSim N).trace 3 (fun _ => bb)
            ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1)
          = { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
                (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0), rc', ilm', false, false),
              input := ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input,
              work := fun _ => wt,
              output := ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output } →
        rc' = (fun (j : Fin k) => if (j : ℕ) < m + 1 then
            decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j) →
        ilm' = (fun (j : Fin k) =>
            if (j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
            true else ilm_in j) →
        wt.head = headBitCell k b ⟨m, hmk⟩ + 3 →
        Scatter1BlockInv wt c.work wact M b (m + 1) →
        ∃ wt' : Tape,
          (singleTapeSim N).trace (3 * (m + 1)) (fun _ => bb) c1 =
            { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
                (⟨if m + 1 < k then m + 1 else 0, by split <;> omega⟩, 0),
                (fun (j : Fin k) => if (j : ℕ) < m + 1 then
                    decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j),
                (fun (j : Fin k) =>
                    if (j : ℕ) < m + 1 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
                    true else ilm_in j), false, false),
              input := c1.input, work := fun _ => wt', output := c1.output }
          ∧ wt'.head = blockStart k b + 3 * (m + 1)
          ∧ Scatter1BlockInv wt' c.work wact M b (m + 1) := by
      intro wt rc' ilm' htr hrc hilm hwh hbi
      refine ⟨wt, ?_, ?_, hbi⟩
      · erw [show 3 * (m + 1) = 3 * m + 3 from by omega, trace_const_add', htr, hrc, hilm,
          show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm],
          show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output
            from by rw [htm]]
      · rw [hwh]; simp only [headBitCell]; omega
    -- helper: ¬(head = b - 1 ∧ right) when head = b
    have hndep_of_eq : (c.work ⟨m, hmk⟩).head = b →
        ¬((c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right) :=
      fun he h => by obtain ⟨h1, _⟩ := h; omega
    -- dispatch on the old head-bit and the carry
    by_cases hhd : (c.work ⟨m, hmk⟩).head = b
    · rcases h3 : (wact ⟨m, hmk⟩).2 with _ | _ | _
      · -- left
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_head_left N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd h3 hcis hcos
        refine key wt RCm (Function.update ILMm ⟨m, hmk⟩ true) htr ?_ ?_ hwh hbi
        · rw [hstep_rc, show decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
              = RCm ⟨m, hmk⟩ from by
            rw [hRCm_at, hrc_in, decide_eq_false
                (fun h => by rw [h3] at h; exact absurd h.2 (by decide)),
              decide_eq_false (hndep_of_eq hhd)], Function.update_eq_self]
        · rw [hstep_ilm, ite_eq_left ⟨hhd, h3⟩]
      · -- right
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_head_right N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd h3 hcis hcos
        refine key wt (Function.update RCm ⟨m, hmk⟩ true) ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, decide_eq_true ⟨hhd, h3⟩]
        · rw [hstep_ilm,
          ite_eq_right (show ¬((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.left)
              from fun h => by rw [h3] at h; exact absurd h.2 (by decide)), ← hILMm_at,
            Function.update_eq_self]
      · -- stay
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_head_stay N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd h3 hcis hcos
        refine key wt RCm ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, show decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
              = RCm ⟨m, hmk⟩ from by
            rw [hRCm_at, hrc_in, decide_eq_false
                (fun h => by rw [h3] at h; exact absurd h.2 (by decide)),
              decide_eq_false (hndep_of_eq hhd)], Function.update_eq_self]
        · rw [hstep_ilm,
          ite_eq_right (show ¬((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.left)
              from fun h => by rw [h3] at h; exact absurd h.2 (by decide)), ← hILMm_at,
            Function.update_eq_self]
    · by_cases hdep : (c.work ⟨m, hmk⟩).head = b - 1 ∧ (wact ⟨m, hmk⟩).2 = Dir3.right
      · -- deposit
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_deposit N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hdep
          (by rw [hRCm_at, hrc_in]; exact decide_eq_true hdep) hcis hcos
        refine key wt (Function.update RCm ⟨m, hmk⟩ false) ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, decide_eq_false (show ¬((c.work ⟨m, hmk⟩).head = b ∧ _)
              from fun h => hhd h.1)]
        · rw [hstep_ilm,
          ite_eq_right (show ¬((c.work ⟨m, hmk⟩).head = b ∧ _) from fun h => hhd h.1),
            ← hILMm_at, Function.update_eq_self]
      · -- nohead
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_tape_nohead N bb c b M hb1 hbM m hmk
          q' wact oWoD iD iSym oSym RCm ILMm _ hcs hch hcbi hhd hdep
          (by rw [hRCm_at, hrc_in]) hcis hcos
        refine key wt RCm ILMm htr ?_ ?_ hwh hbi
        · rw [hstep_rc, show decide ((c.work ⟨m, hmk⟩).head = b ∧ (wact ⟨m, hmk⟩).2 = Dir3.right)
              = RCm ⟨m, hmk⟩ from by
            rw [hRCm_at, hrc_in, decide_eq_false (fun h => hhd h.1), decide_eq_false hdep],
            Function.update_eq_self]
        · rw [hstep_ilm,
          ite_eq_right (show ¬((c.work ⟨m, hmk⟩).head = b ∧ _) from fun h => hhd h.1),
            ← hILMm_at, Function.update_eq_self]

/-- **SCATTER one full block (`trace (3*k)`).** Sweeping all `k` tapes of block `b`
    advances the mid-sweep invariant `Scatter1MidInv … b → … (b+1)`: the head moves
    to `blockStart k (b+1)`, the carry `rc` updates from the incoming
    `decide(head = b-1 ∧ right)` to the outgoing `decide(head = b ∧ right)` (= the
    incoming carry of block `b+1`), and `ilm` records block `b`'s left-movers.
    Wraps `scatter1_block_aux` at `m = k` between `ofMid` and `toMidSucc`. -/
theorem scatter1_block_step {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc_in ilm_in : Fin k → Bool)
    (hrc_in : ∀ j : Fin k, rc_in j = decide ((c.work j).head = b - 1 ∧ (wact j).2 = Dir3.right))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc_in, ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k b)
    (hmid : Scatter1MidInv (c1.work 0) c.work wact M b)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * k) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
            (fun j => decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right)),
            (fun j => if (c.work j).head = b ∧ (wact j).2 = Dir3.left then true else ilm_in j),
            false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k (b + 1)
      ∧ Scatter1MidInv wt c.work wact M (b + 1) := by
  obtain ⟨wt, htr, hwh, hbi⟩ := scatter1_block_aux N bb c b M hb1 hbM q' wact oWoD iD iSym oSym
    rc_in ilm_in hrc_in c1 hst hhead (Scatter1BlockInv.ofMid hbM hmid) his hos k (le_refl k)
  refine ⟨wt, ?_, ?_, Scatter1BlockInv.toMidSucc hbi⟩
  · rw [htr]
    have hrc_k : (fun (j : Fin k) => if (j : ℕ) < k then
          decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j)
        = (fun j => decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right)) := by
      funext j; rw [ite_eq_left j.isLt]
    have hilm_k : (fun (j : Fin k) =>
        if (j : ℕ) < k ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
          true else ilm_in j)
        = (fun j => if (c.work j).head = b ∧ (wact j).2 = Dir3.left then true else ilm_in j) := by
      funext j; simp only [j.isLt, true_and]
    rw [hrc_k, hilm_k]
    simp only [lt_irrefl, ite_false]
  · rw [hwh, blockStart_succ k b hb1, blockWidth]

/-- **SCATTER full block sweep (`trace (3*k*B)`).** Sweeping the first `B ≤ M`
    blocks (from block `1`, tape `0`, slot `0`, work head `blockStart k 1`, incoming
    carry `decide(head = 0 ∧ right)`, the REWIND output `SimInvAt M`): after `B`
    blocks the head is at `blockStart k (B+1)`, the sweep is back at tape `0` slot
    `0`, the carry records the right-movers whose head is at `B`, `ilm` records the
    left-movers in blocks `[1, B]`, and the tape is `Scatter1MidInv … (B+1)`. Proved
    by induction on `B`, each step one `scatter1_block_step` at block `B+1`. -/
private theorem scatter1_sweep_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (ilm_in : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
      (fun j => decide ((c.work j).head = 0 ∧ (wact j).2 = Dir3.right)), ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hsim : SimInvAt k (c1.work 0) c.work M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (B : ℕ) (hB : B ≤ M) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1 =
        { state := SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
            (fun j => decide ((c.work j).head = B ∧ (wact j).2 = Dir3.right)),
            (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
                true else ilm_in j),
            false, false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k (B + 1)
      ∧ Scatter1MidInv wt c.work wact M (B + 1) := by
  induction B with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, scatter1MidInv_init wact hsim⟩
    · have h0 : (singleTapeSim N).trace (3 * k * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
      · rw [show (fun (j : Fin k) => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ 0 ∧
              (wact j).2 = Dir3.left then true else ilm_in j) = ilm_in from by
          funext j; rw [ite_eq_right (by rintro ⟨h1, h2, _⟩; omega)]]
      · funext x
        obtain rfl : x = 0 := Subsingleton.elim x 0
        rfl
    · exact hhead
  | succ B ih =>
    obtain ⟨wtB, htB, hwhB, hmidB⟩ := ih (by omega)
    have hcw : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).work 0 = wtB := by rw [htB]
    have hci : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).input = c1.input := by
      rw [htB]
    have hco : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).output = c1.output := by
      rw [htB]
    obtain ⟨wt, htr, hwh, hmid'⟩ := scatter1_block_step N bb c (B + 1) M (by omega) hB
      q' wact oWoD iD iSym oSym
      (fun j => decide ((c.work j).head = B ∧ (wact j).2 = Dir3.right))
      (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
          true else ilm_in j)
      (fun j => by simp only [Nat.add_sub_cancel])
      ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1) (by rw [htB])
      (by rw [hcw]; exact hwhB) (by rw [hcw]; exact hmidB)
      (by rw [hci]; exact his) (by rw [hco]; exact hos)
    refine ⟨wt, ?_, ?_, hmid'⟩
    · erw [show 3 * k * (B + 1) = 3 * k * B + 3 * k from Nat.mul_succ (3 * k) B,
        trace_const_add', htr, hci, hco]
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
      rw [show (fun (j : Fin k) => if (c.work j).head = B + 1 ∧ (wact j).2 = Dir3.left then true
            else if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
              true else ilm_in j)
          = (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B + 1 ∧ (wact j).2 = Dir3.left then
              true else ilm_in j) from by
        funext j
        by_cases hL : (wact j).2 = Dir3.left
        · simp only [hL, and_true]
          split_ifs with h1 h2 h3 <;> first | rfl | omega
        · simp only [hL, and_false, ite_false]]
    · rw [hwh]

/-- **One non-turnaround SCATTER sweep-1 step stays in `scatter1`.** As long as the
    sweep is not at the turnaround trigger (`mat = true ∧ pos = (0,0)`), one step from
    a `scatter1` config lands in `scatter1` again — `scatter1Step` only escapes to
    `scatter2` in that one branch. The condition is on the **state data alone** (no
    head/read needed), so it threads cleanly through a per-step induction. -/
theorem scatter1_step_stays {k : ℕ} (N : NTM k) (b : Bool) (d : Scatter1Data k N.Q)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter1 d)
    (hnt : ¬ (d.2.2.2.2.2.2.2.2.2.2 = true ∧ d.2.2.2.2.2.2.1 = (0, 0))) :
    ∃ d', ((singleTapeSim N).trace 1 (fun _ => b) c1).state = SimQ.scatter1 d'
      ∧ d'.2.2.2.2.2.2.1 = advanceSweep k d.2.2.2.2.2.2.1 := by
  rw [scatter1_trace1 N d b c1 hst]
  show ∃ d', (scatter1Step d c1.input.read ((c1.work 0).read) c1.output.read).1 = SimQ.scatter1 d'
    ∧ d'.2.2.2.2.2.2.1 = advanceSweep k d.2.2.2.2.2.2.1
  obtain ⟨q', wact, oWoD, iD, iSym, oSym, pos, rightCarry, isLeftMover, writeFlag, mat⟩ := d
  simp only at hnt ⊢
  simp only [scatter1Step]
  by_cases hwH : (c1.work 0).read = Γ.blank
  · rw [ite_eq_left hwH, ite_eq_right (by rintro ⟨hm, hp⟩; exact hnt ⟨hm, hp⟩)]
    exact ⟨_, rfl, rfl⟩
  · rw [ite_eq_right hwH]
    (repeat' split) <;> exact ⟨_, rfl, rfl⟩

/-- **SCATTER block sweep stays in `scatter1` (per step).** Within one block of the
    sweep-1 phase (`mat = false`, slot-0 block entry), every micro-step `s ≤ 3*k`
    keeps the simulator in a `scatter1` state. Proved by reaching the nearest 3-step
    boundary with `scatter1_block_aux` (whose output is a `scatter1`, slot-0,
    `mat = false` config — so `¬turnaround`) and stepping the remaining `s % 3 ≤ 2`
    micro-steps with `scatter1_step_stays` (the carried `pos`/`mat` never hit the
    turnaround trigger). -/
theorem scatter1_block_states {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (b M : ℕ)
    (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc_in ilm_in : Fin k → Bool)
    (hrc_in : ∀ j : Fin k, rc_in j = decide ((c.work j).head = b - 1 ∧ (wact j).2 = Dir3.right))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc_in, ilm_in, false, false))
    (hhead : (c1.work 0).head = blockStart k b)
    (hmid : Scatter1MidInv (c1.work 0) c.work wact M b)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (hk : 1 ≤ k) :
    ∀ s, s ≤ 3 * k →
      ∃ d, ((singleTapeSim N).trace s (fun _ => bb) c1).state = SimQ.scatter1 d := by
  -- Generic single-step extension: from a `scatter1`, `mat = false` config, any one
  -- step stays `scatter1` (and `mat` cannot have become `true` reading a non-blank
  -- cell). We only need: one step from a `scatter1 d` config with `d.mat = false`
  -- stays `scatter1` — `scatter1_step_stays` with `hnt` discharged by `mat = false`.
  have step_from_matFalse : ∀ (cc : Cfg 1 (SimQ k N.Q)) (d : Scatter1Data k N.Q),
      cc.state = SimQ.scatter1 d → d.2.2.2.2.2.2.2.2.2.2 = false →
      ∃ d', ((singleTapeSim N).trace 1 (fun _ => bb) cc).state = SimQ.scatter1 d'
        ∧ d'.2.2.2.2.2.2.1 = advanceSweep k d.2.2.2.2.2.2.1 := by
    intro cc d hcc hmat
    exact scatter1_step_stays N bb d cc hcc (by rw [hmat]; simp)
  -- Generic single-step extension from any `scatter1` config whose `pos ≠ (0,0)`.
  have step_from_posNe : ∀ (cc : Cfg 1 (SimQ k N.Q)) (d : Scatter1Data k N.Q),
      cc.state = SimQ.scatter1 d → d.2.2.2.2.2.2.1 ≠ (0, 0) →
      ∃ d', ((singleTapeSim N).trace 1 (fun _ => bb) cc).state = SimQ.scatter1 d'
        ∧ d'.2.2.2.2.2.2.1 = advanceSweep k d.2.2.2.2.2.2.1 := by
    intro cc d hcc hpos
    exact scatter1_step_stays N bb d cc hcc (by rintro ⟨_, h⟩; exact hpos h)
  intro s hs
  -- reach the nearest 3-step boundary
  obtain ⟨wt, htr, _, _⟩ := scatter1_block_aux N bb c b M hb1 hbM q' wact oWoD iD iSym oSym
    rc_in ilm_in hrc_in c1 hst hhead (Scatter1BlockInv.ofMid hbM hmid) his hos (s / 3) (by omega)
  -- the boundary config is scatter1 with slot `0`, `mat = false`
  have hsplit : s = 3 * (s / 3) + s % 3 := by omega
  erw [hsplit, trace_const_add']
  set c0 := (singleTapeSim N).trace (3 * (s / 3)) (fun _ => bb) c1 with hc0
  -- the boundary config's state (slot `0`, `mat = false`)
  have hc0st : c0.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
      (⟨if s / 3 < k then s / 3 else 0, by split <;> omega⟩, 0),
      (fun (j : Fin k) => if (j : ℕ) < s / 3 then
          decide ((c.work j).head = b ∧ (wact j).2 = Dir3.right) else rc_in j),
      (fun (j : Fin k) => if (j : ℕ) < s / 3 ∧ (c.work j).head = b ∧ (wact j).2 = Dir3.left then
          true else ilm_in j),
      false, false) := by rw [htr]
  have hr3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  -- after one boundary step the pos is at slot 1; after two, slot 2 — never `(0,0)`
  rcases hr3 with hr | hr | hr <;> rw [hr]
  · exact ⟨_, hc0st⟩
  · obtain ⟨d', hd', _⟩ := step_from_matFalse c0 _ hc0st rfl
    exact ⟨d', hd'⟩
  · -- two steps: first lands at slot 1 (`pos ≠ (0,0)`), second stays scatter1
    erw [show (2 : ℕ) = 1 + 1 from rfl, trace_const_add']
    obtain ⟨d', hd', hpos'⟩ := step_from_matFalse c0 _ hc0st rfl
    obtain ⟨d'', hd'', _⟩ := step_from_posNe _ d' hd'
      (by rw [hpos']; simp [advanceSweep])
    exact ⟨d'', hd''⟩

/-- **SCATTER materialize sweep stays in `scatter1` (per step).** During the
    materialize phase (block `M+1`, `3*k` micro-steps), every step `s < 3*k` keeps the
    simulator in `scatter1`. Mirrors `scatter1_block_states`: reach the 3-step boundary
    with `scatter1_mat_aux` (slot-0, `mat = (m ≠ 0)`, so the turnaround trigger
    `mat ∧ pos = (0,0)` needs `m = 0` — but then `mat = false`), then step the residual
    `< 3` micro-steps (`pos ≠ (0,0)`). The trigger is only at the very end `s = 3*k`. -/
theorem scatter1_mat_states {k : ℕ} (N : NTM k) (bb : Bool) (M : ℕ) (q' : N.Q)
    (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (rc ilm : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1
      (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0), rc, ilm, false, false))
    (hhead : (c1.work 0).head = blockStart k (M + 1))
    (hsent : ∀ cc, blockStart k (M + 1) ≤ cc → (c1.work 0).cells cc = Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) (hk : 1 ≤ k) :
    ∀ s, s < 3 * k →
      ∃ d, ((singleTapeSim N).trace s (fun _ => bb) c1).state = SimQ.scatter1 d := by
  have step_stays' : ∀ (cc : Cfg 1 (SimQ k N.Q)) (d : Scatter1Data k N.Q),
      cc.state = SimQ.scatter1 d →
      ¬ (d.2.2.2.2.2.2.2.2.2.2 = true ∧ d.2.2.2.2.2.2.1 = (0, 0)) →
      ∃ d', ((singleTapeSim N).trace 1 (fun _ => bb) cc).state = SimQ.scatter1 d'
        ∧ d'.2.2.2.2.2.2.1 = advanceSweep k d.2.2.2.2.2.2.1 :=
    fun cc d hcc hnt => scatter1_step_stays N bb d cc hcc hnt
  intro s hs
  obtain ⟨wt, htr, _, _, _, _⟩ := scatter1_mat_aux N bb M q' wact oWoD iD iSym oSym rc ilm
    c1 hst hhead hsent his hos (s / 3) (by omega)
  have hsplit : s = 3 * (s / 3) + s % 3 := by omega
  erw [hsplit, trace_const_add']
  set c0 := (singleTapeSim N).trace (3 * (s / 3)) (fun _ => bb) c1 with hc0
  have hc0st : c0.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym,
      (⟨if s / 3 < k then s / 3 else 0, by split <;> omega⟩, 0),
      (fun (j : Fin k) => if (j : ℕ) < s / 3 then false else rc j), ilm, false,
      if s / 3 = 0 then false else true) := by rw [htr]
  -- the boundary is non-trigger: either `m = 0` (then `mat = false`) or `m ≠ 0` (then
  -- `pos.1 = m ≠ 0`, so `pos ≠ (0,0)`).
  have hnt0 : ¬ ((if s / 3 = 0 then false else true) = true ∧
      (⟨if s / 3 < k then s / 3 else 0, by split <;> omega⟩, (0 : Fin 3)) =
        ((0 : Fin (k + 1)), (0 : Fin 3))) := by
    rintro ⟨hm, hp⟩
    have hsk : s / 3 < k := by omega
    have hval : (if s / 3 < k then s / 3 else 0) = 0 := by
      have := congrArg (fun p => (Prod.fst p).val) hp
      simpa using this
    rw [ite_eq_left hsk] at hval
    rw [ite_eq_left hval] at hm
    exact absurd hm (by simp)
  have hr3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases hr3 with hr | hr | hr <;> rw [hr]
  · exact ⟨_, hc0st⟩
  · obtain ⟨d', hd', _⟩ := step_stays' c0 _ hc0st hnt0
    exact ⟨d', hd'⟩
  · erw [show (2 : ℕ) = 1 + 1 from rfl, trace_const_add']
    obtain ⟨d', hd', hpos'⟩ := step_stays' c0 _ hc0st hnt0
    obtain ⟨d'', hd'', _⟩ := step_stays' _ d' hd'
      (by rw [hpos']; rintro ⟨_, h⟩; exact absurd h (by simp [advanceSweep]))
    exact ⟨d'', hd''⟩

/-- **SCATTER sweep-1 state discipline.** Throughout the entire sweep-1 phase
    (all `i < 3*k*(M+1) + 1` steps from its start), the simulator's state is never
    a `gather` state. Used to rule out spurious decision points inside the sweep. -/
theorem scatter1_sweep_states {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
        (fun j => decide ((c.work j).read = Γ.start)), (fun _ => false), false, false))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hinv : SimInvAt k (c1.work 0) c.work M) (hk : 1 ≤ k)
    (hr0 : ∀ j : Fin k, (c.work j).head = 0 → (wact j).2 = Dir3.right)
    (_hwb : ∀ (j : Fin k) (p : ℕ), M < p → (c.work j).cells p = Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∀ i, i < 3 * k * (M + 1) + 1 →
      ¬ ∃ d, ((singleTapeSim N).trace i (fun _ => bb) c1).state = SimQ.gather d := by
  -- It suffices to show the state at every interior step is `scatter1`.
  suffices H : ∀ i, i ≤ 3 * k * (M + 1) →
      ∃ d, ((singleTapeSim N).trace i (fun _ => bb) c1).state = SimQ.scatter1 d by
    intro i hi ⟨dg, hg⟩
    obtain ⟨d1, h1⟩ := H i (by omega)
    rw [h1] at hg
    exact absurd (Sum.inr.inj hg) (by simp [reduceCtorEq])
  -- bridge: the entry carry `decide(read = ▷)` is the block-1 carry `decide(head=0 ∧ right)`
  have hrc : (fun j => decide ((c.work j).read = Γ.start))
      = (fun (j : Fin k) => decide ((c.work j).head = 0 ∧ (wact j).2 = Dir3.right)) := by
    funext j
    rw [decide_eq_decide]
    have hreadhead : ((c.work j).read = Γ.start) ↔ ((c.work j).head = 0) := by
      rw [Tape.read]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · by_contra hne; exact hinv.noStart j _ (by omega) h
      · rw [h]; exact hinv.wfStart j
    rw [hreadhead]
    exact ⟨fun h => ⟨h, hr0 j h⟩, fun h => h.1⟩
  intro i hi
  rcases Nat.lt_or_ge i (3 * k * M + 1) with hib | hib
  · -- BLOCK-SWEEP range `i ≤ 3*k*M`
    have hib' : i ≤ 3 * k * M := by omega
    set B := i / (3 * k) with hBdef
    have hdm : 3 * k * B + i % (3 * k) = i := by rw [hBdef]; exact Nat.div_add_mod i (3 * k)
    have hge : 3 * k * B ≤ i := by omega
    have hmod : i % (3 * k) < 3 * k := Nat.mod_lt _ (by omega)
    have hBM : B ≤ M := by
      by_contra hBM
      have hMB : M + 1 ≤ B := Nat.lt_of_not_le hBM
      have : 3 * k * (M + 1) ≤ 3 * k * B := Nat.mul_le_mul_left _ hMB
      rw [Nat.mul_succ] at this; omega
    -- reach the block-`B+1` entry via `scatter1_sweep_aux`
    obtain ⟨wtB, hSB, hwhB, hmidB⟩ := scatter1_sweep_aux N bb c M q' wact oWoD iD iSym oSym
      (fun _ => false) c1 (by rw [hst, hrc]) hhead hinv his hos B hBM
    rcases Nat.eq_or_lt_of_le hBM with hBeq | hBlt
    · -- `B = M`: then `i = 3*k*M` exactly; the boundary config IS scatter1
      have hiB : i = 3 * k * B := by rw [← hBeq] at hib'; omega
      exact ⟨_, by rw [hiB, hSB]⟩
    · -- `B < M`: residual `s = i - 3*k*B ≤ 3*k` within block `B+1`
      have hs : i - 3 * k * B ≤ 3 * k := by omega
      have hB1M : B + 1 ≤ M := hBlt
      have hbridge : i = 3 * k * B + (i - 3 * k * B) := by omega
      erw [hbridge, trace_const_add']
      obtain ⟨d, hd⟩ := scatter1_block_states N bb c (B + 1) M (Nat.le_add_left 1 B) hB1M
        q' wact oWoD iD iSym oSym
        (fun j => decide ((c.work j).head = B ∧ (wact j).2 = Dir3.right))
        (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ B ∧ (wact j).2 = Dir3.left then
            true else (fun _ => false) j)
        (fun j => by simp only [Nat.add_sub_cancel])
        ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1) (by rw [hSB])
        (by rw [hSB]; exact hwhB) (by rw [hSB]; exact hmidB) (by rw [hSB]; exact his)
        (by rw [hSB]; exact hos) hk (i - 3 * k * B) hs
      exact ⟨d, hd⟩
  · -- MATERIALIZE range `3*k*M < i ≤ 3*k*(M+1)`
    -- reach the materialize entry `trace (3*k*M) c1`
    obtain ⟨wtS, hS, hwhS, hmidS⟩ := scatter1_sweep_aux N bb c M q' wact oWoD iD iSym oSym
      (fun _ => false) c1 (by rw [hst, hrc]) hhead hinv his hos M (le_refl M)
    set cE := (singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1 with hcE
    have hcEst : cE.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
        (fun j => decide ((c.work j).head = M ∧ (wact j).2 = Dir3.right)),
        (fun (j : Fin k) => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ M ∧ (wact j).2 = Dir3.left
            then true else (fun _ => false) j), false, false) := by rw [hS]
    have hcEhead : (cE.work 0).head = blockStart k (M + 1) := by rw [hS]; exact hwhS
    have hcEsent : ∀ cc, blockStart k (M + 1) ≤ cc → (cE.work 0).cells cc = Γ.blank := by
      rw [hS]; exact hmidS.sentinel
    have hcEis : cE.input.read ≠ Γ.start := by rw [hS]; exact his
    have hcEos : cE.output.read ≠ Γ.start := by rw [hS]; exact hos
    -- bridge `i = 3*k*M + s`, `s = i - 3*k*M ≤ 3*k`
    have hge : 3 * k * M ≤ i := by omega
    have hbridge : i = 3 * k * M + (i - 3 * k * M) := by omega
    have hs : i - 3 * k * M ≤ 3 * k := by
      rw [Nat.mul_succ] at hi; omega
    erw [hbridge, trace_const_add', ← hcE]
    rcases Nat.lt_or_ge (i - 3 * k * M) (3 * k) with hslt | hsge
    · -- interior of materialize: `scatter1_mat_states`
      exact scatter1_mat_states N bb M q' wact oWoD iD iSym oSym _ _ cE hcEst hcEhead hcEsent
        hcEis hcEos hk (i - 3 * k * M) hslt
    · -- endpoint `s = 3*k` (turnaround config, still `scatter1`): use `scatter1_mat_aux` at `m=k`
      have hseq : i - 3 * k * M = 3 * k := by omega
      rw [hseq, show 3 * k = 3 * k from rfl]
      obtain ⟨wt, hmt, _, _, _, _⟩ := scatter1_mat_aux N bb M q' wact oWoD iD iSym oSym _ _
        cE hcEst hcEhead hcEsent hcEis hcEos k (le_refl k)
      exact ⟨_, by rw [hmt]⟩

/-- **SCATTER sweep-1 — target (the crux, proof in progress).** From the
    REWIND-produced `scatter1` config (cell 1, `pos (0,0)`, `rightCarry` marking
    the position-0 heads, all else empty, encoding the old `c.work` at `M`), the
    sweep runs `3*k*(M+1) + 1` steps and lands in SCATTER sweep-2 with the work
    tape encoding the **intermediate** configuration (`scatterInterWork` — new
    symbols everywhere, right/stay heads relocated, left-movers parked at the old
    spot) materialized to `M+1`, recording the left-movers in `isLeftMover`. The
    work tape is existential (its exact head position is incidental — sweep-2
    consumes it). This is the research-grade core; the proof will decompose as
    `triple → block (rightCarry in→out) → M-block sweep → materialize → turnaround`. -/
theorem scatter1_sweep {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter1 (q', wact, oWoD, iD, iSym, oSym, (⟨0, by omega⟩, 0),
        (fun j => decide ((c.work j).read = Γ.start)), (fun _ => false), false, false))
    (hhead : (c1.work 0).head = blockStart k 1)
    (hinv : SimInvAt k (c1.work 0) c.work M) (hk : 1 ≤ k)
    (hr0 : ∀ j : Fin k, (c.work j).head = 0 → (wact j).2 = Dir3.right)
    (hwb : ∀ (j : Fin k) (p : ℕ), M < p → (c.work j).cells p = Γ.blank)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wfin : Fin 1 → Tape,
      (singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
            (fun t => decide ((wact t).2 = Dir3.left)), (fun _ => false)),
          input := c1.input, work := wfin, output := c1.output }
      ∧ SimInvAt k (wfin 0) (fun t => scatterInterWork (c.work t) (wact t)) (M + 1)
      ∧ (wfin 0).head = blockStart k (M + 2) - 1 := by
  -- `scatterInterWork.head = M+1` ⟺ the tape's head was at `M` moving right
  have hheadEq : ∀ j : Fin k,
      decide ((c.work j).head = M ∧ (wact j).2 = Dir3.right)
        = decide ((scatterInterWork (c.work j) (wact j)).head = M + 1) := by
    intro j
    rw [decide_eq_decide, scatterInterWork_head]
    have hle := hinv.heads_le j
    by_cases hr : (wact j).2 = Dir3.right
    · rw [ite_eq_left hr]
      exact ⟨fun h => by obtain ⟨h1, _⟩ := h; omega, fun h => ⟨by omega, hr⟩⟩
    · rw [ite_eq_right hr]
      exact ⟨fun h => absurd h.2 hr, fun h => absurd h (by omega)⟩
  -- bridge: the REWIND carry `initRC` is the block-1 carry
  have hrc : (fun j => decide ((c.work j).read = Γ.start))
      = (fun (j : Fin k) => decide ((c.work j).head = 0 ∧ (wact j).2 = Dir3.right)) := by
    funext j
    rw [decide_eq_decide]
    have hreadhead : ((c.work j).read = Γ.start) ↔ ((c.work j).head = 0) := by
      rw [Tape.read]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · by_contra hne; exact hinv.noStart j _ (by omega) h
      · rw [h]; exact hinv.wfStart j
    rw [hreadhead]
    exact ⟨fun h => ⟨h, hr0 j h⟩, fun h => h.1⟩
  -- Phase 1: sweep the M old blocks
  obtain ⟨wtS, hS, hwhS, hmidS⟩ := scatter1_sweep_aux N bb c M q' wact oWoD iD iSym oSym
    (fun _ => false) c1 (by rw [hst, hrc]) hhead hinv his hos M (le_refl M)
  -- Phase 2: materialize block M+1
  have hcwS : ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1).work 0 = wtS := by rw [hS]
  have hSin : ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1).input = c1.input := by rw [hS]
  have hSout : ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1).output = c1.output := by
    rw [hS]
  obtain ⟨wtMat, hMat, hwhMat, hpres, hmat, hblank⟩ := scatter1_mat_aux N bb M q' wact oWoD iD
    iSym oSym
    (fun j => decide ((c.work j).head = M ∧ (wact j).2 = Dir3.right))
    (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ M ∧ (wact j).2 = Dir3.left then
        true else (fun _ => false) j)
    ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1) (by rw [hS])
    (by rw [hcwS]; exact hwhS) (by rw [hcwS]; exact hmidS.sentinel)
    (by rw [hSin]; exact his) (by rw [hSout]; exact hos) k (le_refl k)
  -- Phase 3: turn around into SCATTER sweep-2
  have hcwMat : ((singleTapeSim N).trace (3 * k) (fun _ => bb)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1)).work 0 = wtMat := by rw [hMat]
  have hbs : blockStart k (M + 1) + 3 * k = blockStart k (M + 2) := by
    rw [show (M : ℕ) + 2 = (M + 1) + 1 from rfl, blockStart_succ k (M + 1) (by omega), blockWidth]
  have hmatHead : wtMat.head = blockStart k (M + 2) := by rw [hwhMat]; exact hbs
  have hmatBlank : wtMat.cells wtMat.head = Γ.blank := by
    rw [hmatHead]; exact hblank _ (by omega)
  have hTurn := scatter1_turnaround N bb q' wact oWoD iD iSym oSym
    (fun j => if (j : ℕ) < k then false else
      decide ((c.work j).head = M ∧ (wact j).2 = Dir3.right))
    (fun j => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ M ∧ (wact j).2 = Dir3.left then
        true else (fun _ => false) j) false
    ((singleTapeSim N).trace (3 * k) (fun _ => bb)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1))
    (by rw [hMat]; simp only [ite_eq_right (show ¬ k < k from Nat.lt_irrefl k),
        ite_eq_right (show ¬ k = 0 from by omega), Fin.mk_zero])
    (by rw [hcwMat]; exact hmatBlank)
  have hMatin : ((singleTapeSim N).trace (3 * k) (fun _ => bb)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1)).input = c1.input := by
    rw [hMat]; exact hSin
  have hMatout : ((singleTapeSim N).trace (3 * k) (fun _ => bb)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1)).output = c1.output := by
    rw [hMat]; exact hSout
  refine ⟨fun i => (((singleTapeSim N).trace (3 * k) (fun _ => bb)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1)).work i).writeAndMove
      Γw.blank.toΓ Dir3.left, ?_, ?_, ?_⟩
  · erw [show 3 * k * (M + 1) + 1 = 3 * k * M + (3 * k + 1) from by rw [Nat.mul_succ]; omega,
      trace_const_add', trace_const_add', hTurn, hMatin, hMatout]
    refine (Cfg.mk.injEq ..).mpr ⟨?_, tape_idle_stay c1.input his, rfl,
      tape_idle_writeMove c1.output hos⟩
    rw [show (fun (j : Fin k) => if 1 ≤ (c.work j).head ∧ (c.work j).head ≤ M ∧
            (wact j).2 = Dir3.left then true else (fun _ => false) j)
        = (fun t => decide ((wact t).2 = Dir3.left)) from by
      funext j
      by_cases hL : (wact j).2 = Dir3.left
      · have h1 : 1 ≤ (c.work j).head := by
          rcases Nat.eq_zero_or_pos (c.work j).head with h0 | hp
          · have hrr := hr0 j h0; rw [hL] at hrr; exact absurd hrr (by decide)
          · exact hp
        rw [ite_eq_left ⟨h1, hinv.heads_le j, hL⟩]; simp [hL]
      · rw [ite_eq_right (fun h => hL h.2.2)]; simp [hL]]
  · -- SimInvAt (M+1) for the intermediate config
    have hhead0 : ¬ wtMat.head = 0 := by rw [hmatHead]; have := one_le_blockStart k (M + 2); omega
    have hfc : ((((singleTapeSim N).trace (3 * k) (fun _ => bb)
        ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1)).work 0).writeAndMove
          Γw.blank.toΓ Dir3.left).cells = wtMat.cells := by
      rw [hcwMat]
      show (wtMat.write Γw.blank.toΓ).cells = wtMat.cells
      unfold Tape.write
      rw [ite_eq_right hhead0]
      show Function.update wtMat.cells wtMat.head Γw.blank.toΓ = wtMat.cells
      rw [show (Γw.blank.toΓ : Γ) = wtMat.cells wtMat.head
            from hmatBlank.symm, Function.update_eq_self]
    -- below block M+1, the materialized tape equals the swept tape (blocks [1,M] + cell 0)
    have hbelow : ∀ cc, cc < blockStart k (M + 1) → wtMat.cells cc = wtS.cells cc := fun cc h => by
      rw [hpres cc h, hcwS]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- cell0
      rw [congrFun hfc 0, hbelow 0 (by have := one_le_blockStart k (M + 1); omega)]
      exact hmidS.cell0
    · -- wfStart
      exact fun j => (scatterInterWork_cells_zero (c.work j) (wact j)).trans (hinv.wfStart j)
    · -- noStart
      exact fun j p hp =>
        scatterInterWork_cells_ne_start (c.work j) (wact j) hp (hinv.noStart j p hp)
    · -- heads_le
      exact fun j => scatterInterWork_head_le (c.work j) (wact j) (hinv.heads_le j)
    · -- headBit
      intro p hp1 hpM1 j
      rw [congrFun hfc (headBitCell k p j)]
      rcases Nat.lt_or_ge p (M + 1) with hlt | hge
      · rw [hbelow _ (by
          have := headBitCell_add_three_le_blockStart_succ k p j hp1
          have := blockStart_le k (show p + 1 ≤ M + 1 by omega)
          simp only [headBitCell] at *; omega)]
        exact (hmidS.donePart p hp1 hlt j).1
      · obtain rfl : p = M + 1 := by omega
        rw [(hmat j j.isLt).1]; simp only [hheadEq j, decide_eq_true_eq]
    · -- sym
      intro p hp1 hpM1 j
      rw [congrFun hfc (symCell k p j), congrFun hfc (symCell k p j + 1)]
      rcases Nat.lt_or_ge p (M + 1) with hlt | hge
      · rw [hbelow _ (by
            have := headBitCell_add_three_le_blockStart_succ k p j hp1
            have := blockStart_le k (show p + 1 ≤ M + 1 by omega)
            simp only [headBitCell, symCell] at *; omega),
          hbelow _ (by
            have := headBitCell_add_three_le_blockStart_succ k p j hp1
            have := blockStart_le k (show p + 1 ≤ M + 1 by omega)
            simp only [headBitCell, symCell] at *; omega)]
        exact hmidS.donePart p hp1 hlt j |>.2
      · obtain rfl : p = M + 1 := by omega
        have hcb : (scatterInterWork (c.work j) (wact j)).cells (M + 1)
            = (c.work j).cells (M + 1) :=
          scatterInterWork_cells_of_ne (c.work j) (wact j)
            (show (M + 1 : ℕ) ≠ (c.work j).head by have := hinv.heads_le j; omega)
        rw [(hmat j j.isLt).2.1, (hmat j j.isLt).2.2, hcb,
          show ((c.work j).cells (M + 1)) = Γ.blank from hwb j (M + 1) (by omega)]
        exact ⟨rfl, rfl⟩
    · -- sentinel
      intro cc hcc
      rw [congrFun hfc cc]
      exact hblank cc (by rw [← hbs] at hcc; omega)
  · -- head: the turn-around's left move lands at `blockStart (M+2) - 1`
    show ((((singleTapeSim N).trace (3 * k) (fun _ => bb)
        ((singleTapeSim N).trace (3 * k * M) (fun _ => bb) c1)).work 0).writeAndMove
          Γw.blank.toΓ Dir3.left).head = blockStart k (M + 2) - 1
    rw [hcwMat, work_write_left wtMat Γw.blank.toΓ
        (by rw [hmatHead]; have := one_le_blockStart k (M + 2); omega)]
    show wtMat.head - 1 = blockStart k (M + 2) - 1
    rw [hmatHead]

/-- One **scatter sweep-2** step (`trace 1`): from a `scatter2 d` config, the result is
    the configuration built from `scatter2Step`'s output. Basis of the SCATTER sweep-2
    correctness (the leftward phase that deposits the recorded left-movers). -/
theorem scatter2_trace1 {k : ℕ} (N : NTM k) (d : Scatter2Data k N.Q) (b : Bool)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter2 d) :
    (singleTapeSim N).trace 1 (fun _ => b) c1 =
      (let r := scatter2Step d c1.input.read ((c1.work 0).read) c1.output.read
       { state := r.1, input := c1.input.move r.2.2.2.1,
         work := fun i => (c1.work i).writeAndMove (r.2.1 i) (r.2.2.2.2.1 i),
         output := c1.output.writeAndMove r.2.2.1 r.2.2.2.2.2 } : Cfg 1 (SimQ k N.Q)) := by
  simp only [hst, singleTapeSim, simDelta, SimQ.scatter2, SimQ.halt, Sum.inr.injEq,
    reduceCtorEq, ↓reduceIte, NTM.trace]

/-- **SCATTER sweep-2 → COMMIT turn-around** (`trace 1`): reading `▷` at cell 0 ends the
    leftward sweep, hands the deferred output write/move to COMMIT, and steps the work
    head right to cell 1. -/
theorem scatter2_start {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (pos : SweepPos k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2 (q', oWoD, iD, iSym, oSym, pos, isLeftMover, leftCarry))
    (hstart : (c1.work 0).read = Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.commit (q', oWoD.1, oWoD.2, iD, iSym, oSym),
        input := c1.input,
        work := fun i => (c1.work i).writeAndMove Γw.blank.toΓ Dir3.right,
        output := c1.output } := by
  rw [scatter2_trace1 N (q', oWoD, iD, iSym, oSym, pos, isLeftMover, leftCarry) bb c1 hst]
  simp only [scatter2Step, hstart, ↓reduceIte, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]; rfl

/-- A SCATTER sweep-2 **symbol** step (slot `1` or `2`, non-`▷`): the leftward sweep
    only touches head-bit cells, so a symbol cell is read back unchanged and the head
    retreats one cell. -/
theorem scatter2_sym {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (s : Fin 3) (hs : s ≠ 0)
    (isLeftMover leftCarry : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, s), isLeftMover, leftCarry))
    (hns : (c1.work 0).read ≠ Γ.start)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, s),
          isLeftMover, leftCarry),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head - 1 },
        output := c1.output } := by
  rw [scatter2_trace1 N (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, s), isLeftMover, leftCarry)
      bb c1 hst]
  simp only [scatter2Step, hns, ↓reduceIte, hs, tape_idle_stay c1.input his,
    tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_rewind_step (c1.work 0) hns

/-- A SCATTER sweep-2 **clear** step (slot `0`, head-bit `one`, this tape is a recorded
    left-mover): clear the bit here (`zero`) and set `leftCarry` so the bit is re-deposited
    one block to the left; the head retreats. -/
theorem scatter2_clear_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), isLeftMover, leftCarry))
    (hone : (c1.work 0).read = Γ.one) (hlm : isLeftMover ⟨t, ht⟩ = true) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, 0),
          isLeftMover, Function.update leftCarry ⟨t, ht⟩ true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head - 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.zero.toΓ⟩,
        output := c1.output } := by
  rw [scatter2_trace1 N (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), isLeftMover, leftCarry)
      bb c1 hst]
  simp only [scatter2Step, hone, ↓reduceIte, hlm, dite_eq_left ht, and_self,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_left (c1.work 0) Γw.zero.toΓ hh

/-- A SCATTER sweep-2 **deposit** step (slot `0`, incoming `leftCarry`, not itself a
    left-mover to clear): deposit the head-bit here (`one`), clearing both this tape's
    `isLeftMover` mark and the carry; the head retreats. The left-mover lands one block left. -/
theorem scatter2_deposit_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), isLeftMover, leftCarry))
    (hns : (c1.work 0).read ≠ Γ.start)
    (hnc : ¬((c1.work 0).read = Γ.one ∧ isLeftMover ⟨t, ht⟩ = true))
    (hlc : leftCarry ⟨t, ht⟩ = true) (hh : 1 ≤ (c1.work 0).head)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, 0),
          Function.update isLeftMover ⟨t, ht⟩ false, Function.update leftCarry ⟨t, ht⟩ false),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head - 1,
          Function.update (c1.work 0).cells (c1.work 0).head Γw.one.toΓ⟩,
        output := c1.output } := by
  rw [scatter2_trace1 N (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), isLeftMover, leftCarry)
      bb c1 hst]
  simp only [scatter2Step, hns, ↓reduceIte, hnc, hlc, dite_eq_left ht,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_write_left (c1.work 0) Γw.one.toΓ hh

/-- A SCATTER sweep-2 **keep** step (slot `0`, neither a left-mover to clear nor an
    incoming carry): the head-bit is read back unchanged and the head retreats. -/
theorem scatter2_keep_slot0 {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), isLeftMover, leftCarry))
    (hns : (c1.work 0).read ≠ Γ.start)
    (hnc : ¬((c1.work 0).read = Γ.one ∧ isLeftMover ⟨t, ht⟩ = true))
    (hnl : leftCarry ⟨t, ht⟩ ≠ true)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 1 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, 0),
          isLeftMover, leftCarry),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head - 1 },
        output := c1.output } := by
  rw [scatter2_trace1 N (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 0), isLeftMover, leftCarry)
      bb c1 hst]
  simp only [scatter2Step, hns, ↓reduceIte, hnc, hnl, dite_eq_left ht,
    tape_idle_stay c1.input his, tape_idle_writeMove c1.output hos]
  congr 1
  funext x
  obtain rfl : x = 0 := Subsingleton.elim x 0
  exact work_rewind_step (c1.work 0) hns

/-- **SCATTER sweep-2 clear triple** (`trace 3`): three leftward steps over a tape whose
    head-bit (slot 0) is `one` and which is a recorded left-mover — two symbol cells read
    back unchanged, then the head-bit cleared (`zero`) with `leftCarry` set. Head retreats 3. -/
theorem scatter2_clear_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 2), isLeftMover, leftCarry))
    (hh : 3 ≤ (c1.work 0).head)
    (hns2 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.start)
    (hns1 : (c1.work 0).cells ((c1.work 0).head - 1) ≠ Γ.start)
    (hone : (c1.work 0).cells ((c1.work 0).head - 2) = Γ.one)
    (hlm : isLeftMover ⟨t, ht⟩ = true)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, 0),
          isLeftMover, Function.update leftCarry ⟨t, ht⟩ true),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head - 3,
          Function.update (c1.work 0).cells ((c1.work 0).head - 2) Γw.zero.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter2_sym N bb q' oWoD iD iSym oSym t ht 2 (by decide) isLeftMover leftCarry c1 hst
    (by rw [Tape.read]; exact hns2) his hos
  have e1 := scatter2_sym N bb q' oWoD iD iSym oSym t ht 1 (by decide) isLeftMover leftCarry
    ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0]; simp only [retreatSweep, Fin.reduceEq, Fin.reduceSub, ↓reduceIte])
    (by rw [e0]; show (c1.work 0).cells ((c1.work 0).head - 1) ≠ Γ.start; exact hns1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter2_clear_slot0 N bb q' oWoD iD iSym oSym t ht isLeftMover leftCarry
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [retreatSweep, Fin.reduceEq, Fin.reduceSub, ↓reduceIte])
    (by rw [e1, e0]; show (c1.work 0).cells ((c1.work 0).head - 1 - 1) = Γ.one;
        rw [show (c1.work 0).head - 1 - 1 = (c1.work 0).head - 2 from by omega]; exact hone)
    hlm (by rw [e1, e0]; show 1 ≤ (c1.work 0).head - 1 - 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  rfl

/-- **SCATTER sweep-2 deposit triple** (`trace 3`): three leftward steps over a tape with
    an incoming `leftCarry` (and not itself a clear) — two symbol cells unchanged, then the
    head-bit deposited (`one`), clearing `isLeftMover` and the carry. Head retreats 3. -/
theorem scatter2_deposit_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 2), isLeftMover, leftCarry))
    (hh : 3 ≤ (c1.work 0).head)
    (hns2 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.start)
    (hns1 : (c1.work 0).cells ((c1.work 0).head - 1) ≠ Γ.start)
    (hns0 : (c1.work 0).cells ((c1.work 0).head - 2) ≠ Γ.start)
    (hnc : ¬((c1.work 0).cells ((c1.work 0).head - 2) = Γ.one ∧ isLeftMover ⟨t, ht⟩ = true))
    (hlc : leftCarry ⟨t, ht⟩ = true)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, 0),
          Function.update isLeftMover ⟨t, ht⟩ false, Function.update leftCarry ⟨t, ht⟩ false),
        input := c1.input,
        work := fun _ => ⟨(c1.work 0).head - 3,
          Function.update (c1.work 0).cells ((c1.work 0).head - 2) Γw.one.toΓ⟩,
        output := c1.output } := by
  have e0 := scatter2_sym N bb q' oWoD iD iSym oSym t ht 2 (by decide) isLeftMover leftCarry c1 hst
    (by rw [Tape.read]; exact hns2) his hos
  have e1 := scatter2_sym N bb q' oWoD iD iSym oSym t ht 1 (by decide) isLeftMover leftCarry
    ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0]; simp only [retreatSweep, Fin.reduceEq, Fin.reduceSub, ↓reduceIte])
    (by rw [e0]; show (c1.work 0).cells ((c1.work 0).head - 1) ≠ Γ.start; exact hns1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter2_deposit_slot0 N bb q' oWoD iD iSym oSym t ht isLeftMover leftCarry
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [retreatSweep, Fin.reduceEq, Fin.reduceSub, ↓reduceIte])
    (by rw [e1, e0]; show (c1.work 0).cells ((c1.work 0).head - 1 - 1) ≠ Γ.start;
        rw [show (c1.work 0).head - 1 - 1 = (c1.work 0).head - 2 from by omega]; exact hns0)
    (by rw [e1, e0]; show ¬((c1.work 0).cells ((c1.work 0).head - 1 - 1) = Γ.one ∧
          isLeftMover ⟨t, ht⟩ = true);
        rw [show (c1.work 0).head - 1 - 1 = (c1.work 0).head - 2 from by omega]; exact hnc)
    hlc (by rw [e1, e0]; show 1 ≤ (c1.work 0).head - 1 - 1; omega)
    (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  rfl

/-- **SCATTER sweep-2 keep triple** (`trace 3`): three leftward steps over a tape that is
    neither a left-mover to clear nor a carry to deposit — all three cells read back
    unchanged, head retreats 3. -/
theorem scatter2_keep_triple {k : ℕ} (N : NTM k) (bb : Bool) (q' : N.Q) (oWoD : Γw × Dir3)
    (iD : Dir3) (iSym oSym : Γ) (t : ℕ) (ht : t < k) (isLeftMover leftCarry : Fin k → Bool)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨t, by omega⟩, 2), isLeftMover, leftCarry))
    (hh : 2 ≤ (c1.work 0).head)
    (hns2 : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.start)
    (hns1 : (c1.work 0).cells ((c1.work 0).head - 1) ≠ Γ.start)
    (hns0 : (c1.work 0).cells ((c1.work 0).head - 2) ≠ Γ.start)
    (hnc : ¬((c1.work 0).cells ((c1.work 0).head - 2) = Γ.one ∧ isLeftMover ⟨t, ht⟩ = true))
    (hnl : leftCarry ⟨t, ht⟩ ≠ true)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    (singleTapeSim N).trace 3 (fun _ => bb) c1 =
      { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, retreatSweep k (⟨t, by omega⟩, 0),
          isLeftMover, leftCarry),
        input := c1.input,
        work := fun _ => { c1.work 0 with head := (c1.work 0).head - 3 },
        output := c1.output } := by
  have e0 := scatter2_sym N bb q' oWoD iD iSym oSym t ht 2 (by decide) isLeftMover leftCarry c1 hst
    (by rw [Tape.read]; exact hns2) his hos
  have e1 := scatter2_sym N bb q' oWoD iD iSym oSym t ht 1 (by decide) isLeftMover leftCarry
    ((singleTapeSim N).trace 1 (fun _ => bb) c1)
    (by rw [e0]; simp only [retreatSweep, Fin.reduceEq, Fin.reduceSub, ↓reduceIte])
    (by rw [e0]; show (c1.work 0).cells ((c1.work 0).head - 1) ≠ Γ.start; exact hns1)
    (by rw [e0]; exact his) (by rw [e0]; exact hos)
  have e2 := scatter2_keep_slot0 N bb q' oWoD iD iSym oSym t ht isLeftMover leftCarry
    ((singleTapeSim N).trace 1 (fun _ => bb) ((singleTapeSim N).trace 1 (fun _ => bb) c1))
    (by rw [e1]; simp only [retreatSweep, Fin.reduceEq, Fin.reduceSub, ↓reduceIte])
    (by rw [e1, e0]; show (c1.work 0).cells ((c1.work 0).head - 1 - 1) ≠ Γ.start;
        rw [show (c1.work 0).head - 1 - 1 = (c1.work 0).head - 2 from by omega]; exact hns0)
    (by rw [e1, e0]; show ¬((c1.work 0).cells ((c1.work 0).head - 1 - 1) = Γ.one ∧
          isLeftMover ⟨t, ht⟩ = true);
        rw [show (c1.work 0).head - 1 - 1 = (c1.work 0).head - 2 from by omega]; exact hnc)
    hnl (by rw [e1, e0]; exact his) (by rw [e1, e0]; exact hos)
  rw [trace_three', e2, e1, e0]
  rfl

/-- **SCATTER sweep-2 per-tape — keep.** Tape `k-1-m` of block `p` is neither a
    left-mover to clear at `p` (`¬(scatterInterWork.head = p ∧ isLeftMover)`) nor a
    deposit target (`leftCarry ≠ true`): its head-bit is read back unchanged. The
    intermediate and final head-bits at `p` agree (`hfin`), so this already IS the
    final encoding. Advances `Scatter2BlockInv … p m → … p (m+1)`. -/
theorem scatter2_tape_keep {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (p M : ℕ)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (isLeftMover leftCarry : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨k - 1 - m, by omega⟩, 2), isLeftMover, leftCarry))
    (hhead : (c1.work 0).head = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2)
    (hbm : Scatter2BlockInv (c1.work 0) c.work wact M p m)
    (hnc : ¬((scatterInterWork (c.work ⟨k - 1 - m, by omega⟩) (wact ⟨k - 1 - m, by omega⟩)).head = p
        ∧ isLeftMover ⟨k - 1 - m, by omega⟩ = true))
    (hnl : leftCarry ⟨k - 1 - m, by omega⟩ ≠ true)
    (hfin : ((scatterFinalWork (c.work ⟨k - 1 - m, by omega⟩)
          (wact ⟨k - 1 - m, by omega⟩)).head = p)
        ↔ ((scatterInterWork (c.work ⟨k - 1 - m, by omega⟩) (wact ⟨k - 1 - m, by omega⟩)).head = p))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym,
            retreatSweep k (⟨k - 1 - m, by omega⟩, 0), isLeftMover, leftCarry),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1
      ∧ Scatter2BlockInv wt c.work wact M p (m + 1) := by
  have hot := hbm.oldTape ⟨k - 1 - m, by omega⟩ (by show k - 1 - m < k - m; omega)
  have hsym1 : symCell k p ⟨k - 1 - m, by omega⟩ = headBitCell k p ⟨k - 1 - m, by omega⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k p ⟨k - 1 - m, by omega⟩ + 1
      = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 := by
    simp only [symCell, headBitCell]
  have heq2 : (c1.work 0).head - 2 = headBitCell k p ⟨k - 1 - m, by omega⟩ := by rw [hhead]; omega
  have htriple := scatter2_keep_triple N bb q' oWoD iD iSym oSym (k - 1 - m) (by omega)
    isLeftMover leftCarry c1 hst
    (by rw [hhead]; omega)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    (by rw [hhead, show headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 - 1
          = headBitCell k p ⟨k - 1 - m, by omega⟩ + 1 from by omega, ← hsym1, hot.2.1]
        exact (encSymΓ_ne_start _).1)
    (by rw [heq2, hot.1]; split_ifs <;> decide)
    (by rw [heq2, hot.1]
        rintro ⟨h1, h2⟩
        refine hnc ⟨?_, h2⟩
        by_cases hb : (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩)
            (wact ⟨k - 1 - m, by omega⟩)).head = p
        · exact hb
        · rw [ite_eq_right hb] at h1; exact absurd h1 (by decide))
    hnl his hos
  refine ⟨{ c1.work 0 with head := (c1.work 0).head - 3 }, htriple, ?_, ?_⟩
  · show (c1.work 0).head - 3 = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1
    rw [hhead]; omega
  · apply scatter2_blockinv_step hp1 hpM hmk hbm
    · show (c1.work 0).cells (headBitCell k p ⟨k - 1 - m, by omega⟩) = _
      rw [hot.1]; exact (if_congr hfin rfl rfl).symm
    · intro cc _; rfl

/-- **SCATTER sweep-2 per-tape — clear.** Tape `k-1-m` of block `p` is a recorded
    left-mover whose intermediate head-bit sits at `p` (`hheadp`, `hlm`): clear the
    bit here (→ `zero`, since the left-mover's final head is `p-1 ≠ p`, `hfinne`) and
    set `leftCarry` so the bit re-deposits one block left. Advances
    `Scatter2BlockInv … p m → … p (m+1)`. -/
theorem scatter2_tape_clear {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (p M : ℕ)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (isLeftMover leftCarry : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨k - 1 - m, by omega⟩, 2), isLeftMover, leftCarry))
    (hhead : (c1.work 0).head = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2)
    (hbm : Scatter2BlockInv (c1.work 0) c.work wact M p m)
    (hheadp : (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩)
        (wact ⟨k - 1 - m, by omega⟩)).head = p)
    (hlm : isLeftMover ⟨k - 1 - m, by omega⟩ = true)
    (hfinne : (scatterFinalWork (c.work ⟨k - 1 - m, by omega⟩)
        (wact ⟨k - 1 - m, by omega⟩)).head ≠ p)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym,
            retreatSweep k (⟨k - 1 - m, by omega⟩, 0), isLeftMover,
            Function.update leftCarry ⟨k - 1 - m, by omega⟩ true),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1
      ∧ Scatter2BlockInv wt c.work wact M p (m + 1) := by
  have hot := hbm.oldTape ⟨k - 1 - m, by omega⟩ (by show k - 1 - m < k - m; omega)
  have hsym1 : symCell k p ⟨k - 1 - m, by omega⟩ = headBitCell k p ⟨k - 1 - m, by omega⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k p ⟨k - 1 - m, by omega⟩ + 1
      = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 := by
    simp only [symCell, headBitCell]
  have heq2 : (c1.work 0).head - 2 = headBitCell k p ⟨k - 1 - m, by omega⟩ := by rw [hhead]; omega
  have htriple := scatter2_clear_triple N bb q' oWoD iD iSym oSym (k - 1 - m) (by omega)
    isLeftMover leftCarry c1 hst
    (by rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k p; omega)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    (by rw [hhead, show headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 - 1
          = headBitCell k p ⟨k - 1 - m, by omega⟩ + 1 from by omega, ← hsym1, hot.2.1]
        exact (encSymΓ_ne_start _).1)
    (by rw [heq2, hot.1, ite_eq_left hheadp])
    hlm his hos
  refine ⟨⟨(c1.work 0).head - 3,
      Function.update (c1.work 0).cells ((c1.work 0).head - 2) Γw.zero.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head - 3 = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1
    rw [hhead]; omega
  · apply scatter2_blockinv_step hp1 hpM hmk hbm
    · show Function.update (c1.work 0).cells ((c1.work 0).head - 2) Γw.zero.toΓ
        (headBitCell k p ⟨k - 1 - m, by omega⟩) = _
      rw [← heq2, Function.update_self, ite_eq_right hfinne]; rfl
    · intro cc hcc
      exact Function.update_of_ne (fun h => hcc (h.trans heq2)) _ _

/-- **SCATTER sweep-2 per-tape — deposit.** Tape `k-1-m` of block `p` has an
    incoming `leftCarry` (`hlc`, set when its left-mover bit was cleared at block
    `p+1`): its intermediate head-bit at `p` is `zero` (`hninter`), but its final head
    lands at `p` (`hfineq`), so deposit the bit here (→ `one`), clearing both this
    tape's `isLeftMover` mark and the carry. Advances `Scatter2BlockInv … p m → … p (m+1)`. -/
theorem scatter2_tape_deposit {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (p M : ℕ)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (m : ℕ) (hmk : m < k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (isLeftMover leftCarry : Fin k → Bool) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨k - 1 - m, by omega⟩, 2), isLeftMover, leftCarry))
    (hhead : (c1.work 0).head = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2)
    (hbm : Scatter2BlockInv (c1.work 0) c.work wact M p m)
    (hninter : (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩)
        (wact ⟨k - 1 - m, by omega⟩)).head ≠ p)
    (hlc : leftCarry ⟨k - 1 - m, by omega⟩ = true)
    (hfineq : (scatterFinalWork (c.work ⟨k - 1 - m, by omega⟩)
        (wact ⟨k - 1 - m, by omega⟩)).head = p)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace 3 (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym,
            retreatSweep k (⟨k - 1 - m, by omega⟩, 0),
            Function.update isLeftMover ⟨k - 1 - m, by omega⟩ false,
            Function.update leftCarry ⟨k - 1 - m, by omega⟩ false),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1
      ∧ Scatter2BlockInv wt c.work wact M p (m + 1) := by
  have hot := hbm.oldTape ⟨k - 1 - m, by omega⟩ (by show k - 1 - m < k - m; omega)
  have hsym1 : symCell k p ⟨k - 1 - m, by omega⟩ = headBitCell k p ⟨k - 1 - m, by omega⟩ + 1 := by
    simp only [symCell, headBitCell]
  have hsym2 : symCell k p ⟨k - 1 - m, by omega⟩ + 1
      = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 := by
    simp only [symCell, headBitCell]
  have heq2 : (c1.work 0).head - 2 = headBitCell k p ⟨k - 1 - m, by omega⟩ := by rw [hhead]; omega
  have htriple := scatter2_deposit_triple N bb q' oWoD iD iSym oSym (k - 1 - m) (by omega)
    isLeftMover leftCarry c1 hst
    (by rw [hhead]; simp only [headBitCell]; have := one_le_blockStart k p; omega)
    (by rw [hhead, ← hsym2, hot.2.2]; exact (encSymΓ_ne_start _).2)
    (by rw [hhead, show headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 - 1
          = headBitCell k p ⟨k - 1 - m, by omega⟩ + 1 from by omega, ← hsym1, hot.2.1]
        exact (encSymΓ_ne_start _).1)
    (by rw [heq2, hot.1]; split_ifs <;> decide)
    (by rw [heq2, hot.1, ite_eq_right hninter]; rintro ⟨h1, _⟩; exact absurd h1 (by decide))
    hlc his hos
  refine ⟨⟨(c1.work 0).head - 3,
      Function.update (c1.work 0).cells ((c1.work 0).head - 2) Γw.one.toΓ⟩, htriple, ?_, ?_⟩
  · show (c1.work 0).head - 3 = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1
    rw [hhead]; omega
  · apply scatter2_blockinv_step hp1 hpM hmk hbm
    · show Function.update (c1.work 0).cells ((c1.work 0).head - 2) Γw.one.toΓ
        (headBitCell k p ⟨k - 1 - m, by omega⟩) = _
      rw [← heq2, Function.update_self, ite_eq_left hfineq]; rfl
    · intro cc hcc
      exact Function.update_of_ne (fun h => hcc (h.trans heq2)) _ _

/-- **SCATTER sweep-2 one block (`trace (3*m)`).** Sweeping the top `m` tapes of block
    `p` (leftward, tapes `k-1` down to `k-m`) advances `Scatter2BlockInv … p 0 → … p m`,
    threading per-tape `leftCarry` (set by clears at `p`, the outgoing carry for block
    `p-1`) and `isLeftMover` (cleared on deposit). Dispatches `scatter2_tape_clear/
    deposit/keep` per tape from the pinned-down inputs `isLeftMover_in`/`leftCarry_in`.
    Mirrors `scatter1_block_aux` with `k-1-j < m` (descending) as the "processed" test. -/
private theorem scatter2_block_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (p M : ℕ)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (hk : 1 ≤ k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (isLeftMover_in leftCarry_in : Fin k → Bool)
    (hilm_in : ∀ j : Fin k,
      isLeftMover_in j = decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ p + 1))
    (hlc_in : ∀ j : Fin k,
      leftCarry_in j = decide ((c.work j).head = p + 1 ∧ (wact j).2 = Dir3.left))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2), isLeftMover_in, leftCarry_in))
    (hhead : (c1.work 0).head = headBitCell k p ⟨k - 1, by omega⟩ + 2)
    (hbm : Scatter2BlockInv (c1.work 0) c.work wact M p 0)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (m : ℕ) (hm : m ≤ k) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * m) (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym,
            (⟨if m < k then k - 1 - m else k - 1, by split <;> omega⟩, 2),
            (fun j => if k - 1 - (j : ℕ) < m ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
                false else isLeftMover_in j),
            (fun j => if k - 1 - (j : ℕ) < m then
                decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p) else leftCarry_in j)),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k p + 3 * (k - 1) + 2 - 3 * m
      ∧ Scatter2BlockInv wt c.work wact M p m := by
  induction m with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, hbm⟩
    · have h0 : (singleTapeSim N).trace (3 * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      simp only [Nat.not_lt_zero, false_and, ↓reduceIte] at hst ⊢
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, ?_, rfl⟩
      · split <;> rfl
      · funext x
        obtain rfl : x = 0 := Subsingleton.elim x 0
        rfl
    · simp only [Nat.mul_zero, Nat.sub_zero]; rw [hhead, headBitCell]
  | succ m ih =>
    obtain ⟨wtm, htm, hwhm, hbim⟩ := ih (by omega)
    have hmk : m < k := by omega
    set ILMm := (fun (j : Fin k) =>
        if k - 1 - (j : ℕ) < m ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
          false else isLeftMover_in j) with hILMm
    set LCm := (fun (j : Fin k) =>
        if k - 1 - (j : ℕ) < m then decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p)
          else leftCarry_in j) with hLCm
    have hjval : k - 1 - (↑(⟨k - 1 - m, by omega⟩ : Fin k) : ℕ) = m := by
      show k - 1 - (k - 1 - m) = m; omega
    -- structural step lemmas: the m+1 closed forms are single-slot updates of the m forms
    have hstep_lc : (fun (j : Fin k) => if k - 1 - (j : ℕ) < m + 1 then
          decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p) else leftCarry_in j)
        = Function.update LCm ⟨k - 1 - m, by omega⟩
            (decide ((wact ⟨k - 1 - m, by omega⟩).2 = Dir3.left
              ∧ (c.work ⟨k - 1 - m, by omega⟩).head = p)) := by
      funext j
      by_cases hj : j = ⟨k - 1 - m, by omega⟩
      · subst hj; rw [Function.update_self, ite_eq_left (by rw [hjval]; omega)]
      · rw [Function.update_of_ne hj, hLCm]
        have hjm : (j : ℕ) ≠ k - 1 - m := fun h => hj (Fin.ext h)
        have hjlt := j.isLt
        by_cases hlt : k - 1 - (j : ℕ) < m
        · simp only [ite_eq_left hlt, ite_eq_left (show k - 1 - (j : ℕ) < m + 1 by omega)]
        · simp only [ite_eq_right hlt, ite_eq_right (show ¬ k - 1 - (j : ℕ) < m + 1 by omega)]
    have hstep_ilm : (fun (j : Fin k) =>
          if k - 1 - (j : ℕ) < m + 1 ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
            false else isLeftMover_in j)
        = Function.update ILMm ⟨k - 1 - m, by omega⟩
            (if (wact ⟨k - 1 - m, by omega⟩).2 = Dir3.left
              ∧ (c.work ⟨k - 1 - m, by omega⟩).head = p + 1 then false
              else isLeftMover_in ⟨k - 1 - m, by omega⟩) := by
      funext j
      by_cases hj : j = ⟨k - 1 - m, by omega⟩
      · subst hj; rw [Function.update_self]; simp only [hjval, Nat.lt_succ_self, true_and]
      · rw [Function.update_of_ne hj, hILMm]
        have hjm : (j : ℕ) ≠ k - 1 - m := fun h => hj (Fin.ext h)
        have hjlt := j.isLt
        have hiff : (k - 1 - (j : ℕ) < m + 1 ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1)
            ↔ (k - 1 - (j : ℕ) < m ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1) :=
          ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
        simp only [hiff]
    have hLCm_at : LCm ⟨k - 1 - m, by omega⟩ = leftCarry_in ⟨k - 1 - m, by omega⟩ := by
      rw [hLCm]; simp only [hjval, lt_irrefl, ite_false]
    have hILMm_at : ILMm ⟨k - 1 - m, by omega⟩ = isLeftMover_in ⟨k - 1 - m, by omega⟩ := by
      rw [hILMm]; simp only [hjval, lt_irrefl, false_and, ite_false]
    -- facts about the IH config cM = trace (3*m) c1
    have hcs : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).state
        = SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1 - m, by omega⟩, 2), ILMm, LCm) := by
      rw [htm]; simp only [ite_eq_left hmk]; rfl
    have hch : (((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0).head
        = headBitCell k p ⟨k - 1 - m, by omega⟩ + 2 := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm
            from by rw [htm], hwhm]
      simp only [headBitCell]; omega
    have hcbi : Scatter2BlockInv (((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0)
        c.work wact M p m := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).work 0 = wtm from by rw [htm]]
      exact hbim
    have hcis : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm]]
      exact his
    have hcos : ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output.read ≠ Γ.start := by
      rw [show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output
            from by rw [htm]]
      exact hos
    -- pos reconciliation: retreatSweep ↦ the m+1 closed-form tape index
    have hpos_eq : retreatSweep k (⟨k - 1 - m, by omega⟩, (0 : Fin 3))
        = ((⟨if m + 1 < k then k - 1 - (m + 1) else k - 1, by split <;> omega⟩ : Fin (k + 1)),
            (2 : Fin 3)) := by
      simp only [retreatSweep, ↓reduceIte]
      apply Prod.ext
      · apply Fin.ext; simp only; split <;> split <;> omega
      · rfl
    -- assembly closure (trace_const_add' + input/output reconciliation, done once)
    have key : ∀ (wt : Tape) (ilm' lc' : Fin k → Bool),
        (singleTapeSim N).trace 3 (fun _ => bb)
            ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1)
          = { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym,
                (⟨if m + 1 < k then k - 1 - (m + 1) else k - 1, by split <;> omega⟩, 2), ilm', lc'),
              input := ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input,
              work := fun _ => wt,
              output := ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output } →
        ilm' = (fun (j : Fin k) =>
            if k - 1 - (j : ℕ) < m + 1 ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
              false else isLeftMover_in j) →
        lc' = (fun (j : Fin k) => if k - 1 - (j : ℕ) < m + 1 then
            decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p) else leftCarry_in j) →
        wt.head = headBitCell k p ⟨k - 1 - m, by omega⟩ - 1 →
        Scatter2BlockInv wt c.work wact M p (m + 1) →
        ∃ wt' : Tape,
          (singleTapeSim N).trace (3 * (m + 1)) (fun _ => bb) c1 =
            { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym,
                (⟨if m + 1 < k then k - 1 - (m + 1) else k - 1, by split <;> omega⟩, 2),
                (fun j => if k - 1 - (j : ℕ) < m + 1 ∧ (wact j).2 = Dir3.left
                    ∧ (c.work j).head = p + 1 then false else isLeftMover_in j),
                (fun j => if k - 1 - (j : ℕ) < m + 1 then
                    decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p) else leftCarry_in j)),
              input := c1.input, work := fun _ => wt', output := c1.output }
          ∧ wt'.head = blockStart k p + 3 * (k - 1) + 2 - 3 * (m + 1)
          ∧ Scatter2BlockInv wt' c.work wact M p (m + 1) := by
      intro wt ilm' lc' htr hilm hlc hwh hbi
      refine ⟨wt, ?_, ?_, hbi⟩
      · erw [show 3 * (m + 1) = 3 * m + 3 from by omega, trace_const_add', htr, hilm, hlc,
          show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).input = c1.input from by rw [htm],
          show ((singleTapeSim N).trace (3 * m) (fun _ => bb) c1).output = c1.output
            from by rw [htm]]
      · rw [hwh]; simp only [headBitCell]; omega
    -- head facts for the tape currently processed (j = k-1-m)
    have hih : (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩) (wact ⟨k - 1 - m, by omega⟩)).head
        = if (wact ⟨k - 1 - m, by omega⟩).2 = Dir3.right then
            (c.work ⟨k - 1 - m, by omega⟩).head + 1
          else (c.work ⟨k - 1 - m, by omega⟩).head := scatterInterWork_head _ _
    have hfh : (scatterFinalWork (c.work ⟨k - 1 - m, by omega⟩) (wact ⟨k - 1 - m, by omega⟩)).head
        = if (wact ⟨k - 1 - m, by omega⟩).2 = Dir3.left then (c.work ⟨k - 1 - m, by omega⟩).head - 1
          else (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩)
              (wact ⟨k - 1 - m, by omega⟩)).head :=
      scatterFinalWork_head _ _
    -- dispatch on the action / head of tape k-1-m
    by_cases hleft : (wact ⟨k - 1 - m, by omega⟩).2 = Dir3.left
    · have hihl : (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩)
          (wact ⟨k - 1 - m, by omega⟩)).head
          = (c.work ⟨k - 1 - m, by omega⟩).head := by
        rw [hih, ite_eq_right (by rw [hleft]; decide)]
      have hfhl : (scatterFinalWork (c.work ⟨k - 1 - m, by omega⟩)
          (wact ⟨k - 1 - m, by omega⟩)).head
          = (c.work ⟨k - 1 - m, by omega⟩).head - 1 := by rw [hfh, ite_eq_left hleft]
      by_cases hcp : (c.work ⟨k - 1 - m, by omega⟩).head = p
      · -- clear
        obtain ⟨wt, htr, hwh, hbi⟩ := scatter2_tape_clear N bb c p M hp1 hpM m hmk
          q' wact oWoD iD iSym oSym ILMm LCm _ hcs hch hcbi
          (by rw [hihl]; exact hcp)
          (by rw [hILMm_at, hilm_in]; exact decide_eq_true ⟨hleft, by omega⟩)
          (by rw [hfhl]; omega) hcis hcos
        rw [hpos_eq] at htr
        refine key wt ILMm (Function.update LCm ⟨k - 1 - m, by omega⟩ true) htr ?_ ?_ hwh hbi
        · rw [hstep_ilm, ite_eq_right (by rintro ⟨_, h2⟩; omega), ← hILMm_at,
          Function.update_eq_self]
        · rw [hstep_lc, decide_eq_true ⟨hleft, hcp⟩]
      · by_cases hcp1 : (c.work ⟨k - 1 - m, by omega⟩).head = p + 1
        · -- deposit
          obtain ⟨wt, htr, hwh, hbi⟩ := scatter2_tape_deposit N bb c p M hp1 hpM m hmk
            q' wact oWoD iD iSym oSym ILMm LCm _ hcs hch hcbi
            (by rw [hihl]; omega)
            (by rw [hLCm_at, hlc_in]; exact decide_eq_true ⟨hcp1, hleft⟩)
            (by rw [hfhl]; omega) hcis hcos
          rw [hpos_eq] at htr
          refine key wt (Function.update ILMm ⟨k - 1 - m, by omega⟩ false)
            (Function.update LCm ⟨k - 1 - m, by omega⟩ false) htr ?_ ?_ hwh hbi
          · rw [hstep_ilm, ite_eq_left ⟨hleft, hcp1⟩]
          · rw [hstep_lc, decide_eq_false (by rintro ⟨_, h2⟩; omega)]
        · -- keep (left-mover, head not p or p+1)
          obtain ⟨wt, htr, hwh, hbi⟩ := scatter2_tape_keep N bb c p M hp1 hpM m hmk
            q' wact oWoD iD iSym oSym ILMm LCm _ hcs hch hcbi
            (by rw [hihl]; rintro ⟨h1, _⟩; exact hcp h1)
            (by rw [hLCm_at, hlc_in]; simp only [ne_eq, decide_eq_true_eq]
                rintro ⟨h1, _⟩; exact hcp1 h1)
            (by rw [hihl, hfhl]; constructor <;> intro h <;> omega) hcis hcos
          rw [hpos_eq] at htr
          refine key wt ILMm LCm htr ?_ ?_ hwh hbi
          · rw [hstep_ilm, ite_eq_right (by rintro ⟨_, h3⟩; omega), ← hILMm_at,
            Function.update_eq_self]
          · rw [hstep_lc,
              show (decide ((wact ⟨k - 1 - m, by omega⟩).2 = Dir3.left
                  ∧ (c.work ⟨k - 1 - m, by omega⟩).head = p)) = LCm ⟨k - 1 - m, by omega⟩ from by
                rw [hLCm_at, hlc_in, decide_eq_false (fun h => hcp h.2),
                  decide_eq_false (fun h => hcp1 h.1)],
              Function.update_eq_self]
    · -- keep (not a left-mover: isLeftMover/leftCarry both false here)
      have hilmf : isLeftMover_in ⟨k - 1 - m, by omega⟩ = false := by
        rw [hilm_in]; exact decide_eq_false (by rintro ⟨h1, _⟩; exact hleft h1)
      have hlcf : leftCarry_in ⟨k - 1 - m, by omega⟩ = false := by
        rw [hlc_in]; exact decide_eq_false (by rintro ⟨_, h2⟩; exact hleft h2)
      have hfhnl : (scatterFinalWork (c.work ⟨k - 1 - m, by omega⟩)
          (wact ⟨k - 1 - m, by omega⟩)).head
          = (scatterInterWork (c.work ⟨k - 1 - m, by omega⟩)
              (wact ⟨k - 1 - m, by omega⟩)).head := by
        rw [hfh, ite_eq_right hleft]
      obtain ⟨wt, htr, hwh, hbi⟩ := scatter2_tape_keep N bb c p M hp1 hpM m hmk
        q' wact oWoD iD iSym oSym ILMm LCm _ hcs hch hcbi
        (by rw [hILMm_at, hilmf]; rintro ⟨_, h2⟩; exact absurd h2 (by decide))
        (by rw [hLCm_at, hlcf]; decide)
        (by rw [hfhnl]) hcis hcos
      rw [hpos_eq] at htr
      refine key wt ILMm LCm htr ?_ ?_ hwh hbi
      · rw [hstep_ilm, ite_eq_right (by rintro ⟨h2, _⟩; exact hleft h2), ← hILMm_at,
          Function.update_eq_self]
      · rw [hstep_lc,
          show (decide ((wact ⟨k - 1 - m, by omega⟩).2 = Dir3.left
              ∧ (c.work ⟨k - 1 - m, by omega⟩).head = p)) = LCm ⟨k - 1 - m, by omega⟩ from by
            rw [hLCm_at, hlcf]; exact decide_eq_false (fun h => hleft h.1),
          Function.update_eq_self]

/-- **SCATTER sweep-2 single block (`trace (3*k)`).** Processing one full block `p`
    (leftward) from the block-`(p+1)` boundary: after `3*k` steps the head sits at
    `blockStart k p - 1`, the `isLeftMover`/`leftCarry` flags are updated to their
    boundary-`p` forms, and the tape satisfies `Scatter2MidInv … p`. -/
theorem scatter2_block_step {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (p M : ℕ)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (hk : 1 ≤ k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (isLeftMover_in leftCarry_in : Fin k → Bool)
    (hilm_in : ∀ j : Fin k,
      isLeftMover_in j = decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ p + 1))
    (hlc_in : ∀ j : Fin k,
      leftCarry_in j = decide ((c.work j).head = p + 1 ∧ (wact j).2 = Dir3.left))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2), isLeftMover_in, leftCarry_in))
    (hhead : (c1.work 0).head = headBitCell k p ⟨k - 1, by omega⟩ + 2)
    (hmid : Scatter2MidInv (c1.work 0) c.work wact M (p + 1))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * k) (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
            (fun j => if (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
                false else isLeftMover_in j),
            (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p))),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k p - 1
      ∧ Scatter2MidInv wt c.work wact M p := by
  obtain ⟨wt, htr, hwh, hbi⟩ := scatter2_block_aux N bb c p M hp1 hpM hk q' wact oWoD iD iSym oSym
    isLeftMover_in leftCarry_in hilm_in hlc_in c1 hst hhead
    (Scatter2BlockInv.ofMid hp1 hmid) his hos k (le_refl k)
  refine ⟨wt, ?_, ?_, Scatter2BlockInv.toMidPred hbi⟩
  · rw [htr]
    have hilm_k : (fun (j : Fin k) =>
          if k - 1 - (j : ℕ) < k ∧ (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
            false else isLeftMover_in j)
        = (fun j => if (wact j).2 = Dir3.left ∧ (c.work j).head = p + 1 then
            false else isLeftMover_in j) := by
      funext j
      simp only [show k - 1 - (j : ℕ) < k from by have := j.isLt; omega, true_and]
    have hlc_k : (fun (j : Fin k) => if k - 1 - (j : ℕ) < k then
          decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p) else leftCarry_in j)
        = (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head = p)) := by
      funext j; rw [ite_eq_left (by have := j.isLt; omega)]
    rw [hilm_k, hlc_k]
    simp only [lt_irrefl, ite_false]
  · rw [hwh]; omega

/-- **SCATTER sweep-2 full block sweep (`trace (3*k*B)`).** Sweeping the first `B ≤ M+1`
    blocks (leftward, from block `M+1` down to `M+2-B`) starting from the sweep-1 output
    `Scatter2MidInv … (M+2)`: after `B` blocks the head is at `blockStart k (M+2-B) - 1`,
    the sweep is back at tape `k-1` slot `2`, the carry/`isLeftMover` track the
    boundary-`(M+2-B)` forms, and the tape is `Scatter2MidInv … (M+2-B)`. Proved by
    induction on `B`, each step one `scatter2_block_step` at block `M+1-B`. -/
private theorem scatter2_sweep_aux {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (hk : 1 ≤ k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
        (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2)),
        (fun j => decide ((c.work j).head = M + 2 ∧ (wact j).2 = Dir3.left))))
    (hhead : (c1.work 0).head = blockStart k (M + 2) - 1)
    (hmid : Scatter2MidInv (c1.work 0) c.work wact M (M + 2))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start)
    (B : ℕ) (hB : B ≤ M + 1) :
    ∃ wt : Tape,
      (singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1 =
        { state := SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
            (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2 - B)),
            (fun j => decide ((c.work j).head = M + 2 - B ∧ (wact j).2 = Dir3.left))),
          input := c1.input, work := fun _ => wt, output := c1.output }
      ∧ wt.head = blockStart k (M + 2 - B) - 1
      ∧ Scatter2MidInv wt c.work wact M (M + 2 - B) := by
  induction B with
  | zero =>
    refine ⟨c1.work 0, ?_, ?_, ?_⟩
    · have h0 : (singleTapeSim N).trace (3 * k * 0) (fun _ => bb) c1 = c1 := by
        simp only [Nat.mul_zero]; rfl
      rw [h0]
      obtain ⟨cst, cin, cwk, cout⟩ := c1
      simp only [Nat.sub_zero] at hst ⊢
      subst hst
      refine (Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, rfl⟩
      funext x
      obtain rfl : x = 0 := Subsingleton.elim x 0
      rfl
    · simp only [Nat.sub_zero]; exact hhead
    · simp only [Nat.sub_zero]; exact hmid
  | succ B ih =>
    obtain ⟨wtB, htB, hwhB, hmidB⟩ := ih (by omega)
    have hci : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).input = c1.input := by
      rw [htB]
    have hco : ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).output = c1.output := by
      rw [htB]
    have hsucc : M + 2 - B = (M + 1 - B) + 1 := by omega
    obtain ⟨wt, htr, hwh, hmid'⟩ := scatter2_block_step N bb c (M + 1 - B) M
      (by omega) (by omega) hk
      q' wact oWoD iD iSym oSym
      (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2 - B))
      (fun j => decide ((c.work j).head = M + 2 - B ∧ (wact j).2 = Dir3.left))
      (fun j => by rw [show (M + 1 - B) + 1 = M + 2 - B from by omega])
      (fun j => by rw [show (M + 1 - B) + 1 = M + 2 - B from by omega])
      ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1) (by rw [htB])
      (by rw [show ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).work 0 = wtB
                from by rw [htB],
            hwhB, hsucc, blockStart_succ k (M + 1 - B) (by omega), headBitCell]
          simp only [blockWidth]; omega)
      (by rw [show ((singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1).work 0 = wtB
                from by rw [htB],
            show (M + 1 - B) + 1 = M + 2 - B from by omega]
          exact hmidB)
      (by rw [hci]; exact his) (by rw [hco]; exact hos)
    refine ⟨wt, ?_, ?_, ?_⟩
    · erw [show 3 * k * (B + 1) = 3 * k * B + 3 * k from Nat.mul_succ (3 * k) B,
        trace_const_add', htr, hci, hco]
      refine (Cfg.mk.injEq ..).mpr ⟨?_, rfl, rfl, rfl⟩
      rw [show (fun j : Fin k =>
              if (wact j).2 = Dir3.left ∧ (c.work j).head = M + 1 - B + 1 then false
              else decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2 - B))
            = (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2 - (B + 1))) from by
          funext j
          by_cases hL : (wact j).2 = Dir3.left
          · by_cases hh : (c.work j).head = M + 1 - B + 1
            · rw [ite_eq_left ⟨hL, hh⟩]; symm; exact decide_eq_false (by rintro ⟨_, h2⟩; omega)
            · rw [ite_eq_right (fun h => hh h.2), decide_eq_decide]
              constructor
              · rintro ⟨hl, _⟩; exact ⟨hl, by omega⟩
              · rintro ⟨hl, _⟩; exact ⟨hl, by omega⟩
          · rw [ite_eq_right (fun h => hL h.1), decide_eq_false (fun h => hL h.1),
              decide_eq_false (fun h => hL h.1)],
        show (fun j : Fin k => decide ((wact j).2 = Dir3.left ∧ (c.work j).head = M + 1 - B))
            = (fun j => decide ((c.work j).head = M + 2 - (B + 1) ∧ (wact j).2 = Dir3.left)) from by
          funext j
          rw [show M + 2 - (B + 1) = M + 1 - B from by omega, decide_eq_decide]
          exact And.comm]
    · rw [hwh, show M + 2 - (B + 1) = M + 1 - B from by omega]
    · rw [show M + 2 - (B + 1) = M + 1 - B from by omega]; exact hmid'

/-- **SCATTER sweep-2 stays in `scatter2` off `▷` (per step), with tape geometry.** One
    sweep-2 step from a `scatter2` config whose work head is `≥ 1` (so it does NOT read
    `▷`, given the cells below the head are non-`▷`) stays in `scatter2`. The new work
    head is `head - 1` and only the old head cell is overwritten — every other cell is
    preserved. This is the per-step lever for the `scatter2` sweep `¬gather` lemma. -/
theorem scatter2_step_stays {k : ℕ} (N : NTM k) (b : Bool) (d : Scatter2Data k N.Q)
    (c1 : Cfg 1 (SimQ k N.Q)) (hst : c1.state = SimQ.scatter2 d)
    (hh : 1 ≤ (c1.work 0).head)
    (hns : (c1.work 0).cells ((c1.work 0).head) ≠ Γ.start) :
    ∃ d', ((singleTapeSim N).trace 1 (fun _ => b) c1).state = SimQ.scatter2 d'
      ∧ (((singleTapeSim N).trace 1 (fun _ => b) c1).work 0).head = (c1.work 0).head - 1
      ∧ ∀ p, p ≠ (c1.work 0).head →
          (((singleTapeSim N).trace 1 (fun _ => b) c1).work 0).cells p = (c1.work 0).cells p := by
  have hnsr : (c1.work 0).read ≠ Γ.start := by rw [Tape.read]; exact hns
  rw [scatter2_trace1 N d b c1 hst]
  -- the work field is `writeAndMove (r.2.1 0).toΓ (r.2.2.2.2.1 0)`; off-`▷` the dir is `left`
  set r := scatter2Step d c1.input.read ((c1.work 0).read) c1.output.read with hr
  -- the move direction `r.2.2.2.2.1 0` is `left` (off `▷`)
  have hdir : r.2.2.2.2.1 0 = Dir3.left := by
    rw [hr]; obtain ⟨q', oWoD, iD, iSym, oSym, pos, isLeftMover, leftCarry⟩ := d
    simp only [scatter2Step, ite_eq_right hnsr]
  have hwork : ((c1.work 0).writeAndMove (r.2.1 0).toΓ (r.2.2.2.2.1 0))
      = ⟨(c1.work 0).head - 1,
        Function.update (c1.work 0).cells (c1.work 0).head (r.2.1 0).toΓ⟩ := by
    rw [hdir]; exact work_write_left (c1.work 0) (r.2.1 0).toΓ hh
  -- the state is `r.1`; off `▷` every branch yields `scatter2`
  obtain ⟨d', hd'⟩ : ∃ d', r.1 = SimQ.scatter2 d' := by
    rw [hr]; obtain ⟨q', oWoD, iD, iSym, oSym, pos, isLeftMover, leftCarry⟩ := d
    simp only [scatter2Step, ite_eq_right hnsr]
    (repeat' split) <;> exact ⟨_, rfl⟩
  refine ⟨d', hd', ?_, ?_⟩
  · show (((c1.work (0 : Fin 1)).writeAndMove (r.2.1 0).toΓ (r.2.2.2.2.1 0))).head
        = (c1.work 0).head - 1
    rw [hwork]
  · intro p hp
    show (((c1.work (0 : Fin 1)).writeAndMove (r.2.1 0).toΓ (r.2.2.2.2.1 0))).cells p
        = (c1.work 0).cells p
    rw [hwork]; exact Function.update_of_ne hp _ _

/-- **SCATTER sweep-2 block sweep stays in `scatter2` (per step).** Within one block of the
    leftward sweep-2 phase (from the `Scatter2MidInv … (p+1)` entry), every micro-step
    `s ≤ 3*k` keeps the simulator in a `scatter2` state. Proved by reaching the nearest
    3-step (per-tape) boundary with `scatter2_block_aux` (whose output is `scatter2` with a
    known head `≥ blockStart k p + 2 ≥ 3` and a `Scatter2BlockInv` tape, so the read is
    `≠ ▷`) and stepping the remaining `s % 3 ≤ 2` micro-steps with `scatter2_step_stays`
    (each read is at a cell `≥ 1`, hence non-`▷` by `Scatter2BlockInv.cells_ne_start`). -/
theorem scatter2_block_states {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (p M : ℕ)
    (hp1 : 1 ≤ p) (hpM : p ≤ M + 1) (hk : 1 ≤ k)
    (q' : N.Q) (wact : Fin k → Γw × Dir3) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (isLeftMover_in leftCarry_in : Fin k → Bool)
    (hilm_in : ∀ j : Fin k,
      isLeftMover_in j = decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ p + 1))
    (hlc_in : ∀ j : Fin k,
      leftCarry_in j = decide ((c.work j).head = p + 1 ∧ (wact j).2 = Dir3.left))
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2
      (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2), isLeftMover_in, leftCarry_in))
    (hhead : (c1.work 0).head = headBitCell k p ⟨k - 1, by omega⟩ + 2)
    (hmid : Scatter2MidInv (c1.work 0) c.work wact M (p + 1))
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∀ s, s ≤ 3 * k →
      ∃ d, ((singleTapeSim N).trace s (fun _ => bb) c1).state = SimQ.scatter2 d := by
  -- one step from a `scatter2` config whose head is `≥ 1` and whose `head`/`head-1` cells
  -- are non-`▷` (the carried `Scatter2BlockInv`) stays `scatter2`, retreating the head by 1.
  intro s hs
  -- reach the nearest 3-step (per-tape) boundary `m = s / 3`
  obtain ⟨wt, htr, hwh, hbi⟩ := scatter2_block_aux N bb c p M hp1 hpM hk q' wact oWoD iD iSym oSym
    isLeftMover_in leftCarry_in hilm_in hlc_in c1 hst hhead
    (Scatter2BlockInv.ofMid hp1 hmid) his hos (s / 3) (by omega)
  have hsplit : s = 3 * (s / 3) + s % 3 := by omega
  erw [hsplit, trace_const_add']
  set c0 := (singleTapeSim N).trace (3 * (s / 3)) (fun _ => bb) c1 with hc0
  -- the boundary config: scatter2 with datum `d0`, tape `wt`, `Scatter2BlockInv … p (s/3)`
  obtain ⟨d0, hc0st⟩ : ∃ d, c0.state = SimQ.scatter2 d := ⟨_, by rw [htr]⟩
  have hc0w : c0.work 0 = wt := by rw [htr]
  have hc0head : (c0.work 0).head = blockStart k p + 3 * (k - 1) + 2 - 3 * (s / 3) := by
    rw [hc0w]; exact hwh
  have hc0bi : Scatter2BlockInv (c0.work 0) c.work wact M p (s / 3) := by rw [hc0w]; exact hbi
  have hr3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rcases hr3 with hr | hr | hr <;> rw [hr]
  · exact ⟨d0, hc0st⟩
  · -- residual 1: `s % 3 = 1 ⟹ s / 3 ≤ k - 1 ⟹ head ≥ 3`; one `scatter2` step
    have hdm := Nat.div_add_mod s 3
    have hHge : 3 ≤ (c0.work 0).head := by
      rw [hc0head]; have := one_le_blockStart k p; omega
    have hread0 : (c0.work 0).cells ((c0.work 0).head) ≠ Γ.start :=
      hc0bi.cells_ne_start hp1 hpM (by omega)
    obtain ⟨d', hd', _, _⟩ := scatter2_step_stays N bb d0 c0 hc0st (by omega) hread0
    exact ⟨d', hd'⟩
  · -- residual 2: two `scatter2` steps; the second read is the (preserved) cell `head - 1`
    have hdm := Nat.div_add_mod s 3
    have hHge : 3 ≤ (c0.work 0).head := by
      rw [hc0head]; have := one_le_blockStart k p; omega
    have hread0 : (c0.work 0).cells ((c0.work 0).head) ≠ Γ.start :=
      hc0bi.cells_ne_start hp1 hpM (by omega)
    have hread1 : (c0.work 0).cells ((c0.work 0).head - 1) ≠ Γ.start :=
      hc0bi.cells_ne_start hp1 hpM (by omega)
    erw [show (2 : ℕ) = 1 + 1 from rfl, trace_const_add']
    obtain ⟨d', hd', hh', hcells'⟩ := scatter2_step_stays N bb d0 c0 hc0st (by omega) hread0
    set c0' := (singleTapeSim N).trace 1 (fun _ => bb) c0 with hc0'
    have hread' : (c0'.work 0).cells ((c0'.work 0).head) ≠ Γ.start := by
      rw [hh', hcells' ((c0.work 0).head - 1) (by omega)]; exact hread1
    obtain ⟨d'', hd'', _, _⟩ := scatter2_step_stays N bb d' c0' hd' (by rw [hh']; omega) hread'
    exact ⟨d'', hd''⟩

/-- **SCATTER sweep-2 — no GATHER step (per micro-step).** Over the whole `3*k*(M+1) + 1`
    sweep-2 phase (from the same entry as `scatter2_sweep`), no intermediate state is a
    `gather` state — the simulator stays in `scatter2` until the final `▷`-triggered turn
    into `commit`. Companion to `scatter1_sweep_states`: it shows the constant-choice trace
    has no choice-consuming (`gather`-on-`□`) step in this phase, the input to
    `trace_congr_choices` for `macroStepCorr_rev`. The hypotheses are identical to
    `scatter2_sweep` for call-site uniformity. Decomposes as a `scatter2_sweep_aux` block
    sweep (every `3*k`-boundary is `scatter2`) plus a `scatter2_block_states` residual. -/
theorem scatter2_sweep_states {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ)
    (hk : 1 ≤ k) (q' : N.Q) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ)
    (wact : Fin k → Γw × Dir3) (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
        (fun t => decide ((wact t).2 = Dir3.left)), (fun _ => false)))
    (hhead : (c1.work 0).head = blockStart k (M + 2) - 1)
    (hinv : SimInvAt k (c1.work 0) (fun t => scatterInterWork (c.work t) (wact t)) (M + 1))
    (hle : ∀ j : Fin k, (c.work j).head ≤ M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∀ i, i < 3 * k * (M + 1) + 1 →
      ¬ ∃ d, ((singleTapeSim N).trace i (fun _ => bb) c1).state = SimQ.gather d := by
  -- It suffices to show the state at every interior step is `scatter2`.
  suffices H : ∀ i, i ≤ 3 * k * (M + 1) →
      ∃ d, ((singleTapeSim N).trace i (fun _ => bb) c1).state = SimQ.scatter2 d by
    intro i hi ⟨dg, hg⟩
    obtain ⟨d1, h1⟩ := H i (by omega)
    rw [h1] at hg
    exact absurd (Sum.inr.inj hg) (by simp [reduceCtorEq])
  -- bridge the entry carries to the `B = 0` boundary forms
  have hilm_eq : (fun t : Fin k => decide ((wact t).2 = Dir3.left))
      = (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2)) := by
    funext j; rw [decide_eq_decide]
    exact ⟨fun h => ⟨h, by have := hle j; omega⟩, fun h => h.1⟩
  have hlc_eq : (fun _ : Fin k => false)
      = (fun j => decide ((c.work j).head = M + 2 ∧ (wact j).2 = Dir3.left)) := by
    funext j; symm; exact decide_eq_false (by rintro ⟨h1, _⟩; have := hle j; omega)
  intro i hi
  -- block index `B = i / (3*k)` and residual `r = i % (3*k)`
  set B := i / (3 * k) with hBdef
  have hdm : 3 * k * B + i % (3 * k) = i := by rw [hBdef]; exact Nat.div_add_mod i (3 * k)
  have hmod : i % (3 * k) < 3 * k := Nat.mod_lt _ (by omega)
  -- `B ≤ M+1`; at `B = M+1` we are exactly at `i = 3*k*(M+1)` (the final boundary)
  have hBM1 : B ≤ M + 1 := by
    rw [hBdef]
    calc i / (3 * k) ≤ (3 * k * (M + 1)) / (3 * k) := Nat.div_le_div_right hi
      _ = M + 1 := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel _ (by omega)
  rcases Nat.eq_or_lt_of_le hBM1 with hBeq | hBlt
  · -- `B = M+1`: `i = 3*k*(M+1)` exactly (residual 0); the final boundary IS scatter2
    have hi0 : i = 3 * k * (M + 1) := by
      rw [hBeq] at hdm; omega
    obtain ⟨wtB, hSB, _, _⟩ := scatter2_sweep_aux N bb c M hk q' wact oWoD iD iSym oSym c1
      (by rw [hst, hilm_eq, hlc_eq]) hhead (Scatter2MidInv.ofSimInv hinv) his hos (M + 1)
      (le_refl _)
    exact ⟨_, by rw [hi0, hSB]⟩
  · -- `B ≤ M`: reach the block-`(M+1-B)` entry, then run the `scatter2_block_states` residual
    have hBM : B ≤ M := Nat.lt_succ_iff.mp hBlt
    obtain ⟨wtB, hSB, hwhB, hmidB⟩ := scatter2_sweep_aux N bb c M hk q' wact oWoD iD iSym oSym c1
      (by rw [hst, hilm_eq, hlc_eq]) hhead (Scatter2MidInv.ofSimInv hinv) his hos B (by omega)
    -- block being swept is `p = M+1-B`; its `Scatter2MidInv … (p+1)` is the `B`-boundary at `M+2-B`
    have hp1 : 1 ≤ M + 1 - B :=
      Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.add_le_add_right hBM 1)
    have hpM : M + 1 - B ≤ M + 1 := Nat.sub_le _ _
    have hp1eq : (M + 1 - B) + 1 = M + 2 - B := by
      clear_value B; omega
    -- residual `r = i - 3*k*B ≤ 3*k`
    have hbridge : i = 3 * k * B + (i - 3 * k * B) := by omega
    have hres : i - 3 * k * B ≤ 3 * k := by omega
    erw [hbridge, trace_const_add']
    set cE := (singleTapeSim N).trace (3 * k * B) (fun _ => bb) c1 with hcE
    -- the block-`p` entry: scatter2 at slot 2 tape `k-1`, head `headBitCell p (k-1) + 2`,
    -- the `B`-boundary carries are the `p`-block-states carries, `Scatter2MidInv … (p+1)`
    have hcEst : cE.state = SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
        (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2 - B)),
        (fun j => decide ((c.work j).head = M + 2 - B ∧ (wact j).2 = Dir3.left))) := by rw [hSB]
    have hcEhead : (cE.work 0).head = headBitCell k (M + 1 - B) ⟨k - 1, by omega⟩ + 2 := by
      rw [hSB, hwhB, ← hp1eq, blockStart_succ k (M + 1 - B) hp1, headBitCell]
      simp only [blockWidth]; omega
    have hcEmid : Scatter2MidInv (cE.work 0) c.work wact M ((M + 1 - B) + 1) := by
      rw [hSB, hp1eq]; exact hmidB
    have hcEis : cE.input.read ≠ Γ.start := by rw [hSB]; exact his
    have hcEos : cE.output.read ≠ Γ.start := by rw [hSB]; exact hos
    exact scatter2_block_states N bb c (M + 1 - B) M hp1 hpM hk q' wact oWoD iD iSym oSym
      (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2 - B))
      (fun j => decide ((c.work j).head = M + 2 - B ∧ (wact j).2 = Dir3.left))
      (fun j => by rw [hp1eq]) (fun j => by rw [hp1eq])
      cE hcEst hcEhead hcEmid hcEis hcEos (i - 3 * k * B) hres

/-- **SCATTER sweep-2 → COMMIT (`trace (3*k*(M+1) + 1)`).** From the sweep-1 output
    (scatter2 entry: `isLeftMover = decide(left)`, `leftCarry = 0`, head at
    `blockStart (M+2) - 1`, the work tape `SimInvAt (M+1)`-encoding `scatterInterWork`),
    sweep all `M+1` blocks leftward (turning each left-mover's head-bit) and then read
    `▷` to hand off to COMMIT. The work tape now `SimInvAt (M+1)`-encodes the **final**
    config `scatterFinalWork` — exactly `N`'s one-step images. Wraps `scatter2_sweep_aux`
    (at `B = M+1`) between `ofSimInv` and `toSimInv`, then `scatter2_start`. -/
theorem scatter2_sweep {k : ℕ} (N : NTM k) (bb : Bool) (c : Cfg k N.Q) (M : ℕ) (hk : 1 ≤ k)
    (q' : N.Q) (oWoD : Γw × Dir3) (iD : Dir3) (iSym oSym : Γ) (wact : Fin k → Γw × Dir3)
    (c1 : Cfg 1 (SimQ k N.Q))
    (hst : c1.state = SimQ.scatter2 (q', oWoD, iD, iSym, oSym, (⟨k - 1, by omega⟩, 2),
        (fun t => decide ((wact t).2 = Dir3.left)), (fun _ => false)))
    (hhead : (c1.work 0).head = blockStart k (M + 2) - 1)
    (hinv : SimInvAt k (c1.work 0) (fun t => scatterInterWork (c.work t) (wact t)) (M + 1))
    (hwf0 : ∀ j : Fin k, (c.work j).cells 0 = Γ.start)
    (hns0 : ∀ (j : Fin k) (p : ℕ), 1 ≤ p → (c.work j).cells p ≠ Γ.start)
    (hle : ∀ j : Fin k, (c.work j).head ≤ M)
    (his : c1.input.read ≠ Γ.start) (hos : c1.output.read ≠ Γ.start) :
    ∃ wfin : Fin 1 → Tape,
      (singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => bb) c1 =
        { state := SimQ.commit (q', oWoD.1, oWoD.2, iD, iSym, oSym),
          input := c1.input, work := wfin, output := c1.output }
      ∧ SimInvAt k (wfin 0) (fun t => scatterFinalWork (c.work t) (wact t)) (M + 1)
      ∧ (wfin 0).head = 1 := by
  have hilm_eq : (fun t : Fin k => decide ((wact t).2 = Dir3.left))
      = (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ M + 2)) := by
    funext j; rw [decide_eq_decide]
    exact ⟨fun h => ⟨h, by have := hle j; omega⟩, fun h => h.1⟩
  have hlc_eq : (fun _ : Fin k => false)
      = (fun j => decide ((c.work j).head = M + 2 ∧ (wact j).2 = Dir3.left)) := by
    funext j; symm; exact decide_eq_false (by rintro ⟨h1, _⟩; have := hle j; omega)
  obtain ⟨wtS, hS, hwhS, hmidS⟩ := scatter2_sweep_aux N bb c M hk q' wact oWoD iD iSym oSym c1
    (by rw [hst, hilm_eq, hlc_eq]) hhead (Scatter2MidInv.ofSimInv hinv) his hos (M + 1) (le_refl _)
  rw [show M + 2 - (M + 1) = 1 from by omega] at hS hwhS hmidS
  have hcwS : ((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1).work 0 = wtS := by
    rw [hS]
  have hSin : ((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1).input = c1.input := by
    rw [hS]
  have hSout : ((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1).output = c1.output := by
    rw [hS]
  have hh0 : wtS.head = 0 := by rw [hwhS, blockStart_one]
  have hsimFinal : SimInvAt k wtS (fun t => scatterFinalWork (c.work t) (wact t)) (M + 1) :=
    Scatter2MidInv.toSimInv hwf0 hns0 hle hmidS
  have hstart := scatter2_start N bb q' oWoD iD iSym oSym (⟨k - 1, by omega⟩, 2)
    (fun j => decide ((wact j).2 = Dir3.left ∧ (c.work j).head ≤ 1))
    (fun j => decide ((c.work j).head = 1 ∧ (wact j).2 = Dir3.left))
    ((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1)
    (by rw [hS])
    (by simp only [Tape.read]; rw [hcwS, hh0]; exact hsimFinal.cell0)
    (by rw [hSin]; exact his) (by rw [hSout]; exact hos)
  refine ⟨fun i =>
      (((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1).work i).writeAndMove
      Γw.blank.toΓ Dir3.right, ?_, ?_, ?_⟩
  · erw [trace_const_add', hstart, hSin, hSout]
  · apply hsimFinal.cells_congr
    show ((((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1).work 0).writeAndMove
        Γw.blank.toΓ Dir3.right).cells = wtS.cells
    rw [hcwS]
    show (wtS.write Γw.blank.toΓ).cells = wtS.cells
    unfold Tape.write
    rw [ite_eq_left hh0]
  · show ((((singleTapeSim N).trace (3 * k * (M + 1)) (fun _ => bb) c1).work 0).writeAndMove
        Γw.blank.toΓ Dir3.right).head = 1
    rw [hcwS, work_blank_right_at0 wtS hh0]

/-- `N`'s one-step work-tape image (`writeAndMove w d`) is exactly the SCATTER
    **final** tape `scatterFinalWork ct (w, d)`: both write `w` at the old head and
    then move per `d` (left ↦ `head-1`, right ↦ `head+1`, stay ↦ `head`). This is the
    bridge between `N.trace 1` and the SCATTER phases' encoding target. -/
theorem writeAndMove_eq_scatterFinal (ct : Tape) (wd : Γw × Dir3) :
    ct.writeAndMove (wd.1 : Γ) wd.2 = scatterFinalWork ct wd := by
  obtain ⟨w, d⟩ := wd
  show (ct.write (w : Γ)).move d = scatterFinalWork ct (w, d)
  cases d <;>
    · simp only [scatterFinalWork, scatterInterWork, Tape.move, Tape.write]
      split <;> rfl

/-- **`N.trace 1` in SCATTER-final form.** From a non-halted `c`, one `N`-step
    (choice `bitf 0`) yields the state/input/output of `N.δ` and work tapes that are
    exactly `scatterFinalWork` of the old tapes under the `δ`-action `wact` (work
    write/dir). The encoding-side description that the SCATTER phases produce. -/
theorem trace_one_scatterFinal {k : ℕ} (N : NTM k) (bitf : Fin 1 → Bool) (c : Cfg k N.Q)
    (hne : c.state ≠ N.qhalt) :
    N.trace 1 bitf c =
      { state := (N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).1,
        input := c.input.move
          (N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.1,
        work := fun t => scatterFinalWork (c.work t)
          ((N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).2.1 t,
            (N.δ (bitf 0) c.state c.input.read
              (fun i => (c.work i).read) c.output.read).2.2.2.2.1 t),
        output := c.output.writeAndMove
          (N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.1
          (N.δ (bitf 0) c.state c.input.read
            (fun i => (c.work i).read) c.output.read).2.2.2.2.2 } := by
  have hbase : N.trace 1 bitf c =
      { state := (N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).1,
        input := c.input.move
          (N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.1,
        work := fun i => (c.work i).writeAndMove
          ((N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).2.1 i : Γ)
          ((N.δ (bitf 0) c.state c.input.read
            (fun i => (c.work i).read) c.output.read).2.2.2.2.1 i),
        output := c.output.writeAndMove
          (N.δ (bitf 0) c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.1
          (N.δ (bitf 0) c.state c.input.read
            (fun i => (c.work i).read) c.output.read).2.2.2.2.2 } := by
    rw [NTM.trace]; simp only [hne, ↓reduceIte]; rfl
  rw [hbase]
  refine (Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, rfl⟩
  funext t
  rw [← writeAndMove_eq_scatterFinal]

/-- **Deterministic front half (`run → gather → COMPUTE → rewind`).** From a
    corresponding non-halted config, the simulator (constant choice `bit`) reaches
    the SCATTER sweep-1 entry in `3 + 6*k*M` steps: the work tape still encodes
    `c.work` at `M` (head parked at cell `1`), the SCATTER actions `wact`/`oWoD`/`iD`
    are read off `N.δ bit …` (the one COMPUTE use of `bit`), and the input/output
    heads have dodged off `▷`. -/
theorem run_to_scatter1 {k : ℕ} (N : NTM k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (bit : Bool) :
    (singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => bit) c1 =
      { state := SimQ.scatter1
          ((N.δ bit c.state c.input.read (fun j => (c.work j).read) c.output.read).1,
           (fun i => ((N.δ bit c.state c.input.read (fun j => (c.work j).read) c.output.read).2.1 i,
              (N.δ bit c.state c.input.read (fun j => (c.work j).read) c.output.read).2.2.2.2.1 i)),
           ((N.δ bit c.state c.input.read (fun j => (c.work j).read) c.output.read).2.2.1,
            (N.δ bit c.state c.input.read (fun j => (c.work j).read) c.output.read).2.2.2.2.2),
           (N.δ bit c.state c.input.read (fun j => (c.work j).read) c.output.read).2.2.2.1,
           c.input.read, c.output.read, (0, 0),
           (fun j => decide ((c.work j).read = Γ.start)), (fun _ => false), false, false),
        input := c.input.move (TM.idleDir c.input.read),
        output := c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ
          (TM.idleDir c.output.read),
        work := fun _ => { head := 1, cells := (c1.work 0).cells } }
    ∧ SimInvAt k { head := 1, cells := (c1.work 0).cells } c.work M := by
  obtain ⟨hstate, hheadLe, hinputEq, houtputEq, hinv, hwbeyond, hinputWf, houtputWf⟩ := hcorr
  have hns1 : (c1.work 0).cells 1 ≠ Γ.start := by
    by_cases h1 : 1 < blockStart k (M + 1)
    · exact hinv.materialized_ne_start (le_refl 1) h1
    · rw [hinv.sentinel 1 (by omega)]; decide
  have hisR : (c1.input.move (TM.idleDir c1.input.read)).read ≠ Γ.start := by
    rw [hinputEq]; exact move_idle_read_ne c.input hinputWf
  have hosR : (c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
      (TM.idleDir c1.output.read)).read ≠ Γ.start := by
    rw [houtputEq]; exact writeMove_idle_read_ne c.output houtputWf
  -- Phase 0: run step (work head → 1, cells preserved)
  have e1 : (singleTapeSim N).trace 1 (fun _ => bit) c1 =
      { state := SimQ.gather (c.state, (fun _ => Γ.start), c1.input.read, c1.output.read,
          (0, 0), false, Γ.blank),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun _ => { head := 1, cells := (c1.work 0).cells },
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
    rw [run_step N c.state hne bit c1 hstate]
    refine (Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, rfl⟩
    funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
    exact run_work_eq (c1.work 0) hheadLe hinv.cell0 hns1
  -- Phase 1: gather sweep over the M materialized blocks (acc collects the head reads)
  obtain ⟨rf', pending', hgather⟩ := gather_sweep_aux N bit c M c.state c1.input.read c1.output.read
    ((singleTapeSim N).trace 1 (fun _ => bit) c1) false Γ.blank
    (by rw [e1]; rfl) (by rw [e1, blockStart_one]) (by rw [e1]; exact hinv.cells_congr rfl)
    (by rw [e1]; exact hisR) (by rw [e1]; exact hosR) M (le_refl M)
  rw [gather_acc_eq hinv] at hgather
  refine ⟨?_, hinv.cells_congr rfl⟩
  have hir : c1.input.read = c.input.read := by rw [hinputEq]
  have hor : c1.output.read = c.output.read := by rw [houtputEq]
  -- the gather-sweep config's input/output/work, in simplified form
  have hcgi : ((singleTapeSim N).trace (3 * k * M) (fun _ => bit)
      ((singleTapeSim N).trace 1 (fun _ => bit) c1)).input
      = c1.input.move (TM.idleDir c1.input.read) := by rw [hgather, e1]
  have hcgo : ((singleTapeSim N).trace (3 * k * M) (fun _ => bit)
      ((singleTapeSim N).trace 1 (fun _ => bit) c1)).output
      = c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
        (TM.idleDir c1.output.read) := by
    rw [hgather, e1]
  have hcgw : ((singleTapeSim N).trace (3 * k * M) (fun _ => bit)
      ((singleTapeSim N).trace 1 (fun _ => bit) c1)).work 0
      = { head := blockStart k (M + 1), cells := (c1.work 0).cells } := by
    rw [hgather]; dsimp only; rw [e1]
  -- Phase 2: gather sentinel (the one COMPUTE step — fires `N.δ bit …`)
  have hsent : (singleTapeSim N).trace 1 (fun _ => bit)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => bit)
        ((singleTapeSim N).trace 1 (fun _ => bit) c1)) =
      { state := SimQ.rewind
          ((N.δ bit c.state c1.input.read (fun j => (c.work j).read) c1.output.read).1,
           (fun i => ((N.δ bit c.state c1.input.read
              (fun j => (c.work j).read) c1.output.read).2.1 i,
              (N.δ bit c.state c1.input.read
                (fun j => (c.work j).read) c1.output.read).2.2.2.2.1 i)),
           ((N.δ bit c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.1,
            (N.δ bit c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.2.2),
           (N.δ bit c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.1,
           c1.input.read, c1.output.read, (fun j => decide ((c.work j).read = Γ.start))),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun _ => { head := blockStart k (M + 1) - 1, cells := (c1.work 0).cells },
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
    rw [gather_sentinel N bit c.state (fun j => (c.work j).read) c1.input.read c1.output.read
        (⟨0, by omega⟩, 0) rf' pending'
        ((singleTapeSim N).trace (3 * k * M) (fun _ => bit)
          ((singleTapeSim N).trace 1 (fun _ => bit) c1)) (by rw [hgather])
        (by rw [hcgw]; exact hinv.sentinel (blockStart k (M + 1)) (le_refl _))]
    refine (Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩
    · rw [hcgi]; exact tape_idle_stay _ hisR
    · funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
      rw [hcgw, work_write_left _ Γw.blank.toΓ (by have := one_le_blockStart k (M + 1); omega),
        show Γw.blank.toΓ = (c1.work 0).cells (blockStart k (M + 1)) from
          (hinv.sentinel (blockStart k (M + 1)) (le_refl _)).symm, Function.update_eq_self]
    · rw [hcgo]; exact tape_idle_writeMove _ hosR
  -- Phase 3: rewind sweep + trace_const_add' chaining
  have hbs1 : blockStart k (M + 1) = blockStart k (M + 1) - 1 + 1 := by
    have := one_le_blockStart k (M + 1); omega
  rw [trace_const_add', trace_const_add', trace_const_add', hbs1,
      rewind_sweep N bit _ _ _ _ c1.input.read c1.output.read
        (fun j => decide ((c.work j).read = Γ.start))
        ((singleTapeSim N).trace 1 (fun _ => bit)
          ((singleTapeSim N).trace (3 * k * M) (fun _ => bit)
            ((singleTapeSim N).trace 1 (fun _ => bit) c1)))
        (blockStart k (M + 1) - 1)
        (by rw [hsent]) (by rw [hsent]) (by rw [hsent]; exact hinv.cell0)
        (fun p' hp1 hp2 => by rw [hsent]; exact hinv.materialized_ne_start hp1 (by omega))
        (by rw [hsent]; exact hisR) (by rw [hsent]; exact hosR),
      hsent, hir, hor, hinputEq, houtputEq]

/-- **Decision-point characterization (constant-choice macro-step).** Along the
    CONSTANT-choice trace of one macro-step (the `run → gather → rewind →
    scatter1 → scatter2 → commit` cycle, total length `m`), a step index `i` is a
    `trace_congr_choices` decision point — the simulator is in a `gather` state and
    the work head reads the `□` sentinel — **iff** `i = p0 = 1 + 3*k*M`, the single
    GATHER-sentinel (COMPUTE) step. This is the lever that turns `trace_congr_choices`
    and forward `corr_macroStep` into the backward (arbitrary-choice) correspondence.

    Assembled per phase: `i = 0` is `run` (not gather); the gather sweep
    `[1, p0)` reads non-`□` (`gather_sweep_no_sentinel`); `i = p0` is the unique
    `gather`-on-`□`; the rewind sweep keeps `rewind` (`rewind_sweep_states`); the
    two scatter sweeps keep `scatter1`/`scatter2` (`scatter{1,2}_sweep_states`); the
    final `commit` step is not gather. -/
theorem macroStep_decision_point_iff {k : ℕ} (N : NTM k) (hk : 1 ≤ k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (b : Bool) :
    ∀ i, i < 1 + 3 * k * M + 1 + blockStart k (M + 1)
            + (3 * k * (M + 1) + 1) + (3 * k * (M + 1) + 1) + 1 →
      ((∃ d, ((singleTapeSim N).trace i (fun _ => b) c1).state = SimQ.gather d) ∧
        (((singleTapeSim N).trace i (fun _ => b) c1).work 0).read = Γ.blank
       ↔ i = 1 + 3 * k * M) := by
  -- `blockStart k (M+1) = 1 + 3*k*M = p0`
  have hbs : blockStart k (M + 1) = 1 + 3 * k * M := by
    simp only [blockStart, blockWidth, Nat.add_sub_cancel]; rw [Nat.mul_comm M (3 * k)]
  obtain ⟨hstate, hheadLe, hinputEq, houtputEq, hinv, hwbeyond, hinputWf, houtputWf⟩ := hcorr
  -- restore `hcorr` (the sub-lemmas take it / its projections)
  have hcorr : Corr N M c1 c :=
    ⟨hstate, hheadLe, hinputEq, houtputEq, hinv, hwbeyond, hinputWf, houtputWf⟩
  -- the gather-sweep / sentinel input & output reads are off `▷`
  have hisR : (c1.input.move (TM.idleDir c1.input.read)).read ≠ Γ.start := by
    rw [hinputEq]; exact move_idle_read_ne c.input hinputWf
  have hosR : (c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
      (TM.idleDir c1.output.read)).read ≠ Γ.start := by
    rw [houtputEq]; exact writeMove_idle_read_ne c.output houtputWf
  have hns1 : (c1.work 0).cells 1 ≠ Γ.start := by
    by_cases h1 : 1 < blockStart k (M + 1)
    · exact hinv.materialized_ne_start (le_refl 1) h1
    · rw [hinv.sentinel 1 (by omega)]; decide
  -- ===== Phase 0: the run step → GATHER-sweep entry config `cg = trace 1 c1` =====
  have e1 : (singleTapeSim N).trace 1 (fun _ => b) c1 =
      { state := SimQ.gather (c.state, (fun _ => Γ.start), c1.input.read, c1.output.read,
          (0, 0), false, Γ.blank),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun _ => { head := 1, cells := (c1.work 0).cells },
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
    rw [run_step N c.state hne b c1 hstate]
    refine (Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, rfl⟩
    funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
    exact run_work_eq (c1.work 0) hheadLe hinv.cell0 hns1
  -- ===== Phase 1: GATHER sweep `trace (3*k*M) cg`, landing at the sentinel-ready config =====
  obtain ⟨rf', pending', hgather⟩ := gather_sweep_aux N b c M c.state c1.input.read c1.output.read
    ((singleTapeSim N).trace 1 (fun _ => b) c1) false Γ.blank
    (by rw [e1]; rfl) (by rw [e1, blockStart_one]) (by rw [e1]; exact hinv.cells_congr rfl)
    (by rw [e1]; exact hisR) (by rw [e1]; exact hosR) M (le_refl M)
  rw [gather_acc_eq hinv] at hgather
  have hcgw : ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
      ((singleTapeSim N).trace 1 (fun _ => b) c1)).work 0
      = { head := blockStart k (M + 1), cells := (c1.work 0).cells } := by
    rw [hgather]; dsimp only; rw [e1]
  -- the work head reads the `□` sentinel at this config
  have hsentBlank : (((singleTapeSim N).trace (3 * k * M) (fun _ => b)
      ((singleTapeSim N).trace 1 (fun _ => b) c1)).work 0).read = Γ.blank := by
    rw [hcgw]; show (c1.work 0).cells (blockStart k (M + 1)) = Γ.blank
    exact hinv.sentinel (blockStart k (M + 1)) (le_refl _)
  have hsentGather : ∃ d, ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
      ((singleTapeSim N).trace 1 (fun _ => b) c1)).state = SimQ.gather d := by
    rw [hgather]; exact ⟨_, rfl⟩
  -- input/output of the gather-sweep config (unchanged from `cg`)
  have hcgi : ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
      ((singleTapeSim N).trace 1 (fun _ => b) c1)).input
      = c1.input.move (TM.idleDir c1.input.read) := by rw [hgather, e1]
  have hcgo : ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
      ((singleTapeSim N).trace 1 (fun _ => b) c1)).output
      = c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) := by rw [hgather, e1]
  -- ===== Phase 2: the GATHER sentinel step → REWIND entry config =====
  have hsent : (singleTapeSim N).trace 1 (fun _ => b)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
        ((singleTapeSim N).trace 1 (fun _ => b) c1)) =
      { state := SimQ.rewind
          ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).1,
           (fun i => ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.1 i,
              (N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.2.1 i)),
           ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.1,
            (N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.2.2),
           (N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.1,
           c1.input.read, c1.output.read, (fun j => decide ((c.work j).read = Γ.start))),
        input := c1.input.move (TM.idleDir c1.input.read),
        work := fun _ => { head := blockStart k (M + 1) - 1, cells := (c1.work 0).cells },
        output := c1.output.writeAndMove (TM.readBackWrite c1.output.read).toΓ
          (TM.idleDir c1.output.read) } := by
    rw [gather_sentinel N b c.state (fun j => (c.work j).read) c1.input.read c1.output.read
        (⟨0, by omega⟩, 0) rf' pending'
        ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
          ((singleTapeSim N).trace 1 (fun _ => b) c1)) (by rw [hgather])
        (by rw [hcgw]; exact hinv.sentinel (blockStart k (M + 1)) (le_refl _))]
    refine (Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩
    · rw [hcgi]; exact tape_idle_stay _ hisR
    · funext i; obtain rfl : i = 0 := Subsingleton.elim i 0
      rw [hcgw, work_write_left _ Γw.blank.toΓ (by have := one_le_blockStart k (M + 1); omega),
        show Γw.blank.toΓ = (c1.work 0).cells (blockStart k (M + 1)) from
          (hinv.sentinel (blockStart k (M + 1)) (le_refl _)).symm, Function.update_eq_self]
    · rw [hcgo]; exact tape_idle_writeMove _ hosR
  -- ===== the SCATTER-1 entry config (via `run_to_scatter1`) =====
  obtain ⟨hr1, hsi1⟩ := run_to_scatter1 N hcorr hne b
  set dr := N.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read with hdr
  -- ===== Phase 4: SCATTER sweep-1 → SCATTER-2 entry =====
  obtain ⟨wfin1, hs1, hsi2, hh1⟩ := scatter1_sweep N b c M
    dr.1 (fun i => (dr.2.1 i, dr.2.2.2.2.1 i)) (dr.2.2.1, dr.2.2.2.2.2) dr.2.2.2.1
    c.input.read c.output.read
    ((singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => b) c1)
    (by rw [hr1]; rfl) (by rw [hr1, blockStart_one]) (by rw [hr1]; exact hsi1) hk
    (fun j hj => (N.δ_right_of_start b c.state c.input.read
        (fun j => (c.work j).read) c.output.read).2.1 j
      (by rw [Tape.read, hj]; exact hcorr.inv.wfStart j))
    hcorr.wbeyond
    (by rw [hr1]; exact move_idle_read_ne c.input hcorr.inputWf)
    (by rw [hr1]; exact writeMove_idle_read_ne c.output hcorr.outputWf)
  -- ===== Phase 5: SCATTER sweep-2 → COMMIT entry =====
  obtain ⟨wfin2, hs2, hsi3, hh2⟩ := scatter2_sweep N b c M hk
    dr.1 (dr.2.2.1, dr.2.2.2.2.2) dr.2.2.2.1 c.input.read c.output.read
    (fun i => (dr.2.1 i, dr.2.2.2.2.1 i))
    ((singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
      ((singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => b) c1))
    (by rw [hs1]) (by rw [hs1]; exact hh1) (by rw [hs1]; exact hsi2)
    hcorr.inv.wfStart hcorr.inv.noStart hcorr.inv.heads_le
    (by rw [hs1, hr1]; exact move_idle_read_ne c.input hcorr.inputWf)
    (by rw [hs1, hr1]; exact writeMove_idle_read_ne c.output hcorr.outputWf)
  -- abbreviations for the phase boundaries
  set A := 1 + 3 * k * M + 1 + blockStart k (M + 1) with hA
  set B := A + (3 * k * (M + 1) + 1) with hBdef
  -- per-step `¬gather` for the SCATTER-1 phase (entry at `trace A c1`)
  have hsc1 : ∀ j, j < 3 * k * (M + 1) + 1 →
      ¬ ∃ d, ((singleTapeSim N).trace j (fun _ => b)
        ((singleTapeSim N).trace A (fun _ => b) c1)).state = SimQ.gather d := by
    apply scatter1_sweep_states N b c M
      dr.1 (fun i => (dr.2.1 i, dr.2.2.2.2.1 i)) (dr.2.2.1, dr.2.2.2.2.2) dr.2.2.2.1
      c.input.read c.output.read
      _ (by rw [hr1]; rfl) (by rw [hr1, blockStart_one]) (by rw [hr1]; exact hsi1) hk
      (fun j hj => (N.δ_right_of_start b c.state c.input.read
          (fun j => (c.work j).read) c.output.read).2.1 j
        (by rw [Tape.read, hj]; exact hcorr.inv.wfStart j))
      hcorr.wbeyond
      (by rw [hr1]; exact move_idle_read_ne c.input hcorr.inputWf)
      (by rw [hr1]; exact writeMove_idle_read_ne c.output hcorr.outputWf)
  -- per-step `¬gather` for the SCATTER-2 phase (entry at `trace B c1`)
  have hsc2 : ∀ j, j < 3 * k * (M + 1) + 1 →
      ¬ ∃ d, ((singleTapeSim N).trace j (fun _ => b)
        ((singleTapeSim N).trace B (fun _ => b) c1)).state = SimQ.gather d := by
    have hBc1 : (singleTapeSim N).trace B (fun _ => b) c1
        = (singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
            ((singleTapeSim N).trace A (fun _ => b) c1) := by
      erw [hBdef, trace_const_add']
    rw [hBc1]
    apply scatter2_sweep_states N b c M hk
      dr.1 (dr.2.2.1, dr.2.2.2.2.2) dr.2.2.2.1 c.input.read c.output.read
      (fun i => (dr.2.1 i, dr.2.2.2.2.1 i)) _
      (by rw [hs1]) (by rw [hs1]; exact hh1) (by rw [hs1]; exact hsi2)
      hcorr.inv.heads_le
      (by rw [hs1, hr1]; exact move_idle_read_ne c.input hcorr.inputWf)
      (by rw [hs1, hr1]; exact writeMove_idle_read_ne c.output hcorr.outputWf)
  -- per-step `¬gather` for the GATHER sweep (entry at `cg = trace 1 c1`)
  have hgsweep := gather_sweep_no_sentinel N b
    ((singleTapeSim N).trace 1 (fun _ => b) c1)
    (by rw [e1]; exact ⟨_, rfl⟩) (by rw [e1])
    (by rw [e1]; exact hinv.cells_congr rfl)
    (by rw [e1]; exact hisR) (by rw [e1]; exact hosR)
  -- per-step `rewind` state for the REWIND sweep (entry at `trace (p0+1) c1`)
  have hrewind := rewind_sweep_states N b
    ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).1)
    (fun i => ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.1 i,
       (N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.2.1 i))
    ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.1,
     (N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.2.2)
    ((N.δ b c.state c1.input.read (fun j => (c.work j).read) c1.output.read).2.2.2.1)
    c1.input.read c1.output.read (fun j => decide ((c.work j).read = Γ.start))
    ((singleTapeSim N).trace 1 (fun _ => b)
      ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
        ((singleTapeSim N).trace 1 (fun _ => b) c1)))
    (blockStart k (M + 1) - 1)
    (by rw [hsent]) (by rw [hsent])
    (fun p' hp1 hp2 => by rw [hsent]; exact hinv.materialized_ne_start hp1 (by omega))
    (by rw [hsent]; exact hisR) (by rw [hsent]; exact hosR)
  -- the REWIND entry config `trace (p0+1) c1 = trace 1 (trace (3*k*M) (trace 1 c1))`
  have hRewEntry : (singleTapeSim N).trace (1 + 3 * k * M + 1) (fun _ => b) c1
      = (singleTapeSim N).trace 1 (fun _ => b)
          ((singleTapeSim N).trace (3 * k * M) (fun _ => b)
            ((singleTapeSim N).trace 1 (fun _ => b) c1)) := by
    erw [show 1 + 3 * k * M + 1 = 1 + (3 * k * M + 1) from by omega, trace_const_add',
      trace_const_add']
  -- the SCATTER-2 entry config `trace B c1 = trace (3*k*(M+1)+1) (trace A c1)`
  have hBc1 : (singleTapeSim N).trace B (fun _ => b) c1
      = (singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
          ((singleTapeSim N).trace A (fun _ => b) c1) := by
    erw [hBdef, trace_const_add']
  -- helper: off the sentinel position, no step is a `gather`-on-`□` decision point
  have key : ∀ i, i < B + (3 * k * (M + 1) + 1) + 1 → i ≠ 1 + 3 * k * M →
      ¬ ((∃ d, ((singleTapeSim N).trace i (fun _ => b) c1).state = SimQ.gather d) ∧
        (((singleTapeSim N).trace i (fun _ => b) c1).work 0).read = Γ.blank) := by
    rintro i hib hip0 ⟨⟨dg, hg⟩, hbl⟩
    rcases Nat.lt_trichotomy i (1 + 3 * k * M) with hlt | heq | hgt
    · -- before the sentinel: `i = 0` (run) or gather sweep (read ≠ blank)
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · -- `i = 0`: state is `run`, not `gather`
        subst hi0
        rw [show (singleTapeSim N).trace 0 (fun _ => b) c1 = c1 from rfl] at hg
        rw [hstate] at hg
        exact absurd hg.symm (by simp [SimQ.run, SimQ.gather, reduceCtorEq])
      · -- `i ∈ [1, p0)`: the GATHER sweep, where the read is non-blank
        obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
        have hj : j < 3 * k * M := by omega
        erw [trace_const_add'] at hbl
        exact (hgsweep j hj).2 hbl
    · exact hip0 heq
    · -- after the sentinel: rewind / scatter1 / scatter2 / commit — never `gather`
      rcases Nat.lt_or_ge i A with hiA | hiA
      · -- REWIND sweep: `i ∈ (p0, A)`
        obtain ⟨j, rfl⟩ : ∃ j, i = (1 + 3 * k * M + 1) + j := ⟨i - (1 + 3 * k * M + 1), by omega⟩
        have hj : j ≤ blockStart k (M + 1) - 1 := by
          have := one_le_blockStart k (M + 1); rw [hA] at hiA; omega
        erw [trace_const_add', hRewEntry, hrewind j hj] at hg
        exact absurd (Sum.inr.inj hg) (by simp [reduceCtorEq])
      · -- SCATTER-1 / SCATTER-2 / COMMIT
        rcases Nat.lt_or_ge i B with hiB | hiB
        · -- SCATTER-1: `i ∈ [A, B)`
          obtain ⟨j, rfl⟩ : ∃ j, i = A + j := ⟨i - A, by omega⟩
          have hj : j < 3 * k * (M + 1) + 1 := by rw [hBdef] at hiB; omega
          erw [trace_const_add'] at hg
          exact hsc1 j hj ⟨dg, hg⟩
        · -- SCATTER-2 / COMMIT
          rcases Nat.lt_or_ge i (B + (3 * k * (M + 1) + 1)) with hiC | hiC
          · -- SCATTER-2: `i ∈ [B, B + (3*k*(M+1)+1))`
            obtain ⟨j, rfl⟩ : ∃ j, i = B + j := ⟨i - B, by omega⟩
            have hj : j < 3 * k * (M + 1) + 1 := by omega
            erw [trace_const_add'] at hg
            exact hsc2 j hj ⟨dg, hg⟩
          · -- COMMIT: `i = B + (3*k*(M+1)+1)`
            have hiCommit : i = B + (3 * k * (M + 1) + 1) := by omega
            subst hiCommit
            erw [trace_const_add', hBc1, hs2] at hg
            exact absurd (Sum.inr.inj hg) (by simp [reduceCtorEq])
  intro i hi
  by_cases hip0 : i = 1 + 3 * k * M
  · -- the decision point: both `mp` (trivially `i = p0`) and `mpr` (state/read facts) hold
    subst hip0
    have hp0 : (singleTapeSim N).trace (1 + 3 * k * M) (fun _ => b) c1
        = (singleTapeSim N).trace (3 * k * M) (fun _ => b)
            ((singleTapeSim N).trace 1 (fun _ => b) c1) :=
      trace_const_add (singleTapeSim N) 1 (3 * k * M) b c1
    exact ⟨fun _ => rfl, fun _ => ⟨by rw [hp0]; exact hsentGather, by rw [hp0]; exact hsentBlank⟩⟩
  · -- off the decision point: both sides false
    exact ⟨fun h => absurd (key i (by omega) hip0 h) (by simp), fun h => absurd h hip0⟩

/-- **Macro-step correspondence — explicit form.** Same content as
    `corr_macroStep`, but with the step count `m` written out literally (the
    macro-step length) and the choice sequence fixed to the constant `fun _ => b`.
    `corr_macroStep` is a thin existential wrapper around this; `macroStepCorr_rev`
    needs the explicit `m` so it can invoke `macroStep_decision_point_iff` (which
    is stated over exactly this length) to discharge `trace_congr_choices`. -/
theorem corr_macroStep_explicit {k : ℕ} (N : NTM k) (hk : 1 ≤ k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (b : Bool) :
    Corr N (M + 1)
        ((singleTapeSim N).trace
          (1 + 3 * k * M + 1 + blockStart k (M + 1)
            + (3 * k * (M + 1) + 1) + (3 * k * (M + 1) + 1) + 1) (fun _ => b) c1)
        (N.trace 1 (fun _ => b) c) := by
  obtain ⟨hr1, hsi1⟩ := run_to_scatter1 N hcorr hne b
  set dr := N.δ b c.state c.input.read (fun j => (c.work j).read) c.output.read with hdr
  -- Phase 4: SCATTER sweep-1
  obtain ⟨wfin1, hs1, hsi2, hh1⟩ := scatter1_sweep N b c M
    dr.1 (fun i => (dr.2.1 i, dr.2.2.2.2.1 i)) (dr.2.2.1, dr.2.2.2.2.2) dr.2.2.2.1
    c.input.read c.output.read
    ((singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => b) c1)
    (by rw [hr1]; rfl) (by rw [hr1, blockStart_one]) (by rw [hr1]; exact hsi1) hk
    (fun j hj => (N.δ_right_of_start b c.state c.input.read
        (fun j => (c.work j).read) c.output.read).2.1 j
      (by rw [Tape.read, hj]; exact hcorr.inv.wfStart j))
    hcorr.wbeyond
    (by rw [hr1]; exact move_idle_read_ne c.input hcorr.inputWf)
    (by rw [hr1]; exact writeMove_idle_read_ne c.output hcorr.outputWf)
  -- Phase 5: SCATTER sweep-2 → COMMIT
  obtain ⟨wfin2, hs2, hsi3, hh2⟩ := scatter2_sweep N b c M hk
    dr.1 (dr.2.2.1, dr.2.2.2.2.2) dr.2.2.2.1 c.input.read c.output.read
    (fun i => (dr.2.1 i, dr.2.2.2.2.1 i))
    ((singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
      ((singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => b) c1))
    (by rw [hs1]) (by rw [hs1]; exact hh1) (by rw [hs1]; exact hsi2)
    hcorr.inv.wfStart hcorr.inv.noStart hcorr.inv.heads_le
    (by rw [hs1, hr1]; exact move_idle_read_ne c.input hcorr.inputWf)
    (by rw [hs1, hr1]; exact writeMove_idle_read_ne c.output hcorr.outputWf)
  -- Phase 6: COMMIT step → run q'
  have hcommit := commit_step N dr.1 dr.2.2.1 dr.2.2.2.2.2 dr.2.2.2.1 c.input.read c.output.read
    b
    ((singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
      ((singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
        ((singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => b) c1)))
    (by rw [hs2])
  -- `N.trace 1` in SCATTER-final form (defeq to `dr`)
  have htr1 : N.trace 1 (fun _ => b) c =
      { state := dr.1, input := c.input.move dr.2.2.2.1,
        work := fun t => scatterFinalWork (c.work t) (dr.2.1 t, dr.2.2.2.2.1 t),
        output := c.output.writeAndMove dr.2.2.1 dr.2.2.2.2.2 } := by
    rw [trace_one_scatterFinal N (fun _ => b) c hne]
  erw [show 1 + 3 * k * M + 1 + blockStart k (M + 1) + (3 * k * (M + 1) + 1)
            + (3 * k * (M + 1) + 1) + 1
          = 1 + 3 * k * M + 1 + blockStart k (M + 1)
            + ((3 * k * (M + 1) + 1) + ((3 * k * (M + 1) + 1) + 1)) from by omega,
      trace_const_add', trace_const_add', trace_const_add', hcommit, htr1]
  -- abbreviate the COMMIT-config (input/output/work after the two scatter sweeps)
  set cc := (singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
    ((singleTapeSim N).trace (3 * k * (M + 1) + 1) (fun _ => b)
      ((singleTapeSim N).trace (1 + 3 * k * M + 1 + blockStart k (M + 1)) (fun _ => b) c1))
  have hci : cc.input = c.input.move (TM.idleDir c.input.read) := by rw [hs2, hs1, hr1]
  have hco : cc.output =
      c.output.writeAndMove (TM.readBackWrite c.output.read).toΓ (TM.idleDir c.output.read) := by
    rw [hs2, hs1, hr1]
  have hcw0 : cc.work 0 = wfin2 0 := by rw [hs2]
  have hns1' : (wfin2 0).cells 1 ≠ Γ.start := by
    by_cases h1 : 1 < blockStart k (M + 1 + 1)
    · exact hsi3.materialized_ne_start (le_refl 1) h1
    · rw [hsi3.sentinel 1 (by omega)]; decide
  have hfw : (cc.work 0).writeAndMove ((TM.readBackWrite (cc.work 0).read : Γw) : Γ)
      (TM.idleDir (cc.work 0).read) = { head := 1, cells := (wfin2 0).cells } := by
    rw [hcw0, run_work_eq (wfin2 0) (by omega) hsi3.cell0 hns1']
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- headLe
    show ((cc.work 0).writeAndMove ((TM.readBackWrite (cc.work 0).read : Γw) : Γ)
      (TM.idleDir (cc.work 0).read)).head ≤ 1
    rw [hfw]
  · -- inputEq
    show cc.input.move (if c.input.read = Γ.start then TM.idleDir cc.input.read
      else safeDir cc.input.read dr.2.2.2.1) = c.input.move dr.2.2.2.1
    rw [hci]
    exact commit_input_eq c.input dr.2.2.2.1 hcorr.inputWf
      (N.δ_right_of_start b c.state c.input.read (fun j => (c.work j).read) c.output.read).1
  · -- outputEq
    show cc.output.writeAndMove (if c.output.read = Γ.start then
          TM.readBackWrite cc.output.read else dr.2.2.1).toΓ
        (if c.output.read = Γ.start then TM.idleDir cc.output.read
         else safeDir cc.output.read dr.2.2.2.2.2)
      = c.output.writeAndMove dr.2.2.1.toΓ dr.2.2.2.2.2
    rw [hco]
    exact commit_output_eq c.output dr.2.2.1 dr.2.2.2.2.2 hcorr.outputWf
      (N.δ_right_of_start b c.state c.input.read (fun j => (c.work j).read) c.output.read).2.2
  · -- inv
    show SimInvAt k ((cc.work 0).writeAndMove ((TM.readBackWrite (cc.work 0).read : Γw) : Γ)
      (TM.idleDir (cc.work 0).read))
      (fun t => scatterFinalWork (c.work t) (dr.2.1 t, dr.2.2.2.2.1 t)) (M + 1)
    rw [hfw]
    exact hsi3.cells_congr rfl
  · -- wbeyond
    intro j p hp
    show (scatterFinalWork (c.work j) (dr.2.1 j, dr.2.2.2.2.1 j)).cells p = Γ.blank
    rw [scatterFinalWork_cells,
      scatterInterWork_cells_of_ne (c.work j) _ (by have := hcorr.inv.heads_le j; omega)]
    exact hcorr.wbeyond j p (by omega)
  · -- inputWf
    intro p hp
    show (c.input.move dr.2.2.2.1).cells p ≠ Γ.start
    cases dr.2.2.2.1 <;> exact hcorr.inputWf p hp
  · -- outputWf
    intro p hp
    show (c.output.writeAndMove dr.2.2.1.toΓ dr.2.2.2.2.2).cells p ≠ Γ.start
    have hc : (c.output.writeAndMove dr.2.2.1.toΓ dr.2.2.2.2.2).cells
        = (c.output.write dr.2.2.1.toΓ).cells := by cases dr.2.2.2.2.2 <;> rfl
    rw [hc, Tape.write]
    split
    · exact hcorr.outputWf p hp
    · show Function.update c.output.cells c.output.head dr.2.2.1.toΓ p ≠ Γ.start
      rw [Function.update_apply]
      split
      · cases dr.2.2.1 <;> decide
      · exact hcorr.outputWf p hp

/-- **Macro-step correspondence (the core obligation).** From a corresponding,
    non-halted configuration, for any nondeterministic choice `bit`, the
    simulator runs some number `m` of steps (with a choice sequence that feeds
    `bit` at the COMPUTE sub-step) and lands in a configuration corresponding to
    `N`'s one-step image under `bit`, with the materialized region grown by one,
    within `macroBound k M` sim steps.

    This is the heart of the behavioural correctness proof: it is established by
    tracing the phase machine `run → gather → rewind → scatter1 → scatter2 →
    commit` and showing each phase preserves/advances `SimInvAt`. -/
theorem corr_macroStep {k : ℕ} (N : NTM k) (hk : 1 ≤ k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (bitf : Fin 1 → Bool) :
    ∃ (m : ℕ) (choices : Fin m → Bool),
      Corr N (M + 1) ((singleTapeSim N).trace m choices c1) (N.trace 1 bitf c)
        ∧ m ≤ macroBound k M := by
  -- `N.trace 1 bitf c` depends only on `bitf 0`, so we may use the constant choice.
  have hbeq : N.trace 1 bitf c = N.trace 1 (fun _ => bitf 0) c := by
    rw [trace_one_scatterFinal N bitf c hne, trace_one_scatterFinal N (fun _ => bitf 0) c hne]
  refine ⟨1 + 3 * k * M + 1 + blockStart k (M + 1) + (3 * k * (M + 1) + 1)
      + (3 * k * (M + 1) + 1) + 1, fun _ => bitf 0, ?_, ?_⟩
  · rw [hbeq]; exact corr_macroStep_explicit N hk hcorr hne (bitf 0)
  · -- step count ≤ macroBound k M
    have hbs : blockStart k (M + 1) = 1 + 3 * k * M := by
      simp only [blockStart, blockWidth, Nat.add_sub_cancel]
      rw [Nat.mul_comm M (3 * k)]
    have h3 : 3 * k * (M + 1) = 3 * k * M + 3 * k := by rw [Nat.mul_add, Nat.mul_one]
    have hmb : macroBound k M = 16 * k * M + 16 * k + 16 * M + 16 := by
      unfold macroBound
      rw [Nat.mul_add 16 k 1, Nat.mul_one, Nat.add_mul, Nat.mul_add (16 * k) M 1, Nat.mul_one,
        Nat.mul_add 16 M 1, Nat.mul_one]
      omega
    have hle : 4 * (3 * k * M) ≤ 16 * k * M := by
      calc 4 * (3 * k * M) = 4 * (3 * k) * M := by rw [← Nat.mul_assoc]
        _ ≤ 16 * k * M := Nat.mul_le_mul (by omega) (le_refl M)
    rw [hbs, h3, hmb]; omega

/-- **Trace-level choice irrelevance.** Two choice sequences that agree at every
    step where the simulator is at a GATHER state reading the `□` sentinel (the
    only step consulting the nondeterministic bit — the COMPUTE sub-step) drive
    the simulator to the same configuration. Proved by induction on the step
    count, using `simDelta_eq_of_forall_ne_blank` at each step: where the configuration is
    not a `□`-reading GATHER step the choice is irrelevant, and where it is the
    hypothesis forces the two sequences to agree. -/
theorem trace_congr_choices {k : ℕ} (N : NTM k) :
    ∀ (m : ℕ) (choices choices' : ℕ → Bool) (c1 : Cfg 1 (SimQ k N.Q)),
    (∀ i, i < m →
       (∃ d, ((singleTapeSim N).trace i (fun j => choices j.val) c1).state = SimQ.gather d) →
       (((singleTapeSim N).trace i (fun j => choices j.val) c1).work 0).read = Γ.blank →
       choices i = choices' i) →
    (singleTapeSim N).trace m (fun j => choices j.val) c1
      = (singleTapeSim N).trace m (fun j => choices' j.val) c1 := by
  intro m
  induction m with
  | zero => intro choices choices' c1 _; rfl
  | succ m ih =>
    intro choices choices' c1 hyp
    rw [(singleTapeSim N).trace_add_fun m 1 choices c1,
      (singleTapeSim N).trace_add_fun m 1 choices' c1]
    have hcm : (singleTapeSim N).trace m (fun j => choices j.val) c1
        = (singleTapeSim N).trace m (fun j => choices' j.val) c1 :=
      ih choices choices' c1 (fun i hi => hyp i (Nat.lt_succ_of_lt hi))
    rw [← hcm]
    set cm0 := (singleTapeSim N).trace m (fun j => choices j.val) c1 with hcm0def
    by_cases hcmhalt : cm0.state = (singleTapeSim N).qhalt
    · rw [(singleTapeSim N).trace_halted 1 _ hcmhalt,
        (singleTapeSim N).trace_halted 1 _ hcmhalt]
    · have hsimeq : simDelta N (choices m) cm0.state cm0.input.read
            (fun i => (cm0.work i).read) cm0.output.read
          = simDelta N (choices' m) cm0.state cm0.input.read
            (fun i => (cm0.work i).read) cm0.output.read := by
        by_cases hgather : (∃ d, cm0.state = SimQ.gather d) ∧ (cm0.work 0).read = Γ.blank
        · obtain ⟨hd, hb⟩ := hgather
          rw [hyp m (Nat.lt_succ_self m) hd hb]
        · apply simDelta_eq_of_forall_ne_blank
          intro d hd_eq hbad
          exact hgather ⟨⟨d, hd_eq⟩, hbad⟩
      simp only [NTM.trace, ite_eq_right hcmhalt, Nat.add_zero]
      exact congrArg
        (fun r => ({ state := r.1, input := cm0.input.move r.2.2.2.1,
                     work := fun i => (cm0.work i).writeAndMove (r.2.1 i).toΓ (r.2.2.2.2.1 i),
                     output := cm0.output.writeAndMove r.2.2.1.toΓ r.2.2.2.2.2 } :
                   Cfg 1 N.singleTapeSim.Q))
        hsimeq

/-- **Iterated correspondence.** Simulating `t` steps of `N` (choices `g`): the
    simulator reaches, in some number `m` of steps (choices from a single
    `ℕ`-indexed `F`), a configuration corresponding to `N.trace t g c` (at some
    materialization level `M'`). Proved by induction on `t`, composing
    macro-steps with `trace_add_fun`; the halted case reuses the previous one. -/
theorem corr_iterate {k : ℕ} (N : NTM k) (hk : 1 ≤ k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (g : ℕ → Bool) (t : ℕ) :
    ∃ (m M' : ℕ) (F : ℕ → Bool),
      Corr N M' ((singleTapeSim N).trace m (fun i => F i.val) c1)
        (N.trace t (fun i => g i.val) c)
        ∧ M' ≤ M + t ∧ m ≤ t * macroBound k (M + t) := by
  induction t with
  | zero => exact ⟨0, M, g, hcorr, by omega, by omega⟩
  | succ t ih =>
    obtain ⟨m, M', f, hcorr_t, hM'le, hmle⟩ := ih
    set s_t := (singleTapeSim N).trace m (fun i => f i.val) c1 with hs_t
    set c_t := N.trace t (fun i => g i.val) c with hc_t
    -- N's (t+1)-step trace splits as one step from c_t
    have hNsplit : N.trace (t + 1) (fun i => g i.val) c
        = N.trace 1 (fun i => g (t + i.val)) c_t := by
      rw [hc_t]; exact N.trace_add_fun t 1 g c
    -- the new bound `(t+1)·macroBound k (M+(t+1))` dominates the old one
    have hgrow : t * macroBound k (M + t) ≤ (t + 1) * macroBound k (M + (t + 1)) :=
      le_trans (Nat.mul_le_mul (Nat.le_succ t) (macroBound_mono (by omega)))
        (le_refl _)
    by_cases hh : c_t.state = N.qhalt
    · -- N has halted: the (t+1) step is a no-op, reuse the IH config
      refine ⟨m, M', f, ?_, by omega, le_trans hmle hgrow⟩
      rw [hNsplit, N.trace_halted 1 _ hh]
      exact hcorr_t
    · -- N steps: apply the macro-step correspondence and concatenate choices
      obtain ⟨m', choices', hstep, hbound'⟩ :=
        corr_macroStep N hk hcorr_t hh (fun i => g (t + i.val))
      -- concatenate `f` (first m steps) and `choices'` (next m') into one `F`
      set F : ℕ → Bool :=
        fun j => if j < m then f j else if h : j - m < m' then choices' ⟨j - m, h⟩ else false
        with hF
      refine ⟨m + m', M' + 1, F, ?_, by omega, ?_⟩
      · rw [hNsplit, (singleTapeSim N).trace_add_fun m m' F c1]
        have hpre : (fun i : Fin m => F i.val) = (fun i : Fin m => f i.val) := by
          funext i; rw [hF]; simp only []; rw [ite_eq_left i.isLt]
        have hsuf : (fun i : Fin m' => F (m + i.val)) = choices' := by
          funext i; rw [hF]; simp only []
          rw [ite_eq_right (by omega), dite_eq_left (by omega)]
          have hsub : m + i.val - m = i.val := by omega
          simp only [hsub, Fin.eta]
        rw [hpre, ← hs_t, hsuf]
        exact hstep
      · -- m + m' ≤ (t+1)·macroBound k (M+(t+1))
        have hb1 : m ≤ t * macroBound k (M + (t + 1)) :=
          le_trans hmle (Nat.mul_le_mul (le_refl t) (macroBound_mono (by omega)))
        have hb2 : m' ≤ macroBound k (M + (t + 1)) :=
          le_trans hbound' (macroBound_mono (by omega))
        calc m + m' ≤ t * macroBound k (M + (t + 1)) + macroBound k (M + (t + 1)) :=
              Nat.add_le_add hb1 hb2
          _ = (t + 1) * macroBound k (M + (t + 1)) := by rw [Nat.succ_mul]

/-- **Forward acceptance.** If `N` accepts `x` within `Tn` steps, then
    `singleTapeSim N` accepts `x` within `Tn · macroBound k Tn + 1` steps:
    simulate `N`'s accepting run (`corr_iterate`), then one `halted_of_corr` step lands in
    a halted accepting simulator config; pad via `AcceptsInTime.mono`. -/
theorem acceptsInTime_singleTapeSim_of_acceptsInTime {k : ℕ} (N : NTM k) (hk : 1 ≤ k)
    (x : List Bool) (Tn : ℕ)
    (h : N.AcceptsInTime x Tn) :
    (singleTapeSim N).AcceptsInTime x (Tn * macroBound k Tn + 1) := by
  obtain ⟨chN, hhalt, hacc⟩ := h
  set g : ℕ → Bool := fun i => if hi : i < Tn then chN ⟨i, hi⟩ else false with hg
  obtain ⟨m, M', F, hcorr, _hM', hm⟩ := corr_iterate N hk (corr_init N x) g Tn
  have hgN : (fun i : Fin Tn => g i.val) = chN := by
    funext i; rw [hg]; simp only []; rw [dite_eq_left i.isLt]
  rw [hgN] at hcorr
  -- one halt step lands in a halted, accepting simulator config
  obtain ⟨hhalted, hbit⟩ := halted_of_corr N hcorr hhalt
  -- the accepting config is reached after `m + 1` sim steps
  set sCfg := (singleTapeSim N).trace m (fun i => F i.val) ((singleTapeSim N).initCfg x) with hsCfg
  set F' : ℕ → Bool := fun j => if j < m then F j else false with hF'
  have hcompose : (singleTapeSim N).trace (m + 1) (fun i => F' i.val) ((singleTapeSim N).initCfg x)
      = (singleTapeSim N).trace 1 (fun _ => false) sCfg := by
    rw [(singleTapeSim N).trace_add_fun m 1 F']
    have e1 : (fun i : Fin m => F' i.val) = (fun i : Fin m => F i.val) := by
      funext i; rw [hF']; simp only [i.isLt, ite_true]
    have e2 : (fun i : Fin 1 => F' (m + i.val)) = (fun _ => false) := by
      funext i; rw [hF']; simp only []; rw [ite_eq_right (by omega)]
    rw [e1, e2, ← hsCfg]
  have key : (singleTapeSim N).AcceptsInTime x (m + 1) := by
    refine ⟨fun i => F' i.val, ?_, ?_⟩
    · rw [hcompose]; exact hhalted
    · rw [hcompose]; exact hbit.mpr hacc
  exact NTM.AcceptsInTime.mono (by
    have : Tn * macroBound k (0 + Tn) = Tn * macroBound k Tn := by rw [Nat.zero_add]
    omega) key

/-! ### Reverse direction: arbitrary simulator choices induce an `N`-run

The forward theorems (`corr_iterate`,
`acceptsInTime_singleTapeSim_of_acceptsInTime`) drive the simulator with a
purpose-built choice stream. The surface lemmas also need the converse flow:
an ARBITRARY simulator stream still walks the macro-step structure, because
each macro-step consults its nondeterministic bit only at one decision point
(`macroStep_decision_point_iff`), so `trace_congr_choices` replaces each
arbitrary segment with the constant-choice segment of
`corr_macroStep_explicit`. Crucially the decision positions are closed-form
(`decisionPos` — independent of the run), so the induced `N`-choices can be
read off the stream up front, with no circularity. -/

/-- Micro-step length of the macro-step at materialization level `M` (the
    explicit count in `corr_macroStep_explicit`). -/
def macroLen (k M : ℕ) : ℕ :=
  1 + 3 * k * M + 1 + blockStart k (M + 1) + (3 * k * (M + 1) + 1) + (3 * k * (M + 1) + 1) + 1

/-- Micro-step position of the start of the `t`-th macro-step (cumulative sum
    of the preceding macro-step lengths; the materialization level after `t`
    macro-steps is exactly `t`). -/
def macroPos (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => macroPos k t + macroLen k t

/-- Position of the single decision point (the GATHER-on-`□` COMPUTE sub-step)
    inside the `t`-th macro-step: offset `1 + 3kt` from the macro-step start. -/
def decisionPos (k t : ℕ) : ℕ := macroPos k t + (1 + 3 * k * t)

/-- The `N`-choice stream induced by a simulator choice stream: the bits the
    simulator consults at the (closed-form) decision positions. -/
def inducedChoices (k : ℕ) (ch : ℕ → Bool) : ℕ → Bool := fun t => ch (decisionPos k t)

/-- Each macro-step's length fits in the per-macro-step budget `macroBound`. -/
theorem macroLen_le_macroBound (k M : ℕ) : macroLen k M ≤ macroBound k M := by
  have hbs : blockStart k (M + 1) = 1 + 3 * k * M := by
    simp only [blockStart, blockWidth, Nat.add_sub_cancel]
    rw [Nat.mul_comm M (3 * k)]
  have h3 : 3 * k * (M + 1) = 3 * k * M + 3 * k := by rw [Nat.mul_add, Nat.mul_one]
  have hmb : macroBound k M = 16 * k * M + 16 * k + 16 * M + 16 := by
    unfold macroBound
    rw [Nat.mul_add 16 k 1, Nat.mul_one, Nat.add_mul, Nat.mul_add (16 * k) M 1, Nat.mul_one,
      Nat.mul_add 16 M 1, Nat.mul_one]
    omega
  have hle : 4 * (3 * k * M) ≤ 16 * k * M := by
    calc 4 * (3 * k * M) = 4 * (3 * k) * M := by rw [← Nat.mul_assoc]
      _ ≤ 16 * k * M := Nat.mul_le_mul (by omega) (le_refl M)
  unfold macroLen
  rw [hbs, h3, hmb]
  omega

/-- Macro-step boundaries are monotone in the step index. -/
theorem macroPos_mono (k : ℕ) {t t' : ℕ} (h : t ≤ t') : macroPos k t ≤ macroPos k t' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (Nat.le_add_right _ _)

/-- The macro-step boundary position is bounded by the cumulative budget:
    `macroPos k t ≤ t * macroBound k t`. -/
theorem macroPos_le_mul_macroBound (k t : ℕ) : macroPos k t ≤ t * macroBound k t := by
  induction t with
  | zero => simp [macroPos]
  | succ t ih =>
    have h1 : macroPos k t ≤ t * macroBound k (t + 1) :=
      le_trans ih (Nat.mul_le_mul_left t (macroBound_mono (Nat.le_succ t)))
    have h2 : macroLen k t ≤ macroBound k (t + 1) :=
      le_trans (macroLen_le_macroBound k t) (macroBound_mono (Nat.le_succ t))
    calc macroPos k (t + 1) = macroPos k t + macroLen k t := rfl
      _ ≤ t * macroBound k (t + 1) + macroBound k (t + 1) := Nat.add_le_add h1 h2
      _ = (t + 1) * macroBound k (t + 1) := (Nat.succ_mul t _).symm

/-- The full reverse-simulation budget (`Tn` macro-steps plus the halt step)
    fits under the surface bound `16(k+1)(Tn + n + 1)²` (= `singleTapeSimTime`). -/
theorem mul_macroBound_succ_le (k Tn n : ℕ) :
    Tn * macroBound k Tn + 1 ≤ 16 * (k + 1) * (Tn + n + 1) ^ 2 := by
  have h1 : Tn * macroBound k Tn = 16 * (k + 1) * (Tn * (Tn + 1)) := by
    unfold macroBound
    rw [← Nat.mul_assoc, Nat.mul_comm Tn (16 * (k + 1)), Nat.mul_assoc]
  have hsq : (Tn + 1) ^ 2 ≤ (Tn + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hsq' : (Tn + 1) ^ 2 = Tn * (Tn + 1) + 1 * (Tn + 1) := by
    rw [Nat.pow_succ, Nat.pow_one, Nat.add_mul]
  have hkey : Tn * (Tn + 1) + 1 ≤ (Tn + n + 1) ^ 2 := by omega
  have h2 : 16 * (k + 1) * (Tn * (Tn + 1) + 1) ≤ 16 * (k + 1) * (Tn + n + 1) ^ 2 :=
    Nat.mul_le_mul_left _ hkey
  have h3 : 16 * (k + 1) * (Tn * (Tn + 1) + 1)
      = 16 * (k + 1) * (Tn * (Tn + 1)) + 16 * (k + 1) * 1 := Nat.mul_add _ _ _
  omega

/-- **Segment choice replacement.** Along one macro-step from a corresponding,
    non-halted configuration, an arbitrary choice stream drives the simulator to
    the same configuration as the constant stream feeding the arbitrary stream's
    bit at the macro-step's single decision point (offset `1 + 3kM`). -/
theorem macroStep_choice_replace {k : ℕ} (N : NTM k) (hk : 1 ≤ k) {M : ℕ}
    {c1 : Cfg 1 (SimQ k N.Q)} {c : Cfg k N.Q}
    (hcorr : Corr N M c1 c) (hne : c.state ≠ N.qhalt) (ch : ℕ → Bool) :
    (singleTapeSim N).trace (macroLen k M) (fun i => ch i.val) c1
      = (singleTapeSim N).trace (macroLen k M) (fun _ => ch (1 + 3 * k * M)) c1 := by
  refine (trace_congr_choices N (macroLen k M) (fun _ => ch (1 + 3 * k * M)) ch c1 ?_).symm
  intro i hi hgather hblank
  exact congrArg ch
    ((macroStep_decision_point_iff N hk hcorr hne (ch (1 + 3 * k * M)) i hi).mp
      ⟨hgather, hblank⟩).symm

/-- **Reverse iterated correspondence.** For an ARBITRARY simulator choice
    stream `ch`: as long as `N`'s induced run (`inducedChoices`) has not halted,
    the simulator's configuration at the macro-step boundary `macroPos k t`
    corresponds to `N`'s `t`-step configuration. -/
theorem corr_trace_macroPos {k : ℕ} (N : NTM k) (hk : 1 ≤ k) (ch : ℕ → Bool) (x : List Bool) :
    ∀ t : ℕ,
      (∀ s, s < t →
        (N.trace s (fun i => inducedChoices k ch i.val) (N.initCfg x)).state ≠ N.qhalt) →
      Corr N t
        ((singleTapeSim N).trace (macroPos k t) (fun i => ch i.val)
          ((singleTapeSim N).initCfg x))
        (N.trace t (fun i => inducedChoices k ch i.val) (N.initCfg x)) := by
  intro t
  induction t with
  | zero => exact fun _ => corr_init N x
  | succ t ih =>
    intro hrun
    have hcorr_t := ih (fun s hs => hrun s (Nat.lt_succ_of_lt hs))
    have hne := hrun t (Nat.lt_succ_self t)
    -- sim side: split at `macroPos k t`, replace the segment by the constant choice
    have hsim : (singleTapeSim N).trace (macroPos k (t + 1)) (fun i => ch i.val)
        ((singleTapeSim N).initCfg x)
        = (singleTapeSim N).trace (macroLen k t) (fun _ => ch (decisionPos k t))
            ((singleTapeSim N).trace (macroPos k t) (fun i => ch i.val)
              ((singleTapeSim N).initCfg x)) := by
      rw [show macroPos k (t + 1) = macroPos k t + macroLen k t from rfl,
        (singleTapeSim N).trace_add_fun (macroPos k t) (macroLen k t) ch]
      exact macroStep_choice_replace N hk hcorr_t hne (fun j => ch (macroPos k t + j))
    -- `N` side: the `(t+1)`-step trace is one more step from the `t`-step trace
    have hN : N.trace (t + 1) (fun i => inducedChoices k ch i.val) (N.initCfg x)
        = N.trace 1 (fun _ => inducedChoices k ch t)
            (N.trace t (fun i => inducedChoices k ch i.val) (N.initCfg x)) := by
      have e : (fun i : Fin 1 => inducedChoices k ch (t + i.val))
          = (fun _ => inducedChoices k ch t) := by
        funext i
        obtain rfl : i = 0 := Subsingleton.elim i 0
        rfl
      rw [N.trace_add_fun t 1 (inducedChoices k ch), e]
    rw [hsim, hN]
    exact corr_macroStep_explicit N hk hcorr_t hne (inducedChoices k ch t)

/-- **Reverse halting.** If the `N`-run induced by an arbitrary simulator stream
    `ch` halts within `Tn` steps, the simulator (driven by `ch`) halts within
    `Tn * macroBound k Tn + 1` micro-steps, with its accept bit agreeing with
    `N`'s output bit. This is the engine behind both surface lemmas: it bounds
    EVERY simulator path by the simulated machine's halting bound. -/
theorem halted_singleTapeSim_of_trace_qhalt {k : ℕ} (N : NTM k) (hk : 1 ≤ k) (ch : ℕ → Bool)
    (x : List Bool) (Tn : ℕ)
    (hhalt : (N.trace Tn (fun i => inducedChoices k ch i.val) (N.initCfg x)).state
      = N.qhalt) :
    ∃ m ≤ Tn * macroBound k Tn + 1,
      (singleTapeSim N).halted
        ((singleTapeSim N).trace m (fun i => ch i.val) ((singleTapeSim N).initCfg x)) ∧
      (((singleTapeSim N).trace m (fun i => ch i.val)
          ((singleTapeSim N).initCfg x)).output.cells 1 = Γ.one
        ↔ (N.trace Tn (fun i => inducedChoices k ch i.val)
            (N.initCfg x)).output.cells 1 = Γ.one) := by
  classical
  -- the first time `N`'s induced run halts
  have hex : ∃ t, (N.trace t (fun i => inducedChoices k ch i.val) (N.initCfg x)).state
      = N.qhalt := ⟨Tn, hhalt⟩
  have ht0le : Nat.find hex ≤ Tn := Nat.find_min' hex hhalt
  have hth := Nat.find_spec hex
  have hrun : ∀ s, s < Nat.find hex →
      (N.trace s (fun i => inducedChoices k ch i.val) (N.initCfg x)).state ≠ N.qhalt :=
    fun s hs => Nat.find_min hex hs
  have hcorr := corr_trace_macroPos N hk ch x (Nat.find hex) hrun
  -- one halt step lands the simulator in `SimQ.halt` (choice-irrelevant: the
  -- simulator is parked at a `run` state, never a GATHER decision point)
  obtain ⟨hhalted, hbit⟩ := halted_of_corr N hcorr hth
  have hstep : (singleTapeSim N).trace 1 (fun j : Fin 1 => ch (macroPos k (Nat.find hex) + j.val))
      ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
        ((singleTapeSim N).initCfg x))
      = (singleTapeSim N).trace 1 (fun _ => false)
          ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
            ((singleTapeSim N).initCfg x)) := by
    refine (trace_congr_choices N 1 (fun _ => false)
      (fun j => ch (macroPos k (Nat.find hex) + j)) _ ?_).symm
    intro i hi hgather _
    obtain rfl : i = 0 := by omega
    obtain ⟨d, hd⟩ := hgather
    have hd' : ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
        ((singleTapeSim N).initCfg x)).state = SimQ.gather d := hd
    rw [hcorr.state] at hd'
    exact absurd hd'.symm (by simp [SimQ.run, SimQ.gather, reduceCtorEq])
  have hsplit : (singleTapeSim N).trace (macroPos k (Nat.find hex) + 1) (fun i => ch i.val)
      ((singleTapeSim N).initCfg x)
      = (singleTapeSim N).trace 1 (fun _ => false)
          ((singleTapeSim N).trace (macroPos k (Nat.find hex)) (fun i => ch i.val)
            ((singleTapeSim N).initCfg x)) := by
    rw [(singleTapeSim N).trace_add_fun (macroPos k (Nat.find hex)) 1 ch]
    exact hstep
  -- `N` is frozen between `Nat.find hex` and `Tn`
  have hfreeze : N.trace Tn (fun i => inducedChoices k ch i.val) (N.initCfg x)
      = N.trace (Nat.find hex) (fun i => inducedChoices k ch i.val) (N.initCfg x) :=
    N.trace_mono ht0le (fun i => rfl) hth
  refine ⟨macroPos k (Nat.find hex) + 1, ?_, ?_, ?_⟩
  · have h1 := macroPos_le_mul_macroBound k (Nat.find hex)
    have h2 : Nat.find hex * macroBound k (Nat.find hex) ≤ Tn * macroBound k Tn :=
      Nat.mul_le_mul ht0le (macroBound_mono ht0le)
    omega
  · rw [hsplit]; exact hhalted
  · rw [hsplit, hfreeze]; exact hbit

end NTM.SingleTape

end Complexity
