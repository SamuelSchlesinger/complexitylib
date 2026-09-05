/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute

/-!
# The sentinel step moves heads and nothing else

Every machine begins with all heads on `▷`, and `TM.δ_right_of_start` forces that first
transition to move each of them right. Since cell zero is immutable, the transition's writes are
no-ops, so the step's whole effect is to move every head from cell zero to cell one — the control
state it lands in, `TM.retargetInputStartState`, being determined by the machine alone.

`TM.startedCfg` records this for the *canonical* initial configuration, where every work tape is
blank. But the reads are `▷` on every tape whatever the tapes hold beyond cell zero, so the same
description holds from any configuration with its heads at zero. That generality is what lets a
composed machine hand a simulation an already-loaded work tape — a counter, say — and still enter
it at the state `TM.retargetInputStarted` expects.

## Main results

- `TM.step_of_heads_zero` — the sentinel step from any all-heads-at-zero configuration
- `TM.startedTM` — a machine resumed after that step, ready to be a stage of a composed machine
- `TM.reachesIn_of_startedTM`, `TM.reachesIn_startedTM` — the two machines reach the same
  configurations
- `TM.reachesIn_succ_of_startedTM` — a run of the resumed machine is a run of the original
- `TM.step_input_cells`, `TM.reachesIn_input_cells` — the input tape is read-only
- `TM.startInvariant_reachesIn` — the left-marker invariant survives a whole run
- `TM.step_work_cells_ne` — a step writes only under its head
- `TM.head_transitionTape_le_max`, `TM.head_transitionInput_le_max` — a phase transition never
  pushes a head outward
- `TM.startInvariant_transitionTape`, `TM.startInvariant_transitionInput` — and preserves the
  left-marker invariant
-/

@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- A write at cell zero is a no-op, so writing and moving there is just moving. -/
theorem writeAndMove_of_head_zero (t : Tape) (s : Γ) (d : Dir3) (h : t.head = 0) :
    t.writeAndMove s d = t.move d := by
  simp only [Tape.writeAndMove, Tape.write, h, ↓reduceIte]

/-- **The sentinel step, from any configuration whose heads are at cell zero.** Only the heads
move; every tape keeps its contents, and the state reached is the machine's own
`TM.retargetInputStartState`. -/
theorem step_of_heads_zero (M : TM k) (c : Cfg k M.Q)
    (hstate : c.state = M.qstart) (hne : M.qstart ≠ M.qhalt)
    (hin : c.input.head = 0) (hwork : ∀ i, (c.work i).head = 0) (hout : c.output.head = 0)
    (hin0 : c.input.cells 0 = Γ.start) (hwork0 : ∀ i, (c.work i).cells 0 = Γ.start)
    (hout0 : c.output.cells 0 = Γ.start) :
    M.step c = some ⟨retargetInputStartState M, c.input.move Dir3.right,
      fun i => (c.work i).move Dir3.right, c.output.move Dir3.right⟩ := by
  have hri : c.input.read = Γ.start := by rw [Tape.read, hin]; exact hin0
  have hrw : ∀ i, (c.work i).read = Γ.start := by
    intro i; rw [Tape.read, hwork i]; exact hwork0 i
  have hro : c.output.read = Γ.start := by rw [Tape.read, hout]; exact hout0
  have hdirs := M.δ_right_of_start M.qstart Γ.start (fun _ => Γ.start) Γ.start
  simp only [TM.step, hstate, ite_eq_right hne, hri, hro, funext hrw]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · show (c.input.move _) = _
    rw [hdirs.1 rfl]
  · funext i
    show (c.work i).writeAndMove _ _ = _
    rw [writeAndMove_of_head_zero _ _ _ (hwork i), hdirs.2.1 i rfl]
  · show c.output.writeAndMove _ _ = _
    rw [writeAndMove_of_head_zero _ _ _ hout, hdirs.2.2 rfl]


/-- **A machine resumed after its sentinel step.** Same transition function, same halt state;
only the start state is moved forward to where the compulsory `▷`-step lands. This is the form a
machine has to take to be run as a stage of a composed machine, which can never hand it a head at
cell zero.

Unlike `TM.retargetInputStarted` this leaves the input tape alone. That is the right choice when
the composed machine's own input tape already carries what the stage should read: it is parked at
cell one, which is exactly where the sentinel step would have left it. -/
def startedTM (M : TM k) : TM k :=
  { M with
    qstart := if M.qstart = M.qhalt then M.qhalt
      else (M.δ M.qstart Γ.start (fun _ => Γ.start) Γ.start).1 }

@[simp] theorem startedTM_qhalt (M : TM k) : (startedTM M).qhalt = M.qhalt := rfl

/-- Resuming changes no transition, so the two machines step identically. -/
@[simp] theorem startedTM_step (M : TM k) (c : Cfg k M.Q) :
    (startedTM M).step c = M.step c := rfl

/-- …and therefore reach exactly the same configurations. -/
theorem reachesIn_of_startedTM (M : TM k) {t : ℕ} {c c' : Cfg k (startedTM M).Q}
    (h : (startedTM M).reachesIn t c c') : M.reachesIn t c c' := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step hs ih

/-- …and conversely. -/
theorem reachesIn_startedTM (M : TM k) {t : ℕ} {c c' : Cfg k M.Q}
    (h : M.reachesIn t c c') : (startedTM M).reachesIn t c c' := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step hs ih

/-- **What the resumed machine's start state is worth.** A configuration with every head at cell
zero steps, in one move, to the resumed machine's own start configuration on the same tapes with
every head at cell one. So a run of the resumed machine from there is a run of the original, one
step in — with whatever the tapes were carrying still on them. -/
theorem reachesIn_succ_of_startedTM (M : TM k) (c : Cfg k M.Q)
    (hstate : c.state = M.qstart) (hne : M.qstart ≠ M.qhalt)
    (hin : c.input.head = 0) (hwork : ∀ i, (c.work i).head = 0) (hout : c.output.head = 0)
    (hin0 : c.input.cells 0 = Γ.start) (hwork0 : ∀ i, (c.work i).cells 0 = Γ.start)
    (hout0 : c.output.cells 0 = Γ.start)
    {t : ℕ} {c' : Cfg k M.Q}
    (hreach : (startedTM M).reachesIn t
      ⟨(startedTM M).qstart, c.input.move Dir3.right,
        fun i => (c.work i).move Dir3.right, c.output.move Dir3.right⟩ c') :
    M.reachesIn (t + 1) c c' := by
  have hq : (startedTM M).qstart = retargetInputStartState M := by
    show (if M.qstart = M.qhalt then M.qhalt else retargetInputStartState M) = _
    rw [ite_eq_right hne]
  have hstep : M.step c = some ⟨(startedTM M).qstart, c.input.move Dir3.right,
      fun i => (c.work i).move Dir3.right, c.output.move Dir3.right⟩ := by
    rw [hq]
    exact step_of_heads_zero M c hstate hne hin hwork hout hin0 hwork0 hout0
  exact .step hstep (reachesIn_of_startedTM M hreach)


/-- **The input tape is read-only.** A transition moves its head and nothing else, so its
contents survive any run — which is what lets a stage rewind the real input and hand the next
stage the tape it started with. -/
theorem step_input_cells (M : TM k) {c c' : Cfg k M.Q} (h : M.step c = some c') :
    c'.input.cells = c.input.cells := by
  simp only [TM.step] at h
  split at h
  · exact absurd h (by simp)
  · rw [← Option.some_inj.mp h]
    show (c.input.move _).cells = _
    rw [Tape.move_cells]

/-- …and therefore across a whole run. -/
theorem reachesIn_input_cells (M : TM k) {t : ℕ} {c c' : Cfg k M.Q}
    (h : M.reachesIn t c c') : c'.input.cells = c.input.cells := by
  induction h with
  | zero => rfl
  | step hs _ ih => exact ih.trans (step_input_cells M hs)

/-- **The left-marker invariant survives a whole run**, not just one step. Every transition
writes symbols drawn from `Γw`, and cell zero is immutable, so a machine can neither erase a
marker nor create one. -/
theorem startInvariant_reachesIn (tm : TM n) {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') :
    c.input.StartInvariant → (∀ i, (c.work i).StartInvariant) → c.output.StartInvariant →
    c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
      c'.output.StartInvariant := by
  induction h with
  | zero => exact fun a b c => ⟨a, b, c⟩
  | step hstep _ ih =>
      intro hi hw ho
      obtain ⟨h1, h2, h3⟩ := Tape.StartInvariant.step _ hstep hi hw ho
      exact ih h1 h2 h3


/-- **A step writes only under the head.** Every other cell of a work tape is left alone. -/
theorem step_work_cells_ne (M : TM k) {c c' : Cfg k M.Q} (h : M.step c = some c')
    (j : Fin k) (i : ℕ) (hi : i ≠ (c.work j).head) :
    (c'.work j).cells i = (c.work j).cells i := by
  simp only [TM.step] at h
  split at h
  · exact absurd h (by simp)
  · rw [← Option.some_inj.mp h]
    show ((c.work j).writeAndMove _ _).cells i = _
    rw [Tape.writeAndMove, Tape.move_cells, Tape.write]
    split
    · rfl
    · exact Function.update_of_ne hi _ _

/-- **A phase transition never pushes a head outward.** On a tape carrying its marker only at
cell zero it moves a head sitting on the marker to cell one and leaves every other head alone, so
the head ends at `max head 1`. The library's bound of `head + 1` is too weak to survive a loop. -/
theorem head_transitionTape_le_max {t : Tape} (h : Tape.StartInvariant t) :
    (transitionTape t).head ≤ max t.head 1 := by
  by_cases hh : t.head = 0
  · have hread : t.read = Γ.start := by
      show t.cells t.head = Γ.start
      rw [hh]; exact h.1
    unfold transitionTape Tape.writeAndMove
    simp only [Tape.write, hh, ↓reduceIte, hread, idleDir, Tape.move]
    omega
  · have hread : t.read ≠ Γ.start := h.2 t.head (by omega)
    rw [transitionTape_eq_self hread]
    omega

/-- The same for the input tape, which a transition only moves. -/
theorem head_transitionInput_le_max {t : Tape} (h : Tape.StartInvariant t) :
    (transitionInput t).head ≤ max t.head 1 := by
  by_cases hh : t.head = 0
  · have hread : t.read = Γ.start := by
      show t.cells t.head = Γ.start
      rw [hh]; exact h.1
    unfold transitionInput
    simp only [hread, idleDir, ↓reduceIte, Tape.move, hh]
    omega
  · have hread : t.read ≠ Γ.start := h.2 t.head (by omega)
    rw [transitionInput_eq_self hread]
    omega

/-- A phase transition preserves the left-marker invariant. -/
theorem startInvariant_transitionTape {t : Tape} (h : Tape.StartInvariant t) :
    Tape.StartInvariant (transitionTape t) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [transitionTape_cells t (fun i hi => h.2 i hi)]; exact h.1
  · rw [transitionTape_cells t (fun i hi => h.2 i hi)]; exact h.2 j hj

/-- …and so does the input tape's. -/
theorem startInvariant_transitionInput {t : Tape} (h : Tape.StartInvariant t) :
    Tape.StartInvariant (transitionInput t) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [transitionInput_cells]; exact h.1
  · rw [transitionInput_cells]; exact h.2 j hj


/-- **Runs from the same configuration are prefixes of one another.** A deterministic machine has
only one future, so a shorter run is an initial segment of a longer one. This is what lets a loop's
space argument work one iteration at a time: any configuration a run passes through either lies
inside the current iteration or is reached *through* the next iteration's start. -/
theorem reachesIn_prefix (M : TM k) : ∀ {t t' : ℕ} {c d d' : Cfg k M.Q},
    M.reachesIn t c d → M.reachesIn t' c d' → t ≤ t' → M.reachesIn (t' - t) d d' := by
  intro t
  induction t with
  | zero =>
      intro t' c d d' h h' _
      cases h
      simpa using h'
  | succ t ih =>
      intro t' c d d' h h' hle
      obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
      cases h with
      | step hs hr =>
          cases h' with
          | step hs' hr' =>
              have heq := Option.some_inj.mp (hs.symm.trans hs')
              subst heq
              simpa using ih hr hr' (by omega)

end TM

end Complexity
