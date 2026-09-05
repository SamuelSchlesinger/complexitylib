/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine

/-!
# Padding a 0-work-tape NTM with a dummy work tape

`NTM.pad0` turns an `NTM 0` into an `NTM 1` deciding the same language in the
same time bound: the added work tape is never used. The dummy head steps right
off `▷` on its first move (respecting the `δ_right_of_start` discipline) and
then parks at cell 1, writing `□` over the `□` already there, so the dummy
tape's cells never change.

This closes the `k = 0` case of the single-tape reduction
(`NTM.exists_singleTape_decidesInTime`): the simulation machinery requires at least
one work tape, while a padded machine *is* already single-work-tape.
-/


@[expose] public section

namespace Complexity

namespace NTM

/-- Pad a 0-work-tape machine with one never-used work tape. The dummy tape's
    action: step right off `▷`, otherwise stay put and write `□` (over the `□`
    already under the head). -/
def pad0 (N : NTM 0) : NTM 1 where
  Q := N.Q
  qstart := N.qstart
  qhalt := N.qhalt
  δ := fun b q si sw so =>
    let r := N.δ b q si (fun i => i.elim0) so
    (r.1, fun _ => Γw.blank, r.2.2.1, r.2.2.2.1,
      fun i => if sw i = Γ.start then Dir3.right else Dir3.stay, r.2.2.2.2.2)
  δ_right_of_start := fun b q iHead wHeads oHead =>
    ⟨(N.δ_right_of_start b q iHead (fun i => i.elim0) oHead).1,
     fun i hi => by simp [hi],
     (N.δ_right_of_start b q iHead (fun i => i.elim0) oHead).2.2⟩

/-- One dummy-tape action keeps the cells at their initial value and the head
    at cell 0 or 1: at cell 0 the write is a structural no-op and the head
    steps right; at cell 1 it writes `□` over `□` and stays. -/
private theorem pad0_dummy_step (w : Tape) (hc : w.cells = (Tape.init []).cells)
    (hh : w.head ≤ 1) :
    (w.writeAndMove (Γw.blank : Γ)
        (if w.read = Γ.start then Dir3.right else Dir3.stay)).cells
        = (Tape.init []).cells
      ∧ (w.writeAndMove (Γw.blank : Γ)
          (if w.read = Γ.start then Dir3.right else Dir3.stay)).head ≤ 1 := by
  have hread : w.read = (Tape.init []).cells w.head := by rw [Tape.read, hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with h0 | h1
  · -- head at cell 0: reading `▷`, write is a no-op, move right to cell 1
    have hr : w.read = Γ.start := by rw [hread, h0]; rfl
    rw [hr, ite_eq_left rfl]
    show ((w.write _).move .right).cells = _ ∧ ((w.write _).move .right).head ≤ 1
    rw [Tape.write, ite_eq_left h0]
    exact ⟨hc, by rw [Tape.move, h0]⟩
  · -- head at cell 1: reading `□`, write `□` over `□`, stay
    have hr : w.read = Γ.blank := by rw [hread, h1]; rfl
    rw [hr, ite_eq_right (by decide : ¬ Γ.blank = Γ.start)]
    show ((w.write _).move .stay).cells = _ ∧ ((w.write _).move .stay).head ≤ 1
    rw [Tape.move, Tape.write, ite_eq_right (by rw [h1]; decide : ¬ w.head = 0)]
    constructor
    · show Function.update w.cells w.head (Γw.blank : Γ) = (Tape.init []).cells
      have hv : (Γw.blank : Γ) = w.cells w.head := by
        rw [Tape.read] at hr; rw [hr]; rfl
      rw [hv, Function.update_eq_self, hc]
    · show w.head ≤ 1
      exact hh

/-- The padded transition function, in applied form: the original's action on
    state/input/output, the dummy action on the work tape. -/
private theorem pad0_δ_apply (N : NTM 0) (b : Bool) (q : N.Q) (si : Γ)
    (sw : Fin 1 → Γ) (so : Γ) :
    (pad0 N).δ b q si sw so
      = ((N.δ b q si (fun i => i.elim0) so).1, fun _ => Γw.blank,
         (N.δ b q si (fun i => i.elim0) so).2.2.1,
         (N.δ b q si (fun i => i.elim0) so).2.2.2.1,
         fun i => if sw i = Γ.start then Dir3.right else Dir3.stay,
         (N.δ b q si (fun i => i.elim0) so).2.2.2.2.2) := rfl

/-- **Trace correspondence.** The padded machine's run tracks the original's
    component-wise; the dummy work tape keeps its initial cells with the head
    parked at cell 0 or 1. -/
theorem pad0_trace (N : NTM 0) :
    ∀ (T : ℕ) (choices : Fin T → Bool) (c : Cfg 0 N.Q) (c1 : Cfg 1 N.Q),
      c1.state = c.state → c1.input = c.input → c1.output = c.output →
      (c1.work 0).cells = (Tape.init []).cells → (c1.work 0).head ≤ 1 →
      ((pad0 N).trace T choices c1).state = (N.trace T choices c).state
        ∧ ((pad0 N).trace T choices c1).input = (N.trace T choices c).input
        ∧ ((pad0 N).trace T choices c1).output = (N.trace T choices c).output := by
  intro T
  induction T with
  | zero => exact fun _ _ _ hs hi ho _ _ => ⟨hs, hi, ho⟩
  | succ T ih =>
    intro choices c c1 hs hi ho hwc hwh
    by_cases hh : c.state = N.qhalt
    · -- both machines are halted: traces freeze
      have hh1 : (pad0 N).halted c1 := by show c1.state = N.qhalt; rw [hs]; exact hh
      rw [(pad0 N).trace_halted (T + 1) choices hh1, N.trace_halted (T + 1) choices hh]
      exact ⟨hs, hi, ho⟩
    · -- one step, then the inductive hypothesis
      have hvec : (fun i : Fin 0 => (c.work i).read) = (fun i => i.elim0) :=
        funext fun i => i.elim0
      dsimp only [NTM.trace, pad0]
      simp only [hh, ite_false]
      split
      · -- the `pad0` halt test cannot fire: `c.state ≠ qhalt`
        next hcontra => exact absurd (hs.symm.trans hcontra) hh
      · rw [hs, hi, ho, hvec]
        refine ih _ _ _ ?_ ?_ ?_ ?_ ?_
        · rfl
        · rfl
        · rfl
        · exact (pad0_dummy_step (c1.work 0) hwc hwh).1
        · exact (pad0_dummy_step (c1.work 0) hwc hwh).2

/-- The trace correspondence at the initial configurations. -/
theorem pad0_trace_init (N : NTM 0) (x : List Bool) (T : ℕ) (choices : Fin T → Bool) :
    ((pad0 N).trace T choices ((pad0 N).initCfg x)).state
        = (N.trace T choices (N.initCfg x)).state
      ∧ ((pad0 N).trace T choices ((pad0 N).initCfg x)).input
        = (N.trace T choices (N.initCfg x)).input
      ∧ ((pad0 N).trace T choices ((pad0 N).initCfg x)).output
        = (N.trace T choices (N.initCfg x)).output :=
  pad0_trace N T choices (N.initCfg x) ((pad0 N).initCfg x) rfl rfl rfl rfl (Nat.zero_le 1)

/-- Padding preserves the all-paths halting bound. -/
theorem pad0_allPathsHaltIn {N : NTM 0} {T : ℕ → ℕ} (h : N.AllPathsHaltIn T) :
    (pad0 N).AllPathsHaltIn T := fun x choices => by
  show ((pad0 N).trace (T x.length) choices ((pad0 N).initCfg x)).state = N.qhalt
  rw [(pad0_trace_init N x (T x.length) choices).1]
  exact h x choices

/-- Padding preserves timed acceptance, in both directions. -/
theorem pad0_acceptsInTime_iff (N : NTM 0) (x : List Bool) (Tn : ℕ) :
    (pad0 N).AcceptsInTime x Tn ↔ N.AcceptsInTime x Tn := by
  constructor
  · rintro ⟨choices, hhalt, hout⟩
    obtain ⟨hs, _, ho⟩ := pad0_trace_init N x Tn choices
    refine ⟨choices, ?_, ?_⟩
    · show (N.trace Tn choices (N.initCfg x)).state = N.qhalt
      rw [← hs]; exact hhalt
    · rw [← ho]; exact hout
  · rintro ⟨choices, hhalt, hout⟩
    obtain ⟨hs, _, ho⟩ := pad0_trace_init N x Tn choices
    refine ⟨choices, ?_, ?_⟩
    · show ((pad0 N).trace Tn choices ((pad0 N).initCfg x)).state = N.qhalt
      rw [hs]; exact hhalt
    · rw [ho]; exact hout

/-- **Padding preserves deciding.** A 0-work-tape decider yields a 1-work-tape
    decider for the same language in the same time bound. -/
theorem pad0_decidesInTime {L : Language} {N : NTM 0} {T : ℕ → ℕ}
    (hdec : N.DecidesInTime L T) : (pad0 N).DecidesInTime L T :=
  ⟨pad0_allPathsHaltIn hdec.1,
   fun x => (hdec.2 x).trans (pad0_acceptsInTime_iff N x (T x.length)).symm⟩

end NTM

end Complexity
