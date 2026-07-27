/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine

/-!
# Output-frontier invariants — proof internals

This module records the blank-suffix invariant of a one-way output tape. An
initial output tape is blank strictly beyond its head, and a transducer step
preserves that property because its output head never moves left.
-/

@[expose] public section

namespace Complexity

namespace Tape

/-- Every cell strictly beyond the tape head is blank. For a one-way output
tape, the head is therefore a frontier beyond which no output has been
written. -/
def BlankAfterHead (t : Tape) : Prop :=
  ∀ j, t.head < j → t.cells j = Γ.blank

/-- The empty initialized tape is blank beyond its initial head. -/
theorem BlankAfterHead.init_nil : (Tape.init []).BlankAfterHead := by
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact Tape.init_nil_cells_succ i

/-- Writing at the current head and then moving right or staying put
preserves the blank suffix beyond the head. -/
theorem BlankAfterHead.writeAndMove {t : Tape} (h : t.BlankAfterHead)
    (s : Γ) (d : Dir3) (hd : d ≠ Dir3.left) :
    (t.writeAndMove s d).BlankAfterHead := by
  cases d with
  | left => exact (hd rfl).elim
  | right =>
      intro j hj
      simp only [Tape.writeAndMove, Tape.move, Tape.write_head] at hj ⊢
      simp only [Tape.write]
      split
      · exact h j (by omega)
      · change Function.update t.cells t.head s j = Γ.blank
        rw [Function.update_of_ne (by omega)]
        exact h j (by omega)
  | stay =>
      intro j hj
      simp only [Tape.writeAndMove, Tape.move, Tape.write_head] at hj ⊢
      simp only [Tape.write]
      split
      · exact h j hj
      · change Function.update t.cells t.head s j = Γ.blank
        rw [Function.update_of_ne (by omega)]
        exact h j hj

end Tape

namespace TM

variable {n : ℕ}

/-- The output tape of an initial configuration is blank beyond its head. -/
theorem initCfg_output_blankAfterHead (tm : TM n) (x : List Bool) :
    (tm.initCfg x).output.BlankAfterHead :=
  Tape.BlankAfterHead.init_nil

/-- One step of a transducer preserves the blank output suffix. -/
theorem IsTransducer.output_blankAfterHead_step {tm : TM n}
    (htrans : tm.IsTransducer) {c c' : Cfg n tm.Q}
    (hblank : c.output.BlankAfterHead) (hstep : tm.step c = some c') :
    c'.output.BlankAfterHead := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    exact hblank.writeAndMove _ _
      (htrans c.state c.input.read (fun i => (c.work i).read) c.output.read)

/-- Exact-step reachability from a configuration with a blank output suffix
preserves that suffix for a transducer. -/
theorem IsTransducer.output_blankAfterHead_reachesIn {tm : TM n}
    (htrans : tm.IsTransducer) {t : ℕ} {c c' : Cfg n tm.Q}
    (hreach : tm.reachesIn t c c') (hblank : c.output.BlankAfterHead) :
    c'.output.BlankAfterHead := by
  induction hreach with
  | zero => exact hblank
  | step hstep _ ih =>
      exact ih (htrans.output_blankAfterHead_step hblank hstep)

/-- Reachability from a configuration with a blank output suffix preserves
that suffix for a transducer. -/
theorem IsTransducer.output_blankAfterHead_reaches {tm : TM n}
    (htrans : tm.IsTransducer) {c c' : Cfg n tm.Q}
    (hreach : tm.reaches c c') (hblank : c.output.BlankAfterHead) :
    c'.output.BlankAfterHead := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact hblank
  | head hstep _ ih =>
      exact ih (htrans.output_blankAfterHead_step hblank hstep)

/-- Every output tape reachable in an exact number of steps from an initial
configuration of a transducer is blank beyond its head. -/
theorem IsTransducer.initCfg_output_blankAfterHead_reachesIn {tm : TM n}
    (htrans : tm.IsTransducer) {x : List Bool} {t : ℕ} {c : Cfg n tm.Q}
    (hreach : tm.reachesIn t (tm.initCfg x) c) :
    c.output.BlankAfterHead :=
  htrans.output_blankAfterHead_reachesIn hreach (initCfg_output_blankAfterHead tm x)

/-- Every output tape reachable from an initial configuration of a
transducer is blank beyond its head. -/
theorem IsTransducer.initCfg_output_blankAfterHead_reaches {tm : TM n}
    (htrans : tm.IsTransducer) {x : List Bool} {c : Cfg n tm.Q}
    (hreach : tm.reaches (tm.initCfg x) c) :
    c.output.BlankAfterHead :=
  htrans.output_blankAfterHead_reaches hreach (initCfg_output_blankAfterHead tm x)

end TM

end Complexity
