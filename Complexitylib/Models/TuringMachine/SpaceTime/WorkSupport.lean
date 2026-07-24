/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Bounded support of work tapes

A machine whose work head stays at or below `bound` cannot change cells
strictly above `bound`. This module packages that elementary fact for cleanup
arguments that must restore an initially blank work tape exactly.
-/

namespace Complexity

namespace Tape

/-- Every cell strictly above `bound` is blank. -/
def BlankAfter (tape : Tape) (bound : ℕ) : Prop :=
  ∀ index, bound < index → tape.cells index = Γ.blank

/-- A canonical blank tape has blank support above every bound. -/
theorem BlankAfter.init_nil (bound : ℕ) :
    (Tape.init []).BlankAfter bound := by
  intro index hindex
  simp [Tape.init]
  omega

/-- Canonical binary contents are blank above any bound covering their bit
length. -/
theorem HasBinaryContent.blankAfter_of_length_le
    {tape : Tape} {bits : List Bool} {bound : ℕ}
    (hcontent : tape.HasBinaryContent bits) (hlength : bits.length ≤ bound) :
    tape.BlankAfter bound := by
  intro index hindex
  let offset := index - 1
  have hindexEq : index = offset + 1 := by
    dsimp only [offset]
    omega
  rw [hindexEq]
  exact hcontent.2 offset (by omega)

private theorem BlankAfter.writeAndMove_of_head_le
    {tape : Tape} {bound : ℕ} (hblank : tape.BlankAfter bound)
    (hhead : tape.head ≤ bound) (symbol : Γ) (direction : Dir3) :
    (tape.writeAndMove symbol direction).BlankAfter bound := by
  intro index hindex
  have hne : index ≠ tape.head := by omega
  rw [Tape.writeAndMove, Tape.move_cells, Tape.write]
  split
  · exact hblank index hindex
  · change Function.update tape.cells tape.head symbol index = Γ.blank
    rw [Function.update_of_ne hne]
    exact hblank index hindex

end Tape

namespace TM

/-- One machine step preserves blank support above any bound that covers the
current target-work head. -/
private theorem work_blankAfter_step {tm : TM n} {before after : Cfg n tm.Q}
    (idx : Fin n) (bound : ℕ)
    (hblank : (before.work idx).BlankAfter bound)
    (hhead : (before.work idx).head ≤ bound)
    (hstep : tm.step before = some after) :
    (after.work idx).BlankAfter bound := by
  have hne := state_ne_qhalt_of_step hstep
  generalize htransition :
      tm.δ before.state before.input.read (fun i => (before.work i).read)
        before.output.read = transition at hstep
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs, outputDir⟩ :=
    transition
  simp only [TM.step, hne, ↓reduceIte, htransition,
    Option.some.injEq] at hstep
  subst after
  exact hblank.writeAndMove_of_head_le hhead _ _

/-- A complete run preserves an initially blank suffix when every prefix
configuration keeps the selected work head inside the same bound. -/
theorem work_blankAfter_reachesIn {tm : TM n}
    {time inputLength bound : ℕ} {start done : Cfg n tm.Q}
    (idx : Fin n) (hstart : (start.work idx).BlankAfter bound)
    (hreach : tm.reachesIn time start done)
    (hprefix : ∀ elapsed cfg, elapsed ≤ time →
      tm.reachesIn elapsed start cfg →
      cfg.WithinAuxSpace inputLength bound) :
    (done.work idx).BlankAfter bound := by
  induction hreach with
  | zero => exact hstart
  | @step before middle restTime final hstep hrest ih =>
      have hspaceStart := hprefix 0 before (by omega) .zero
      have hmiddle := work_blankAfter_step idx bound hstart
        (hspaceStart.1 idx) hstep
      apply ih hmiddle
      intro elapsed cfg helapsed hmiddleReach
      apply hprefix (elapsed + 1) cfg (by omega)
      exact TM.reachesIn.step hstep hmiddleReach

end TM

end Complexity
