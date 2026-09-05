/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Registers.RegisterOps

/-!
# Publishing a work-tape bit on the output tape

Every branching combinator in the library — `TM.ifTM` and `TM.loopTM` alike — decides on the
*real output tape's* verdict cell. A machine that keeps its intermediate results on work tapes
therefore has no way to branch on them, and the library has no subroutine that moves a bit from a
work tape to the output.

`TM.writeOutputBitTM` is that subroutine, and it is as small as it can be: a single transition
that writes the symbol under a designated work head onto the output tape, leaving every tape
otherwise exactly as it was. Parked tapes stay parked, so it composes with everything.

## Main results

- `TM.writeOutputBitTM` — publish a work-tape bit on the output tape
- `TM.writeOutputBitTM_hoareTime_frame` — its contract, with a full external frame
- `TM.writeOutputBitTM_clears` — pointed at a blank tape it clears the output, which is what the
  wipe subroutine requires
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Publish the symbol under work head `vIdx` on the output tape, in one transition. -/
def writeOutputBitTM (vIdx : Fin n) : TM n where
  Q := BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ iHead wHeads oHead =>
    (.done, fun i => readBackWrite (wHeads i), readBackWrite (wHeads vIdx),
     idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

/-- **Publishing a bit.** One transition writes the symbol under work head `vIdx` at the output
head, leaving the input and every work tape exactly as they were and moving no head. -/
theorem writeOutputBitTM_hoareTime_frame (vIdx : Fin n)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i)) (hout : Parked out₀) :
    (writeOutputBitTM vIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧
        out = out₀.write (readBackWrite ((work₀ vIdx).read)).toΓ)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨⟨BumpPhase.done, inp, work,
      out.write (readBackWrite ((work vIdx).read)).toΓ⟩, 1, le_rfl, ?_, rfl, rfl, rfl, rfl⟩
  refine TM.reachesIn.step ?_ TM.reachesIn.zero
  simp only [TM.step, writeOutputBitTM, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · show (out.write (readBackWrite ((work vIdx).read)).toΓ).move (idleDir out.read) = _
    have hne : out.read ≠ Γ.start := hout.2 out.head hout.1
    rw [idleDir, ite_eq_right hne]
    rfl


/-- **Clearing the output needs no new machine.** Pointing the publisher at a work tape whose head
reads blank writes a blank to the output; if the output was only ever written at its verdict cell,
that restores it to the parked blank tape the wipe subroutine demands. -/
theorem writeOutputBitTM_clears (vIdx : Fin n)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i)) (hout : Parked out₀)
    (hblank : (work₀ vIdx).read = Γ.blank)
    (hhead : out₀.head = 1)
    (hcells : ∀ j, j ≠ 1 → out₀.cells j = (Tape.init ([] : List Γ)).cells j) :
    (writeOutputBitTM vIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧
        out = (Tape.init ([] : List Γ)).move Dir3.right)
      1 := by
  refine (writeOutputBitTM_hoareTime_frame vIdx inp₀ work₀ out₀ hinp hwork hout).strengthen_post ?_
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, rfl, ?_⟩
  rw [hblank]
  have hne0 : ¬ (out₀.head = 0) := by omega
  refine Tape.ext ?_ ?_
  · rw [Tape.write_head, hhead]
    rfl
  · funext j
    rw [Tape.move_cells]
    simp only [Tape.write, ite_eq_right hne0]
    rw [show Function.update out₀.cells out₀.head (readBackWrite Γ.blank).toΓ
        = Function.update out₀.cells 1 (readBackWrite Γ.blank).toΓ from by rw [hhead]]
    by_cases hj : j = 1
    · subst hj
      rw [Function.update_self]
      simp [Tape.init, readBackWrite]
    · rw [Function.update_of_ne hj]
      exact hcells j hj

end TM

end Complexity
