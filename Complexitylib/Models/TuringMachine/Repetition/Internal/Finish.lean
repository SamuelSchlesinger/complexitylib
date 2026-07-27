/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Repetition.Internal

/-!
# Setup and finish phases for fixed-time repetition

Correctness lemmas for the zero-time setup path and the final majority-writing
transition of `NTM.repeatAtTime`.
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- For `T = 0`, the second setup transition enters rewind immediately. Trial
zero is the exact source initial configuration, inactive banks and the real
output remain parked, and all tape start invariants hold. -/
theorem repeatAtTime_begin_zero_simulates (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (choice : Fin 1 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    let votes : Fin k → Bool := fun _ => false
    let C := (repeatAtTime tm k 0).trace 1 choice (repeatParkedCfg tm k 0 x)
    C.state = RepeatQ.rewind j ⟨0, by omega⟩ tm.qstart votes false (fun _ => false) ∧
      repeatProjectCfg tm j tm.qstart C = tm.initCfg x ∧
      C.input.StartInvariant ∧ (∀ i, (C.work i).StartInvariant) ∧
      C.output.StartInvariant ∧
      (∀ i, (repeatTapeCoord i).1 ≠ j →
        C.work i = (Tape.init []).move Dir3.right) ∧
      C.output = (Tape.init []).move Dir3.right := by
  dsimp only
  have hinv := (repeatAtTime tm k 0).trace_startInvariant 1 choice
    (repeatParkedCfg tm k 0 x)
    ((Tape.StartInvariant.init_ofBool x).move Dir3.right)
    (fun _ => Tape.StartInvariant.init_nil.move Dir3.right)
    (Tape.StartInvariant.init_nil.move Dir3.right)
  refine ⟨?_, ?_, hinv.1, hinv.2.1, hinv.2.2, ?_, ?_⟩
  · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg, hk]
  · apply (Cfg.mk.injEq ..).mpr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg, hk]
      have hread := Tape.init_ofBool_move_right_read_ne_start x
      rw [show repeatSafeDir ((Tape.init (x.map Γ.ofBool)).move .right).read
          (TM.moveLeftDir ((Tape.init (x.map Γ.ofBool)).move .right).read) = .left by
        simp [repeatSafeDir, TM.moveLeftDir, hread]]
      rfl
    · funext i
      simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
        repeatPositionBankDirs, repeatWorkIdx, hk]
      simpa [Tape.read, Tape.move, Tape.init, TM.readBackWrite, Γw.toΓ] using
        repeatPositionBlank_init
    · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
        repeatPositionBankDirs, repeatOutputIdx, hk]
      simpa [Tape.read, Tape.move, Tape.init, TM.readBackWrite, Γw.toΓ] using
        repeatPositionBlank_init
  · intro i hi
    simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
      repeatPositionBankDirs, hi, hk, repeatSafeDir, TM.idleDir,
      TM.readBackWrite, Tape.read, Tape.writeAndMove, Tape.write, Tape.move,
      Tape.init, Γw.toΓ]
  · simp [NTM.trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg, hk,
      repeatSafeDir, TM.idleDir, TM.readBackWrite, Tape.read,
      Tape.writeAndMove, Tape.write, Tape.move, Tape.init, Γw.toΓ]

/-- On the last repetition, one `.finish` transition records the current
trial's source verdict, halts the wrapper, and writes the strict majority to
real output cell one. -/
theorem repeatAtTime_trace_finish_last (tm : NTM n)
    (j : Fin k) (q : tm.Q) (votes : Fin k → Bool) (c : Cfg n tm.Q)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) (choice : Fin 1 → Bool)
    (hstate : C.state = RepeatQ.finish j q votes)
    (hlast : ¬j.val + 1 < k) (hsim : RepeatSimulates tm j q c C)
    (hactiveHead : (C.work (repeatOutputIdx j)).head = 1)
    (hout : C.output.StartInvariant) (houtHead : C.output.head = 1) :
    let accepted := decide (c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one)
    let verdict := majority (Function.update votes j accepted)
    let C' := (repeatAtTime tm k T).trace 1 choice C
    C'.state = RepeatQ.halt ∧ C'.output.head = 1 ∧
      C'.output.cells 1 = Γ.ofBool verdict := by
  let accepted := decide (c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one)
  have hread : (C.work (repeatOutputIdx j)).read = c.output.cells 1 := by
    simp only [Tape.read, hactiveHead]
    exact congrFun hsim.2.2.2.1 1
  have hacceptedSource :
      (decide (c.state = tm.qhalt) && decide (c.output.cells 1 = Γ.one)) =
        accepted := by
    by_cases hq' : c.state = tm.qhalt <;>
      by_cases ho : c.output.cells 1 = Γ.one <;> simp [accepted, hq', ho]
  have haccepted :
      (decide (q = tm.qhalt) &&
        decide ((C.work (repeatOutputIdx j)).read = Γ.one)) = accepted := by
    rw [hsim.1, hread]
    exact hacceptedSource
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp [NTM.trace, repeatAtTime, hstate, hlast, repeatGuardTransition]
  · have hreadOut : C.output.read ≠ Γ.start := by
      exact hout.read_ne_start (by omega)
    simp [NTM.trace, repeatAtTime, hstate, hlast, repeatGuardTransition,
      repeatSafeDir, TM.idleDir, hreadOut, Tape.writeAndMove,
      Tape.write, Tape.move, houtHead]
  · simp [NTM.trace, repeatAtTime, hstate, hlast, repeatGuardTransition,
      haccepted, Tape.writeAndMove, Tape.move_cells, Tape.write, houtHead,
      Function.update_self, Γw.toΓ, hacceptedSource]
    cases majority (Function.update votes j accepted) <;> rfl

end NTM

end Complexity
