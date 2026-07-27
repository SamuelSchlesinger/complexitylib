/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseDefs
public import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Program.DenseInternal

/-!
# Dense-overlay RAM program controller
-/

@[expose] public section

namespace Complexity
namespace RAM
namespace RegisterStore
namespace Machine

/-- Final overlay-aware lookup recovers decoded `R₀` and emits its Boolean
verdict. -/
theorem denseProgramOutputTM_hoareTime {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseProgramOutputTM tapes).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp _work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        out = registerVerdictOutput (DenseOverlay.read input overlay 0))
      (denseProgramOutputTime tapes input overlay) :=
  denseProgramOutputTM_hoareTime_internal tapes input overlay pcValue
    initialWork hvalid hready

/-- The dense verdict extractor can overwrite the loop's halt-test bit
directly. -/
theorem denseProgramOutputTM_hoareTime_haltOutput {n : ℕ}
    (tapes : ControlInstructionTapes n) (input : List Bool)
    (overlay : Store) (pcValue : ℕ)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid overlay)
    (hready : InstructionExecutionReady tapes overlay pcValue initialWork) :
    (denseProgramOutputTM tapes).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = instructionHaltOutput .halt)
      (fun inp _work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        out = registerVerdictOutput (DenseOverlay.read input overlay 0))
      (denseProgramOutputTime tapes input overlay) :=
  denseProgramOutputTM_hoareTime_haltOutput_internal tapes input overlay
    pcValue initialWork hvalid hready

/-- A halted dense snapshot is stationary under one program step. -/
theorem DenseOverlay.Snapshot.step_eq_self_of_halted
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hhalted : snapshot.Halted program) :
    snapshot.step program input = snapshot :=
  denseSnapshot_step_eq_self_of_halted_internal program input snapshot hhalted

/-- A halted dense snapshot remains fixed for all additional fuel. -/
theorem DenseOverlay.Snapshot.run_halted
    (program : Program) (input : List Bool)
    (snapshot : DenseOverlay.Snapshot)
    (hhalted : snapshot.Halted program) (fuel : ℕ) :
    snapshot.run program input fuel = snapshot :=
  denseSnapshot_run_halted_internal program input snapshot hhalted fuel

/-- If a fuel-bounded dense run is halted, the fixed controller reaches that
exact reusable snapshot and exposes its halt verdict. -/
theorem denseProgramLoopTM_hoareTime_run {n : ℕ}
    (tapes : ControlInstructionTapes n) (program : Program)
    (input : List Bool) (fuel : ℕ) (snapshot : DenseOverlay.Snapshot)
    (initialWork : Fin (n + 1) → Tape)
    (hvalid : DenseOverlay.Valid snapshot.overlay)
    (hready : InstructionExecutionReady tapes snapshot.overlay snapshot.pc
      initialWork)
    (hhalted : (snapshot.run program input fuel).Halted program) :
    (denseProgramLoopTM tapes program).HoareTime
      (fun inp work out =>
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        work = initialWork ∧ out = (Tape.init []).move Dir3.right)
      (fun inp work out =>
        let final := snapshot.run program input fuel
        inp = (Tape.init (input.map Γ.ofBool)).move Dir3.right ∧
        InstructionExecutionReady tapes final.overlay final.pc work ∧
        out = instructionHaltOutput (final.curInstr program))
      (denseProgramLoopTime tapes program input (fuel + 1) snapshot) :=
  denseProgramLoopTM_hoareTime_run_internal tapes program input fuel snapshot
    initialWork hvalid hready hhalted

end Machine
end RegisterStore
end RAM
end Complexity
