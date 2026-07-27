/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import Complexitylib.SAT.Tseitin.Machine.Internal.ValidationFramed

/-!
# Execution of the Tseitin syntax-validation machine

This file proves the first execution layer for the concrete reduction machine.
Starting from the standard initial configuration, `validationTM` performs one
left-end-marker bounce, scans one input bit per step, and uses one final step
to write its verdict. Thus it halts in exactly `|z| + 2` steps.

The canonical scan induction lives in `Internal.ValidationFramed`. This file
only proves the initial left-end-marker bounce and composes it with that exact
started execution theorem.

## Main results

- `validationTM_reachesIn_internal` — exact execution from `initCfg`
- `validationTM_hoareTime_internal` — compositional `HoareTime` interface
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

private def validationStartedCfg (z : List Bool) :
    Cfg n (validationTM (n := n)).Q :=
  { state := (validationTM (n := n)).qstart
    input := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
    work := fun _ => ⟨1, (Tape.init []).cells⟩
    output := ⟨1, (Tape.init []).cells⟩ }

/-- The initial left-end-marker bounce enters the scan state and parks every
tape head at cell one without changing any cells. -/
private theorem validationTM_step_init (z : List Bool) :
    (validationTM (n := n)).step ((validationTM (n := n)).initCfg z) =
      some (validationStartedCfg (n := n) z) := by
  rfl

/-- **Exact validation execution.** Starting from `initCfg z`, the machine
halts in exactly `|z|+2` steps, preserves the input cells and all work cells,
and writes the Boolean `validEncoding z` to output cell one. -/
theorem validationTM_reachesIn_internal (z : List Bool) :
    ∃ c', (validationTM (n := n)).reachesIn (z.length + 2)
        ((validationTM (n := n)).initCfg z) c' ∧
      (validationTM (n := n)).halted c' ∧
      c'.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      c'.input.head = z.length + 1 ∧
      c'.work = (fun _ => ⟨1, (Tape.init []).cells⟩) ∧
      c'.output.head = 1 ∧
      c'.output.cells 1 = if validEncoding z then Γ.one else Γ.zero := by
  have hstep := validationTM_step_init (n := n) z
  have hwork : ∀ i, TM.Parked ((validationStartedCfg (n := n) z).work i) :=
    fun _ => TM.reg_zero_init_bumped.parked
  have hout : TM.OutAcc [] (validationStartedCfg (n := n) z).output :=
    TM.outAcc_nil_init
  obtain ⟨c', hreach, hhalt, hpost⟩ :=
    validationTM_started_framed_reachesIn_internal z
      (validationStartedCfg (n := n) z).work
      (validationStartedCfg (n := n) z).output hwork hout
  rcases hpost with ⟨hiCells, hiHead, hwEq, hoHead, _, hoCell, _⟩
  refine ⟨c', .step hstep hreach, hhalt, hiCells, hiHead, ?_, hoHead, ?_⟩
  · simpa [validationStartedCfg] using hwEq
  · cases hvalid : validEncoding z <;>
      simpa [hvalid, Γ.ofBool] using hoCell

/-- Hoare interface for the exact initial-tape execution theorem. -/
theorem validationTM_hoareTime_internal (z : List Bool) :
    (validationTM (n := n)).HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head = z.length + 1 ∧
        work = (fun _ => ⟨1, (Tape.init []).cells⟩) ∧
        out.head = 1 ∧
        out.cells 1 = if validEncoding z then Γ.one else Γ.zero)
      (z.length + 2) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', hreach, hhalt, hiCells, hiHead, hwork, hoHead, hoCell⟩ :=
    validationTM_reachesIn_internal (n := n) z
  exact ⟨c', z.length + 2, le_rfl, hreach, hhalt,
    hiCells, hiHead, hwork, hoHead, hoCell⟩

end Machine

end ThreeSAT

end SAT

end Complexity
