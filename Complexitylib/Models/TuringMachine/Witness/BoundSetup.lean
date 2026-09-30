/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Witness.BoundSetup.Defs
public import Complexitylib.Models.TuringMachine.Witness.PhaseSafety
import Complexitylib.Models.TuringMachine.Witness.BoundSetup.Internal

/-!
# Finite witness-bound setup

The bound interface has a concrete instance for the linear certificate bound
`n + 1`. It charges initialization, counter generation, and every visited work
or output cell. The certificate-storing compiler can consume the resulting
canonical unary counter without inspecting the external witness stream.
-/

@[expose] public section

namespace Complexity
namespace WitnessBoundSetup

/-- A bound-setup phase can run alongside an uncharged external witness tape
without changing its ordinary all-prefix decision-space budget. -/
theorem liftedSafety (setup : WitnessBoundSetup r bound) (x : List Bool) :
    (TM.liftLast setup.machine).HoareSafety
      (fun inp work out => fresh x inp (fun i => work i.castSucc) out)
      (fun inp work out =>
        (⟨(), inp, (fun i => work i.castSucc), out⟩ : Cfg (r + 1) Unit).WithinDecisionSpace
          x.length (setup.space x.length)) :=
  TM.liftLast_hoareSafety setup.machine (setup.withinSpace x)

/-- Realize the linear witness bound with one charged counter tape.
Both explicit resource budgets are `4 * n + 11`. -/
def linear : WitnessBoundSetup 0 (fun n => n + 1) where
  machine := linearMachine
  time := fun n => 4 * n + 11
  space := fun n => 4 * n + 11
  prepares := by exact linearMachine_prepares_internal
  withinSpace := by exact linearMachine_withinSpace_internal

end WitnessBoundSetup
end Complexity
