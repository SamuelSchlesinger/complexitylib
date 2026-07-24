/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanLoop.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken
import Complexitylib.Models.TuringMachine.OutputProbeIndexed
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor

/-!
# Bounded forward postfix scan loop -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

theorem ForwardScanLoopLayout.counter_ne_limit_internal (n : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    layout.counterIdx n ≠ layout.limitIdx n := by
  intro heq
  have hlogical := outputProbeIndexedControllerIdx_injective n heq
  have hroles := layout.roles.injective hlogical
  have hvals := congrArg Fin.val hroles
  omega

theorem ForwardScanLoopLayout.tokenRole_ne_counter_internal
    (layout : ForwardScanLoopLayout controllerTapes) (i : Fin 16) :
    layout.tokenLayout.roles i ≠ layout.counterRole := by
  change layout.roles (Fin.castLE (by omega : 16 ≤ 18) i) ≠
    layout.roles ⟨16, by omega⟩
  exact layout.roles.injective.ne (by
    intro heq
    have hvals := congrArg (fun j : Fin 18 => j.val) heq
    simp only [Fin.castLE] at hvals
    omega)

theorem ForwardScanLoopLayout.tokenRole_ne_limit_internal
    (layout : ForwardScanLoopLayout controllerTapes) (i : Fin 16) :
    layout.tokenLayout.roles i ≠ layout.limitRole := by
  change layout.roles (Fin.castLE (by omega : 16 ≤ 18) i) ≠
    layout.roles ⟨17, by omega⟩
  exact layout.roles.injective.ne (by
    intro heq
    have hvals := congrArg (fun j : Fin 18 => j.val) heq
    simp only [Fin.castLE] at hvals
    omega)

theorem forwardScanTokenLoopTM_isTransducer_internal (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    (forwardScanTokenLoopTM tm controllerTapes layout).IsTransducer := by
  unfold forwardScanTokenLoopTM
  exact (forwardScanDecodedTokenTM_isTransducer tm controllerTapes
    layout.tokenLayout).binaryForTM (layout.counterIdx n) (layout.limitIdx n)

end Machine

end BPCode

end Complexity
