/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanLoop.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanLoop.Internal

/-!
# Bounded forward postfix scan loop

This module exposes the fresh loop-control roles and the one-way-output
certificate for bounded iteration of the complete decoded-token scanner.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- The bounded loop counter and its preserved token limit are distinct. -/
theorem ForwardScanLoopLayout.counter_ne_limit (n : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    layout.counterIdx n ≠ layout.limitIdx n :=
  layout.counter_ne_limit_internal n

/-- No decoded-token role aliases the private loop counter. -/
theorem ForwardScanLoopLayout.tokenRole_ne_counter
    (layout : ForwardScanLoopLayout controllerTapes) (i : Fin 16) :
    layout.tokenLayout.roles i ≠ layout.counterRole :=
  layout.tokenRole_ne_counter_internal i

/-- No decoded-token role aliases the preserved token limit. -/
theorem ForwardScanLoopLayout.tokenRole_ne_limit
    (layout : ForwardScanLoopLayout controllerTapes) (i : Fin 16) :
    layout.tokenLayout.roles i ≠ layout.limitRole :=
  layout.tokenRole_ne_limit_internal i

/-- Bounded decoded-token scanning preserves one-way output behavior. -/
theorem forwardScanTokenLoopTM_isTransducer (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanLoopLayout controllerTapes) :
    (forwardScanTokenLoopTM tm controllerTapes layout).IsTransducer :=
  forwardScanTokenLoopTM_isTransducer_internal tm controllerTapes layout

end Machine

end BPCode

end Complexity
