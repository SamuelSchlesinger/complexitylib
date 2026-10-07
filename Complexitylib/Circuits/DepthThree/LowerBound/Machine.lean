/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Machine.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MachineBridge

/-!
# Finite-alphabet multitape polynomial time is canonical `P`

The explicit binary simulator takes at most `2 * n + T + 3` CSLib steps for a source
computation of `T` steps. The existing CSLib-to-complexitylib simulation then transfers
polynomial-time membership to complexitylib's fixed-alphabet, one-sided machine model.
-/

public section

namespace Complexity.DepthThreeLowerBound

/-- The simulator emits the source verdict with a linear input-initialization overhead. -/
theorem FiniteMultiTapeBridge.computes (M : FiniteMultiTapeMachine) (w : List Bool)
    (b : Bool) (T : ℕ) (h : MultiTapeHaltsIn M w b T) :
    (FiniteMultiTapeBridge.machine M).ComputesInTimeAndSpace w [b] (2 * w.length + T + 3)
      ((FiniteMultiTapeBridge.machine M).spaceUsed
        ((FiniteMultiTapeBridge.machine M).initCfg w) (2 * w.length + T + 3)) :=
  FiniteMultiTapeBridge.computes_proof M w b T h

/-- A polynomial-time source decider establishes membership in complexitylib's `P`. -/
theorem FiniteMultiTapeMachine.mem_P {M : FiniteMultiTapeMachine} {L : List Bool → Bool}
    {p : Polynomial ℕ} (h : ∀ w, MultiTapeHaltsIn M w (L w) (p.eval w.length)) :
    {w | L w = true} ∈ Complexity.P :=
  FiniteMultiTapeMachine.mem_P_proof h

end Complexity.DepthThreeLowerBound
