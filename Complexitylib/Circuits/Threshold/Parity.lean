/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthClasses
public import Complexitylib.Circuits.Threshold.Parity.Defs
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.Threshold.Parity.Internal

/-!
# Parity in `TC0`

`Circuit.thresholdParity N` computes `N`-input parity (`Schnorr.xorBool`) with
`N` unweighted threshold gates of fan-in `N`, one output threshold gate, and
depth two. Collecting these circuits into a family shows that parity lies in the
nonuniform class `TC0`: polynomial-size, constant-depth threshold circuits with
free negation on gate inputs.
-/


public section

namespace Complexity

/-- Parity is the parity of the number of true inputs. -/
theorem xorBool_eq_decide_countP (N : ℕ) (x : BitString N) :
    Schnorr.xorBool N x = decide (Fin.countP x % 2 = 1) :=
  xorBool_eq_decide_countP_internal N x

namespace Circuit

/-- The depth-two threshold circuit computes parity. -/
theorem eval_thresholdParity (N : ℕ) [NeZero N] (x : BitString N) :
    (thresholdParity N).eval x 0 = Schnorr.xorBool N x :=
  eval_thresholdParity_internal N x

/-- The parity circuit has `N` internal gates and one output gate. -/
theorem size_thresholdParity (N : ℕ) [NeZero N] :
    (thresholdParity N).size = N + 1 :=
  rfl

/-- The parity circuit has depth at most two. -/
theorem depth_thresholdParity_le (N : ℕ) [NeZero N] :
    (thresholdParity N).depth ≤ 2 :=
  depth_thresholdParity_le_internal N

end Circuit

namespace CircuitFamily

/-- The threshold parity family computes parity at every length, including the
empty input. -/
theorem thresholdParity_computes :
    thresholdParity.Computes Schnorr.xorBool :=
  thresholdParity_computes_internal

/-- The threshold parity family has size at most `n + 1` at length `n`. -/
theorem thresholdParity_sizeBoundedBy :
    thresholdParity.SizeBoundedBy fun n => n + 1 :=
  thresholdParity_size_internal

/-- The threshold parity family has depth at most two at every length. -/
theorem thresholdParity_depthBoundedBy :
    thresholdParity.DepthBoundedBy fun _ => 2 :=
  thresholdParity_depth_internal

end CircuitFamily

/-- **Parity is in `TC0`.** The parity family is computed by polynomial-size,
constant-depth, unbounded-fan-in threshold circuits. -/
theorem xorBool_mem_TC0 : Schnorr.xorBool ∈ TC0 :=
  xorBool_mem_TC0_internal

end Complexity
