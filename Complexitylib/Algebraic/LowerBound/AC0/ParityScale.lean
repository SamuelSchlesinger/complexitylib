/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.ParitySizeArithmetic

/-!
# The quantitative AC0 parity lower bound at an explicit scale

The integral lower bound becomes especially transparent when parameterized by
an arbitrary scale `t`. If

`(20 * (t + 1))^(d - 1) <= n`,

then every depth-`d` circuit computing parity, even with arbitrary internal
NOT gates, satisfies

`2^(t + 1) <= 20 * t * S`,

where `S` is its AND/OR-gate count. The input hypothesis implies the exact
floor-divided survivor inequality, and contradiction with the fully integral
finite theorem yields the size tradeoff.

This is the standard quantitative lower bound before choosing a particular
integer root of `n`: it displays the exponent `1/(d-1)` directly while keeping
root rounding out of the structural theorem.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace ParityParameters

/-- The exact survivor denominator times `t+1` is bounded by the cleaner
scale power. -/
theorem survivorDenominator_mul_succ_le_scalePow
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth) :
    20 * (20 * t) ^ (depth - 2) * (t + 1) ≤
      (20 * (t + 1)) ^ (depth - 1) := by
  have exponentEq : depth - 1 = (depth - 2) + 1 := by omega
  rw [exponentEq, pow_succ]
  calc
    20 * (20 * t) ^ (depth - 2) * (t + 1) =
        (20 * t) ^ (depth - 2) * (20 * (t + 1)) := by ring
    _ ≤ (20 * (t + 1)) ^ (depth - 2) * (20 * (t + 1)) := by
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (by omega) (depth - 2))

/-- The clean scale hypothesis implies the exact floor-divided survivor
condition used by depth reduction. -/
theorem survivors_of_scalePow
    (n depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (oneLe : 1 ≤ t)
    (inputLarge : (20 * (t + 1)) ^ (depth - 1) ≤ n) :
    t < n / (20 * (20 * t) ^ (depth - 2)) := by
  let denominator := 20 * (20 * t) ^ (depth - 2)
  have denominatorPositive : 0 < denominator := by
    dsimp [denominator]
    positivity
  have scaled : denominator * (t + 1) ≤ n :=
    (survivorDenominator_mul_succ_le_scalePow
      depth t twoLeDepth).trans inputLarge
  have quotient : t + 1 ≤ n / denominator :=
    (Nat.le_div_iff_mul_le denominatorPositive).2 (by
      simpa [mul_comm] using scaled)
  exact (Nat.lt_succ_self t).trans_le (by
    simpa [denominator] using quotient)

end ParityParameters

namespace Circuit

/-- Quantitative parity size tradeoff at an arbitrary integral scale, with
arbitrary internal NOT gates charged at zero. -/
theorem parity_size_tradeoff_at_scale_raw
    (circuit : Algebraic.Circuit signature n 1)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (inputLarge : (20 * (t + 1)) ^ (depth - 1) ≤ n) :
    2 ^ (t + 1) ≤
      20 * t * circuit.program.cost andOrCost := by
  by_contra notLarge
  have small :
      20 * t * circuit.program.cost andOrCost < 2 ^ (t + 1) := by
    omega
  exact not_computes_parity_of_integral_bounds_raw
    circuit depth t twoLeDepth circuitDepth oneLe small
    (ParityParameters.survivors_of_scalePow
      n depth t twoLeDepth oneLe inputLarge) computes

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem parity_size_tradeoff_at_scale
    (circuit : Algebraic.Circuit signature n 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (inputLarge : (20 * (t + 1)) ^ (depth - 1) ≤ n) :
    2 ^ (t + 1) ≤
      20 * t * circuit.program.cost andOrCost :=
  parity_size_tradeoff_at_scale_raw circuit computes depth t twoLeDepth
    circuitDepth oneLe inputLarge

end Circuit
end AC0
end Algebraic
