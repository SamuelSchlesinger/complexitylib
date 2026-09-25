/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.ParityLowerBound

/-!
# Integral size arithmetic for the AC0 parity lower bound

The concrete depth-reduction theorem states its switching smallness condition
in exact finite probabilities. This module proves that, for `t >= 1`, it is
equivalent to the natural-number inequality

`20 * t * S < 2^(t+1)`.

Thus the finite parity lower bound can be consumed without any `NNReal` or
`ENNReal` arithmetic: the size inequality above and the survivor inequality
`t < n / (20 * (20t)^(d-2))` suffice. Denominator cancellation is proved
symbolically in the nonnegative reals and transported through the exact order
embedding into extended nonnegative reals.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace ParityParameters

open scoped ENNReal

/-- The extended-real switching failure is the coercion of the corresponding
finite nonnegative-real expression. -/
theorem switchingFailure_eq_coe
    (program : Algebraic.Program signature n g)
    (t : Nat) :
    switchingFailure program t =
      (((program.cost andOrCost : NNReal) *
        ((1 / 2 : NNReal) ^ (t + 1)) : NNReal) : ENNReal) := by
  unfold switchingFailure
  simp [ENNReal.coe_mul, ENNReal.coe_pow]
  rw [← ENNReal.inv_pow]

/-- Integral size smallness implies the finite nonnegative-real probability
inequality. -/
theorem switchingFailure_lt_minimum_nnreal
    (program : Algebraic.Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t)
    (small :
      20 * t * program.cost andOrCost < 2 ^ (t + 1)) :
    (program.cost andOrCost : NNReal) *
        ((1 / 2 : NNReal) ^ (t + 1)) <
      minimumRatio t := by
  have smallNN :
      ((20 * t * program.cost andOrCost : Nat) : NNReal) <
        ((2 ^ (t + 1) : Nat) : NNReal) := by
    exact_mod_cast small
  unfold minimumRatio
  rw [div_pow]
  simp only [one_pow]
  rw [mul_one_div]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_comm, mul_left_comm]
    using smallNN

/-- Exact finite-real equivalence between switching smallness and the
integral size inequality. -/
theorem switchingFailure_lt_minimum_nnreal_iff
    (program : Algebraic.Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t) :
    (program.cost andOrCost : NNReal) *
          ((1 / 2 : NNReal) ^ (t + 1)) <
        minimumRatio t ↔
      20 * t * program.cost andOrCost < 2 ^ (t + 1) := by
  unfold minimumRatio
  rw [div_pow]
  simp only [one_pow]
  rw [mul_one_div]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  constructor <;> intro small <;>
    simpa [mul_assoc, mul_comm, mul_left_comm] using small

/-- Natural-number size smallness supplies the exact extended-real condition
used by depth reduction. -/
theorem switchingFailure_lt_minimum_of_nat
    (program : Algebraic.Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t)
    (small :
      20 * t * program.cost andOrCost < 2 ^ (t + 1)) :
    switchingFailure program t < (minimumRatio t : ENNReal) := by
  have finite := switchingFailure_lt_minimum_nnreal
    program t oneLe small
  rw [switchingFailure_eq_coe]
  exact ENNReal.coe_lt_coe.mpr finite

/-- Exact extended-real equivalence with the integral size inequality. -/
theorem switchingFailure_lt_minimum_iff
    (program : Algebraic.Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t) :
    switchingFailure program t < (minimumRatio t : ENNReal) ↔
      20 * t * program.cost andOrCost < 2 ^ (t + 1) := by
  rw [switchingFailure_eq_coe, ENNReal.coe_lt_coe]
  exact switchingFailure_lt_minimum_nnreal_iff program t oneLe

end ParityParameters

namespace Circuit

/-- Fully integral finite AC0 parity lower bound, allowing arbitrary internal
NOT gates without changing the AND/OR cost. -/
theorem not_computes_parity_of_integral_bounds_raw
    (circuit : Algebraic.Circuit signature n g 1)
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (small :
      20 * t * circuit.program.cost andOrCost < 2 ^ (t + 1))
    (survivors :
      t < n / (20 * (20 * t) ^ (depth - 2))) :
    ¬circuit.ComputesWith interpretation (Parity.target n) := by
  exact not_computes_parity_of_concrete_depth_reduction_raw
    circuit depth t twoLeDepth circuitDepth oneLe
    (ParityParameters.switchingFailure_lt_minimum_of_nat
      circuit.program t oneLe small)
    survivors

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem not_computes_parity_of_integral_bounds
    (circuit : Algebraic.Circuit signature n g 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (small :
      20 * t * circuit.program.cost andOrCost < 2 ^ (t + 1))
    (survivors :
      t < n / (20 * (20 * t) ^ (depth - 2))) :
    ¬circuit.ComputesWith interpretation (Parity.target n) :=
  not_computes_parity_of_integral_bounds_raw circuit depth t twoLeDepth
    circuitDepth oneLe small survivors

end Circuit
end AC0
end Algebraic
