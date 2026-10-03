/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Internal

/-!
# A finite parameter choice with source capacity, rate, and error bounds

For `T = e + clog 2 (9*(n+1)*(k+1)) + 1`, retain the sparse choices
`b = sparseFieldBits u T` and `r = sparsePowerBits u T`. Round the extension
degree `d` to a power of three above both three and `ceil(n/b)`. Then `b*d`
covers the source, `d` is linear in `n`, and the integer error budget pays for
loss `2^(-e)`. The coordinate count is `condenserCoordinates k r`.

These explicit rounding choices are our deduction from the finite sparse
rate and loss bounds in `Parameters.Sparse`, whose source credit is given
there. This layer contains exact natural-number inequalities. Its sibling
`Explicit.Unary` supplies uniform certificates for constructing the numerical
parameters; no asymptotic or extractor statement is asserted here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The error and degree budget is positive even when all inputs are zero. -/
theorem explicitCondenserBudget_pos (n k e : Nat) : 0 < explicitCondenserBudget n k e :=
  Internal.explicitCondenserBudget_pos n k e

/-- Every selected base field has a positive bit width. -/
theorem explicitCondenserFieldBits_pos (n k e u : Nat) :
    0 < sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserFieldBits_pos n k e u

/-- A positive rate parameter leaves positive capacity in every coordinate. -/
theorem explicitCondenserPowerBits_pos (n k e : Nat) {u : Nat} (rate : 0 < u) :
    0 < sparsePowerBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserPowerBits_pos n k e rate

/-- The selected extension exponent is always positive. -/
theorem explicitCondenserExtensionExponent_pos (n k e u : Nat) :
    0 < explicitCondenserExtensionExponent n k e u :=
  Internal.explicitCondenserExtensionExponent_pos n k e u

/-- The extension degree is at least three, as required for the expansion regime. -/
theorem explicitCondenser_degree_lower (n k e u : Nat) :
    3 ≤ explicitCondenserExtensionDegree n k e u :=
  Internal.explicitCondenser_degree_lower n k e u

/-- The coefficient rectangle holds the entire `n`-bit source. -/
theorem explicitCondenser_source_capacity (n k e u : Nat) :
    n ≤ sparseFieldBits u (explicitCondenserBudget n k e) *
      explicitCondenserExtensionDegree n k e u :=
  Internal.explicitCondenser_source_capacity n k e u

/-- Rounding the extension degree costs at most a linear factor in source length. -/
theorem explicitCondenser_degree_le (n k e u : Nat) :
    explicitCondenserExtensionDegree n k e u ≤ 9 * (n + 1) :=
  Internal.explicitCondenser_degree_le n k e u

/-- The selected number of coordinates carries at least `k` entropy bits. -/
theorem explicitCondenser_entropy_capacity (n k e : Nat) {u : Nat} (rate : 0 < u) :
    k ≤ sparsePowerBits u (explicitCondenserBudget n k e) *
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) :=
  Internal.explicitCondenser_entropy_capacity n k e rate

/-- The seed bit length is bounded by six times the rate-adjusted slack budget. -/
theorem explicitCondenser_fieldBits_le (n k e u : Nat) :
    sparseFieldBits u (explicitCondenserBudget n k e) ≤
      6 * (u + 1) * explicitCondenserBudget n k e :=
  Internal.explicitCondenser_fieldBits_le n k e u

/-- The coordinate output approaches rate `1+1/u`, with one field element of slack. -/
theorem explicitCondenser_output_rate (n k e u : Nat) :
    u * (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
      sparseFieldBits u (explicitCondenserBudget n k e)) ≤
        (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenser_output_rate n k e u

/-- The exact integer budget needed for inverse-power-of-two error. -/
theorem explicitCondenser_error_budget (n k e u : Nat) :
    explicitCondenserExtensionDegree n k e u * k * 2 ^ e ≤
      2 ^ explicitCondenserBudget n k e :=
  Internal.explicitCondenser_error_budget n k e u

end Algebraic.Cutwidth.Extractor
