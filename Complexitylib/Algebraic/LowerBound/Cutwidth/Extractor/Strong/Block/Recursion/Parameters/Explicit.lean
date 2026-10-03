/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit.Internal

/-!
# An explicit finite reserve for constant-rate block recursion

The reserve `4096*(L+E+1)` controls the initial rate-one compression and pays
for the later rate-three split budgets. The initial output width is between
the initial entropy and sixty-four times that entropy. Its condenser budget
is bounded by `E+4*h+2*clog 2 (L+E+1)+64`, retaining logarithmic dependence
on the reserve instead of charging its full size to every seed.

These estimates are our arithmetic deductions from the checked sparse-field
rate bounds. The recursive condensation and splitting method is credited in
`Recursion.Extraction`. This module proves finite inequalities only; the
recurrence, its total seed cost, and an encoded evaluator are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The explicit reserve is positive for every pair of natural parameters. -/
theorem recursiveBlockReserve_pos (L E : Nat) : 0 < recursiveBlockReserve L E :=
  Internal.recursiveBlockReserve_pos L E

/-- The initial entropy has a logarithm linear in depth and logarithmic in the reserve. -/
theorem recursiveBlockEntropy_zero_clog_le (L E h : Nat) :
    Nat.clog 2 (recursiveBlockEntropy h (recursiveBlockReserve L E) 0 + 1) ≤
      2 * h + 13 + Nat.clog 2 (L + E + 1) :=
  Internal.recursiveBlockEntropy_zero_clog_le L E h

/-- Initial rate-one compression preserves capacity and has bounded expansion. -/
theorem recursiveBlockInitialWidth_bounds (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) :
    let Q := recursiveBlockReserve L E
    let k := recursiveBlockEntropy h Q 0
    let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
    k ≤ N ∧ N ≤ 64 * k :=
  Internal.recursiveBlockInitialWidth_bounds n L E h length

/-- The largest later budget depends on the logarithm of the initial compressed width. -/
theorem recursiveBlockInitialBudget_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) :
    let Q := recursiveBlockReserve L E
    let k := recursiveBlockEntropy h Q 0
    let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
    explicitCondenserBudget N k E ≤ E + 4 * h + 2 * Nat.clog 2 (L + E + 1) + 64 :=
  Internal.recursiveBlockInitialBudget_le n L E h length

/-- The reserve pays the uniform field-width and split-error slack for rate three. -/
theorem recursiveBlockReserve_budget (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    let Q := recursiveBlockReserve L E
    let k := recursiveBlockEntropy h Q 0
    let N := explicitCondenserHalfWidth n k E 1 + explicitCondenserHalfWidth n k E 1
    3 * (24 * explicitCondenserBudget N k E) + 6 * E ≤ 2 * Q :=
  Internal.recursiveBlockReserve_budget n L E h length depth

end Algebraic.Cutwidth.Extractor
