/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Nat.Log

/-!
# Sparse binary field sizes and condenser coordinates

The field bit length is rounded up to `2 * 3^s`. Choosing the powering bit
length after this rounding preserves the target output rate `1 + 1/u`.
These are total natural-number parameters; their useful bounds assume
positive budgets. No field representation or running time is defined here.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The exponent selecting the first sparse field bit length above `(u+1)*T`. -/
def sparseFieldExponent (u T : Nat) : Nat :=
  Nat.clog 3 (((u + 1) * T + 1) / 2)

/-- A binary field bit length on the grid `2 * 3^s`. -/
def sparseFieldBits (u T : Nat) : Nat := 2 * 3 ^ sparseFieldExponent u T

/-- The powering exponent leaves `T` bits of slack below the field bit length. -/
def sparsePowerBits (u T : Nat) : Nat := sparseFieldBits u T - T

/-- The number of coordinates needed to carry `k` entropy bits at `r` bits each.
At `r = 0`, natural-number division makes this total definition equal to zero. -/
def condenserCoordinates (k r : Nat) : Nat := (k + r - 1) / r

end Algebraic.Cutwidth.Extractor
