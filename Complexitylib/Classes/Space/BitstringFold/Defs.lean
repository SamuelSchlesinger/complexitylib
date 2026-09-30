/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Mathlib.NatBits

/-!
# Ordered folds over fixed-width bitstrings

The first `count` strings are enumerated by their little-endian numeric value.
The complete fold visits all `2 ^ width` strings, including the single empty
string when `width = 0`. The update need not be associative or commutative.
-/

@[expose] public section

namespace Complexity

/-- Fold over the first `count` fixed-width bitstrings in little-endian numeric
order. Prefixes past `2 ^ width` repeat candidates; the space theorem only
bounds and uses prefixes up to that endpoint. -/
def bitstringFoldPrefix (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width : ℕ) : ℕ → List Bool
  | 0 => seed
  | count + 1 => update (Nat.toBitsLE width count)
      (bitstringFoldPrefix update seed width count)

@[simp] theorem bitstringFoldPrefix_zero (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width : ℕ) : bitstringFoldPrefix update seed width 0 = seed := rfl

@[simp] theorem bitstringFoldPrefix_succ (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width count : ℕ) :
    bitstringFoldPrefix update seed width (count + 1) =
      update (Nat.toBitsLE width count) (bitstringFoldPrefix update seed width count) := rfl

/-- Fold over every string of exactly `width` bits, in little-endian numeric order. -/
def bitstringFold (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width : ℕ) : List Bool :=
  bitstringFoldPrefix update seed width (2 ^ width)

/-- A zero-width fold still performs one update, with the empty candidate. -/
@[simp] theorem bitstringFold_zero (update : List Bool → List Bool → List Bool)
    (seed : List Bool) : bitstringFold update seed 0 = update [] seed := rfl

end Complexity
