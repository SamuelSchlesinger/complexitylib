/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Ring

/-!
# Multilinear extension (one variable)

The one-variable **multilinear extension** of a Boolean-indexed value into a
commutative ring, `mle₁ f x = f false · (1 - x) + f true · x`, and its defining
interpolation identities at the Boolean points `0` and `1` (roadmap track L1,
toward arithmetization and the sum-check protocol). This is the atomic building
block of the multilinear extension of a full Boolean function, and the reason
arithmetized formulas agree with their Boolean originals on the cube.

## Main results

- `mle₁` — the one-variable multilinear interpolant
- `mle₁_zero`, `mle₁_one` — it recovers `f false` at `0` and `f true` at `1`
- `mle₁_bool` — it agrees with `f` at both Boolean points
-/

@[expose] public section

namespace Complexity

/-- The one-variable multilinear extension of `f : Bool → R` into a commutative
    ring `R`: the unique degree-`≤ 1` polynomial interpolating `f false` at `0`
    and `f true` at `1`. -/
def mle₁ {R : Type*} [CommRing R] (f : Bool → R) (x : R) : R :=
  f false * (1 - x) + f true * x

@[simp] theorem mle₁_zero {R : Type*} [CommRing R] (f : Bool → R) :
    mle₁ f 0 = f false := by
  simp [mle₁]

@[simp] theorem mle₁_one {R : Type*} [CommRing R] (f : Bool → R) :
    mle₁ f 1 = f true := by
  simp [mle₁]

/-- At either Boolean point (`0` or `1`), the extension agrees with `f`. -/
theorem mle₁_bool {R : Type*} [CommRing R] (f : Bool → R) (b : Bool) :
    mle₁ f (if b then 1 else 0) = f b := by
  cases b <;> simp

end Complexity
