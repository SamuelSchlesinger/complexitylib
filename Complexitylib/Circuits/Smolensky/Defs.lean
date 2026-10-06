/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Complexitylib.Circuits.Basis.Defs

/-!
# Low-degree functions over `ZMod 3` -- definitions

Smolensky's lower bound approximates circuits by low-degree polynomials over
the field with three elements. This module avoids formal polynomials: it works
with functions `{0,1}^n → ZMod 3` directly, reading each input bit as `0` or `1`
in `ZMod 3`. The monomial of a set `S` of coordinates is the function
`x ↦ ∏_{i ∈ S} x_i`, and a function has degree at most `D` when it is a
`ZMod 3`-linear combination of monomials of at most `D` coordinates. On Boolean
inputs every polynomial function is multilinear, so this is the usual notion of
degree for functions on the Boolean cube.

## Main definitions

* `Smolensky.bitVal` — a bit read as `0` or `1` in `ZMod 3`
* `Smolensky.monomial` — the function `x ↦ ∏_{i ∈ S} x_i`
* `Smolensky.lowDegree` — the submodule of functions of degree at most `D`
-/


@[expose] public section

namespace Complexity

namespace Smolensky

/-- A bit read as `0` or `1` in `ZMod 3`. -/
def bitVal (b : Bool) : ZMod 3 := if b then 1 else 0

/-- The monomial of a set `S` of coordinates: the product of the selected input
bits, read in `ZMod 3`. The empty monomial is the constant `1`. -/
def monomial {n : ℕ} (S : Finset (Fin n)) (x : BitString n) : ZMod 3 :=
  ∏ i ∈ S, bitVal (x i)

/-- The functions `{0,1}^n → ZMod 3` of degree at most `D`: the
`ZMod 3`-linear span of the monomials of at most `D` coordinates. -/
def lowDegree (n D : ℕ) : Submodule (ZMod 3) (BitString n → ZMod 3) :=
  Submodule.span (ZMod 3) (monomial '' {S | S.card ≤ D})

end Smolensky

end Complexity
