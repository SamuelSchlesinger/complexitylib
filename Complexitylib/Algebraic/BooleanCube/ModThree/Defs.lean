/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Hamming residue on binary affine parametrizations

The residue records the full Hamming weight modulo three, rather than one Boolean
residue predicate. Coordinates are elements of `ZMod 2`, with their usual zero/one
interpretation. An affine parametrization has coordinates `a i + L i u`.
-/

@[expose] public section

namespace Algebraic.BooleanCube.ModThree

/-- A binary coordinate, interpreted as a zero/one element of `ZMod 3`. -/
def bit (x : ZMod 2) : ZMod 3 := if x = 0 then 0 else 1

/-- The full Hamming-weight residue modulo three. -/
def residue {ι : Type*} [Fintype ι] (x : ι → ZMod 2) : ZMod 3 :=
  ∑ i, bit (x i)

/-- The sign character of a binary coordinate, with values in `ZMod 3`. -/
def sign (x : ZMod 2) : ZMod 3 := if x = 0 then 1 else -1

end Algebraic.BooleanCube.ModThree
