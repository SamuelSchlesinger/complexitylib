/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs

/-!
# Affine flats in the Boolean cube

A nonempty subset of the Boolean cube is an affine flat exactly when it is closed
under ternary XOR. This finite presentation keeps the original Boolean coordinates.
Affine Boolean functions preserve that ternary operation on their domain flat.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Algebraic.Cutwidth

/-- Ternary affine addition over the two-element field. -/
def xorThree {n : Nat} (x y z : Fin n → Bool) : Fin n → Bool :=
  xorInput (xorInput x y) z

/-- A finite nonempty affine flat, expressed without changing the input encoding. -/
structure AffineFlat (n : Nat) where
  /-- The points of the flat, in the original Boolean-coordinate representation. -/
  carrier : Finset (Fin n → Bool)
  /-- Affine restrictions retain at least one point. -/
  nonempty : carrier.Nonempty
  /-- The characteristic affine closure law in characteristic two. -/
  closed : ∀ x ∈ carrier, ∀ y ∈ carrier, ∀ z ∈ carrier, xorThree x y z ∈ carrier

/-- A Boolean function is affine on a flat when it preserves ternary XOR. -/
def AffineOn {n : Nat} (S : AffineFlat n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, ∀ z ∈ S.carrier,
    f (xorThree x y z) = Bool.xor (Bool.xor (f x) (f y)) (f z)

/-- The function has one constant value throughout the flat. -/
def ConstantOn {n : Nat} (S : AffineFlat n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ b, ∀ x ∈ S.carrier, f x = b

end Algebraic.Aggregate.Geometry
