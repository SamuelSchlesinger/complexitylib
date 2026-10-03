/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Defs
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Extension.Internal

/-!
# The binomial quotient supplies the next noncube coefficient

The adjoined root of `X^(3^s) - a` has norm `a`. If `a` is a noncube, norm
multiplicativity shows that the root is also a noncube. It therefore gives
another monic irreducible binomial of every power-of-three degree.

The norm computation reuses Mathlib's power-basis norm formula
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` and its monic
`AdjoinRoot` power basis:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Norm/Basic.html.
The next irreducibility step uses the Kummer theorem documented in `Binomial`.
These are semantic algebraic facts about supplied data; no encoded field
representation, coefficient-selection algorithm, or runtime bound is asserted.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Odd degree makes the quotient root's norm equal to the supplied coefficient.
This identity does not require irreducibility. -/
theorem norm_root_binomialModulus {F : Type*} [Field F] (a : F) (s : Nat) :
    Algebra.norm F (AdjoinRoot.root (binomialModulus a s)) = a :=
  Internal.norm_root_binomialModulus a s

/-- A cube root of the adjoined root would have norm a cube root of `a`. -/
theorem root_binomialModulus_noncube {F : Type*} [Field F] (a : F) (s : Nat)
    (noncube : ∀ b : F, b ^ 3 ≠ a) :
    ∀ b : AdjoinRoot (binomialModulus a s),
      b ^ 3 ≠ AdjoinRoot.root (binomialModulus a s) :=
  Internal.root_binomialModulus_noncube a s noncube

/-- The first quotient's root supplies the coefficient of a second monic
irreducible binomial, with exact degree `3^v`. Both exponents may be zero. -/
theorem binomialModulus_root_properties {F : Type*} [Field F] (a : F) (s v : Nat)
    (noncube : ∀ b : F, b ^ 3 ≠ a) :
    (binomialModulus (AdjoinRoot.root (binomialModulus a s)) v).Monic ∧
      Irreducible (binomialModulus (AdjoinRoot.root (binomialModulus a s)) v) ∧
      (binomialModulus (AdjoinRoot.root (binomialModulus a s)) v).natDegree = 3 ^ v :=
  Internal.binomialModulus_root_properties a s v noncube

end Algebraic.Cutwidth.Extractor
