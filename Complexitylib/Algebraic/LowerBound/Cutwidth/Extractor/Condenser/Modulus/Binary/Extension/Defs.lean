/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Defs
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The binomial extension of an explicit binary quotient

The root of the binary modulus supplies the coefficient of `X^(3^v) - t`.
The resulting quotient is identified with the larger binary quotient in the
surface module. No field or finiteness instances are installed globally.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The extension modulus over the binary quotient, with its named root as coefficient. -/
noncomputable def extensionModulus (s v : Nat) : Polynomial (AdjoinRoot (binaryModulus s)) :=
  binomialModulus (AdjoinRoot.root (binaryModulus s)) v

end Algebraic.Cutwidth.Extractor
