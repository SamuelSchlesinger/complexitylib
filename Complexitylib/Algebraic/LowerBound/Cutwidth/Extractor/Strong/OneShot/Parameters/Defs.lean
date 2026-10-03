/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs

/-!
# Parameters for one round of condensation and linear hashing

For output length `ell` and inverse-error exponent `e`, the entropy threshold
is `ell + 2*e`. The condenser uses rate parameter one and error exponent
`e+1`. Its output is embedded in a second sparse binary field large enough
for both that output and the requested hash prefix. The two half-errors
are intended to add to `2^(-e)`; the numerical theorems are separate.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The sparse field exponent for the first, condensing stage. -/
def oneShotCondenserExponent (n ell e : Nat) : Nat :=
  sparseFieldExponent 1 (explicitCondenserBudget n (ell + 2 * e) (e + 1))

/-- The exact bit length of the first stage's output. -/
def oneShotCondenserOutputBits (n ell e : Nat) : Nat :=
  let T := explicitCondenserBudget n (ell + 2 * e) (e + 1)
  condenserCoordinates (ell + 2 * e) (sparsePowerBits 1 T) * sparseFieldBits 1 T

/-- The hashing field covers the condensed word and requested output prefix. -/
def oneShotHashExponent (n ell e : Nat) : Nat :=
  sparseFieldExponent 0 (max (oneShotCondenserOutputBits n ell e) ell)

end Algebraic.Cutwidth.Extractor
