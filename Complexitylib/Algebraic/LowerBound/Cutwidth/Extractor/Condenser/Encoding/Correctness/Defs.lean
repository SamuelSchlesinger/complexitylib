/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Defs
public import Complexitylib.Encoding.BitPolynomial.BlockEval.Defs

/-!
# Source polynomials represented by binary coefficient blocks

The first `d` blocks of width `2 * 3^s` represent coefficients in the explicit
binary quotient. The source polynomial has degree below `d`; missing input
bits are zero, and bits beyond these blocks are ignored. This is the semantic
input convention of the runtime condenser, with no source-length promise.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Interpret the first `d` fixed-width blocks as an extension polynomial. -/
noncomputable def sourcePolynomial (s d : Nat) (bits : List Bool) :
    Polynomial (AdjoinRoot (binaryModulus s)) :=
  Polynomial.ofFn d fun j => BinaryFieldCodec.decode s
    (Complexity.BitPolynomial.coefficientBlock bits (2 * 3 ^ s) j.val)

/-- The runtime condenser viewed on semantic field seeds and output coordinates.
The seed is encoded at its canonical width before calling the list program. -/
noncomputable def decodedCondenser (s : Nat)
    (halfDegree extensionCount stride count bits : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) : Fin count.length → AdjoinRoot (binaryModulus s) :=
  fun i => BinaryFieldCodec.decode s
    (Complexity.BitPolynomial.coefficientBlock
      (condenserBits bits halfDegree extensionCount (BinaryFieldCodec.encode s seed) stride count)
      (2 * 3 ^ s) i.val)

end Algebraic.Cutwidth.Extractor
