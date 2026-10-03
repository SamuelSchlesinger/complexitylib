/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Parameters.Defs

/-!
# A concrete condense-then-hash extractor program

For `ell` output bits and inverse-error exponent `e`, condense at entropy
budget `ell+2*e` and error exponent `e+1`, then multiply and truncate using
an independent field seed. The hash field has capacity for the whole
condensed word and the requested output. Both seeds remain available for
the joint statistical comparison, although the program emits only output bits.

The paired evaluator reads `n`, `ell`, and `e` from unary word lengths.
Every function is total; statistical theorems additionally require source
words of length `n` and the specified support size.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- Condense at half the requested error, then hash the complete output with a fresh seed. -/
def oneShotExtractorBits (n ell e : Nat) (source condenserSeed hashSeed : List Bool) : List Bool :=
  binaryHashBits (explicitCondenserBits n (ell + 2 * e) (e + 1) 1 source condenserSeed)
    hashSeed (List.replicate (3 ^ oneShotHashExponent n ell e) true) (List.replicate ell true)

/-- Codec: `pair (pair source (pair condenserSeed hashSeed)) (pair n (pair ell e))`. -/
def oneShotExtractorEval (z : List Bool) : List Bool :=
  let data := pairFst z
  let params := pairSnd z
  oneShotExtractorBits (pairFst params).length (pairFst (pairSnd params)).length
    (pairSnd (pairSnd params)).length (pairFst data)
    (pairFst (pairSnd data)) (pairSnd (pairSnd data))

/-- Read the actual output at canonically encoded, independent field seeds. -/
noncomputable def decodedOneShotExtractor (n ell e : Nat) (source : List Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) : Fin ell → ZMod 2 :=
  Polynomial.toFn ell (ofBits (oneShotExtractorBits n ell e source
    (BinaryFieldCodec.encode (oneShotCondenserExponent n ell e) seeds.1)
    (BinaryFieldCodec.encode (oneShotHashExponent n ell e) seeds.2)))

end Algebraic.Cutwidth.Extractor
