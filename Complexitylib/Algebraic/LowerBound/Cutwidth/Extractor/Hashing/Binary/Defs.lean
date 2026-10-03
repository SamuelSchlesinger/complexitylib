/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec.Defs
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs

/-!
# Binary field multiplication followed by a coefficient prefix

The semantic projection reads the first `m` coefficients of the unique
remainder representing a binary field element. The concrete list program
multiplies two input words, reduces modulo a generated trinomial, and takes
the requested prefix. This is the linear universal hash used by the
leftover-hash construction, specialized to our explicit binary fields.

Field and statistical claims require the intended power-of-three modulus
degree and an output width no larger than the field width. The runtime
definitions are total without those promises.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- The first `m` coefficients of the canonical field representative. -/
noncomputable def binaryCoefficientPrefix (s m : Nat) :
    AdjoinRoot (binaryModulus s) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  (Polynomial.toFn m).comp (AdjoinRoot.modByMonicHom (binaryModulus_monic s))

/-- Linear hashing with one uniform binary field element as seed. -/
noncomputable def binaryFieldHash (s m : Nat)
    (source seed : AdjoinRoot (binaryModulus s)) : Fin m → ZMod 2 :=
  binaryCoefficientPrefix s m (seed * source)

/-- Multiply, reduce modulo the generated binary trinomial, and retain a prefix. -/
def binaryHashBits (source seed halfDegree outputCount : List Bool) : List Bool :=
  (remainderBits (mulBits seed source) (trinomialBits halfDegree.length)).take outputCount.length

/-- Codec: `pair (pair source seed) (pair halfDegree outputCount)`. -/
def binaryHashEval (z : List Bool) : List Bool :=
  binaryHashBits (pairFst (pairFst z)) (pairSnd (pairFst z))
    (pairFst (pairSnd z)) (pairSnd (pairSnd z))

/-- The actual hash program, read as binary coordinates at a semantic field seed. -/
noncomputable def decodedBinaryHash (s m : Nat) (source : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) : Fin m → ZMod 2 :=
  Polynomial.toFn m (ofBits (binaryHashBits source (BinaryFieldCodec.encode s seed)
    (List.replicate (3 ^ s) true) (List.replicate m true)))

end Algebraic.Cutwidth.Extractor
