/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Correctness.Internal

/-!
# The one-shot bit program computes the linear statistical composition

Encoding the decoded explicit condenser recovers its exact runtime word.
Hashing that word therefore gives the same map used by the probability
argument. For every pair of fixed seeds, this actual map preserves source
XOR. The identity holds even outside the fixed-length source promise.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Serialization recovers the exact scheduled condenser output. -/
theorem encodeCondenserOutput_decodedExplicitCondenser (n k e u : Nat) (source : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    let T := explicitCondenserBudget n k e
    let s := sparseFieldExponent u T
    let m := condenserCoordinates k (sparsePowerBits u T)
    encodeCondenserOutput s m (decodedExplicitCondenser n k e u source seed) =
      explicitCondenserBits n k e u source (BinaryFieldCodec.encode s seed) :=
  Internal.encodeCondenserOutput_decodedExplicitCondenser n k e u source seed

/-- The decoded bit program is condensation, exact serialization, and field hashing. -/
theorem decodedOneShotExtractor_eq_composition (n ell e : Nat) (source : List Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) :
    let T := explicitCondenserBudget n (ell + 2 * e) (e + 1)
    let sC := oneShotCondenserExponent n ell e
    let sH := oneShotHashExponent n ell e
    let m := condenserCoordinates (ell + 2 * e) (sparsePowerBits 1 T)
    decodedOneShotExtractor n ell e source seeds =
      binaryFieldHash sH ell (BinaryFieldCodec.decode sH
        (encodeCondenserOutput sC m
          (decodedExplicitCondenser n (ell + 2 * e) (e + 1) 1 source seeds.1))) seeds.2 :=
  Internal.decodedOneShotExtractor_eq_composition n ell e source seeds

/-- For fixed seeds, the actual output preserves padded XOR of source words. -/
theorem decodedOneShotExtractor_addBits (n ell e : Nat) (a b : List Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) :
    decodedOneShotExtractor n ell e (Complexity.BitPolynomial.addBits a b) seeds =
      decodedOneShotExtractor n ell e a seeds + decodedOneShotExtractor n ell e b seeds :=
  Internal.decodedOneShotExtractor_addBits n ell e a b seeds

end Algebraic.Cutwidth.Extractor
