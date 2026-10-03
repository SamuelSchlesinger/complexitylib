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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary

/-!
# Runtime composition and linearity of one-shot extraction

The fixed-width serializer recovers the scheduled condenser's exact output.
The checked runtime hash then identifies the one-shot bit program with the
statistical composition. Each component preserves addition in the source.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Complexity.BitPolynomial

theorem encodeCondenserOutput_decodedExplicitCondenser (n k e u : Nat) (source : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    let T := explicitCondenserBudget n k e
    let s := sparseFieldExponent u T
    let m := condenserCoordinates k (sparsePowerBits u T)
    encodeCondenserOutput s m (decodedExplicitCondenser n k e u source seed) =
      explicitCondenserBits n k e u source (BinaryFieldCodec.encode s seed) := by
  dsimp only
  change encodeCondenserOutput _ _ (decodeCondenserOutput _ _ _) = _
  apply encode_decodeCondenserOutput
  exact explicitCondenserBits_length n k e u source _

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
          (decodedExplicitCondenser n (ell + 2 * e) (e + 1) 1 source seeds.1))) seeds.2 := by
  dsimp only
  erw [encodeCondenserOutput_decodedExplicitCondenser n (ell + 2 * e) (e + 1) 1 source seeds.1]
  exact decodedBinaryHash_eq _ _ _ _

theorem decodedOneShotExtractor_addBits (n ell e : Nat) (a b : List Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) :
    decodedOneShotExtractor n ell e (addBits a b) seeds =
      decodedOneShotExtractor n ell e a seeds + decodedOneShotExtractor n ell e b seeds := by
  simp only [decodedOneShotExtractor_eq_composition]
  dsimp only [oneShotCondenserExponent] at seeds ⊢
  rw [decodedExplicitCondenser_addBits n (ell + 2 * e) (e + 1) 1 a b seeds.1]
  simp only [encodeCondenserOutput_add, BinaryFieldCodec.decode_addBits, binaryFieldHash_add]

end Algebraic.Cutwidth.Extractor.Internal
