/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Linear
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec
import Complexitylib.Encoding.BitPolynomial.Addition
import Mathlib.Data.List.OfFn

/-!
# Inverse laws for serialized condenser coordinates

Equal-width list blocks can be extracted and reassembled without losing
leading or trailing zeros. Applying the field codec's inverse laws to
each block gives exact serialization, including the empty-coordinate case.
The fixed runtime output length then identifies serialization of decoded
coordinates with the original output word.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial

private theorem coefficientBlock_flatten_ofFn (m width : Nat) (blocks : Fin m → List Bool)
    (length : ∀ i, (blocks i).length = width) (i : Fin m) :
    coefficientBlock (List.ofFn blocks).flatten width i.val = blocks i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coefficientBlock, Fin.val_zero, Nat.zero_mul, List.drop_zero,
        List.ofFn_succ, List.flatten_cons]
      exact List.take_left' (length 0)
    · simp only [coefficientBlock, Fin.val_succ, List.ofFn_succ, List.flatten_cons]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (j.val * width) width, ← length 0,
        List.drop_length_add_append]
      simpa only [coefficientBlock, ← length 0] using
        ih (fun j => blocks j.succ) (fun j => length j.succ) j

private theorem coefficientBlock_length_of_length (m width : Nat) (bits : List Bool)
    (length : bits.length = m * width) (i : Fin m) :
    (coefficientBlock bits width i.val).length = width := by
  have bound := Nat.mul_le_mul_right width i.isLt
  rw [Nat.succ_mul] at bound
  simp only [coefficientBlock, List.length_take, List.length_drop, length]
  exact min_eq_left (by lia)

private theorem flatten_coefficientBlocks (m width : Nat) (bits : List Bool)
    (length : bits.length = m * width) :
    (List.ofFn fun i : Fin m => coefficientBlock bits width i.val).flatten = bits := by
  induction m generalizing bits with
  | zero =>
    have empty : bits = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
    simp [empty]
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    have rest : (bits.drop width).length = m * width := by
      simp only [List.length_drop, length, Nat.succ_mul]
      lia
    have tail : (fun i : Fin m => coefficientBlock bits width i.succ.val) =
        (fun i : Fin m => coefficientBlock (bits.drop width) width i.val) := by
      funext i
      simp only [coefficientBlock, Fin.val_succ, Nat.add_mul, Nat.one_mul, List.drop_drop,
        Nat.add_comm]
    rw [tail, ih (bits.drop width) rest]
    simp only [coefficientBlock, Fin.val_zero, Nat.zero_mul, List.drop_zero,
      List.take_append_drop]

theorem encodeCondenserOutput_length (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) :
    (encodeCondenserOutput s m coords).length = m * (2 * 3 ^ s) := by
  simp [encodeCondenserOutput, List.map_ofFn, Function.comp_def, BinaryFieldCodec.length_encode]

theorem coefficientBlock_encodeCondenserOutput (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) (i : Fin m) :
    coefficientBlock (encodeCondenserOutput s m coords) (2 * 3 ^ s) i.val =
      BinaryFieldCodec.encode s (coords i) :=
  coefficientBlock_flatten_ofFn m (2 * 3 ^ s) _ (fun _ => BinaryFieldCodec.length_encode s _) i

theorem decode_encodeCondenserOutput (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) :
    decodeCondenserOutput s m (encodeCondenserOutput s m coords) = coords := by
  funext i
  rw [decodeCondenserOutput, coefficientBlock_encodeCondenserOutput,
    BinaryFieldCodec.decode_encode]

theorem encode_decodeCondenserOutput (s m : Nat) (bits : List Bool)
    (length : bits.length = m * (2 * 3 ^ s)) :
    encodeCondenserOutput s m (decodeCondenserOutput s m bits) = bits := by
  unfold encodeCondenserOutput decodeCondenserOutput
  have each (i : Fin m) :
      BinaryFieldCodec.encode s
        (BinaryFieldCodec.decode s (coefficientBlock bits (2 * 3 ^ s) i.val)) =
          coefficientBlock bits (2 * 3 ^ s) i.val :=
    BinaryFieldCodec.encode_decode s _ (coefficientBlock_length_of_length m _ bits length i)
  simp only [each]
  exact flatten_coefficientBlocks m _ bits length

theorem encodeCondenserOutput_injective (s m : Nat) :
    Function.Injective (encodeCondenserOutput s m) :=
  Function.LeftInverse.injective (decode_encodeCondenserOutput s m)

theorem decodeCondenserOutput_addBits (s m : Nat) (a b : List Bool) :
    decodeCondenserOutput s m (addBits a b) =
      decodeCondenserOutput s m a + decodeCondenserOutput s m b := by
  funext i
  simp only [decodeCondenserOutput, Pi.add_apply]
  have coefficients := congrArg (fun p => p.coeff i.val) (sourcePolynomial_addBits s m a b)
  simpa only [sourcePolynomial, Polynomial.coeff_add,
    Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt] using coefficients

theorem encodeCondenserOutput_add (s m : Nat)
    (a b : Fin m → AdjoinRoot (binaryModulus s)) :
    encodeCondenserOutput s m (a + b) =
      addBits (encodeCondenserOutput s m a) (encodeCondenserOutput s m b) := by
  have same := decodeCondenserOutput_addBits s m
    (encodeCondenserOutput s m a) (encodeCondenserOutput s m b)
  rw [decode_encodeCondenserOutput, decode_encodeCondenserOutput] at same
  rw [← same]
  apply encode_decodeCondenserOutput
  simp only [addBits_length, encodeCondenserOutput_length, Nat.max_self]

theorem encodeCondenserOutput_decodedCondenser (s : Nat)
    (halfDegree extensionCount stride count bits : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) (half : halfDegree.length = 3 ^ s) :
    encodeCondenserOutput s count.length
        (decodedCondenser s halfDegree extensionCount stride count bits seed) =
      condenserBits bits halfDegree extensionCount (BinaryFieldCodec.encode s seed)
        stride count := by
  apply encode_decodeCondenserOutput
  rw [condenserBits_length, half]

end Algebraic.Cutwidth.Extractor.Internal
