/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
import Complexitylib.Encoding.BitPolynomial
import Complexitylib.Encoding.BitPolynomial.Addition
import Complexitylib.Encoding.BitPolynomial.Frobenius
import Complexitylib.Encoding.BitPolynomial.Remainder
import Mathlib.Tactic.FinCases

/-!
# The canonical binary quotient codec round trips

Coefficients of the monic remainder lie in the two-element field, so the
zero/one bit conversion is exact. The remainder's strict degree bound makes
the fixed coefficient list complete.
-/

public section

namespace Algebraic.Cutwidth.Extractor.BinaryFieldCodec.Internal

private theorem cast_bit (c : ZMod 2) : ((decide (c = 1)).toNat : ZMod 2) = c := by
  have cases : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases with rfl | rfl <;> decide

private theorem bit_cast (b : Bool) : decide ((b.toNat : ZMod 2) = 1) = b := by
  cases b <;> decide

theorem length_encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    (encode s x).length = 2 * 3 ^ s := by
  simp only [encode, List.length_ofFn]

private theorem remainder_degree (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    (AdjoinRoot.modByMonicHom (binaryModulus_monic s) x).degree <
      ((2 * 3 ^ s : Nat) : WithBot Nat) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [AdjoinRoot.modByMonicHom_mk]
    have bound := Polynomial.degree_modByMonic_lt p (binaryModulus_monic s)
    simpa only [Polynomial.degree_eq_natDegree (binaryModulus_monic s).ne_zero,
      binaryModulus_natDegree] using bound

theorem ofBits_encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    Complexity.BitPolynomial.ofBits (encode s x) =
      AdjoinRoot.modByMonicHom (binaryModulus_monic s) x := by
  ext k
  rw [Complexity.BitPolynomial.ofBits_coeff]
  by_cases small : k < 2 * 3 ^ s
  · simp only [encode, List.getElem?_ofFn, small, dite_eq_left, Option.getD_some]
    exact cast_bit _
  · rw [List.getElem?_eq_none (by rw [length_encode]; lia), Option.getD_none,
      Bool.toNat_false, Nat.cast_zero]
    symm
    apply Polynomial.coeff_eq_zero_of_degree_lt
    exact (remainder_degree s x).trans_le (by exact_mod_cast (Nat.le_of_not_gt small))

theorem decode_encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) :
    decode s (encode s x) = x := by
  rw [decode, ofBits_encode]
  exact AdjoinRoot.mk_leftInverse (binaryModulus_monic s) x

theorem encode_decode (s : Nat) (bits : List Bool) (length : bits.length = 2 * 3 ^ s) :
    encode s (decode s bits) = bits := by
  have degree : (Complexity.BitPolynomial.ofBits bits).degree < (binaryModulus s).degree := by
    rw [Polynomial.degree_eq_natDegree (binaryModulus_monic s).ne_zero,
      binaryModulus_natDegree, ← length]
    exact Polynomial.ofFn_degree_lt _
  have reduced := (Polynomial.modByMonic_eq_self_iff (binaryModulus_monic s)).mpr degree
  apply List.ext_getElem ((length_encode s _).trans length.symm)
  intro k hk hbits
  simp only [encode, List.getElem_ofFn, decode, AdjoinRoot.modByMonicHom_mk,
    reduced, Complexity.BitPolynomial.ofBits_coeff, List.getElem?_eq_getElem hbits,
    Option.getD_some]
  exact bit_cast _

theorem decode_addBits (s : Nat) (a b : List Bool) :
    decode s (Complexity.BitPolynomial.addBits a b) = decode s a + decode s b := by
  simp only [decode, Complexity.BitPolynomial.ofBits_addBits, map_add]

theorem decode_mulBits (s : Nat) (a b : List Bool) :
    decode s (Complexity.BitPolynomial.mulBits a b) = decode s a * decode s b := by
  simp only [decode, Complexity.BitPolynomial.ofBits_mulBits, map_mul]

private theorem mk_modByMonic (s : Nat) (p : Polynomial (ZMod 2)) :
    AdjoinRoot.mk (binaryModulus s) (p %ₘ binaryModulus s) =
      AdjoinRoot.mk (binaryModulus s) p :=
  AdjoinRoot.mk_leftInverse (binaryModulus_monic s) (AdjoinRoot.mk (binaryModulus s) p)

theorem decode_remainderBits (s : Nat) (a modulus : List Bool)
    (represents : Complexity.BitPolynomial.ofBits modulus = binaryModulus s) :
    decode s (Complexity.BitPolynomial.remainderBits a modulus) = decode s a := by
  simp only [decode, Complexity.BitPolynomial.ofBits_remainderBits, represents, mk_modByMonic]

theorem decode_frobeniusBits (s : Nat) (a modulus count : List Bool)
    (represents : Complexity.BitPolynomial.ofBits modulus = binaryModulus s) :
    decode s (Complexity.BitPolynomial.frobeniusBits a modulus count) =
      decode s a ^ (2 ^ count.length) := by
  have nonzero : Complexity.BitPolynomial.ofBits modulus ≠ 0 := by
    rw [represents]
    exact (binaryModulus_monic s).ne_zero
  simp only [decode, Complexity.BitPolynomial.ofBits_frobeniusBits a modulus count nonzero,
    represents, mk_modByMonic, map_pow]

end Algebraic.Cutwidth.Extractor.BinaryFieldCodec.Internal
