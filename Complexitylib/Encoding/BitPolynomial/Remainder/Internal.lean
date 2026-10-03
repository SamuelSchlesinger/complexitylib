/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial.Remainder.Internal.Step

/-!
# Correctness and bounds for binary-polynomial remainder

The scan maintains the monic remainder of the coefficients already read. Its
fixed width gives a state bound independent of the dividend length, and the
outer zero-modulus branch agrees with `Polynomial.modByMonic_zero`.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

open Polynomial

theorem remainderScan_length (modulus a : List Bool) :
    (remainderScan modulus a).length = significantLength modulus - 1 := by
  cases a with
  | nil => simp [remainderScan]
  | cons bit tail => exact remainderStep_length modulus bit (remainderScan modulus tail)

private theorem insert_modByMonic (bit : Bool) (p modulus : Polynomial (ZMod 2))
    (hm : modulus.Monic) :
    (C (bit.toNat : ZMod 2) + X * (p %ₘ modulus)) %ₘ modulus =
      (C (bit.toNat : ZMod 2) + X * p) %ₘ modulus := by
  rw [Polynomial.add_modByMonic, Polynomial.add_modByMonic]
  congr 1
  rw [Polynomial.mul_modByMonic X (p %ₘ modulus), Polynomial.mul_modByMonic X p]
  rw [(Polynomial.modByMonic_eq_self_iff hm).mpr (Polynomial.degree_modByMonic_lt p hm)]

theorem remainderScan_correct (modulus a : List Bool) (hm : 0 < significantLength modulus) :
    ofBits (remainderScan modulus a) = ofBits a %ₘ ofBits modulus := by
  induction a with
  | nil =>
      rw [remainderScan, ofBits_replicate_false]
      simp [ofBits]
  | cons bit tail ih =>
      rw [remainderScan, remainderStep_correct modulus bit _ hm (remainderScan_length _ _),
        ofBits_cons, ih, ofBits_cons]
      exact insert_modByMonic bit (ofBits tail) (ofBits modulus)
        (ofBits_isMonicOfDegree modulus hm).monic

theorem remainderBits_length (a modulus : List Bool) :
    (remainderBits a modulus).length =
      if significantLength modulus = 0 then a.length else significantLength modulus - 1 := by
  by_cases hm : significantLength modulus = 0
  · simp [remainderBits, hm]
  · simp [remainderBits, hm, remainderScan_length]

theorem remainderBits_length_le (a modulus : List Bool) :
    (remainderBits a modulus).length ≤ max a.length modulus.length := by
  rw [remainderBits_length]
  split
  · exact le_max_left _ _
  · exact ((Nat.sub_le _ _).trans (significantLength_le modulus)).trans (le_max_right _ _)

theorem ofBits_remainderBits (a modulus : List Bool) :
    ofBits (remainderBits a modulus) = ofBits a %ₘ ofBits modulus := by
  by_cases hm : significantLength modulus = 0
  · rw [remainderBits, ite_eq_left hm, (significantLength_eq_zero_iff modulus).mp hm,
      Polynomial.modByMonic_zero]
  · rw [remainderBits, ite_eq_right hm]
    exact remainderScan_correct modulus a (Nat.pos_of_ne_zero hm)

end BitPolynomial.Internal
end Complexity
