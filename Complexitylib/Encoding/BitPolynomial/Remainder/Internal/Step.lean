/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Remainder.Internal.Width
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial
import Mathlib.Tactic.Ring

/-!
# The bounded long-division step

Inserting one coefficient raises the stored degree by at most one. The single
XOR cancellation removes its possible leading term, giving the unique monic
remainder while restoring the fixed state width.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

open Polynomial

theorem ofBits_cons (bit : Bool) (bits : List Bool) :
    ofBits (bit :: bits) = C (bit.toNat : ZMod 2) + X * ofBits bits := by
  ext k
  cases k with
  | zero => simp [BitPolynomial.ofBits_coeff]
  | succ k => simp [BitPolynomial.ofBits_coeff, Polynomial.coeff_X_mul]

theorem ofBits_replicate_false (n : Nat) : ofBits (List.replicate n false) = 0 := by
  ext k
  by_cases hk : k < n
  · simp [BitPolynomial.ofBits_coeff, hk]
  · have hout : (List.replicate n false)[k]? = none :=
      List.getElem?_eq_none (by simp only [List.length_replicate]; lia)
    rw [BitPolynomial.ofBits_coeff, hout]
    rfl

private theorem cast_xor_and (a b c : Bool) :
    ((Bool.xor a (b && c)).toNat : ZMod 2) =
      (a.toNat : ZMod 2) - (b.toNat : ZMod 2) * (c.toNat : ZMod 2) := by
  cases a <;> cases b <;> cases c <;> decide

theorem remainderStep_length (modulus : List Bool) (bit : Bool) (state : List Bool) :
    (remainderStep modulus bit state).length = significantLength modulus - 1 := by
  simp [remainderStep]

private theorem remainderStep_polynomial (modulus : List Bool) (bit : Bool) (state : List Bool)
    (hm : 0 < significantLength modulus)
    (hs : state.length = significantLength modulus - 1) :
    ofBits (remainderStep modulus bit state) = ofBits (bit :: state) -
      C (((bit :: state)[significantLength modulus - 1]?.getD false).toNat : ZMod 2) *
        ofBits modulus := by
  ext k
  rw [BitPolynomial.ofBits_coeff, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    BitPolynomial.ofBits_coeff, BitPolynomial.ofBits_coeff]
  by_cases hk : k < significantLength modulus - 1
  · rw [remainderStep, List.getElem?_map, List.getElem?_range hk]
    exact cast_xor_and _ _ _
  · have hout : (remainderStep modulus bit state)[k]? = none :=
      List.getElem?_eq_none (by rw [remainderStep_length]; lia)
    rw [hout]
    by_cases heq : k = significantLength modulus - 1
    · subst k
      rw [bit_at_significantLength modulus hm]
      simp
    · have hstate : (bit :: state)[k]? = none :=
        List.getElem?_eq_none (by simp only [List.length_cons]; lia)
      rw [hstate, bit_eq_false_of_significantLength_le modulus k (by lia)]
      simp

theorem remainderStep_correct (modulus : List Bool) (bit : Bool) (state : List Bool)
    (hm : 0 < significantLength modulus)
    (hs : state.length = significantLength modulus - 1) :
    ofBits (remainderStep modulus bit state) = ofBits (bit :: state) %ₘ ofBits modulus := by
  have hmonic := ofBits_isMonicOfDegree modulus hm
  refine ((Polynomial.div_modByMonic_unique
    (C (((bit :: state)[significantLength modulus - 1]?.getD false).toNat : ZMod 2))
    (ofBits (remainderStep modulus bit state)) hmonic.monic ⟨?_, ?_⟩).2).symm
  · rw [remainderStep_polynomial modulus bit state hm hs]
    ring
  · rw [Polynomial.degree_eq_natDegree hmonic.monic.ne_zero, hmonic.natDegree_eq,
      ← remainderStep_length modulus bit state]
    exact Polynomial.ofFn_degree_lt _

end BitPolynomial.Internal
end Complexity
