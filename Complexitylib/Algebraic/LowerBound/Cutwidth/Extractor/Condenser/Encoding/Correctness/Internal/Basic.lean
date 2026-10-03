/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
import Complexitylib.Encoding.BitPolynomial
import Complexitylib.Encoding.BitPolynomial.BlockEval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Polynomial evaluation of padded coefficient data

Bit interpretation is unchanged by padding to a larger fixed width. Expanding
the polynomial as a finite coefficient sum makes both the packing convention
and the Horner evaluator's interpretation explicit.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity.BitPolynomial
open scoped Classical

theorem sourcePolynomial_degree_lt (s d : Nat) (bits : List Bool) :
    (sourcePolynomial s d bits).degree < (d : WithBot Nat) :=
  Polynomial.ofFn_degree_lt _

theorem eval₂_ofFn {R S : Type*} [Semiring R] [DecidableEq R] [CommSemiring S]
    (f : R →+* S) (x : S) {n : Nat} (coeffs : Fin n → R) :
    (Polynomial.ofFn n coeffs).eval₂ f x =
      ∑ j : Fin n, f (coeffs j) * x ^ j.val := by
  simp only [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]

theorem ofBits_eq_ofFn_padded (bits : List Bool) (n : Nat) (length : bits.length ≤ n) :
    ofBits bits = Polynomial.ofFn n fun j => ((bits[j.val]?.getD false).toNat : ZMod 2) := by
  ext k
  rw [ofBits_coeff]
  by_cases hk : k < n
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk),
      List.getElem?_eq_none (by lia)]
    rfl

theorem eval₂_ofBits_padded {R : Type*} [CommSemiring R] (f : ZMod 2 →+* R)
    (x : R) (bits : List Bool) (n : Nat) (length : bits.length ≤ n) :
    (ofBits bits).eval₂ f x =
      ∑ j : Fin n, f ((bits[j.val]?.getD false).toNat : ZMod 2) * x ^ j.val := by
  rw [ofBits_eq_ofFn_padded bits n length, eval₂_ofFn]

theorem coefficientBlock_getD (bits : List Bool) (width j i : Nat) (hi : i < width) :
    (coefficientBlock bits width j)[i]?.getD false = bits[j * width + i]?.getD false := by
  simp only [coefficientBlock, List.getElem?_take, hi, ite_true, List.getElem?_drop]

theorem sum_fin_mul {R : Type*} [AddCommMonoid R] (m n : Nat) (f : Nat → R) :
    (∑ k : Fin (m * n), f k.val) =
      ∑ i : Fin m, ∑ j : Fin n, f (i.val * n + j.val) := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)), Fintype.sum_prod_type]
  change (∑ i : Fin m, ∑ j : Fin n, f (j.val + n * i.val)) = _
  simp only [Nat.add_comm, Nat.mul_comm]

end Algebraic.Cutwidth.Extractor.Internal
