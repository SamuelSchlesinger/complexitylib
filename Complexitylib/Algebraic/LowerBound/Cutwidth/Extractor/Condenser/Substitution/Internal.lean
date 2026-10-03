/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

/-!
# Degree and evaluation bounds for the substituted interpolation polynomial

Reduction bounds each source-power coordinate by one less than the modulus
degree. A base-`h` monomial uses at most `h - 1` copies of each coordinate,
so its degree grows by at most `(n - 1) * (h - 1) * m`. Multiplication by a
coefficient polynomial of degree below `A` leaves degree below that quantity
plus `A`. No bound on the unreduced source polynomial is needed here.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem natDegree_digitMonomial_le {F : Type*} [CommSemiring F]
    {m d : Nat} (g : Fin m → Polynomial F) (bound : ∀ i, (g i).natDegree ≤ d)
    {h : Nat} (positive : 0 < h) (j : Nat) :
    (digitMonomial h j g).natDegree ≤ d * (h - 1) * m := by
  calc
    (digitMonomial h j g).natDegree ≤
        ∑ i, ((g i) ^ monomialDigit h j i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin m, (h - 1) * d := by
      apply Finset.sum_le_sum
      intro i _
      exact Polynomial.natDegree_pow_le.trans
        (Nat.mul_le_mul (Nat.le_sub_one_of_lt (Nat.mod_lt _ positive)) (bound i))
    _ = d * (h - 1) * m := by simp; ring

theorem substitutedSum_eval {F : Type*} [CommRing F] {K : Nat}
    (E : Polynomial F) (h m : Nat) (p : Fin K → Polynomial F) (f : Polynomial F) (y : F) :
    (substitutedSum E h m p f).eval y =
      ∑ j, (p j).eval y * digitMonomial h j.val
        (fun i : Fin m => (f ^ (h ^ i.val) %ₘ E).eval y) := by
  simp only [substitutedSum, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    digitMonomial, Polynomial.eval_prod, Polynomial.eval_pow]

theorem substitutedSum_natDegree_le {F : Type*} [CommRing F]
    {K A h m : Nat} (E : Polynomial F) (p : Fin K → Polynomial F) (f : Polynomial F)
    (monic : E.Monic) (base : 0 < h)
    (coeff : ∀ j, (p j).degree < A) :
    (substitutedSum E h m p f).natDegree ≤
      (A - 1) + (E.natDegree - 1) * (h - 1) * m := by
  have coordinate (i : Fin m) : (f ^ (h ^ i.val) %ₘ E).natDegree ≤ E.natDegree - 1 := by
    by_cases he : E = 1
    · simp [he]
    · exact Nat.le_sub_one_of_lt (Polynomial.natDegree_modByMonic_lt _ monic he)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply Polynomial.natDegree_mul_le.trans
  apply Nat.add_le_add
  · by_cases hj : p j = 0
    · simp [hj]
    · exact Nat.le_sub_one_of_lt ((Polynomial.natDegree_lt_iff_degree_lt hj).mpr (coeff j))
  · exact natDegree_digitMonomial_le _ coordinate base j.val

theorem substitutedSum_degree_lt {F : Type*} [CommRing F]
    {K A h m : Nat} (E : Polynomial F) (p : Fin K → Polynomial F) (f : Polynomial F)
    (monic : E.Monic) (positive : 0 < A) (base : 0 < h)
    (coeff : ∀ j, (p j).degree < A) :
    (substitutedSum E h m p f).degree <
      (A + (E.natDegree - 1) * (h - 1) * m : Nat) := by
  have hn := substitutedSum_natDegree_le (m := m) E p f monic base coeff
  have strict : (substitutedSum E h m p f).natDegree <
      A + (E.natDegree - 1) * (h - 1) * m := by lia
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast strict)

end Algebraic.Cutwidth.Extractor.Internal
