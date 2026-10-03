/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Removing common modulus factors from an interpolating family

If every coefficient polynomial is divisible by the modulus, divide each by
it. The family stays nonzero, its degree budget decreases, and its weighted
evaluation constraints persist wherever the modulus evaluates nonzero.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem exists_primitive_polynomialFamily {F X : Type*} [Field F] {A K : Nat}
    (E : Polynomial F) (monic : E.Monic) (positive : 0 < E.natDegree)
    (T : Finset X) (seed : X → F) (weight : X → Fin K → F)
    (nonvanishing : ∀ x ∈ T, E.eval (seed x) ≠ 0)
    (p : Fin K → Polynomial F) (nonzero : p ≠ 0)
    (degree : ∀ j, (p j).degree < A)
    (vanish : ∀ x ∈ T, ∑ j, (p j).eval (seed x) * weight x j = 0) :
    ∃ q : Fin K → Polynomial F, q ≠ 0 ∧
      (∀ j, (q j).degree < A) ∧
      (∀ x ∈ T, ∑ j, (q j).eval (seed x) * weight x j = 0) ∧
      ∃ j, ¬ E ∣ q j := by
  induction A generalizing p with
  | zero =>
      exfalso
      apply nonzero
      funext j
      by_contra hn
      have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hn).mpr (degree j)
      lia
  | succ A ih =>
      by_cases primitive : ∃ j, ¬ E ∣ p j
      · exact ⟨p, nonzero, degree, vanish, primitive⟩
      have divides : ∀ j, E ∣ p j := by
        intro j
        by_contra hn
        exact primitive ⟨j, hn⟩
      let q : Fin K → Polynomial F := fun j => p j /ₘ E
      have factor (j : Fin K) : E * q j = p j := by
        have hrem : p j %ₘ E = 0 :=
          (Polynomial.modByMonic_eq_zero_iff_dvd monic).mpr (divides j)
        simpa only [hrem, zero_add] using Polynomial.modByMonic_add_div (p j) E
      have qnonzero : q ≠ 0 := by
        intro hq
        apply nonzero
        funext j
        rw [← factor j, hq]
        simp
      have qdegree (j : Fin K) : (q j).degree < A := by
        by_cases hq : q j = 0
        · rw [hq, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe A
        have hp : p j ≠ 0 := by
          rw [← factor j]
          exact mul_ne_zero monic.ne_zero hq
        have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (degree j)
        rw [← factor j, Polynomial.natDegree_mul monic.ne_zero hq] at hdeg
        apply (Polynomial.natDegree_lt_iff_degree_lt hq).mp
        lia
      have qvanish (x : X) (hx : x ∈ T) :
          ∑ j, (q j).eval (seed x) * weight x j = 0 := by
        have scale : E.eval (seed x) * (∑ j, (q j).eval (seed x) * weight x j) =
            ∑ j, (p j).eval (seed x) * weight x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← factor j, Polynomial.eval_mul, mul_assoc]
        exact (mul_eq_zero.mp (scale.trans (vanish x hx))).resolve_left (nonvanishing x hx)
      obtain ⟨v, hv, hvdegree, hvvanish, hvprimitive⟩ := ih q qnonzero qdegree qvanish
      refine ⟨v, hv, fun j => (hvdegree j).trans ?_, hvvanish, hvprimitive⟩
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self A)

end Algebraic.Cutwidth.Extractor.Internal
