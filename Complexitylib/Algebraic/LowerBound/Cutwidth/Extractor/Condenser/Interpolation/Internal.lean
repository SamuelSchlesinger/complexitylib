/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A nonzero coefficient family satisfying fewer linear constraints

The interpolation family has `A * K` scalar coefficients. Evaluation at
each constraint is linear in those coefficients, so fewer than `A * K`
constraints leave a nonzero kernel vector. Grouping its coefficients gives
`K` polynomials of degree less than `A`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem exists_polynomial_interpolant {F X : Type*} [Field F] {A K : Nat}
    (T : Finset X) (seed : X → F) (weight : X → Fin K → F)
    (budget : T.card < A * K) :
    ∃ p : Fin K → Polynomial F, p ≠ 0 ∧
      (∀ j, (p j).degree < A) ∧
      ∀ x ∈ T, ∑ j, (p j).eval (seed x) * weight x j = 0 := by
  let eval : (Fin K × Fin A → F) →ₗ[F] (T → F) :=
    { toFun := fun c x => ∑ j, ∑ i, c (j, i) * seed x ^ i.val * weight x j
      map_add' := by
        intro c d
        funext x
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have dimension : Module.finrank F (T → F) <
      Module.finrank F (Fin K × Fin A → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using budget
  obtain ⟨c, hker, hc⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := eval) dimension)
  let p : Fin K → Polynomial F := fun j => Polynomial.ofFn A (fun i => c (j, i))
  refine ⟨p, ?_, fun j => Polynomial.ofFn_degree_lt _, ?_⟩
  · intro hp
    apply hc
    funext ji
    have row : Polynomial.ofFn A (fun i => c (ji.1, i)) = 0 := congrFun hp ji.1
    have zeroRow : (fun i => c (ji.1, i)) = 0 :=
      (Polynomial.injective_ofFn A) (row.trans (Polynomial.ofFn_zero A).symm)
    exact congrFun zeroRow ji.2
  · intro x hx
    have vanish := congrFun (LinearMap.mem_ker.mp hker) ⟨x, hx⟩
    simpa only [eval, LinearMap.coe_mk, AddHom.coe_mk, p,
      Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial, Finset.sum_mul, Pi.zero_apply] using vanish

end Algebraic.Cutwidth.Extractor.Internal
