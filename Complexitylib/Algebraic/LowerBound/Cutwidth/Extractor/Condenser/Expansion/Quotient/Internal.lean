/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution.Defs
public import Mathlib.RingTheory.AdjoinRoot
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials
import Mathlib.Algebra.Polynomial.Roots

/-!
# Quotient substitution and the final polynomial root bound

Reducing source powers modulo `E` does not change their classes in `AdjoinRoot E`.
The base-`h` monomials then become distinct powers indexed by `Fin K`. A surviving
coefficient makes the resulting polynomial nonzero of degree below `K`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem mk_modByMonic {F : Type*} [Field F]
    (E : Polynomial F) (monic : E.Monic) (p : Polynomial F) :
    AdjoinRoot.mk E (p %ₘ E) = AdjoinRoot.mk E p :=
  AdjoinRoot.mk_leftInverse monic (AdjoinRoot.mk E p)

private theorem mk_injectiveOn_reduced {F : Type*} [Field F]
    (E : Polynomial F) (monic : E.Monic) :
    Set.InjOn (AdjoinRoot.mk E) {f | f.degree < E.degree} := by
  intro f hf g hg same
  have reduced := congrArg (AdjoinRoot.modByMonicHom monic) same
  simpa only [AdjoinRoot.modByMonicHom_mk,
    (Polynomial.modByMonic_eq_self_iff monic).mpr hf,
    (Polynomial.modByMonic_eq_self_iff monic).mpr hg] using reduced

theorem substitutedSum_quotient_eval {F : Type*} [Field F] {h K m : Nat}
    (E : Polynomial F) (monic : E.Monic) (bound : K ≤ h ^ m)
    (p : Fin K → Polynomial F) (f : Polynomial F) :
    (∑ j : Fin K, Polynomial.monomial j.val (AdjoinRoot.mk E (p j))).eval
        (AdjoinRoot.mk E f) = AdjoinRoot.mk E (substitutedSum E h m p f) := by
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, substitutedSum,
    map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  have monomial : AdjoinRoot.mk E
      (digitMonomial h j.val (fun i : Fin m => f ^ (h ^ i.val) %ₘ E)) =
        (AdjoinRoot.mk E f) ^ j.val := by
    simp only [digitMonomial, map_prod, map_pow, mk_modByMonic E monic]
    exact digitMonomial_pow (j.isLt.trans_le bound) (AdjoinRoot.mk E f)
  rw [monomial]

theorem card_lt_of_quotient_polynomial_roots {F : Type*} [Field F] {K : Nat}
    (E : Polynomial F) (monic : E.Monic) (irreducible : Irreducible E)
    (p : Fin K → Polynomial F) (primitive : ∃ j, ¬ E ∣ p j)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (roots : ∀ f ∈ P,
      (∑ j : Fin K, Polynomial.monomial j.val (AdjoinRoot.mk E (p j))).eval
        (AdjoinRoot.mk E f) = 0) : P.card < K := by
  let : Fact (Irreducible E) := ⟨irreducible⟩
  let Q : Polynomial (AdjoinRoot E) :=
    ∑ j : Fin K, Polynomial.monomial j.val (AdjoinRoot.mk E (p j))
  have nonzero : Q ≠ 0 := by
    apply (fin_monomial_sum_ne_zero_iff _).mpr
    obtain ⟨j, hj⟩ := primitive
    exact ⟨j, AdjoinRoot.mk_eq_zero.not.mpr hj⟩
  have degree : Q.natDegree < K :=
    (Polynomial.natDegree_lt_iff_degree_lt nonzero).mpr (fin_monomial_sum_degree_lt _)
  have imageCard : (P.image (AdjoinRoot.mk E)).card = P.card :=
    Finset.card_image_of_injOn fun f hf g hg same =>
      mk_injectiveOn_reduced E monic (source f hf) (source g hg) same
  have rootSubset : (P.image (AdjoinRoot.mk E)).val ⊆ Q.roots := by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
    exact (Polynomial.mem_roots nonzero).mpr (roots f hf)
  have count := Polynomial.card_le_degree_of_subset_roots rootSubset
  rw [imageCard] at count
  exact count.trans_lt degree

end Algebraic.Cutwidth.Extractor.Internal
