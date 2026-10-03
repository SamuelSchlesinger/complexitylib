/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Primitive
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Quotient
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Interpolation
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Prod

/-!
# Polynomial graph expansion by interpolation and two root counts

The interpolation dimension and the quotient polynomial degree both use the
actual source size. The no-root condition on the modulus is used only to
normalize the interpolation coefficients.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem polynomialNeighbor_mem {F : Type*} [CommRing F] [Fintype F]
    (E : Polynomial F) (h m : Nat) (P : Finset (Polynomial F))
    {f : Polynomial F} (member : f ∈ P) (y : F) :
    polynomialNeighbor E h m f y ∈ polynomialNeighborSet E h m P := by
  apply Finset.mem_biUnion.mpr
  exact ⟨f, member, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩

theorem polynomialNeighbor_pow_two {F : Type*} [CommRing F]
    (E : Polynomial F) (r m : Nat) (f : Polynomial F) (y : F) :
    polynomialNeighbor E (2 ^ r) m f y = (y, polynomialCondenser E r m f y) := by
  refine Prod.ext (by rfl) ?_
  funext i
  exact (polynomialCondenser_apply E f r m y i).symm

theorem card_polynomialNeighborSet_of_degree_one {F : Type*} [Field F] [Fintype F]
    (E : Polynomial F) (monic : E.Monic) (degree : E.natDegree = 1)
    (h m : Nat) (P : Finset (Polynomial F))
    (source : ∀ f ∈ P, f.degree < E.degree) :
    (polynomialNeighborSet E h (m + 1) P).card = Fintype.card F * P.card := by
  have constant : ∀ f ∈ P, f = Polynomial.C (f.coeff 0) := by
    intro f member
    have small : f.degree < (1 : Nat) := by
      simpa only [Polynomial.degree_eq_natDegree monic.ne_zero, degree] using source f member
    apply Polynomial.eq_C_of_natDegree_eq_zero
    by_cases zero : f = 0
    · simp [zero]
    · have bound := (Polynomial.natDegree_lt_iff_degree_lt zero).mpr small
      lia
  let graph : Polynomial F × F → F × (Fin (m + 1) → F) :=
    fun x => polynomialNeighbor E h (m + 1) x.1 x.2
  have injective : Set.InjOn graph ↑(P ×ˢ (Finset.univ : Finset F)) := by
    intro a ha b hb same
    have memberA := (Finset.mem_product.mp ha).1
    have memberB := (Finset.mem_product.mp hb).1
    have seed : a.2 = b.2 := congrArg Prod.fst same
    have value := congrArg (fun x : F × (Fin (m + 1) → F) => x.2 0) same
    change (a.1 ^ (h ^ (0 : Fin (m + 1)).val) %ₘ E).eval a.2 =
      (b.1 ^ (h ^ (0 : Fin (m + 1)).val) %ₘ E).eval b.2 at value
    simp only [Fin.val_zero, pow_zero, pow_one] at value
    rw [(Polynomial.modByMonic_eq_self_iff monic).mpr (source a.1 memberA),
      (Polynomial.modByMonic_eq_self_iff monic).mpr (source b.1 memberB),
      constant a.1 memberA, constant b.1 memberB, Polynomial.eval_C,
      Polynomial.eval_C] at value
    apply Prod.ext _ seed
    rw [constant a.1 memberA, constant b.1 memberB, value]
  have representation : polynomialNeighborSet E h (m + 1) P =
      (P ×ˢ (Finset.univ : Finset F)).image graph := by
    ext x
    simp only [polynomialNeighborSet, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨f, member, y, same⟩
      exact ⟨(f, y), member, same⟩
    · rintro ⟨⟨f, y⟩, member, same⟩
      exact ⟨f, member, y, same⟩
  rw [representation, Finset.card_image_of_injOn injective]
  simp only [Finset.card_product, Finset.card_univ, mul_comm]

theorem le_card_polynomialNeighborSet {F : Type*} [Field F] [Fintype F]
    {A h m : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree) (base : 0 < h)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (size : P.card ≤ h ^ m)
    (budget : A + (E.natDegree - 1) * (h - 1) * m ≤ Fintype.card F) :
    A * P.card ≤ (polynomialNeighborSet E h m P).card := by
  apply le_of_not_gt
  intro small
  have positive : 0 < A := by
    by_contra notPositive
    have zero : A = 0 := by lia
    simp [zero] at small
  let T := polynomialNeighborSet E h m P
  let weight : F × (Fin m → F) → Fin P.card → F :=
    fun x j => digitMonomial h j.val x.2
  obtain ⟨p, nonzero, coeff, vanish⟩ :=
    exists_polynomial_interpolant T Prod.fst weight small
  have nonvanishing : ∀ x ∈ T, E.eval (Prod.fst x) ≠ 0 := by
    intro x _
    exact irreducible.not_isRoot_of_natDegree_ne_one (by lia)
  obtain ⟨p, _, coeff, vanish, primitive⟩ :=
    exists_primitive_polynomialFamily E monic (by lia) T Prod.fst weight
      nonvanishing p nonzero coeff vanish
  have substitutedZero : ∀ f ∈ P, substitutedSum E h m p f = 0 := by
    intro f member
    by_cases zero : substitutedSum E h m p f = 0
    · exact zero
    have roots : ∀ y : F, (substitutedSum E h m p f).eval y = 0 := by
      intro y
      rw [substitutedSum_eval]
      exact vanish (polynomialNeighbor E h m f y)
        (polynomialNeighbor_mem E h m P member y)
    have bound := substitutedSum_degree_lt (m := m) E p f monic positive base coeff
    have natBound := (Polynomial.natDegree_lt_iff_degree_lt zero).mpr bound
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      Function.injective_id roots (natBound.trans_le budget)
  have impossible := card_lt_of_quotient_polynomial_roots E monic irreducible
    p primitive P source (by
      intro f member
      rw [substitutedSum_quotient_eval E monic size, substitutedZero f member, map_zero])
  exact (lt_irrefl P.card) impossible

theorem polynomialNeighborSet_expansion {F : Type*} [Field F] [Fintype F]
    {h m : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree) (base : 0 < h)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (size : P.card ≤ h ^ m) :
    (Fintype.card F - (E.natDegree - 1) * (h - 1) * m) * P.card ≤
      (polynomialNeighborSet E h m P).card := by
  by_cases loss : (E.natDegree - 1) * (h - 1) * m ≤ Fintype.card F
  · exact le_card_polynomialNeighborSet E monic irreducible degree base P source size
      (Nat.sub_add_cancel loss).le
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge loss), zero_mul]
    exact Nat.zero_le _

end Algebraic.Cutwidth.Extractor.Internal
