/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Affine restrictions of inversion in characteristic two

The reciprocal identity on a nondegenerate affine plane excludes affine
restrictions with more than four points. Scaling one additive defect also rules
out every nonzero additive component of inversion over a field larger than four.

The affine-plane obstruction is a special case of the inverse-function sum
identities discussed by Claude Carlet, "On the vector subspaces of F₂ⁿ over which
the multiplicative inverse function sums to zero", Designs, Codes and Cryptography
93 (2025), 1237–1254, https://doi.org/10.1007/s10623-024-01531-6.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Inversion

variable {K : Type*} [Field K] [CharP K 2]

/-- A reciprocal ternary identity forces a repeated point or a zero entry. -/
theorem eq_of_inverse_three {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hs : a + b + c ≠ 0)
    (identity : (a + b + c)⁻¹ = a⁻¹ + b⁻¹ + c⁻¹) :
    a = b ∨ a = c ∨ b = c := by
  have product : (a + b) * (a + c) * (b + c) = 0 := by
    field_simp at identity
    linear_combination (norm := ring_nf) identity
    have two : (2 : K) = 0 := CharTwo.two_eq_zero
    have four : (4 : K) = 0 := by linear_combination 2 * two
    simp only [two, four, mul_zero, add_zero]
  rcases mul_eq_zero.mp product with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by simpa only [CharTwo.add_eq_zero] using h)
    · exact Or.inr (Or.inl (by simpa only [CharTwo.add_eq_zero] using h))
  · exact Or.inr (Or.inr (by simpa only [CharTwo.add_eq_zero] using h))

/-- Inversion preserves ternary addition on at most four points of a binary field. -/
theorem card_le_four_of_inverse_affine (S : Finset K)
    (affine : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      (a + b + c)⁻¹ = a⁻¹ + b⁻¹ + c⁻¹) : S.card ≤ 4 := by
  classical
  by_cases zero : ∀ a ∈ S, a = 0
  · have sub : S ⊆ {0} := by
      intro x hx
      simp only [Finset.mem_singleton]
      exact zero x hx
    have := Finset.card_le_card sub
    simp only [Finset.card_singleton] at this
    lia
  push Not at zero
  obtain ⟨a, ha, ane⟩ := zero
  by_cases pair : ∀ b ∈ S, b = 0 ∨ b = a
  · have sub : S ⊆ {0, a} := by
      intro x hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using pair x hx
    exact (Finset.card_le_card sub).trans (Finset.card_le_two.trans (by decide))
  push Not at pair
  obtain ⟨b, hb, bne, ba⟩ := pair
  have sub : S ⊆ {0, a, b, a + b} := by
    intro c hc
    by_cases cz : c = 0
    · simp [cz]
    by_cases ca : c = a
    · simp [ca]
    by_cases cb : c = b
    · simp [cb]
    by_cases sum : a + b + c = 0
    · have eq : c = a + b := (CharTwo.add_eq_zero.mp sum).symm
      simp [eq]
    have repeated := eq_of_inverse_three ane bne cz sum (affine a ha b hb c hc)
    rcases repeated with h | h | h
    · exact (ba h.symm).elim
    · exact (ca h.symm).elim
    · exact (cb h.symm).elim
  exact (Finset.card_le_card sub).trans Finset.card_le_four

/-- A binary field with more than four elements has an additive inversion defect. -/
theorem exists_inverse_add_defect [Fintype K] (large : 4 < Fintype.card K) :
    ∃ a b : K, (a + b)⁻¹ ≠ a⁻¹ + b⁻¹ := by
  by_contra absent
  push Not at absent
  have small := card_le_four_of_inverse_affine (Finset.univ : Finset K)
    (fun a _ b _ c _ => by rw [absent, absent])
  simp only [Finset.card_univ] at small
  lia

/-- No nonzero additive component of inversion is additive over a field larger than four. -/
theorem eq_zero_of_additive_inverse_component [Fintype K] (large : 4 < Fintype.card K)
    (L R : K →+ ZMod 2) (component : ∀ x, L x⁻¹ = R x) : L = 0 := by
  obtain ⟨a, b, defect⟩ := exists_inverse_add_defect large
  let d := a⁻¹ + b⁻¹ + (a + b)⁻¹
  have dne : d ≠ 0 := by
    intro zero
    exact defect (CharTwo.add_eq_zero.mp zero).symm
  have vanishes (t : K) : L (d * t⁻¹) = 0 := by
    dsimp only [d]
    rw [add_mul, add_mul, ← mul_inv, ← mul_inv, ← mul_inv,
      map_add, map_add, component, component, component, add_mul, map_add]
    exact CharTwo.add_self_eq_zero _
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have same : d * (d / x)⁻¹ = x := by field_simp
    simpa only [same, AddMonoidHom.zero_apply] using vanishes (d / x)

end Algebraic.Aggregate.Geometry.Inversion
