/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Affine restrictions of the Gold map in characteristic two

In characteristic two, `(a + b + c)³` differs from `a³ + b³ + c³` by the product of
the three pairwise sums. Hence cubing preserves ternary addition only on sets of at
most two points (it is almost perfect nonlinear), and a linear component `ℓ(x³)` is
affine on a coset of `U` exactly when `U` is totally isotropic for the alternating
form `B(u, w) = ℓ(u²w + uw²)`. When cubing is injective, this form has at most one
nonzero radical vector, so its totally isotropic subspaces have dimension at most
`(dim K + 1) / 2`.

The Gold map `x ↦ x^(2^k+1)` and its almost perfect nonlinearity are classical; see
Robert Gold, "Maximal recursive sequences with 3-valued recursive cross-correlation
functions", IEEE Transactions on Information Theory 14 (1968), 154–156, and
Claude Carlet, "Vectorial Boolean Functions for Cryptography", Section 3.1.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Gold

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

/-- The cube of a ternary sum differs from the sum of cubes by the product of the three
pairwise sums. -/
theorem cube_add_add (a b c : K) :
    (a + b + c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + (a + b) * (b + c) * (c + a) := by
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (a + b) * (b + c) * (c + a) * two

/-- Cubing preserves ternary addition on at most two points of a binary field. -/
theorem card_le_two_of_cube_affine (S : Finset K)
    (affine : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, (a + b + c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3) :
    S.card ≤ 2 := by
  by_contra large
  push Not at large
  obtain ⟨a, ha, b, hb, c, hc, ab, ac, bc⟩ := Finset.two_lt_card.mp large
  have product : (a + b) * (b + c) * (c + a) = 0 := by
    have same := affine a ha b hb c hc
    rw [cube_add_add] at same
    exact add_eq_left.mp same
  rcases mul_eq_zero.mp product with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ab (CharTwo.add_eq_zero.mp h)
    · exact bc (CharTwo.add_eq_zero.mp h)
  · exact ac (CharTwo.add_eq_zero.mp h).symm

/-- A linear component of cubing is affine on three points exactly when it vanishes on
the product of their pairwise sums. -/
theorem map_product_eq_zero_of_cube_affine (ℓ : K →+ ZMod 2) {a b c : K}
    (affine : ℓ ((a + b + c) ^ 3) = ℓ (a ^ 3) + ℓ (b ^ 3) + ℓ (c ^ 3)) :
    ℓ ((a + b) * (b + c) * (c + a)) = 0 := by
  rw [cube_add_add, map_add, map_add, map_add] at affine
  exact add_eq_left.mp affine

omit [CharP K 2] in
/-- Cubing is injective when three is coprime to the multiplicative group order. -/
theorem cube_injective [Fintype K] (coprime : Nat.Coprime 3 (Fintype.card K - 1)) :
    Function.Injective fun x : K => x ^ 3 := by
  intro x y same
  simp only at same
  by_cases hy : y = 0
  · subst hy
    simpa using same
  · have ratio : (x / y) ^ 3 = 1 := by
      rw [div_pow, same, div_self (pow_ne_zero 3 hy)]
    have nonzero : x / y ≠ 0 := by
      intro zero
      rw [zero] at ratio
      simp at ratio
    have order := FiniteField.pow_card_sub_one_eq_one (x / y) nonzero
    have one : (x / y) ^ Nat.gcd 3 (Fintype.card K - 1) = 1 :=
      pow_gcd_eq_one.mpr ⟨ratio, order⟩
    rw [coprime, pow_one] at one
    exact (div_eq_one_iff_eq hy).mp one

omit [CharP K 2] in
/-- A nonzero radical vector `u` of the polar form identifies `ℓ r` with `ℓ (r² / u³)`. -/
theorem map_eq_map_sq_div_of_radical (ℓ : K →+ ZMod 2) {u : K} (hu : u ≠ 0)
    (radical : ∀ w, ℓ (u ^ 2 * w + u * w ^ 2) = 0) (r : K) :
    ℓ r = ℓ (r ^ 2 / u ^ 3) := by
  have h := radical (r / u ^ 2)
  have first : u ^ 2 * (r / u ^ 2) = r := by field_simp
  have second : u * (r / u ^ 2) ^ 2 = r ^ 2 / u ^ 3 := by field_simp
  rw [first, second, map_add] at h
  exact CharTwo.add_eq_zero.mp h

/-- When cubing is injective, the polar form of a nonzero component has at most one
nonzero radical vector. -/
theorem eq_of_radical [Finite K] (ℓ : K →+ ZMod 2) (nonzero : ℓ ≠ 0)
    (cube : Function.Injective fun x : K => x ^ 3) {u v : K} (hu : u ≠ 0) (hv : v ≠ 0)
    (ru : ∀ w, ℓ (u ^ 2 * w + u * w ^ 2) = 0) (rv : ∀ w, ℓ (v ^ 2 * w + v * w ^ 2) = 0) :
    u = v := by
  apply cube
  simp only
  by_contra different
  apply nonzero
  have hd : (u ^ 3)⁻¹ + (v ^ 3)⁻¹ ≠ 0 := by
    intro h
    exact different (inv_injective (CharTwo.add_eq_zero.mp h))
  ext y
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (y / ((u ^ 3)⁻¹ + (v ^ 3)⁻¹))
  have hy : y = r ^ 2 / u ^ 3 + r ^ 2 / v ^ 3 := by
    rw [← div_mul_cancel₀ y hd, hr]
    ring
  rw [hy, map_add, ← map_eq_map_sq_div_of_radical ℓ hu ru r,
    ← map_eq_map_sq_div_of_radical ℓ hv rv r, CharTwo.add_self_eq_zero]
  rfl

end CharTwo

/-- In odd dimension, three is coprime to the order `2^n - 1` of the multiplicative group. -/
theorem coprime_three_two_pow_sub_one {n : ℕ} (odd : Odd n) : Nat.Coprime 3 (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := odd
  have residue : ∀ k : ℕ, 2 ^ (2 * k + 1) % 3 = 2 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add]
      omega
  have positive : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
  have one : (2 ^ (2 * k + 1) - 1) % 3 = 1 := by
    have := residue k
    omega
  rw [Nat.Coprime, Nat.gcd_rec, one]
  rfl

section Form

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]

/-- The alternating polar form `B(u, w) = ℓ(u²w + uw²)` of the Gold component `ℓ(x³)`. -/
noncomputable def polarForm (ℓ : K →ₗ[ZMod 2] ZMod 2) : LinearMap.BilinForm (ZMod 2) K :=
  LinearMap.mk₂ (ZMod 2) (fun u w => ℓ (u ^ 2 * w + u * w ^ 2))
    (by
      intro u u' w
      have two : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [← map_add]
      congr 1
      linear_combination u * u' * w * two)
    (by
      intro c u w
      have same : (c • u) ^ 2 * w + c • u * w ^ 2 = c • (u ^ 2 * w + u * w ^ 2) := by
        simp only [Algebra.smul_def, mul_pow, ← map_pow, ZMod.pow_card c]
        ring
      rw [same, map_smul])
    (by
      intro u w w'
      have two : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [← map_add]
      congr 1
      linear_combination u * w * w' * two)
    (by
      intro c u w
      have same : u ^ 2 * c • w + u * (c • w) ^ 2 = c • (u ^ 2 * w + u * w ^ 2) := by
        simp only [Algebra.smul_def, mul_pow, ← map_pow, ZMod.pow_card c]
        ring
      rw [same, map_smul])

@[simp] theorem polarForm_apply (ℓ : K →ₗ[ZMod 2] ZMod 2) (u w : K) :
    polarForm ℓ u w = ℓ (u ^ 2 * w + u * w ^ 2) := rfl

/-- If cubing is injective, every subspace on which the polar form of a nonzero
component vanishes has at most half of one more than the field dimension. -/
theorem two_mul_finrank_le_of_isotropic [Finite K] (ℓ : K →ₗ[ZMod 2] ZMod 2) (nonzero : ℓ ≠ 0)
    (cube : Function.Injective fun x : K => x ^ 3) (U : Submodule (ZMod 2) K)
    (isotropic : ∀ u ∈ U, ∀ w ∈ U, ℓ (u ^ 2 * w + u * w ^ 2) = 0) :
    2 * Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) K + 1 := by
  let B := polarForm ℓ
  have total := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) U
  have sub : U ≤ B.orthogonal U := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    exact isotropic u hu v hv
  have additive : ℓ.toAddMonoidHom ≠ 0 := by
    intro zero
    apply nonzero
    ext x
    exact DFunLike.congr_fun zero x
  have radical (u : K) (hu : u ∈ LinearMap.ker B) (w : K) : ℓ (u ^ 2 * w + u * w ^ 2) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hu) w
  have small : Module.finrank (ZMod 2) (LinearMap.ker B) ≤ 1 := by
    by_cases exists_nonzero : ∃ u ∈ LinearMap.ker B, u ≠ 0
    · obtain ⟨u, hu, ne⟩ := exists_nonzero
      apply finrank_le_one ⟨u, hu⟩
      rintro ⟨v, hv⟩
      by_cases zero : v = 0
      · exact ⟨0, by ext; simp [zero]⟩
      · refine ⟨1, ?_⟩
        ext
        simpa using eq_of_radical ℓ.toAddMonoidHom additive cube ne zero
          (radical u hu) (radical v hv)
    · push Not at exists_nonzero
      apply finrank_le_one 0
      rintro ⟨v, hv⟩
      exact ⟨0, by ext; simp [exists_nonzero v hv]⟩
  have mono := Submodule.finrank_mono sub
  have inter := Submodule.finrank_mono (inf_le_right : U ⊓ LinearMap.ker B ≤ LinearMap.ker B)
  change Module.finrank (ZMod 2) U + Module.finrank (ZMod 2) (B.orthogonal U) =
    Module.finrank (ZMod 2) K + Module.finrank (ZMod 2) ↥(U ⊓ LinearMap.ker B) at total
  omega

end Form

end Algebraic.Aggregate.Geometry.Gold
