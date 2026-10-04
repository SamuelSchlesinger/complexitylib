/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.Colex
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Complexitylib.Algebraic.LinearAlgebra.MatrixRank

/-!
# Nonsingular minors: proof internals

Proofs behind `Complexitylib.Algebraic.LinearAlgebra.NonsingularMinor`.

* **Dominance.** In `∑ ±2^{E x}` with pairwise distinct exponents, every term other than the one
  with the least exponent `E₀` is divisible by `2^{E₀ + 1}`, while that term is not, so the sum
  is nonzero.
* **Leibniz expansion.** If every nonzero entry of an integer matrix is `±2^{2^{L i j}}`, then a
  permutation whose diagonal avoids the zero entries contributes `±2^{E σ}` to the determinant,
  where `E σ = ∑_j 2^{L (σ j) j}`. If `L` is injective on the nonzero entries, `E σ` is the
  binary number whose set bits are the labels used by `σ`; these labels determine the pairs
  `(σ j, j)`, hence `σ`, so the exponents are pairwise distinct and dominance applies. Over a
  ring of characteristic zero the matrix is the image of such an integer matrix.
* **Block-diagonal minors.** A minor that is block diagonal with nonsingular blocks is the
  `Matrix.blockDiagonal` of its blocks, so its determinant is their product.
-/

@[expose] public section

namespace Algebraic.NonsingularMinor.Internal

open Finset Matrix

/-- **Dominance.** A nonempty sum `∑ ε x * 2 ^ E x` with unit coefficients `ε x = ±1` and
pairwise distinct exponents `E x` is nonzero. -/
theorem sum_mul_two_pow_ne_zero {κ : Type*} {s : Finset κ} (hs : s.Nonempty) {ε : κ → ℤ}
    (hε : ∀ x ∈ s, IsUnit (ε x)) {E : κ → ℕ} (hE : Set.InjOn E s) :
    ∑ x ∈ s, ε x * 2 ^ E x ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀, hmin⟩ := s.exists_min_image E hs
  rw [← Finset.add_sum_erase s _ hx₀]
  intro h
  have hdvd : (2 : ℤ) ^ (E x₀ + 1) ∣ ∑ x ∈ s.erase x₀, ε x * 2 ^ E x := by
    refine Finset.dvd_sum fun x hx => ?_
    obtain ⟨hne, hxs⟩ := Finset.mem_erase.mp hx
    have hlt : E x₀ < E x :=
      lt_of_le_of_ne (hmin x hxs) fun h => hne (hE hxs hx₀ h.symm)
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hlt) _
  have h₀ : (2 : ℤ) ^ (E x₀ + 1) ∣ ε x₀ * 2 ^ E x₀ := by
    rw [eq_neg_of_add_eq_zero_left h]
    exact (dvd_neg).mpr hdvd
  rw [(hε x₀ hx₀).dvd_mul_left] at h₀
  have hle := Int.le_of_dvd (by positivity) h₀
  rw [pow_succ] at hle
  have : (0 : ℤ) < 2 ^ E x₀ := by positivity
  linarith

/-- The Leibniz-expansion argument over `ℤ`. -/
theorem det_ne_zero_of_two_pow_two_pow_int {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (L : ι → ι → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → M i j = 2 ^ 2 ^ L i j ∨ M i j = -2 ^ 2 ^ L i j)
    (hL : ∀ i j i' j', M i j ≠ 0 → M i' j' ≠ 0 → L i j = L i' j' → i = i' ∧ j = j')
    (σ₀ : Equiv.Perm ι) (hσ₀ : ∀ j, M (σ₀ j) j ≠ 0) : M.det ≠ 0 := by
  classical
  set s := univ.filter fun σ : Equiv.Perm ι => ∀ j, M (σ j) j ≠ 0 with hs_def
  let u : ι → ι → ℤˣ := fun i j => if M i j = 2 ^ 2 ^ L i j then 1 else -1
  have hu : ∀ i j, M i j ≠ 0 → M i j = (u i j : ℤ) * 2 ^ 2 ^ L i j := by
    intro i j h
    simp only [u]
    split_ifs with h'
    · simp [h']
    · rcases hM i j h with h1 | h1
      · exact absurd h1 h'
      · simp [h1]
  let E : Equiv.Perm ι → ℕ := fun σ => ∑ j, 2 ^ L (σ j) j
  let ε : Equiv.Perm ι → ℤ := fun σ => ((Equiv.Perm.sign σ * ∏ j, u (σ j) j : ℤˣ) : ℤ)
  have hterm : ∀ σ ∈ s, Equiv.Perm.sign σ • ∏ j, M (σ j) j = ε σ * 2 ^ E σ := by
    intro σ hσ
    have hσ' := (Finset.mem_filter.mp hσ).2
    rw [Finset.prod_congr rfl fun j _ => hu _ _ (hσ' j), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Units.smul_def]
    simp only [ε, E, Units.val_mul, Units.coe_prod, smul_eq_mul]
    ring
  have hdet : M.det = ∑ σ ∈ s, ε σ * 2 ^ E σ := by
    rw [Matrix.det_apply,
      ← Finset.sum_filter_of_ne (p := fun σ : Equiv.Perm ι => ∀ j, M (σ j) j ≠ 0)]
    · exact Finset.sum_congr rfl hterm
    · intro σ _ hne j hj
      exact hne (by rw [Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hj,
        smul_zero])
  rw [hdet]
  refine sum_mul_two_pow_ne_zero ⟨σ₀, by simp [s, hσ₀]⟩ (fun σ _ => Units.isUnit _) ?_
  intro σ hσ τ hτ hEq
  have hσ' := (Finset.mem_filter.mp hσ).2
  have hτ' := (Finset.mem_filter.mp hτ).2
  have himg : ∀ π : Equiv.Perm ι, (∀ j, M (π j) j ≠ 0) →
      E π = ∑ x ∈ univ.image (fun j => L (π j) j), 2 ^ x := by
    intro π hπ
    rw [Finset.sum_image]
    intro j _ j' _ h
    exact (hL _ _ _ _ (hπ j) (hπ j') h).2
  have hS : univ.image (fun j => L (σ j) j) = univ.image (fun j => L (τ j) j) :=
    Finset.geomSum_injective le_rfl (by simp only; rw [← himg σ hσ', ← himg τ hτ']; exact hEq)
  ext j
  have hmem : L (σ j) j ∈ univ.image (fun j => L (τ j) j) :=
    hS ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)
  obtain ⟨j', -, hj'⟩ := Finset.mem_image.mp hmem
  obtain ⟨h1, h2⟩ := hL _ _ _ _ (hτ' j') (hσ' j) hj'
  subst h2
  rw [h1]

/-- The Leibniz-expansion argument over a commutative ring of characteristic zero: the matrix is
the image of an integer matrix with the same zero pattern. -/
theorem det_ne_zero_of_two_pow_two_pow {R : Type*} [CommRing R] [CharZero R] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (L : ι → ι → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → M i j = 2 ^ 2 ^ L i j ∨ M i j = -2 ^ 2 ^ L i j)
    (hL : ∀ i j i' j', M i j ≠ 0 → M i' j' ≠ 0 → L i j = L i' j' → i = i' ∧ j = j')
    (σ₀ : Equiv.Perm ι) (hσ₀ : ∀ j, M (σ₀ j) j ≠ 0) : M.det ≠ 0 := by
  classical
  let N : Matrix ι ι ℤ := Matrix.of fun i j =>
    if M i j = 0 then 0 else if M i j = 2 ^ 2 ^ L i j then 2 ^ 2 ^ L i j else -2 ^ 2 ^ L i j
  have hpow : ∀ n : ℕ, (2 : R) ^ n ≠ 0 := fun n => by
    exact_mod_cast (show (2 : ℕ) ^ n ≠ 0 by positivity)
  have hNM : ∀ i j, ((N i j : ℤ) : R) = M i j := by
    intro i j
    simp only [N, Matrix.of_apply]
    split_ifs with h0 h1
    · simp [h0]
    · simp [h1]
    · rcases hM i j h0 with h | h
      · exact absurd h h1
      · simp [h]
  have hN0 : ∀ i j, N i j ≠ 0 ↔ M i j ≠ 0 := by
    intro i j
    simp only [N, Matrix.of_apply]
    split_ifs with h0 h1 <;> simp [h0]
  have hmap : (Int.castRingHom R).mapMatrix N = M := by
    ext i j
    exact hNM i j
  have hdet := det_ne_zero_of_two_pow_two_pow_int N L
    (fun i j h => by
      simp only [N, Matrix.of_apply]
      have h0 : M i j ≠ 0 := (hN0 i j).mp h
      simp only [h0, ite_false]
      split_ifs <;> simp)
    (fun i j i' j' h h' => hL i j i' j' ((hN0 i j).mp h) ((hN0 i' j').mp h'))
    σ₀ (fun j => (hN0 _ _).mpr (hσ₀ j))
  rw [← hmap, ← RingHom.map_det, Int.coe_castRingHom]
  exact Int.cast_ne_zero.mpr hdet

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

/-- A minor that is block diagonal with nonsingular square blocks has nonzero determinant, so
its size is at most the rank. -/
theorem card_mul_card_le_rank_of_det_blocks_ne_zero {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β] (A : Matrix m n K) (f : ι → β → m) (g : ι → β → n)
    (hoff : ∀ i i' b b', b ≠ b' → A (f i b) (g i' b') = 0)
    (hdet : ∀ b, (A.submatrix (f · b) (g · b)).det ≠ 0) :
    Fintype.card ι * Fintype.card β ≤ A.rank := by
  have hblk : A.submatrix (fun x : ι × β => f x.1 x.2) (fun x => g x.1 x.2) =
      Matrix.blockDiagonal fun b => A.submatrix (f · b) (g · b) := by
    ext ⟨i, b⟩ ⟨i', b'⟩
    simp only [submatrix_apply, blockDiagonal_apply]
    split_ifs with h
    · subst h
      rfl
    · exact hoff i i' b b' h
  have h := card_le_rank_of_det_submatrix_ne_zero A (fun x : ι × β => f x.1 x.2)
    (fun x => g x.1 x.2) (by
      rw [hblk, det_blockDiagonal]
      exact Finset.prod_ne_zero_iff.mpr fun b _ => hdet b)
  simpa [Fintype.card_prod] using h

end Algebraic.NonsingularMinor.Internal
