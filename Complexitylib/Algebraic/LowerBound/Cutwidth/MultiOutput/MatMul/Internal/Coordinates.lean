/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Defs

/-!
# Coordinates of matrix multiplication

* The coordinates `matMulLeft n i j` and `matMulRight n j k` are distinct and cover all inputs
  (`sum_input`); the outputs `matMulOutput n i k` cover all outputs (`sum_output`).
* `matMul_output` and `matMul_matMulInput`: the map multiplies matrices.
* **Fixing a factor.** With the second factor fixed to `B₀`, the product changes by
  `shiftLeft B₀ d`, whose output `C i k` is `∑ j, d (A i j) B₀ j k` (`matMul_sub_left`);
  symmetrically with the first factor fixed (`matMul_sub_right`). The free coordinates are
  `leftCoords n` and `rightCoords n`.
* **The quadratic form.** For a matrix `Λ`, `bilinForm Λ` is the matrix of the quadratic form
  `z ↦ ∑ i k, Λ i k C i k` (`quadForm_bilinForm`). Its symmetrization `H = M + Mᵀ` pairs `A i j`
  with `B j k` through `Λ i k` (`mulVec_add_transpose_left`, `mulVec_add_transpose_right`).
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput.MatMul.Internal

open Matrix

variable {n : Nat}

/-! ## Distinct coordinates -/

section Index

theorem matMulLeft_inj {i j i' j' : Fin n} :
    matMulLeft n i j = matMulLeft n i' j' ↔ i = i' ∧ j = j' := by
  simp [matMulLeft, Fin.castAdd_inj, Prod.ext_iff]

theorem matMulRight_inj {j k j' k' : Fin n} :
    matMulRight n j k = matMulRight n j' k' ↔ j = j' ∧ k = k' := by
  simp [matMulRight, Prod.ext_iff]

theorem matMulLeft_ne_matMulRight (i j j' k : Fin n) : matMulLeft n i j ≠ matMulRight n j' k := by
  intro h
  have := congrArg Fin.val h
  simp only [matMulLeft, matMulRight, Fin.val_castAdd, Fin.val_natAdd] at this
  have := (finProdFinEquiv (i, j)).isLt
  omega

theorem matMulOutput_inj {i k i' k' : Fin n} :
    matMulOutput n i k = matMulOutput n i' k' ↔ i = i' ∧ k = k' := by
  simp [matMulOutput, Prod.ext_iff]

/-- Every input coordinate holds an entry of one of the factors. -/
theorem input_cases (x : Fin (n * n + n * n)) :
    (∃ i j, x = matMulLeft n i j) ∨ ∃ j k, x = matMulRight n j k := by
  induction x using Fin.addCases with
  | left p =>
    left
    exact ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, by
      simp only [matMulLeft, Prod.mk.eta, Equiv.apply_symm_apply]⟩
  | right p =>
    right
    exact ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2, by
      simp only [matMulRight, Prod.mk.eta, Equiv.apply_symm_apply]⟩

/-- Every output coordinate holds an entry of the product. -/
theorem output_eq (o : Fin (n * n)) :
    o = matMulOutput n (finProdFinEquiv.symm o).1 (finProdFinEquiv.symm o).2 := by
  simp only [matMulOutput, Prod.mk.eta, Equiv.apply_symm_apply]

/-- A sum over the input coordinates is a sum over the entries of the two factors. -/
theorem sum_input {M : Type*} [AddCommMonoid M] (φ : Fin (n * n + n * n) → M) :
    ∑ x, φ x = ∑ i, ∑ j, φ (matMulLeft n i j) + ∑ j, ∑ k, φ (matMulRight n j k) := by
  rw [Fin.sum_univ_add, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  congr 1
  · exact (finProdFinEquiv.sum_comp (fun p => φ (Fin.castAdd (n * n) p))).symm
  · exact (finProdFinEquiv.sum_comp (fun p => φ (Fin.natAdd (n * n) p))).symm

/-- A sum over the output coordinates is a sum over the entries of the product. -/
theorem sum_output {M : Type*} [AddCommMonoid M] (φ : Fin (n * n) → M) :
    ∑ o, φ o = ∑ i, ∑ k, φ (matMulOutput n i k) := by
  rw [← Fintype.sum_prod_type']
  exact (finProdFinEquiv.sum_comp φ).symm

end Index

/-! ## The product -/

section Product

variable {R : Type*} [Semiring R]

theorem matMul_output (z : Fin (n * n + n * n) → R) (i k : Fin n) :
    matMul n z (matMulOutput n i k) = ∑ j, z (matMulLeft n i j) * z (matMulRight n j k) := by
  simp only [matMul, matMulOutput, Equiv.symm_apply_apply]

omit [Semiring R] in
@[simp] theorem matMulInput_left (A B : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    matMulInput A B (matMulLeft n i j) = A i j := by
  simp only [matMulInput, matMulLeft, Fin.append_left, Equiv.symm_apply_apply]

omit [Semiring R] in
@[simp] theorem matMulInput_right (A B : Matrix (Fin n) (Fin n) R) (j k : Fin n) :
    matMulInput A B (matMulRight n j k) = B j k := by
  simp only [matMulInput, matMulRight, Fin.append_right, Equiv.symm_apply_apply]

/-- **`matMul` multiplies.** -/
theorem matMul_matMulInput (A B : Matrix (Fin n) (Fin n) R) (i k : Fin n) :
    matMul n (matMulInput A B) (matMulOutput n i k) = (A * B) i k := by
  simp [matMul_output, Matrix.mul_apply]

end Product

/-! ## Fixing one factor -/

section Shift

variable {R : Type*} [CommRing R]

/-- The coordinates of the first factor. -/
def leftCoords (n : Nat) : Finset (Fin (n * n + n * n)) :=
  Finset.univ.image fun p : Fin n × Fin n => matMulLeft n p.1 p.2

/-- The coordinates of the second factor. -/
def rightCoords (n : Nat) : Finset (Fin (n * n + n * n)) :=
  Finset.univ.image fun p : Fin n × Fin n => matMulRight n p.1 p.2

theorem matMulLeft_mem_leftCoords (i j : Fin n) : matMulLeft n i j ∈ leftCoords n :=
  Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

theorem matMulRight_mem_rightCoords (j k : Fin n) : matMulRight n j k ∈ rightCoords n :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem matMulRight_notMem_leftCoords (j k : Fin n) : matMulRight n j k ∉ leftCoords n := by
  simp only [leftCoords, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact fun p h => matMulLeft_ne_matMulRight p.1 p.2 j k h

theorem matMulLeft_notMem_rightCoords (i j : Fin n) : matMulLeft n i j ∉ rightCoords n := by
  simp only [rightCoords, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact fun p h => matMulLeft_ne_matMulRight i j p.1 p.2 h.symm

theorem card_leftCoords : (leftCoords n).card = n * n := by
  rw [leftCoords, Finset.card_image_of_injective _ fun p q h => Prod.ext_iff.mpr
    (matMulLeft_inj.mp h)]
  simp

theorem card_rightCoords : (rightCoords n).card = n * n := by
  rw [rightCoords, Finset.card_image_of_injective _ fun p q h => Prod.ext_iff.mpr
    (matMulRight_inj.mp h)]
  simp

/-- The change of the product when the input changes by `d` and the second factor is `B₀`. -/
def shiftLeft (B₀ : Matrix (Fin n) (Fin n) R) (d : Fin (n * n + n * n) → R) : Fin (n * n) → R :=
  fun o => ∑ j, d (matMulLeft n (finProdFinEquiv.symm o).1 j) * B₀ j (finProdFinEquiv.symm o).2

/-- The change of the product when the input changes by `d` and the first factor is `A₀`. -/
def shiftRight (A₀ : Matrix (Fin n) (Fin n) R) (d : Fin (n * n + n * n) → R) :
    Fin (n * n) → R :=
  fun o => ∑ j, A₀ (finProdFinEquiv.symm o).1 j * d (matMulRight n j (finProdFinEquiv.symm o).2)

theorem shiftLeft_output (B₀ : Matrix (Fin n) (Fin n) R) (d : Fin (n * n + n * n) → R)
    (i k : Fin n) : shiftLeft B₀ d (matMulOutput n i k) = ∑ j, d (matMulLeft n i j) * B₀ j k := by
  simp only [shiftLeft, matMulOutput, Equiv.symm_apply_apply]

theorem shiftRight_output (A₀ : Matrix (Fin n) (Fin n) R) (d : Fin (n * n + n * n) → R)
    (i k : Fin n) :
    shiftRight A₀ d (matMulOutput n i k) = ∑ j, A₀ i j * d (matMulRight n j k) := by
  simp only [shiftRight, matMulOutput, Equiv.symm_apply_apply]

/-- With the second factor fixed to `B₀`, the product changes by `shiftLeft B₀`. -/
theorem matMul_sub_left (B₀ : Matrix (Fin n) (Fin n) R) (z z' : Fin (n * n + n * n) → R)
    (hz : ∀ x, x ∉ leftCoords n → z x = matMulInput 0 B₀ x)
    (hz' : ∀ x, x ∉ leftCoords n → z' x = matMulInput 0 B₀ x) :
    matMul n z' - matMul n z = shiftLeft B₀ (z' - z) := by
  funext o
  rw [output_eq o]
  simp only [Pi.sub_apply, matMul_output, shiftLeft_output]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hz _ (matMulRight_notMem_leftCoords _ _), hz' _ (matMulRight_notMem_leftCoords _ _),
    matMulInput_right]
  ring

/-- With the first factor fixed to `A₀`, the product changes by `shiftRight A₀`. -/
theorem matMul_sub_right (A₀ : Matrix (Fin n) (Fin n) R) (z z' : Fin (n * n + n * n) → R)
    (hz : ∀ x, x ∉ rightCoords n → z x = matMulInput A₀ 0 x)
    (hz' : ∀ x, x ∉ rightCoords n → z' x = matMulInput A₀ 0 x) :
    matMul n z' - matMul n z = shiftRight A₀ (z' - z) := by
  funext o
  rw [output_eq o]
  simp only [Pi.sub_apply, matMul_output, shiftRight_output]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hz _ (matMulLeft_notMem_rightCoords _ _), hz' _ (matMulLeft_notMem_rightCoords _ _),
    matMulInput_left]
  ring

end Shift

/-! ## The quadratic form -/

section Quadratic

variable {R : Type*} [CommRing R]

/-- The matrix of the quadratic form `z ↦ ∑ i k, Λ i k C i k`: it pairs the entry `A i j` with
the entry `B j k` through `Λ i k`, and has no other nonzero entries. -/
def bilinForm (Λ : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) R :=
  Matrix.of fun x y => Fin.addCases (fun p => Fin.addCases (fun _ => 0) (fun q =>
    if (finProdFinEquiv.symm p).2 = (finProdFinEquiv.symm q).1 then
      Λ (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm q).2 else 0) y) (fun _ => 0) x

theorem bilinForm_left_right (Λ : Matrix (Fin n) (Fin n) R) (i j j' k : Fin n) :
    bilinForm Λ (matMulLeft n i j) (matMulRight n j' k) = if j = j' then Λ i k else 0 := by
  simp only [bilinForm, Matrix.of_apply, matMulLeft, matMulRight, Fin.addCases_left,
    Fin.addCases_right, Equiv.symm_apply_apply]

theorem bilinForm_left_left (Λ : Matrix (Fin n) (Fin n) R) (i j i' j' : Fin n) :
    bilinForm Λ (matMulLeft n i j) (matMulLeft n i' j') = 0 := by
  simp only [bilinForm, Matrix.of_apply, matMulLeft, Fin.addCases_left]

theorem bilinForm_right (Λ : Matrix (Fin n) (Fin n) R) (j k : Fin n)
    (y : Fin (n * n + n * n)) : bilinForm Λ (matMulRight n j k) y = 0 := by
  simp only [bilinForm, Matrix.of_apply, matMulRight, Fin.addCases_right]

theorem mulVec_bilinForm_left (Λ : Matrix (Fin n) (Fin n) R) (z : Fin (n * n + n * n) → R)
    (i j : Fin n) :
    (bilinForm Λ *ᵥ z) (matMulLeft n i j) = ∑ k, Λ i k * z (matMulRight n j k) := by
  rw [Matrix.mulVec, dotProduct, sum_input]
  simp only [bilinForm_left_left, zero_mul, Finset.sum_const_zero, zero_add,
    bilinForm_left_right, ite_mul]
  rw [Finset.sum_eq_single j (fun j' _ hj' => Finset.sum_eq_zero fun k _ =>
    ite_eq_right (Ne.symm hj')) (fun h => absurd (Finset.mem_univ j) h)]
  simp

theorem mulVec_bilinForm_right (Λ : Matrix (Fin n) (Fin n) R) (z : Fin (n * n + n * n) → R)
    (j k : Fin n) : (bilinForm Λ *ᵥ z) (matMulRight n j k) = 0 := by
  simp [Matrix.mulVec, dotProduct, bilinForm_right]

theorem mulVec_transpose_bilinForm_left (Λ : Matrix (Fin n) (Fin n) R)
    (z : Fin (n * n + n * n) → R) (i j : Fin n) :
    ((bilinForm Λ)ᵀ *ᵥ z) (matMulLeft n i j) = 0 := by
  rw [Matrix.mulVec, dotProduct, sum_input]
  simp [bilinForm_left_left, bilinForm_right]

theorem mulVec_transpose_bilinForm_right (Λ : Matrix (Fin n) (Fin n) R)
    (z : Fin (n * n + n * n) → R) (j k : Fin n) :
    ((bilinForm Λ)ᵀ *ᵥ z) (matMulRight n j k) = ∑ i, Λ i k * z (matMulLeft n i j) := by
  rw [Matrix.mulVec, dotProduct, sum_input]
  simp only [Matrix.transpose_apply, bilinForm_left_right, bilinForm_right, zero_mul,
    Finset.sum_const_zero, add_zero, ite_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j (fun j' _ hj' => ite_eq_right hj')
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- **The symmetrized form at `A i j`.** -/
theorem mulVec_add_transpose_left (Λ : Matrix (Fin n) (Fin n) R) (z : Fin (n * n + n * n) → R)
    (i j : Fin n) :
    ((bilinForm Λ + (bilinForm Λ)ᵀ) *ᵥ z) (matMulLeft n i j) =
      ∑ k, Λ i k * z (matMulRight n j k) := by
  rw [Matrix.add_mulVec, Pi.add_apply, mulVec_bilinForm_left, mulVec_transpose_bilinForm_left,
    add_zero]

/-- **The symmetrized form at `B j k`.** -/
theorem mulVec_add_transpose_right (Λ : Matrix (Fin n) (Fin n) R) (z : Fin (n * n + n * n) → R)
    (j k : Fin n) :
    ((bilinForm Λ + (bilinForm Λ)ᵀ) *ᵥ z) (matMulRight n j k) =
      ∑ i, Λ i k * z (matMulLeft n i j) := by
  rw [Matrix.add_mulVec, Pi.add_apply, mulVec_bilinForm_right, mulVec_transpose_bilinForm_right,
    zero_add]

/-- **The quadratic form of `bilinForm Λ`** is the combination `∑ i k, Λ i k C i k` of the
outputs. -/
theorem quadForm_bilinForm (Λ : Matrix (Fin n) (Fin n) R) (z : Fin (n * n + n * n) → R) :
    quadForm (bilinForm Λ) z = ∑ i, ∑ k, Λ i k * matMul n z (matMulOutput n i k) := by
  rw [quadForm, dotProduct, sum_input]
  simp only [mulVec_bilinForm_left, mulVec_bilinForm_right, mul_zero, Finset.sum_const_zero,
    add_zero, matMul_output, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Quadratic

end Algebraic.Cutwidth.MultiOutput.MatMul.Internal
