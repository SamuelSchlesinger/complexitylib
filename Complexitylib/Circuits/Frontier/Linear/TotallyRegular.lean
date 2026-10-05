/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Field.ZMod

/-!
# Totally regular matrices

A matrix is *totally regular* when all of its square submatrices are nonsingular. For a linear
map `x ↦ M x` with a totally regular matrix, any `k` outputs determine any `k` inputs once the
other inputs are fixed: no small set of outputs is blind to a large set of inputs. This is the
property that makes the frontier of a circuit for `M` wide.

*Cauchy matrices* `M i j = 1 / (x i - y j)`, with distinct `x i`, distinct `y j`, and
`x i ≠ y j`, are totally regular: every square submatrix is again a Cauchy matrix, and square
Cauchy matrices are nonsingular. The explicit family `1 / (i - (N + j))` for `0 ≤ i, j < N` is
totally regular over every field of characteristic zero (`Frontier.totallyRegular_cauchyNat`)
and over `ZMod q` for every prime `q ≥ 2 N` (`Frontier.totallyRegular_cauchyZMod`).

## Main definitions

* `Frontier.TotallyRegular M`: every square submatrix of `M` is nonsingular.
* `Frontier.cauchy x y`: the Cauchy matrix with nodes `x` and `y`.

## Main results

* `Frontier.TotallyRegular.eq_zero`: if `v` is supported on a set of columns `C` and `M v`
  vanishes on a set of rows `R` with `|R| = |C|`, then `v = 0`.
* `Frontier.totallyRegular_cauchy`: Cauchy matrices are totally regular.
-/

@[expose] public section

namespace Complexity.Frontier

open Matrix

variable {F : Type*} [Field F] {m n : Type*}

/-- A matrix is *totally regular* when every square submatrix, on distinct rows and distinct
columns, is nonsingular. -/
def TotallyRegular (M : Matrix m n F) : Prop :=
  ∀ (k : ℕ) (r : Fin k → m) (c : Fin k → n), Function.Injective r → Function.Injective c →
    (M.submatrix r c).det ≠ 0

/-- **Square submatrices are injective.** If `M` is totally regular, `v` is supported on the
columns `C`, and `M v` vanishes on the rows `R`, where `|R| = |C|`, then `v = 0`. -/
theorem TotallyRegular.eq_zero [Fintype n] {M : Matrix m n F}
    (hM : TotallyRegular M) {R : Finset m} {C : Finset n} (hRC : R.card = C.card) {v : n → F}
    (hv : ∀ j ∉ C, v j = 0) (hMv : ∀ i ∈ R, (M *ᵥ v) i = 0) : v = 0 := by
  classical
  set k := C.card
  let r : Fin k → m := fun i => (R.equivFin.symm (Fin.cast hRC.symm i) : m)
  let c : Fin k → n := fun j => (C.equivFin.symm j : n)
  have hr : Function.Injective r := fun i i' h => by
    simpa [r, Fin.cast_inj] using R.equivFin.symm.injective (Subtype.ext h)
  have hc : Function.Injective c := fun j j' h =>
    C.equivFin.symm.injective (Subtype.ext h)
  -- The submatrix on `R` and `C` kills `v` restricted to `C`.
  have hsum : ∀ i : m, (M *ᵥ v) i = ∑ j : Fin k, M i (c j) * v (c j) := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ C) fun j _ hj => by simp [hv j hj]]
    rw [← Finset.sum_coe_sort C]
    exact (Equiv.sum_comp C.equivFin.symm fun j : C => M i j * v j).symm
  have hzero : (M.submatrix r c) *ᵥ (v ∘ c) = 0 := by
    funext i
    simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply, Pi.zero_apply]
    rw [← hsum]
    exact hMv _ (R.equivFin.symm _).2
  have hvc := Matrix.eq_zero_of_mulVec_eq_zero (hM k r c hr hc) hzero
  funext j
  by_cases hj : j ∈ C
  · have := congrFun hvc (C.equivFin ⟨j, hj⟩)
    simpa [c] using this
  · exact hv j hj

/-! ### Cauchy matrices -/

/-- The *Cauchy matrix* with nodes `x` and `y`: `M i j = 1 / (x i - y j)`. -/
def cauchy (x : m → F) (y : n → F) : Matrix m n F :=
  Matrix.of fun i j => (x i - y j)⁻¹

/-- **Square Cauchy matrices are nonsingular.** If `∑_j v_j / (x_i - y_j) = 0` for all `i`, the
polynomial interpolating the values `v_j / w_j` at the nodes `y_j`, where `w_j` are the nodal
weights, vanishes at the `k` nodes `x_i`; as its degree is less than `k`, it is zero, so `v = 0`. -/
theorem det_cauchy_ne_zero {k : ℕ} (x y : Fin k → F) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : (cauchy x y).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let w : Fin k → F := fun j => (Lagrange.nodalWeight Finset.univ y j)⁻¹ * v j
  have hweight : ∀ j, Lagrange.nodalWeight Finset.univ y j ≠ 0 := fun j =>
    Lagrange.nodalWeight_ne_zero hy.injOn (Finset.mem_univ j)
  have hP : Lagrange.interpolate Finset.univ y w = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn
      (Lagrange.degree_interpolate_lt w hy.injOn) fun i _ => ?_
    rw [Lagrange.eval_interpolate_not_at_node w fun j _ => hxy i j]
    have hsum : ∑ j ∈ Finset.univ, Lagrange.nodalWeight Finset.univ y j * (x i - y j)⁻¹ * w j =
        (cauchy x y *ᵥ v) i := by
      simp only [Matrix.mulVec, dotProduct, cauchy, Matrix.of_apply, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hweight j]
    rw [hsum, hv, Pi.zero_apply, mul_zero]
  apply hv0
  funext j
  have := Lagrange.eval_interpolate_at_node w hy.injOn (Finset.mem_univ j)
  rw [hP, Polynomial.eval_zero] at this
  have hwj : (Lagrange.nodalWeight Finset.univ y j)⁻¹ * v j = 0 := this.symm
  rcases mul_eq_zero.mp hwj with h | h
  · exact absurd (inv_eq_zero.mp h) (hweight j)
  · simpa using h

/-- **Cauchy matrices are totally regular**: every square submatrix is again a Cauchy
matrix. -/
theorem totallyRegular_cauchy (x : m → F) (y : n → F) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : TotallyRegular (cauchy x y) := by
  intro k r c hr hc
  have : (cauchy x y).submatrix r c = cauchy (x ∘ r) (y ∘ c) := by
    ext i j
    rfl
  rw [this]
  exact det_cauchy_ne_zero _ _ (hx.comp hr) (hy.comp hc) fun i j => hxy (r i) (c j)

/-- The explicit Cauchy matrix `M i j = 1 / (i - (N + j))` for `0 ≤ i, j < N`. -/
def cauchyNat (F : Type*) [Field F] (N : ℕ) : Matrix (Fin N) (Fin N) F :=
  cauchy (fun i : Fin N => ((i : ℕ) : F)) fun j : Fin N => ((N + j : ℕ) : F)

/-- **The explicit Cauchy matrices are totally regular** over fields of characteristic zero. -/
theorem totallyRegular_cauchyNat [CharZero F] (N : ℕ) : TotallyRegular (cauchyNat F N) :=
  totallyRegular_cauchy _ _ (fun i i' h => Fin.ext (by exact_mod_cast h))
    (fun j j' h => Fin.ext (by
      have : N + (j : ℕ) = N + j' := by exact_mod_cast h
      omega))
    fun i j h => by have : (i : ℕ) = N + j := by exact_mod_cast h
                    omega

/-- **The explicit Cauchy matrices are totally regular** over `ZMod q` for a prime `q ≥ 2 N`. -/
theorem totallyRegular_cauchyZMod (q N : ℕ) [Fact q.Prime] (hq : 2 * N ≤ q) :
    TotallyRegular (cauchyNat (ZMod q) N) := by
  have hcast : ∀ a b : ℕ, a < q → b < q → ((a : ZMod q) = b ↔ a = b) := fun a b ha hb => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  refine totallyRegular_cauchy _ _ (fun i i' h => Fin.ext ?_) (fun j j' h => Fin.ext ?_)
    fun i j h => ?_
  · exact (hcast _ _ (by omega) (by omega)).mp h
  · have := (hcast _ _ (by omega) (by omega)).mp h; omega
  · have := (hcast _ _ (by omega) (by omega)).mp h; omega

end Complexity.Frontier
