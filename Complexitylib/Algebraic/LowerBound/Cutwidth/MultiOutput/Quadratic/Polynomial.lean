/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Quadratic.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Taylor.Internal

/-!
# Quadratic forms over every field

The counting proof of `MultiOutput.Quadratic` needs a finite field. For circuits with
polynomial gates the Taylor cut lemma gives the same rank-cut bound over every field: the
Hessian of the quadratic form `∑ᵢ ∑ⱼ M i j Xᵢ Xⱼ` is `M + Mᵀ` at every point
(`hessian_quadFormPolynomial`), so by the Hessian consequence (`Taylor.blockRank_hessian_le`)
every split `S` of a circuit formally computing the form is crossed by at least
`rank (M + Mᵀ)[X_S, X_T]` signals (`blockRank_add_transpose_le_of_formallyComputes`). The
graph-ordering argument of `MultiOutput.Quadratic` then applies unchanged.

**The bound** (`eventually_lt_size_of_formal_quadForm`). For every `ε > 0` and all large `N`,
over every field, every circuit with polynomial gates of fan-in at most two, of any degree and
with any coefficients, formally computing the quadratic form of an `N × N` matrix `M` with
`M + Mᵀ` totally regular has more than `(1 + 1/(4 κ_E) - ε) N ≥ (25/9 - ε) N` gates. Over an
infinite field the same holds for circuits computing the quadratic function
(`eventually_lt_size_of_quadForm_of_infinite`). For an explicit family, the Hankel Cauchy
matrix `1 / (i + j + 2)` and its symmetrization are totally regular over every field of
characteristic zero (`totallyRegular_hankelCauchyCharZero_add_transpose`), so its quadratic form
needs more than `(25/9 - ε) N` polynomial gates over the rationals, the reals, or the complex
numbers (`eventually_lt_size_hankelCauchyCharZero`).
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

open SingleCut Matrix Filter MvPolynomial

variable {σ : Signature} {N : ℕ}

/-! ## The quadratic form as a polynomial -/

/-- The polynomial quadratic form evaluates to the quadratic form. -/
theorem quadForm_eq_eval {K : Type*} [CommRing K] (M : Matrix (Fin N) (Fin N) K)
    (x : Fin N → K) : quadForm M x = eval x (quadFormPolynomial M) := by
  simp only [quadForm, quadFormPolynomial, dotProduct, mulVec, map_sum, map_mul, eval_C, eval_X,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The Hessian of a quadratic form** is `M + Mᵀ` at every point. -/
theorem hessian_quadFormPolynomial {K : Type*} [CommRing K] (M : Matrix (Fin N) (Fin N) K)
    (a : Fin N → K) : Taylor.hessian (quadFormPolynomial M) a = M + Mᵀ := by
  ext k l
  simp only [Taylor.hessian, of_apply, quadFormPolynomial, map_sum, pderiv_C_mul, map_mul,
    aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    Taylor.Internal.aeval_pderiv_pderiv_X_mul_X, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Matrix.add_apply, transpose_apply]
  rw [Finset.sum_eq_single l (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [↓reduceIte, Finset.sum_ite_eq, Finset.mem_univ]
  exact add_comm _ _

/-! ## The rank-cut bound over every field -/

/-- **The rank-cut bound for quadratic forms over every field.** If a single-output circuit with
polynomial gates over a field formally computes the quadratic form of `M`, every set `S` of its
wires has `rank (M + Mᵀ)[X_S, X_T] ≤ |forward S| + |backward S|`. -/
theorem blockRank_add_transpose_le_of_formallyComputes {K : Type*} [Field K]
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) {c : Circuit σ N 1}
    {M : Matrix (Fin N) (Fin N) K}
    (hc : Taylor.FormallyComputes P c fun _ => quadFormPolynomial M)
    (S : Finset (Wire N c.size)) :
    blockRank (M + Mᵀ) (inputsIn S) (inputsIn S)ᶜ ≤
      (forward c.program S).card + (backward c.program S).card := by
  have h := Taylor.blockRank_hessian_le P c S (0 : Fin N → K) fun _ => 1
  rwa [Fin.sum_univ_one, one_smul, hc 0, hessian_quadFormPolynomial] at h

/-- **The finite bound for quadratic forms over every field.** If a fan-in-two circuit with
polynomial gates over a field formally computes the quadratic form of `M`, with `M + Mᵀ`
totally regular, then `⌊N/2⌋ ≤ (A + η) (s - N)⁺ + 3 log₂ (N + 3 s) + C` for its size `s`. -/
theorem half_le_of_formal_quadForm {A η C : ℝ} (hAη : 0 ≤ A + η)
    (order : Multigraph.OrderingBound A η C) {K : Type*} [Field K]
    (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) {c : Circuit σ N 1}
    (hfan : c.FanInAtMost 2) {M : Matrix (Fin N) (Fin N) K} (hM : TotallyRegular (M + Mᵀ))
    (hc : Taylor.FormallyComputes P c fun _ => quadFormPolynomial M) :
    ((N / 2 : ℕ) : ℝ) ≤
      (A + η) * max ((c.size : ℝ) - N) 0 + 3 * Real.logb 2 (N + 3 * c.size) + C :=
  Internal.half_le_of_quadForm_rank_cuts hAη order c.program hfan hM
    (blockRank_add_transpose_le_of_formallyComputes P hc)

/-! ## Asymptotic bounds -/

universe u v

/-- **Quadratic forms need `(1 + 1/(4 κ_E) - ε) N` polynomial gates over every field.** For every
`ε > 0` and all large `N`, every circuit with polynomial gates of fan-in at most two over any
field formally computing the quadratic form of an `N × N` matrix `M` with `M + Mᵀ` totally
regular has more than `(1 + 1/(4 κ_E) - ε) N ≈ (2.7812 - ε) N` gates. -/
theorem eventually_lt_size_of_formal_quadForm {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : Type u) [Field K] (M : Matrix (Fin N) (Fin N) K),
      TotallyRegular (M + Mᵀ) → ∀ (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (c : Circuit σ N 1),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (fun _ => quadFormPolynomial M) →
          (1 + 1 / (4 * Gaussian.frontierCoefficient) - ε) * N < c.size := by
  have h := Internal.eventually_lt_size_of_quadForm_rank_cuts.{u, v}
    (mul_pos two_pos Gaussian.frontierCoefficient_pos) Multigraph.exists_orderingBound_frontier hε
  have h4 : 2 * (2 * Gaussian.frontierCoefficient) = 4 * Gaussian.frontierCoefficient := by ring
  rw [h4] at h
  filter_upwards [h] with N hN
  intro K _ M hM σ P c hfan hc
  exact hN K M hM σ c hfan (blockRank_add_transpose_le_of_formallyComputes P hc)

/-- **Quadratic forms need `(25/9 - ε) N` polynomial gates over every field.** -/
theorem eventually_lt_size_of_formal_quadForm_twentyFive_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : Type u) [Field K] (M : Matrix (Fin N) (Fin N) K),
      TotallyRegular (M + Mᵀ) → ∀ (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) K) (c : Circuit σ N 1),
        c.FanInAtMost 2 → Taylor.FormallyComputes P c (fun _ => quadFormPolynomial M) →
          (25 / 9 - ε) * N < c.size := by
  have hcoef : (25 / 9 : ℝ) ≤ 1 + 1 / (4 * Gaussian.frontierCoefficient) := by
    have hpos : 0 < 4 * Gaussian.frontierCoefficient :=
      mul_pos (by norm_num) Gaussian.frontierCoefficient_pos
    have h4 : 4 * Gaussian.frontierCoefficient ≤ 9 / 16 := by
      linarith [Gaussian.two_mul_frontierCoefficient_le]
    have := one_div_le_one_div_of_le hpos h4
    norm_num at this ⊢
    linarith
  filter_upwards [eventually_lt_size_of_formal_quadForm.{u, v} hε] with N hN
  intro K _ M hM σ P c hfan hc
  refine lt_of_le_of_lt ?_ (hN K M hM σ P c hfan hc)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)

/-- **Quadratic functions over an infinite field.** For every `ε > 0` and all large `N`, over
every infinite field, every circuit whose operations are polynomial functions of at most two
arguments and which computes the quadratic form of an `N × N` matrix `M` with `M + Mᵀ` totally
regular has more than `(25/9 - ε) N` gates. -/
theorem eventually_lt_size_of_quadForm_of_infinite {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (K : Type u) [Field K] [Infinite K] (M : Matrix (Fin N) (Fin N) K),
      TotallyRegular (M + Mᵀ) → ∀ (σ : Signature.{v}) (I : Interpretation σ K),
      Polynomial.IsPolynomial I → ∀ c : Circuit σ N 1, c.FanInAtMost 2 →
        c.Computes I (fun x _ => quadForm M x) → (25 / 9 - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_of_formal_quadForm_twentyFive_div_nine.{u, v} hε] with N hN
  intro K _ _ M hM σ I hI c hfan hc
  refine hN K M hM σ hI.gatePolynomial c hfan (Taylor.formallyComputes_of_computes hI fun x => ?_)
  funext o
  rw [hc x]
  exact quadForm_eq_eval M x

/-! ## An explicit family in characteristic zero -/

/-- **The Hankel Cauchy matrix in characteristic zero.** Over a field of characteristic zero,
`(1 / (i + j + 2))` is the Cauchy matrix with nodes `i + 1` and `-(j + 1)` and is symmetric, so
it and its symmetrization are totally regular. -/
theorem totallyRegular_hankelCauchyCharZero_add_transpose (F : Type*) [Field F] [CharZero F]
    (N : ℕ) : TotallyRegular (hankelCauchyCharZero F N + (hankelCauchyCharZero F N)ᵀ) := by
  have hcauchy : hankelCauchyCharZero F N =
      cauchy (fun i : Fin N => ((i : ℕ) + 1 : F)) fun j => -((j : ℕ) + 1 : F) := by
    ext i j
    simp only [hankelCauchyCharZero, cauchy, of_apply]
    congr 1
    push_cast
    ring
  have hreg : TotallyRegular (hankelCauchyCharZero F N) := by
    rw [hcauchy]
    refine totallyRegular_cauchy _ _ (fun i i' h => ?_) (fun j j' h => ?_) fun i j h => ?_
    · have h' : (((i : ℕ) + 1 : ℕ) : F) = (((i' : ℕ) + 1 : ℕ) : F) := by
        push_cast
        exact h
      exact Fin.ext (by have := Nat.cast_injective h'; omega)
    · have h' : (((j : ℕ) + 1 : ℕ) : F) = (((j' : ℕ) + 1 : ℕ) : F) := by
        push_cast
        exact neg_inj.mp h
      exact Fin.ext (by have := Nat.cast_injective h'; omega)
    · have h' : (((i : ℕ) + j + 2 : ℕ) : F) = 0 := by
        push_cast
        linear_combination h
      exact absurd (Nat.cast_eq_zero.mp h') (by omega)
  refine totallyRegular_add_transpose hreg ?_ two_ne_zero
  ext i j
  simp only [hankelCauchyCharZero, transpose_apply, of_apply]
  congr 3
  omega

/-- **The explicit family needs `(25/9 - ε) N` polynomial gates in characteristic zero.** For
every `ε > 0` and all large `N`, over every field of characteristic zero, every circuit with
polynomial gates of fan-in at most two formally computing the quadratic form
`∑ᵢ ∑ⱼ xᵢ xⱼ / (i + j + 2)` has more than `(25/9 - ε) N` gates. -/
theorem eventually_lt_size_hankelCauchyCharZero {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : Type u) [Field F] [CharZero F] (σ : Signature.{v})
      (P : (op : σ.Op) → MvPolynomial (Fin (σ.Arity op)) F) (c : Circuit σ N 1),
        c.FanInAtMost 2 →
        Taylor.FormallyComputes P c (fun _ => quadFormPolynomial (hankelCauchyCharZero F N)) →
          (25 / 9 - ε) * N < c.size := by
  filter_upwards [eventually_lt_size_of_formal_quadForm_twentyFive_div_nine.{u, v} hε] with N hN
  intro F _ _ σ P c hfan hc
  exact hN F (hankelCauchyCharZero F N) (totallyRegular_hankelCauchyCharZero_add_transpose F N)
    σ P c hfan hc

end Algebraic.Cutwidth.MultiOutput
