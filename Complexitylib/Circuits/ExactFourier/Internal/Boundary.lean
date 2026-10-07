/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.ExactFourier.Internal.FFTCircuit

/-!
# Exact Fourier circuits: boundary

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Boundary.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

section
namespace ExactFourier.Boundary
open Polynomial
open scoped BigOperators

/-- Division by a fixed monic polynomial as a complex linear map. -/
noncomputable def quotientLinear (ℓ : ℂ[X]) (hℓ : ℓ.Monic) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun f := f /ₘ ℓ
  map_add' f g := by
    apply (div_modByMonic_unique (f /ₘ ℓ + g /ₘ ℓ)
      (f %ₘ ℓ + g %ₘ ℓ) hℓ ?_).1
    constructor
    · rw [mul_add]
      linear_combination modByMonic_add_div f ℓ + modByMonic_add_div g ℓ
    · exact lt_of_le_of_lt (degree_add_le _ _) (max_lt
        (degree_modByMonic_lt _ hℓ) (degree_modByMonic_lt _ hℓ))
  map_smul' c f := by
    apply (div_modByMonic_unique (c • (f /ₘ ℓ)) (c • (f %ₘ ℓ)) hℓ ?_).1
    constructor
    · rw [mul_smul_comm, ← smul_add, modByMonic_add_div]
    · exact (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hℓ)

@[simp] theorem quotientLinear_apply (ℓ : ℂ[X]) (hℓ : ℓ.Monic) (f : ℂ[X]) :
    quotientLinear ℓ hℓ f = f /ₘ ℓ := rfl

/-- Inputs strictly before the final d times do not cross the coefficient boundary. -/
theorem prefix_quotient_zero (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d t b : ℕ} (ht : ℓ.natDegree = t) (hf : f.natDegree ≤ d) (hb : b + d < t) :
    (f * X ^ b) /ₘ ℓ = 0 := by
  apply (divByMonic_eq_zero_iff hℓ).mpr
  rw [degree_eq_natDegree hℓ.ne_zero, ht]
  apply (degree_le_natDegree).trans_lt
  exact_mod_cast (calc
    (f * X ^ b).natDegree ≤ f.natDegree + (X ^ b : ℂ[X]).natDegree := natDegree_mul_le
    _ ≤ d + b := by simpa using Nat.add_le_add_right hf b
    _ < t := by omega)

/-- The quotient, with sign reversed, has strictly fewer than d coefficients. -/
theorem quotient_degree_lt (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d t b : ℕ} (ht : ℓ.natDegree = t) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hb : b < t) :
    ((f * X ^ b) /ₘ ℓ).natDegree < d := by
  rw [natDegree_divByMonic _ hℓ, ht]
  have h : (f * X ^ b).natDegree ≤ d + b := by
    exact natDegree_mul_le.trans (by simpa using Nat.add_le_add_right hf b)
  omega

/-- Exact division of a shifted matrix entry. This keeps the generator coefficients
on the left, ready for the ordered J_i*G_j matrix formula. -/
theorem quotient_shift_expansion (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d : ℕ} (hf : f.natDegree ≤ d) (b : ℕ) :
    (f * X ^ b) /ₘ ℓ =
      ∑ j ∈ Finset.range (d + 1), f.coeff j • ((X ^ (b + j) : ℂ[X]) /ₘ ℓ) := by
  have hF : f * X ^ b =
      ∑ j ∈ Finset.range (d + 1), f.coeff j • (X ^ (b + j) : ℂ[X]) := by
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := d+1) (by omega)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_eq_C_mul, mul_assoc, ← pow_add, Nat.add_comm j b]
  change quotientLinear ℓ hℓ (f * X ^ b) = _
  rw [hF, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp

/-- Entrywise modulus reduction differs from time truncation by minus the modulus
 times precisely the quotient above. No bounds on coefficients are imposed. -/
theorem boundary_difference (ℓ f : ℂ[X]) (b : ℕ) :
    (f * X ^ b) %ₘ ℓ - f * X ^ b = -ℓ * ((f * X ^ b) /ₘ ℓ) := by
  rw [modByMonic_eq_sub_mul_div]
  ring

/-- Truncated coefficient matrix of multiplication by the polynomial matrix `G`. -/
noncomputable def timeMatrix {ι : Type} (t : ℕ) (G : Matrix ι ι ℂ[X]) :
    Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  fun a b => (G a.2 b.2 * X ^ b.1.val).coeff a.1.val

/-- Coefficient matrix of multiplication by `G` followed by reduction modulo `ℓ`. -/
noncomputable def modulusMatrix {ι : Type} (t : ℕ) (ℓ : ℂ[X])
    (G : Matrix ι ι ℂ[X]) : Matrix (Fin t × ι) (Fin t × ι) ℂ :=
  fun a b => ((G a.2 b.2 * X ^ b.1.val) %ₘ ℓ).coeff a.1.val

/-- The modulus correction has no columns at times b<t-d. -/
theorem correction_prefix_zero {ι : Type} {t d : ℕ} (G : Matrix ι ι ℂ[X])
    (ℓ : ℂ[X]) (hℓ : ℓ.Monic) (ht : ℓ.natDegree = t)
    (hG : ∀ i j, (G i j).natDegree ≤ d)
    (a b : Fin t × ι) (hb : b.1.val < t - d) :
    (modulusMatrix t ℓ G - timeMatrix t G) a b = 0 := by
  have hq := prefix_quotient_zero ℓ (G a.2 b.2) hℓ ht (hG _ _) (by omega : b.1.val + d < t)
  simp only [Matrix.sub_apply, modulusMatrix, timeMatrix]
  rw [modByMonic_eq_sub_mul_div, hq]
  simp

/-- Scalar weights for the exact ordered generator formula. Prefix correction uses
η=1. The suffix uses the first t coefficients of ℓ/u^k. -/
noncomputable def orderedWeight (η ℓ : ℂ[X]) (a b i j : ℕ) : ℂ :=
  -(η * X ^ i * ((X ^ (b + j) : ℂ[X]) /ₘ ℓ)).coeff a

theorem polynomial_ordered_expansion (η ℓ f g : ℂ[X]) (hℓ : ℓ.Monic)
    {d e : ℕ} (hg : g.natDegree ≤ d) (hf : f.natDegree ≤ e) (b : ℕ) :
    η * f * (-((g * X ^ b) /ₘ ℓ)) =
      ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (d+1),
        (f.coeff i * g.coeff j) • (-(η * X ^ i * ((X ^ (b+j) : ℂ[X]) /ₘ ℓ))) := by
  rw [quotient_shift_expansion ℓ g hℓ hg]
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := e+1) (by omega)]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib,
    mul_neg, smul_eq_C_mul]
  apply congrArg Neg.neg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring

/-- Extract one coefficient from every entry of a polynomial matrix. -/
noncomputable def coefficientMatrix {ι κ : Type} (G : Matrix ι κ ℂ[X]) (j : ℕ) :
    Matrix ι κ ℂ := fun u v => (G u v).coeff j

/-- Polynomial correction for a single input time b, before taking its output
coefficient. Matrix multiplication is in the original order J then G. -/
noncomputable def weightedCorrection {ι : Type} [Fintype ι] (η ℓ : ℂ[X])
    (J G : Matrix ι ι ℂ[X]) (b : ℕ) : Matrix ι ι ℂ[X] :=
  fun u v => ∑ x, η * J u x * (-((G x v * X ^ b) /ₘ ℓ))

/-- Exact ordered-span part of the coefficient-boundary comparison. There is no
commutation hypothesis on any pair of spatial coefficient matrices. -/
theorem ordered_span {ι : Type} [Fintype ι] (η ℓ : ℂ[X]) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι ℂ[X]) {d e : ℕ}
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e) (a b : ℕ) :
    coefficientMatrix (weightedCorrection η ℓ J G b) a =
      ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (d+1),
        orderedWeight η ℓ a b i j • (coefficientMatrix J i * coefficientMatrix G j) := by
  classical
  ext u v
  simp only [coefficientMatrix, weightedCorrection, finsetSum_coeff,
    polynomial_ordered_expansion η ℓ _ _ hℓ (hG _ _) (hJ _ _) b,
    coeff_smul, coeff_neg]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    coefficientMatrix, orderedWeight, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Explicit prefix coefficient convention, including negative (a-i) indices. -/
theorem orderedWeight_prefix (ℓ : ℂ[X]) (a b i j : ℕ) :
    orderedWeight 1 ℓ a b i j =
      if i ≤ a then -((X ^ (b+j) : ℂ[X]) /ₘ ℓ).coeff (a-i) else 0 := by
  simp only [orderedWeight, one_mul, coeff_X_pow_mul']
  split_ifs <;> simp_all

/-- The prefix correction J*v has no coefficients at times a>=e+d. -/
theorem prefix_row_vanishes {ι : Type} [Fintype ι] (ℓ : ℂ[X]) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι ℂ[X]) {d e t a b : ℕ}
    (ht : ℓ.natDegree = t) (hd : 0 < d)
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e)
    (hb : b < t) (ha : e+d ≤ a) :
    coefficientMatrix (weightedCorrection 1 ℓ J G b) a = 0 := by
  classical
  ext u v
  simp only [coefficientMatrix, weightedCorrection, finsetSum_coeff, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply coeff_eq_zero_of_natDegree_lt
  rw [one_mul]
  have hq := quotient_degree_lt ℓ (G x v) hℓ ht hd (hG _ _) hb
  have hj := hJ u x
  have hp := natDegree_mul_le (p := J u x) (q := -((G x v * X ^ b) /ₘ ℓ))
  rw [natDegree_neg] at hp
  omega

/-- No weighted correction has an input column before the suffix. -/
theorem weightedCorrection_prefix_zero {ι : Type} [Fintype ι]
    (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X]) {d t b : ℕ}
    (ht : ℓ.natDegree = t) (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hb : b+d < t) : weightedCorrection η ℓ J G b = 0 := by
  classical
  funext u v
  simp only [weightedCorrection, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [prefix_quotient_zero ℓ (G x v) hℓ ht (hG _ _) hb]
  simp

/-- The actual early--suffix formula after the scalar prefix conjugation. -/
noncomputable def activeCorrection {ι : Type} [Fintype ι]
    (t d : ℕ) (η ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X]) :
    Matrix (Fin t × ι) (Fin t × ι) ℂ := fun a b =>
  if a.1.val < t-d then
    (weightedCorrection 1 ℓ J G b.1.val a.2 b.2).coeff a.1.val
  else (weightedCorrection η ℓ J G b.1.val a.2 b.2).coeff a.1.val

/-- Times in the initial or final boundary region where a correction can act. -/
def ActiveTime (t d e a : ℕ) : Prop := a < min (t-d) (e+d) ∨ t-d ≤ a

instance (t d e a : ℕ) : Decidable (ActiveTime t d e a) := by
  unfold ActiveTime
  infer_instance

theorem activeCorrection_column_support {ι : Type} [Fintype ι]
    (t d : ℕ) (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X])
    (ht : ℓ.natDegree = t) (hG : ∀ u v, (G u v).natDegree ≤ d)
    (a b : Fin t × ι) (hb : b.1.val < t-d) :
    activeCorrection t d η ℓ J G a b = 0 := by
  have hb' : b.1.val+d < t := by omega
  simp only [activeCorrection]
  rw [weightedCorrection_prefix_zero 1 ℓ hℓ J G ht hG hb',
    weightedCorrection_prefix_zero η ℓ hℓ J G ht hG hb']
  simp

theorem activeCorrection_row_support {ι : Type} [Fintype ι]
    (t d e : ℕ) (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X])
    (ht : ℓ.natDegree = t) (hd : 0<d)
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e)
    (a b : Fin t × ι) (ha : ¬ActiveTime t d e a.1.val) :
    activeCorrection t d η ℓ J G a b = 0 := by
  have ha' : a.1.val < t-d := by unfold ActiveTime at ha; omega
  have ha'' : e+d ≤ a.1.val := by unfold ActiveTime at ha; omega
  rw [activeCorrection, ite_eq_left ha']
  have hh := congrFun (congrFun (prefix_row_vanishes ℓ hℓ J G ht hd hG hJ
    b.1.isLt ha'') a.2) b.2
  exact hh

/-- Simultaneous row/column permutation isolates every matrix correction supported
on a single active index set, with an exact identity on its complement. -/
theorem supported_identity_decomposition {κ : Type} [DecidableEq κ]
    (S : κ → Prop) [DecidablePred S] (L : Matrix κ κ ℂ)
    (hrow : ∀ i j, ¬S i → L i j = 0)
    (hcol : ∀ i j, ¬S j → L i j = 0) :
    (1 + L).submatrix (Equiv.sumCompl S) (Equiv.sumCompl S) =
      Matrix.fromBlocks (1 + L.submatrix Subtype.val Subtype.val)
        (0 : Matrix {i // S i} {i // ¬S i} ℂ) 0 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.submatrix, Matrix.one_apply, Subtype.ext_iff]
  · have hij : (i : κ) ≠ (j : κ) := by intro h; exact j.property (h ▸ i.property)
    simp [Matrix.submatrix, Matrix.one_apply, hcol _ _ j.property]
  · have hij : (i : κ) ≠ (j : κ) := by intro h; exact i.property (h.symm ▸ j.property)
    simp [Matrix.submatrix, Matrix.one_apply, hrow _ _ i.property]
  · simp [Matrix.submatrix, Matrix.one_apply, hrow _ _ i.property, Subtype.ext_iff]

theorem active_identity_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d e : ℕ) (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X])
    (ht : ℓ.natDegree = t) (hd : 0<d)
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e) :
    let S : (Fin t × ι) → Prop := fun a => ActiveTime t d e a.1.val
    (1 + activeCorrection t d η ℓ J G).submatrix (Equiv.sumCompl S) (Equiv.sumCompl S) =
      Matrix.fromBlocks
        (1 + (activeCorrection t d η ℓ J G).submatrix
          (Subtype.val : {a // S a} → Fin t × ι) Subtype.val)
        (0 : Matrix {a // S a} {a // ¬S a} ℂ) 0 1 := by
  classical
  apply supported_identity_decomposition
  · exact fun a b ha => activeCorrection_row_support t d e η ℓ hℓ J G ht hd hG hJ a b ha
  · intro a b hb
    apply activeCorrection_column_support t d η ℓ hℓ J G ht hG a b
    unfold ActiveTime at hb
    omega

end ExactFourier.Boundary

end

section
/- Literal relation between modulus multiplication and the supported correction.
This is the missing interface at 06-feedback:86--196, not an assumed theorem.
Noncommutative coefficient matrices remain ordered J_i G_j. -/
namespace ExactFourier.Boundary
open Polynomial
open CoefficientTime
open scoped Kronecker BigOperators

/-- Embed polynomial matrices into formal power series matrices entrywise. -/
noncomputable def seriesMatrix {ι : Type} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ[X] →+* Matrix ι ι (PowerSeries ℂ) :=
  (Polynomial.coeToPowerSeries.ringHom : ℂ[X] →+* PowerSeries ℂ).mapMatrix

@[simp] theorem seriesMatrix_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ[X]) (i j : ι) : seriesMatrix G i j = (G i j : PowerSeries ℂ) := rfl

theorem timeMatrix_eq_trunc {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (G : Matrix ι ι ℂ[X]) :
    timeMatrix t G = blockTruncHom t (seriesMatrix G) := by
  ext a b
  simp only [timeMatrix, coeff_mul_X_pow', blockTruncHom_apply, seriesMatrix_apply,
    Polynomial.coeff_coe]

/-- Negated quotient columns for the discrepancy between remainder and truncation. -/
noncomputable def quotientColumns {ι : Type} (t : ℕ) (ℓ : ℂ[X])
    (G : Matrix ι ι ℂ[X]) : Matrix ι (Fin t × ι) (PowerSeries ℂ) :=
  fun i b => (-((G i b.2 * X^b.1.val) /ₘ ℓ) : ℂ[X])

/-- The exact remainder-minus-truncation map: minus the quotient times ℓ. -/
theorem difference_eq_columns {ι : Type}
    (t : ℕ) (ℓ : ℂ[X]) (G : Matrix ι ι ℂ[X]) :
    modulusMatrix t ℓ G - timeMatrix t G =
      coefficientColumns t ((ℓ : PowerSeries ℂ) • quotientColumns t ℓ G) := by
  ext a b
  change (((G a.2 b.2 * X^b.1.val) %ₘ ℓ).coeff a.1.val -
    (G a.2 b.2 * X^b.1.val).coeff a.1.val) =
    PowerSeries.coeff a.1.val ((ℓ : PowerSeries ℂ) *
      ((-((G a.2 b.2 * X^b.1.val) /ₘ ℓ) : ℂ[X]) : PowerSeries ℂ))
  rw [← coeff_sub, boundary_difference]
  rw [← Polynomial.coe_mul, Polynomial.coeff_coe]
  congr 1
  ring_nf

/-- The polynomial adjugate/denominator identity gives the TRUE inverse, before
any support reduction. This is not an inverse evaluation assumption. -/
theorem timeMatrix_inverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (u : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hGJ : G * J = Matrix.scalar ι u) :
    (timeMatrix t G)⁻¹ =
      blockTruncHom t ((u : PowerSeries ℂ)⁻¹ • seriesMatrix J) := by
  apply Matrix.inv_eq_right_inv
  rw [timeMatrix_eq_trunc, ← map_mul, Matrix.mul_smul, ← map_mul, hGJ]
  have hu' : PowerSeries.constantCoeff (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hs : (u : PowerSeries ℂ)⁻¹ • seriesMatrix (Matrix.scalar ι u) = 1 := by
    apply Matrix.ext
    intro i j
    by_cases hij : i=j
    · subst j
      simpa [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using
        PowerSeries.inv_mul_cancel (u : PowerSeries ℂ) hu'
    · simp [Matrix.smul_apply, Matrix.scalar_apply, hij]
  rw [hs, map_one]

/-- The relative correction is the coefficient map of (ℓ/u) J v, with the
quotient sign included in v. -/
theorem inverse_mul_difference {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hGJ : G * J = Matrix.scalar ι u) :
    (timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G - timeMatrix t G) =
      coefficientColumns t (((ℓ : PowerSeries ℂ) * (u : PowerSeries ℂ)⁻¹) •
        (seriesMatrix J * quotientColumns t ℓ G)) := by
  rw [timeMatrix_inverse t u G J hu hGJ, difference_eq_columns,
    blocks_mul_columns, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (u : PowerSeries ℂ)⁻¹]

/-- A prefix-only scalar convolution cancels the denominator on early rows, and
literally leaves the late rows unchanged. -/
theorem prefix_scalar_cancels {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f η : PowerSeries ℂ) (hfη : f*η=1)
    (V : Matrix ι κ (PowerSeries ℂ)) (a : Fin t × ι) (b : κ) :
    ((prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) *
      coefficientColumns t (η • V)) a b =
        if a.1.val < T then PowerSeries.coeff a.1.val (V a.2 b)
        else PowerSeries.coeff a.1.val (η * V a.2 b) := by
  rw [prefix_mul_columns]
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hfη, one_mul]

end ExactFourier.Boundary

namespace ExactFourier.Boundary
open Polynomial CoefficientTime
open scoped Kronecker BigOperators

/-- Coefficients below t cannot see the discarded tail of a scalar series. -/
theorem coeff_trunc_mul_series (t : ℕ) (η V : PowerSeries ℂ) (a : Fin t) :
    PowerSeries.coeff a.val (((PowerSeries.trunc t η : ℂ[X]) : PowerSeries ℂ) * V) =
      PowerSeries.coeff a.val (η*V) := by
  rw [coeff_mul_truncated _ _ a, coeff_mul_truncated _ _ a]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hka : k.val ≤ a.val
  · have hat : a.val-k.val < t := by have := a.isLt; omega
    simp [hka, PowerSeries.coeff_trunc, hat]
  · simp [hka]

/-- Converting the finite polynomial ordered generator formula to series changes
neither matrix order nor the sign of the quotient. -/
theorem weightedCorrection_series {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (η ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X])
    (i : ι) (b : Fin t × ι) :
    (((weightedCorrection η ℓ J G b.1.val) i b.2 : ℂ[X]) : PowerSeries ℂ) =
      (η : PowerSeries ℂ) * (seriesMatrix J * quotientColumns t ℓ G) i b := by
  simp only [weightedCorrection, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul,
    Matrix.mul_apply, seriesMatrix_apply, quotientColumns, Finset.mul_sum, mul_assoc]

/-- The finite polynomial η used in the ordered-span certificate is exactly the
first t coefficients of ℓ/u; no truncation error survives in any output row. -/
theorem weightedCorrection_trunc_coeff {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (η : PowerSeries ℂ) (ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X])
    (a b : Fin t × ι) :
    (weightedCorrection (PowerSeries.trunc t η) ℓ J G b.1.val a.2 b.2).coeff a.1.val =
      PowerSeries.coeff a.1.val (η * (seriesMatrix J * quotientColumns t ℓ G) a.2 b) := by
  rw [← Polynomial.coeff_coe, weightedCorrection_series]
  exact coeff_trunc_mul_series t η _ a.1

/-- Quotient columns vanish on the whole coefficient prefix, not merely on an
assumed active direct summand. -/
theorem quotientColumns_prefix_zero {ι : Type} (t d : ℕ) (ℓ : ℂ[X])
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (G : Matrix ι ι ℂ[X])
    (hG : ∀ i j, (G i j).natDegree ≤ d) (i : ι) (b : Fin t × ι)
    (hb : b.1.val < t-d) : quotientColumns t ℓ G i b = 0 := by
  have hb' : b.1.val+d<t := by omega
  simp only [quotientColumns, prefix_quotient_zero ℓ _ hℓ ht (hG _ _) hb',
    neg_zero, Polynomial.coe_zero]

/-- The actual relative map I+S is fixed on its right by every prefix map. -/
theorem inverse_difference_prefix_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hGJ : G*J=Matrix.scalar ι u)
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (hG : ∀ i j, (G i j).natDegree ≤ d)
    (a b : Fin t × ι) (hb : b.1.val < t-d) :
    ((timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G - timeMatrix t G)) a b = 0 := by
  rw [inverse_mul_difference t u ℓ G J hu hGJ]
  simp only [coefficientColumns, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [quotientColumns_prefix_zero t d ℓ hℓ ht G hG _ b hb, mul_zero,
    Finset.sum_const_zero, map_zero]

/-- Premultiplication of the literal relative correction gives exactly the
previously certified finite activeCorrection matrix. -/
theorem prefix_mul_inverse_difference {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hℓ0 : ℓ.coeff 0 ≠ 0)
    (hGJ : G*J=Matrix.scalar ι u) :
    (prefixScalar t (t-d) ((u : PowerSeries ℂ) * (ℓ : PowerSeries ℂ)⁻¹) ⊗ₖ
      (1 : Matrix ι ι ℂ)) *
      ((timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G - timeMatrix t G)) =
        activeCorrection t d
          (PowerSeries.trunc t ((ℓ : PowerSeries ℂ) * (u : PowerSeries ℂ)⁻¹)) ℓ J G := by
  have hu' : PowerSeries.constantCoeff (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hℓ' : PowerSeries.constantCoeff (ℓ : PowerSeries ℂ) ≠ 0 := by simpa using hℓ0
  have hic : ((u : PowerSeries ℂ) * (ℓ : PowerSeries ℂ)⁻¹) *
      ((ℓ : PowerSeries ℂ) * (u : PowerSeries ℂ)⁻¹) = 1 := by
    calc
      _ = ((u : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹) *
          ((ℓ : PowerSeries ℂ)⁻¹*(ℓ : PowerSeries ℂ)) := by ring
      _ = 1 := by rw [PowerSeries.mul_inv_cancel _ hu', PowerSeries.inv_mul_cancel _ hℓ', one_mul]
  rw [inverse_mul_difference t u ℓ G J hu hGJ]
  ext a b
  rw [prefix_scalar_cancels _ _ _ _ hic]
  rw [activeCorrection]
  split_ifs with ha
  · rw [← Polynomial.coeff_coe, weightedCorrection_series]
    simp
  · exact (weightedCorrection_trunc_coeff t _ ℓ J G a b).symm

end ExactFourier.Boundary

namespace ExactFourier.Boundary
open Polynomial CoefficientTime
open scoped Kronecker BigOperators

theorem prefix_conjugated_relative_map {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hℓ0 : ℓ.coeff 0 ≠ 0)
    (hGJ : G*J=Matrix.scalar ι u)
    (hG0 : IsUnit (G.map (fun f => f.coeff 0)))
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (hG : ∀ i j, (G i j).natDegree ≤ d) :
    let P := prefixScalar t (t-d) ((u : PowerSeries ℂ)*(ℓ : PowerSeries ℂ)⁻¹) ⊗ₖ
      (1 : Matrix ι ι ℂ)
    P * ((timeMatrix t G)⁻¹ * modulusMatrix t ℓ G) * P⁻¹ =
      1 + activeCorrection t d
        (PowerSeries.trunc t ((ℓ : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹)) ℓ J G := by
  let f : PowerSeries ℂ := (u : PowerSeries ℂ)*(ℓ : PowerSeries ℂ)⁻¹
  let η : PowerSeries ℂ := (ℓ : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹
  let P := prefixScalar t (t-d) f ⊗ₖ (1 : Matrix ι ι ℂ)
  let Q := prefixScalar t (t-d) η ⊗ₖ (1 : Matrix ι ι ℂ)
  let S := (timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G-timeMatrix t G)
  have hA : IsUnit (timeMatrix t G) := by
    rw [timeMatrix_eq_trunc]
    apply blockTrunc_isUnit
    exact hG0
  have hrel : (timeMatrix t G)⁻¹ * modulusMatrix t ℓ G = 1+S := by
    dsimp only [S]
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)]
    abel
  have hu' : PowerSeries.constantCoeff (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hℓ' : PowerSeries.constantCoeff (ℓ : PowerSeries ℂ) ≠ 0 := by simpa using hℓ0
  have hfη : f*η=1 := by
    calc
      f*η = ((u : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹) *
          ((ℓ : PowerSeries ℂ)⁻¹*(ℓ : PowerSeries ℂ)) := by dsimp [f, η]; ring
      _ = 1 := by rw [PowerSeries.mul_inv_cancel _ hu', PowerSeries.inv_mul_cancel _ hℓ', one_mul]
  have hPQ : P*Q=1 := by
    dsimp only [P, Q]
    rw [← Matrix.mul_kronecker_mul, ← prefixScalar_mul, hfη, prefixScalar_one]
    simp
  have hPinv : P⁻¹=Q := Matrix.inv_eq_right_inv hPQ
  have hSQ : S*Q=S := zero_prefix_columns_mul t (t-d) η S
    (fun a b hb => inverse_difference_prefix_zero t d u ℓ G J hu hGJ hℓ ht hG a b hb)
  change P * ((timeMatrix t G)⁻¹ * modulusMatrix t ℓ G) * P⁻¹ = _
  calc
    _ = P*(1+S)*Q := by rw [hrel, hPinv]
    _ = P*Q+P*(S*Q) := by noncomm_ring
    _ = 1+P*S := by rw [hPQ, hSQ]
    _ = _ := by rw [prefix_mul_inverse_difference t d u ℓ G J hu hℓ0 hGJ]

end ExactFourier.Boundary

end

end Complexity
