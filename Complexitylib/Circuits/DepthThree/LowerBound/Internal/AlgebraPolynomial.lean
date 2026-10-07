/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraBits
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Div

/-!
# Unrestricted depth-three lower bound: algebra polynomial

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/AlgebraPolynomial.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators
open Polynomial

namespace DepthThreeLowerBound.BinaryAlgebra

/-- Pack a finite vector of field elements as polynomial coefficients. -/
def pack {r : ℕ} (v : Fin r → ZMod 2) : Polynomial (ZMod 2) :=
  ∑ i : Fin r, Polynomial.monomial i.val (v i)

theorem degree_pack_lt {r : ℕ} (v : Fin r → ZMod 2) :
    (pack v).degree < (r : WithBot ℕ) := by
  simpa only [pack, Polynomial.C_mul_X_pow_eq_monomial] using
    (Polynomial.degree_sum_fin_lt v)

@[simp] theorem coeff_pack {r : ℕ} (v : Fin r → ZMod 2) (i : Fin r) :
    (pack v).coeff i.val = v i := by
  classical
  simp only [pack, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_eq_val, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]

theorem coeff_pack_of_le {r : ℕ} (v : Fin r → ZMod 2) {j : ℕ} (hj : r ≤ j) :
    (pack v).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_degree_lt
    ((degree_pack_lt v).trans_le (WithBot.coe_le_coe.mpr hj))

theorem coeff_pack_nat {r : ℕ} (v : Fin r → ZMod 2) (j : ℕ) :
    (pack v).coeff j = if h : j < r then v ⟨j, h⟩ else 0 := by
  by_cases hj : j < r
  · rw [dite_eq_left hj]
    exact coeff_pack v ⟨j, hj⟩
  · rw [dite_eq_right hj]
    exact coeff_pack_of_le v (Nat.le_of_not_lt hj)

theorem pack_injective {r : ℕ} :
    Function.Injective (pack : (Fin r → ZMod 2) → Polynomial (ZMod 2)) := by
  intro v w h
  funext i
  simpa only [coeff_pack] using congrArg (fun f : Polynomial (ZMod 2) => f.coeff i.val) h

@[simp] theorem pack_zero {r : ℕ} : pack (0 : Fin r → ZMod 2) = 0 := by
  simp [pack]

@[simp] theorem pack_add {r : ℕ} (v w : Fin r → ZMod 2) :
    pack (v + w) = pack v + pack w := by
  simp only [pack, Pi.add_apply, map_add, Finset.sum_add_distrib]

@[simp] theorem pack_smul {r : ℕ} (c : ZMod 2) (v : Fin r → ZMod 2) :
    pack (c • v) = c • pack v := by
  simp only [pack, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem pack_coeff_of_degree_lt {r : ℕ} (f : Polynomial (ZMod 2))
    (hf : f.degree < (r : WithBot ℕ)) :
    pack (fun i : Fin r => f.coeff i.val) = f := by
  unfold pack
  calc
    (∑ i : Fin r, Polynomial.monomial i.val (f.coeff i.val)) =
        f.sum (fun i c => Polynomial.monomial i c) :=
      Polynomial.sum_fin (fun i c => Polynomial.monomial i c)
        (fun i => Polynomial.monomial_zero_right i) hf
    _ = f := Polynomial.sum_monomial_eq f

/-- The monic polynomial obtained from its lower coefficients. -/
def inputPolynomial {r : ℕ} (v : Fin r → ZMod 2) : Polynomial (ZMod 2) :=
  Polynomial.X ^ r + pack v

theorem inputPolynomial_monic {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).Monic :=
  Polynomial.monic_X_pow_add (degree_pack_lt v)

@[simp] theorem inputPolynomial_degree {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).degree = (r : WithBot ℕ) := by
  have h : (pack v).degree < (Polynomial.X ^ r : Polynomial (ZMod 2)).degree := by
    simpa only [Polynomial.degree_X_pow] using degree_pack_lt v
  simpa only [inputPolynomial, Polynomial.degree_X_pow] using
    Polynomial.degree_add_eq_left_of_degree_lt h

@[simp] theorem inputPolynomial_natDegree {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).natDegree = r := by
  have h : (pack v).degree < (Polynomial.X ^ r : Polynomial (ZMod 2)).degree := by
    simpa only [Polynomial.degree_X_pow] using degree_pack_lt v
  simpa only [inputPolynomial, Polynomial.natDegree_X_pow] using
    Polynomial.natDegree_add_eq_left_of_degree_lt h

theorem inputPolynomial_ne_zero {r : ℕ} (v : Fin r → ZMod 2) :
    inputPolynomial v ≠ 0 :=
  (inputPolynomial_monic v).ne_zero

@[simp] theorem inputPolynomial_coeff_lt {r : ℕ} (v : Fin r → ZMod 2) (i : Fin r) :
    (inputPolynomial v).coeff i.val = v i := by
  rw [inputPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    ite_eq_right (Nat.ne_of_lt i.is_lt), zero_add, coeff_pack]

@[simp] theorem inputPolynomial_coeff_leading {r : ℕ} (v : Fin r → ZMod 2) :
    (inputPolynomial v).coeff r = 1 := by
  rw [inputPolynomial, Polynomial.coeff_add, Polynomial.coeff_X_pow_self,
    coeff_pack_of_le v (Nat.le_refl r), add_zero]

theorem inputPolynomial_coeff_of_gt {r : ℕ} (v : Fin r → ZMod 2)
    {j : ℕ} (hj : r < j) : (inputPolynomial v).coeff j = 0 := by
  apply Polynomial.coeff_eq_zero_of_degree_lt
  rw [inputPolynomial_degree]
  exact WithBot.coe_lt_coe.mpr hj

/-- The monic input polynomial specified by Boolean coefficient bits. -/
def inputPolynomialBits {r : ℕ} (p : Fin r → Bool) : Polynomial (ZMod 2) :=
  inputPolynomial (fun i => bitValue (p i))

theorem inputPolynomialBits_monic {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).Monic :=
  inputPolynomial_monic _

@[simp] theorem inputPolynomialBits_degree {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).degree = (r : WithBot ℕ) :=
  inputPolynomial_degree _

@[simp] theorem inputPolynomialBits_natDegree {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).natDegree = r :=
  inputPolynomial_natDegree _

@[simp] theorem inputPolynomialBits_coeff_lt {r : ℕ} (p : Fin r → Bool) (i : Fin r) :
    (inputPolynomialBits p).coeff i.val = bitValue (p i) :=
  inputPolynomial_coeff_lt _ _

@[simp] theorem inputPolynomialBits_coeff_leading {r : ℕ} (p : Fin r → Bool) :
    (inputPolynomialBits p).coeff r = 1 :=
  inputPolynomial_coeff_leading _

end DepthThreeLowerBound.BinaryAlgebra

end

end Complexity
