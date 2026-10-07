/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Walsh
public import Mathlib.Basic.Complex.BigOperators

/-!
# Gotsman--Linial: PolynomialDegree

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Polynomial degree and the Walsh filtration

The polynomial lemmas concern real multilinear
`MvPolynomial`s. Restriction to the cube is justified by an explicit monomial
expansion rather than assumed as an alternate polynomial representation.
-/

open scoped BigOperators symmDiff

namespace BooleanAnalysis.PolynomialThreshold.Internal

noncomputable section

variable {n d : ℕ}

/-- Adding a constant preserves the multilinearity condition. -/
theorem IsMultilinear.add_C {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (c : ℝ) : IsMultilinear (p + MvPolynomial.C c) := by
  classical
  intro m hm i
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hm | hm
  · exact hp m hm i
  · have hm0 : m = 0 := by
      by_cases hc : c = 0
      · simp [hc] at hm
      · simpa [MvPolynomial.support_C, hc] using hm
    simp [hm0]

/-- Adding a constant cannot violate an existing total-degree upper bound. -/
theorem totalDegree_add_C_le {p : MvPolynomial (Fin n) ℝ}
    (hd : p.totalDegree ≤ d) (c : ℝ) :
    (p + MvPolynomial.C c).totalDegree ≤ d := by
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hd (by simp))

/-- Every exponent occurring in a supported multilinear monomial is one. -/
theorem IsMultilinear.exponent_eq_one {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) {m : Fin n →₀ ℕ} (hm : m ∈ p.support)
    {i : Fin n} (hi : i ∈ m.support) : m i = 1 := by
  exact Nat.le_antisymm (hp m hm i)
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- A supported monomial has no more variables than the polynomial's total
degree. This estimate does not require multilinearity. -/
theorem monomial_support_card_le_totalDegree {p : MvPolynomial (Fin n) ℝ}
    {m : Fin n →₀ ℕ} (hm : m ∈ p.support) : m.support.card ≤ p.totalDegree := by
  calc
    m.support.card = ∑ _i ∈ m.support, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hm

/-- Faithful evaluation of a multilinear polynomial as products over
the supports of its monomials. -/
theorem polynomialValue_eq_multilinear_expansion {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (x : Cube n) :
    polynomialValue p x =
      ∑ m ∈ p.support, p.coeff m * ∏ i ∈ m.support, cubeCoord x i := by
  classical
  unfold polynomialValue
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hp.exponent_eq_one hm hi, pow_one]

/-- The same faithful expansion, with values regarded as complex numbers. -/
theorem polynomialValue_walsh_expansion {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (x : Cube n) :
    (polynomialValue p x : ℂ) =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * walshChar m.support x := by
  rw [polynomialValue_eq_multilinear_expansion hp]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, walshChar]

/-- A character of degree at most `d` belongs to the corresponding filtration. -/
theorem walshChar_mem_fourierSpace {S : Finset (Fin n)} (hS : S.card ≤ d) :
    walshChar S ∈ fourierSpace n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- The exact polynomial bridge into the complex Walsh filtration. -/
theorem polynomialValue_mem_fourierSpace {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => (polynomialValue p x : ℂ)) ∈ fourierSpace n d := by
  classical
  have hsum : (∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) • walshChar m.support) ∈
      fourierSpace n d := by
    apply Submodule.sum_mem
    intro m hm
    exact Submodule.smul_mem _ _
      (walshChar_mem_fourierSpace ((monomial_support_card_le_totalDegree hm).trans hd))
  convert hsum using 1
  ext x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    polynomialValue_walsh_expansion hp x

/-- Complex conjugation preserves Fourier degree, since each character is real. -/
theorem fourierSpace_star {a : Cube n → ℂ} (ha : a ∈ fourierSpace n d) :
    star a ∈ fourierSpace n d := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨S, hS, rfl⟩ := ha
      have hstar : star (walshChar S) = walshChar S := by
        ext x
        exact star_walshChar S x
      rw [hstar]
      exact walshChar_mem_fourierSpace hS
  | zero => simpa only [star_zero] using (fourierSpace n d).zero_mem
  | add a b _ _ ha hb =>
      simpa only [star_add] using (fourierSpace n d).add_mem ha hb
  | smul c a _ ha =>
      simpa only [star_smul] using (fourierSpace n d).smul_mem (star c) ha

/-- The filtration is multiplicative. The symmetric difference of two index
sets has cardinality at most the sum of their cardinalities. -/
theorem fourierSpace_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    a * b ∈ fourierSpace n (r + s) := by
  classical
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨S, hS, rfl⟩ := ha
      obtain ⟨T, hT, rfl⟩ := hb
      have hST : (S ∆ T).card ≤ r + s :=
        (Finset.card_le_card Finset.symmDiff_subset_union).trans
          ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
      convert walshChar_mem_fourierSpace hST using 1
      ext x
      exact walshChar_mul S T x
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c _ _ _ ha hb =>
      simpa only [add_mul] using (fourierSpace n (r + s)).add_mem ha hb
  | add_right a b c _ _ _ ha hb =>
      simpa only [mul_add] using (fourierSpace n (r + s)).add_mem ha hb
  | smul_left c a b _ _ hab =>
      simpa only [smul_mul_assoc] using (fourierSpace n (r + s)).smul_mem c hab
  | smul_right c a b _ _ hab =>
      simpa only [mul_smul_comm] using (fourierSpace n (r + s)).smul_mem c hab

/-- The precise multiplication-conjugation rule used in the weighted pairing. -/
theorem fourierSpace_conj_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    (fun x => star (b x) * a x) ∈ fourierSpace n (r + s) := by
  simpa only [Nat.add_comm, Pi.mul_def, Pi.star_def] using
    fourierSpace_mul (fourierSpace_star hb) ha

/-- Multiplication by one cube coordinate raises the degree by at most one. -/
theorem cubeCoord_mul_mem_fourierSpace {r : ℕ} {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (i : Fin n) :
    (fun x => (cubeCoord x i : ℂ) * a x) ∈ fourierSpace n (r + 1) := by
  have hi : walshChar {i} ∈ fourierSpace n 1 :=
    walshChar_mem_fourierSpace (by simp)
  have h := fourierSpace_mul hi ha
  rw [Nat.add_comm] at h
  convert h using 1
  ext x
  simp only [Pi.mul_apply, walshChar_singleton]

/-- Functions whose Walsh support starts in degree `k`. -/
def fourierSpaceFrom (n k : ℕ) : Submodule ℂ (Cube n → ℂ) :=
  Submodule.span ℂ (walshChar '' {S : Finset (Fin n) | k ≤ S.card})

theorem walshChar_mem_fourierSpaceFrom {S : Finset (Fin n)} (hS : d ≤ S.card) :
    walshChar S ∈ fourierSpaceFrom n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Full parity complements character index sets, taking low degree `d` to
Fourier support in degrees at least `n - d`. -/
theorem parity_mul_mem_fourierSpaceFrom {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n d) :
    (fun x => walshChar Finset.univ x * a x) ∈ fourierSpaceFrom n (n - d) := by
  classical
  change walshChar Finset.univ * a ∈ fourierSpaceFrom n (n - d)
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨S, hS, rfl⟩ := ha
      have hSc : n - d ≤ (Finset.univ \ S).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simpa using Nat.sub_le_sub_left hS n
      convert walshChar_mem_fourierSpaceFrom hSc using 1
      ext x
      exact walshChar_univ_mul S x
  | zero => simp
  | add a b _ _ ha hb =>
      simpa only [mul_add] using (fourierSpaceFrom n (n - d)).add_mem ha hb
  | smul c a _ ha =>
      simpa only [mul_smul_comm] using (fourierSpaceFrom n (n - d)).smul_mem c ha

/-- Low and high Fourier support with a strict gap have zero counting pairing.
There is no conjugation in this formulation because Walsh characters are real;
it applies directly to the product appearing in the weighted proof. -/
theorem sum_mul_eq_zero_of_fourier_separated {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpaceFrom n s) (hrs : r < s) :
    (∑ x : Cube n, a x * b x) = 0 := by
  classical
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨S, hS, rfl⟩ := ha
      obtain ⟨T, hT, rfl⟩ := hb
      have hne : S ≠ T := by
        intro h
        subst T
        exact (not_lt_of_ge (hT.trans hS)) hrs
      simpa only [star_walshChar, ite_eq_right hne] using walshChar_orthogonality S T
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c _ _ _ ha hb =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, hb, add_zero]
  | add_right a b c _ _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul_left c a b _ _ hab =>
      simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_zero] using
        congrArg (fun z : ℂ => c * z) hab
  | smul_right c a b _ _ hab =>
      simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, mul_zero] using
        congrArg (fun z : ℂ => c * z) hab

/-- The polynomial has high Fourier support after multiplication by
full parity, with no alternate polynomial-class assumption. -/
theorem parity_polynomialValue_mem_fourierSpaceFrom {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ)) ∈
      fourierSpaceFrom n (n - d) :=
  parity_mul_mem_fourierSpaceFrom (polynomialValue_mem_fourierSpace hp hd)

/-- Every Fourier coefficient below `n - d` of the parity-transformed
polynomial vanishes. -/
theorem parity_polynomialValue_low_coefficient_eq_zero {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) {S : Finset (Fin n)}
    (hS : S.card < n - d) :
    walshCoefficientLinear S
      (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ)) = 0 := by
  have h := sum_mul_eq_zero_of_fourier_separated
    (walshChar_mem_fourierSpace (Nat.le_refl S.card))
    (parity_polynomialValue_mem_fourierSpaceFrom hp hd) hS
  simpa only [walshCoefficientLinear, LinearMap.coe_mk, AddHom.coe_mk, star_walshChar] using h

end

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
