/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.QuantumSeries
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Rational hitting lists: quantum matrices

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/QuantumMatrices.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.HahnMatrix
open HahnSeries Matrix
open scoped BigOperators
noncomputable section
variable {Γ R S : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Ring R] [Ring S]

/-- Apply a ring homomorphism to every Hahn-series coefficient. -/
def mapCoeff (φ : R →+* S) : HahnSeries Γ R →+* HahnSeries Γ S where
  toFun x := x.map φ.toZeroHom
  map_zero' := HahnSeries.map_zero φ.toZeroHom
  map_one' := HahnSeries.map_one φ.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add φ.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul φ.toNonUnitalRingHom

lemma coeff_mul_support_superset (x y : HahnSeries Γ R) (a : Γ)
    (s t : Set Γ) (hs : s.IsPWO) (ht : t.IsPWO)
    (hxs : x.support ⊆ s) (hyt : y.support ⊆ t) :
    (x*y).coeff a = ∑ ij ∈ Finset.antidiagonal hs ht a,
      x.coeff ij.1 * y.coeff ij.2 := by
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_subset
  · intro ij hij
    rw [Finset.mem_antidiagonal] at hij ⊢
    exact ⟨hxs hij.1, hyt hij.2.1, hij.2.2⟩
  · intro ij hij hnot
    rw [Finset.mem_antidiagonal] at hij
    by_cases hx : x.coeff ij.1 = 0
    · simp [hx]
    by_cases hy : y.coeff ij.2 = 0
    · simp [hy]
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr ⟨hx,hy,hij.2.2⟩))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extract one matrix entry from every Hahn-series coefficient. -/
def entry (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) : HahnSeries Γ R :=
  x.map (⟨fun A => A i j, rfl⟩ : ZeroHom (Matrix ι ι R) R)

@[simp] lemma entry_coeff.{v_1, v_2, v_4} {Γ : Type v_1} {R : Type v_2}
  [LinearOrder Γ] [Ring R] {ι : Type v_4}
  (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) (a : Γ) :
  (RationalHitting.HahnMatrix.entry x i j).coeff a = x.coeff a i j := rfl

lemma entry_support.{v_1, v_2, v_4} {Γ : Type v_1} {R : Type v_2}
  [LinearOrder Γ] [Ring R] {ι : Type v_4}
  (x : HahnSeries Γ (Matrix ι ι R)) (i j : ι) :
  (RationalHitting.HahnMatrix.entry x i j).support ⊆ x.support := by
  intro a ha
  change x.coeff a ≠ 0
  intro h
  exact ha (by change x.coeff a i j = 0; rw [h]; rfl)

/-- Identify a matrix-valued Hahn series with a matrix of scalar Hahn series. -/
def split : HahnSeries Γ (Matrix ι ι R) →+* Matrix ι ι (HahnSeries Γ R) where
  toFun x := entry x
  map_zero' := by ext i j a; rfl
  map_one' := by
    ext i j a
    change (1 : HahnSeries Γ (Matrix ι ι R)).coeff a i j =
      (if i = j then (1 : HahnSeries Γ R) else 0).coeff a
    by_cases hi : i = j <;> by_cases ha : a = 0 <;> simp [hi,ha]
  map_add' x y := by ext i j a; rfl
  map_mul' x y := by
    ext i j a
    change (x*y).coeff a i j = (∑ k, entry x i k * entry y k j).coeff a
    rw [HahnSeries.coeff_mul, Matrix.sum_apply, HahnSeries.coeff_sum]
    simp_rw [coeff_mul_support_superset _ _ a x.support y.support
      x.isPWO_support y.isPWO_support (entry_support x i _) (entry_support y _ j)]
    rw [Finset.sum_comm]
    rfl

lemma split_injective : Function.Injective (split (Γ := Γ) (R := R) (ι := ι)) := by
  intro x y h
  ext a i j
  exact congrArg (fun z : Matrix ι ι (HahnSeries Γ R) => (z i j).coeff a) h

variable {K : Type*} [Field K]

/-- Scalar series embedded as scalar matrices at each coefficient. -/
def scalarSeries : HahnSeries Γ K →+* HahnSeries Γ (Matrix ι ι K) :=
  mapCoeff (algebraMap K (Matrix ι ι K))

lemma split_scalarSeries (x : HahnSeries Γ K) :
    split (scalarSeries (ι := ι) x) = algebraMap (HahnSeries Γ K)
      (Matrix ι ι (HahnSeries Γ K)) x := by
  ext i j a
  change (algebraMap K (Matrix ι ι K) (x.coeff a)) i j = _
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h, ]

lemma scalarSeries_commute (x : HahnSeries Γ K) (y : HahnSeries Γ (Matrix ι ι K)) :
    scalarSeries x * y = y * scalarSeries x := by
  apply split_injective
  rw [map_mul, map_mul, split_scalarSeries, Algebra.commutes]

/-- The natural scalar-series algebra structure, derived through an injective
matrix realization rather than assuming commutative matrix coefficients. -/
@[instance_reducible]
def seriesAlgebra : Algebra (HahnSeries Γ K) (HahnSeries Γ (Matrix ι ι K)) :=
  (scalarSeries (Γ := Γ) (K := K) (ι := ι)).toAlgebra'
    (fun x y => scalarSeries_commute x y)

end
end RationalHitting.HahnMatrix


namespace RationalHitting.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- The Weyl monomial D^a S^b. -/
def weyl (a b : ZMod d) : Matrix (ZMod d) (ZMod d) K :=
  fun i j => if i = j+b then χ (a*i) else 0

@[simp] lemma weyl_zero.{v_1} {K : Type v_1} [Field K] {d : ℕ}
  (χ : AddChar (ZMod d) K) : RationalHitting.QuantumMatrices.weyl χ 0 0 = 1 := by
  ext i j
  simp [weyl, Matrix.one_apply]

lemma weyl_mul (a b c e : ZMod d) :
    weyl χ a b * weyl χ c e = χ (-c*b) • weyl χ (a+c) (b+e) := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i-b)]
  · simp only [weyl, sub_add_cancel, ite_true, Matrix.smul_apply, smul_eq_mul]
    have heq : i-b = j+e ↔ i = j+(b+e) := by constructor <;> intro h <;> linear_combination h
    by_cases h : i = j+(b+e)
    · simp only [ite_eq_left (heq.mpr h), ite_eq_left h]
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [heq, h]
  · intro k hk hne
    have h : i ≠ k+b := by intro heq; apply hne; rw [heq]; ring
    simp [weyl, h]
  · simp

lemma weyl_inverse_right (a b : ZMod d) :
    weyl χ a b * (χ (-a*b) • weyl χ (-a) (-b)) = 1 := by
  rw [Matrix.mul_smul, weyl_mul, add_neg_cancel, add_neg_cancel, weyl_zero, smul_smul,
    ← AddChar.map_add_eq_mul]
  have h : -a*b + -(-a)*b = 0 := by ring
  rw [h, AddChar.map_zero_eq_one, one_smul]

lemma weyl_inverse_left (a b : ZMod d) :
    (χ (-a*b) • weyl χ (-a) (-b)) * weyl χ a b = 1 := by
  rw [Matrix.smul_mul, weyl_mul, neg_add_cancel, neg_add_cancel, weyl_zero, smul_smul,
    ← AddChar.map_add_eq_mul]
  have h : -a*b + -a*(-b) = 0 := by ring
  rw [h, AddChar.map_zero_eq_one, one_smul]

/-- A Weyl matrix with its explicit two-sided inverse. -/
def weylUnit (a b : ZMod d) : (Matrix (ZMod d) (ZMod d) K)ˣ :=
  ⟨weyl χ a b, χ (-a*b) • weyl χ (-a) (-b),
    weyl_inverse_right χ a b, weyl_inverse_left χ a b⟩

@[simp] lemma weylUnit_val (a b : ZMod d) : (weylUnit χ a b : Matrix _ _ K) = weyl χ a b := rfl

@[simp] lemma weylUnit_zero : weylUnit χ 0 0 = 1 := by
  apply Units.ext
  exact weyl_zero χ

end
end RationalHitting.QuantumMatrices

namespace RationalHitting.QuantumMatrices
open Matrix
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K) (hχ : χ.IsPrimitive)

/-- The coefficient of a Weyl matrix in the finite Fourier expansion. -/
def fourierCoeff (R : Matrix (ZMod d) (ZMod d) K) (a b : ZMod d) : K :=
  (d : K)⁻¹ * ∑ j, χ (-a*j) * R j (j-b)

lemma orthogonality.{v_1} {K : Type v_1} [Field K]  {d : ℕ}
  [NeZero d] (χ : AddChar (ZMod d) K) (hχ : χ.IsPrimitive) (x : ZMod d) :
  ∑ a, χ (a * x) = if x = 0 then ↑d else 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx, ZMod.card]
  · rw [ite_eq_right hx]
    simpa [AddChar.mulShift_apply, mul_comm] using AddChar.sum_eq_zero_of_ne_one (hχ hx)

include hχ in
/-- Fourier inversion on each cyclic matrix diagonal. -/

theorem fourier_reconstruction (R : Matrix (ZMod d) (ZMod d) K) :
    (∑ a, ∑ b, fourierCoeff χ R a b • weyl χ a b) = R := by
  classical
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, weyl]
  simp_rw [mul_ite, mul_zero]
  have heq (a : ZMod d) :
      (∑ b, if i = j+b then fourierCoeff χ R a b * χ (a*i) else 0) =
      fourierCoeff χ R a (i-j) * χ (a*i) := by
    rw [Finset.sum_eq_single (i-j)]
    · simp
    · intro b hb hne
      rw [ite_eq_right]
      intro h
      apply hne
      linear_combination -h
    · simp
  simp_rw [heq, fourierCoeff, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hc (k : ZMod d) :
      (∑ a, χ (-a*k) * R k (k-(i-j)) * χ (a*i)) =
      (if i = k then (d : K) else 0) * R k (k-(i-j)) := by
    calc
      _ = (∑ a, χ (a*(i-k))) * R k (k-(i-j)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        rw [mul_right_comm, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      _ = _ := by simp only [orthogonality χ hχ, sub_eq_zero]
  simp_rw [hc]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]

end
end RationalHitting.QuantumMatrices


namespace RationalHitting.QuantumLift
open HahnSeries Matrix
open RationalHitting.QuantumSeries RationalHitting.QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- Lexicographically ordered pairs of integer exponents. -/
abbrev Exponents := ℤ ×ₗ ℤ
/-- Hahn series with matrix coefficients and two integer exponents. -/
abbrev Ambient := HahnSeries Exponents (Matrix (ZMod d) (ZMod d) K)

/-- The Weyl unit assigned to an exponent pair. -/
def monomialUnit (g : Exponents) : (Matrix (ZMod d) (ZMod d) K)ˣ :=
  weylUnit χ (ofLex g).1 (ofLex g).2

lemma monomialUnit_zero.{v_1} {K : Type v_1} [Field K]  {d : ℕ}
  [NeZero d] (χ : AddChar (ZMod d) K) : RationalHitting.QuantumLift.monomialUnit χ 0 = 1 := by
  simp [monomialUnit]

lemma monomialUnit_mul.{v_1} {K : Type v_1} [Field K]  {d : ℕ}
  [NeZero d] (χ : AddChar (ZMod d) K) (g h : RationalHitting.QuantumLift.Exponents) :
  ∃ c : K,
    (RationalHitting.QuantumLift.monomialUnit χ g : Matrix (ZMod d) (ZMod d) K) *
        (RationalHitting.QuantumLift.monomialUnit χ h : Matrix (ZMod d) (ZMod d) K) =
      c • (RationalHitting.QuantumLift.monomialUnit χ (g + h) : Matrix (ZMod d) (ZMod d) K) := by
  refine ⟨χ (-((ofLex h).1 : ZMod d) * ((ofLex g).2 : ZMod d)), ?_⟩
  simp [monomialUnit, weyl_mul]

/-- The Hahn-series subring whose coefficients lie on the Weyl monomial lines. -/
abbrev divisionSubring := coefficientRing (monomialUnit χ) (monomialUnit_zero χ)
    (monomialUnit_mul χ)

noncomputable instance : DivisionRing (divisionSubring χ) :=
  divisionRing (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)

/-- The Fourier lift as a finite Hahn series. -/
def lift (R : Matrix (ZMod d) (ZMod d) K) : Ambient (K := K) (d := d) :=
  ∑ a : ZMod d, ∑ b : ZMod d,
    single (toLex ((a.val : ℤ), (b.val : ℤ))) (fourierCoeff χ R a b • weyl χ a b)

omit [CharZero K] in
lemma lift_mem (R : Matrix (ZMod d) (ZMod d) K) : lift χ R ∈ divisionSubring χ := by
  apply Subring.sum_mem
  intro a ha
  apply Subring.sum_mem
  intro b hb
  apply single_mem (monomialUnit χ) (monomialUnit_zero χ) (monomialUnit_mul χ)
  apply Submodule.mem_span_singleton.mpr
  refine ⟨fourierCoeff χ R a b, ?_⟩
  simp [monomialUnit]

/-- The finite Fourier lift as an element of the division subring. -/
def liftD (R : Matrix (ZMod d) (ZMod d) K) : divisionSubring χ := ⟨lift χ R, lift_mem χ R⟩

/-- The representation used in the rank-gap argument. Its coefficient field
is a commutative Hahn field; all inversion takes place inside the division
subring, never by adjoining arbitrary matrix-field scalars. -/
def representation : divisionSubring χ →+* Matrix (ZMod d) (ZMod d) (HahnSeries Exponents K) :=
  (RationalHitting.HahnMatrix.split (Γ := Exponents)).comp (divisionSubring χ).subtype

end
end RationalHitting.QuantumLift

end Complexity
