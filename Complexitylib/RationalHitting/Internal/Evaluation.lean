/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Defs
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Rational hitting lists: evaluation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Evaluation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting

namespace Formula
variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]

lemma Eval.unique {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a b : R}
    (ha : Eval c X h a) (hb : Eval c X h b) : a = b := by
  induction ha generalizing b with
  | var i => cases hb; rfl
  | const a => cases hb; rfl
  | add hf hg ihf ihg => cases hb with
    | add hf' hg' => rw [ihf hf', ihg hg']
  | mul hf hg ihf ihg => cases hb with
    | mul hf' hg' => rw [ihf hf', ihg hg']
  | @inv h a v ha hav hva ih =>
    cases hb with
    | @inv _ a' w ha' haw hwa =>
      have heq := ih ha'
      subst a'
      calc
        v = v * 1 := (mul_one _).symm
        _ = v * (a*b) := by rw [haw]
        _ = b := by rw [← mul_assoc, hva, one_mul]

lemma Eval.map {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : R}
    (ha : Eval c X h a) (f : R →+* S) :
    Eval (f.comp c) (fun i => f (X i)) h (f a) := by
  induction ha with
  | var i => exact .var i
  | const a => exact .const a
  | add _ _ ihf ihg => simpa only [map_add] using Eval.add ihf ihg
  | mul _ _ ihf ihg => simpa only [map_mul] using Eval.mul ihf ihg
  | inv ha hab hba ih =>
    exact .inv ih (by rw [← map_mul, hab, map_one]) (by rw [← map_mul, hba, map_one])

/-- Defined evaluations lift through a homomorphism reflecting units. In
particular this handles every inverse occurrence before considering the root. -/
lemma Eval.lift (f : R →+* S) (hf : ∀ x, IsUnit (f x) → IsUnit x)
    {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : S}
    (ha : Eval (f.comp c) (fun i => f (X i)) h a) :
    ∃ b : R, Eval c X h b ∧ f b = a := by
  induction ha with
  | var i => exact ⟨X i, .var i, rfl⟩
  | const a => exact ⟨c a, .const a, rfl⟩
  | add ha hb iha ihb =>
    obtain ⟨a',ha',ea⟩ := iha
    obtain ⟨b',hb',eb⟩ := ihb
    exact ⟨a'+b', .add ha' hb', by rw [map_add,ea,eb]⟩
  | mul ha hb iha ihb =>
    obtain ⟨a',ha',ea⟩ := iha
    obtain ⟨b',hb',eb⟩ := ihb
    exact ⟨a'*b', .mul ha' hb', by rw [map_mul,ea,eb]⟩
  | @inv h a b ha hab hba ih =>
    obtain ⟨a',ha',ea⟩ := ih
    have hau : IsUnit (f a') := ea ▸ ⟨⟨a,b,hab,hba⟩,rfl⟩
    obtain ⟨u,hu⟩ := hf a' hau
    have heval : Eval c X (.inv h) (↑u⁻¹ : R) :=
      .inv ha' (by rw [← hu]; exact u.mul_inv) (by rw [← hu]; exact u.inv_mul)
    refine ⟨_,heval,?_⟩
    exact (heval.map f).unique (.inv ha hab hba)

/-- Mapping a defined nonzero value out of a division ring makes it a unit.
This is used after the partial-specialization domain proof, not instead of it. -/
lemma Eval.unit_of_division_lift {D : Type*} [DivisionRing D] [Nontrivial R]
    (f : D →+* R) {c : ℚ →+* D} {X : Fin n → D} {h : Formula n} {a : R}
    (ha : Eval (f.comp c) (fun i => f (X i)) h a) (ha0 : a ≠ 0) : IsUnit a := by
  have hf : ∀ x, IsUnit (f x) → IsUnit x := by
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    exact hx.ne_zero (by rw [hzero,map_zero])
  obtain ⟨b,hb,heq⟩ := ha.lift f hf
  have hb0 : b ≠ 0 := by intro h; apply ha0; rw [← heq,h,map_zero]
  exact heq ▸ (isUnit_iff_ne_zero.mpr hb0).map f

end Formula
end RationalHitting


namespace RationalHitting.NoncommBlocks
open Matrix
variable {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Matrix multiplication over the possibly noncommutative coefficient ring. -/
abbrev matMul {l m n : Type*} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) :
    Matrix l n R := A * B

lemma upper_unit (B : Matrix ι κ R) : IsUnit (fromBlocks (1 : Matrix ι ι R) B 0 (1 : Matrix κ κ
    R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 (-B) 0 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

lemma lower_unit (C : Matrix κ ι R) : IsUnit (fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ
    R)) := by
  apply isUnit_iff_exists.mpr
  refine ⟨fromBlocks 1 0 (-C) 1, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

lemma diag_unit_iff (A : Matrix ι ι R) (D : Matrix κ κ R) :
    IsUnit (fromBlocks A 0 0 D) ↔ IsUnit A ∧ IsUnit D := by
  constructor
  · rintro ⟨u,hu⟩
    have hh := u.val_inv
    have hh' := u.inv_val
    rw [hu] at hh hh'
    refine ⟨isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₁₁, ?_, ?_⟩,
      isUnit_iff_exists.mpr ⟨(↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R).toBlocks₂₂, ?_, ?_⟩⟩
    · have h := congrArg Matrix.toBlocks₁₁ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₁₁ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
    · have h := congrArg Matrix.toBlocks₂₂ hh'
      rw [← fromBlocks_toBlocks u.inv, fromBlocks_multiply] at h
      ext i j
      have hx := congrFun (congrFun h i) j
      simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.submatrix, Matrix.one_apply] using hx
  · rintro ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
    apply isUnit_iff_exists.mpr
    refine ⟨fromBlocks (↑u⁻¹) 0 0 (↑v⁻¹), ?_, ?_⟩ <;> simp [fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul]

lemma schur_factor (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    fromBlocks A B C 0 =
      fromBlocks 1 0 (C * A') 1 * fromBlocks A 0 0 (-C * A' * B) *
      fromBlocks 1 (A' * B) 0 1 := by
  simp only [fromBlocks_multiply, add_zero, zero_add,
    one_mul, mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]
  rw [← Matrix.mul_assoc A A' B, hAA', Matrix.one_mul, Matrix.mul_assoc C A' A, hA'A,
    Matrix.mul_one]
  simp [Matrix.mul_assoc, Matrix.neg_mul]

lemma schur_unit_iff (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    IsUnit (fromBlocks A B C 0) ↔ IsUnit (C * A' * B) := by
  rw [schur_factor A A' B C hAA' hA'A]
  obtain ⟨u,hu⟩ := upper_unit (A' * B)
  obtain ⟨v,hv⟩ := lower_unit (C * A')
  rw [← hu, ← hv, Units.isUnit_mul_units, Units.isUnit_units_mul]
  rw [diag_unit_iff]
  have hA : IsUnit A := isUnit_iff_exists.mpr ⟨A',hAA',hA'A⟩
  simp [hA, Matrix.neg_mul, IsUnit.neg_iff]


lemma schur_inverse (A A' : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (a b : Matrix κ κ R) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (ha : C * A' * B = a) (hab : a*b=1) (hba : b*a=1) :
    ∃ M : Matrix (ι ⊕ κ) (ι ⊕ κ) R,
      fromBlocks A B C 0 * M = 1 ∧ M * fromBlocks A B C 0 = 1 ∧
      matMul (matMul (fromCols (0 : Matrix κ ι R) (-1)) M)
        (fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R)) = b := by
  let U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 0 (C*A') 1, fromBlocks 1 0 (-(C*A')) 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let V : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks 1 (A'*B) 0 1, fromBlocks 1 (-(A'*B)) 0 1,
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]⟩
  let D : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    ⟨fromBlocks A 0 0 (-a), fromBlocks A' 0 0 (-b),
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,hAA',hab],
      by simp [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,hA'A,hba]⟩
  have hS : (↑(U*D*V) : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = fromBlocks A B C 0 := by
    change fromBlocks 1 0 (C*A') 1 * fromBlocks A 0 0 (-a) *
      fromBlocks 1 (A'*B) 0 1 = _
    rw [← ha]
    simpa [Matrix.neg_mul] using (schur_factor A A' B C hAA' hA'A).symm
  refine ⟨↑(U*D*V)⁻¹, ?_, ?_, ?_⟩
  · rw [← hS]; exact (U*D*V).mul_inv
  · rw [← hS]; exact (U*D*V).inv_mul
  · change matMul (matMul (fromCols (0 : Matrix κ ι R) (-1))
      (V.inv * (D.inv * U.inv))) (fromRows (0 : Matrix ι κ R) (1 : Matrix κ κ R)) = b
    simp [matMul,V,D,U,fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,
      Matrix.fromCols_mul_fromBlocks,fromCols_mul_fromRows,
      Matrix.mul_assoc,Matrix.neg_mul,Matrix.mul_neg]

end RationalHitting.NoncommBlocks

end Complexity
