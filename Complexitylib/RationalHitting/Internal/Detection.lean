/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.RationalHitting.Evaluation.Defs
public import Complexitylib.RationalHitting.Internal.Evaluation

/-!
# Correctness of finite matrix tests

The domain test uses the size-two extension `f + 1`: at a defined point,
either `f` is nonzero or `f + 1` is nonzero. A hitting list for both therefore
contains a point in the domain of `f`, even if `f` is identically zero.
-/

public section

namespace Complexity.RationalHitting.Internal
open Formula Output


lemma matrix_inverse_left {d : ℕ} (a : Mat d) (ha : a.det ≠ 0) :
    a * (a.det⁻¹ • a.adjugate) = 1 := by
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ ha, one_smul]

lemma matrix_inverse_right {d : ℕ} (a : Mat d) (ha : a.det ≠ 0) :
    (a.det⁻¹ • a.adjugate) * a = 1 := by
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]

lemma evalMatrix_sound {n d : ℕ} (f : Formula n) (X : Tuple n d)
    {v : Mat d} (h : f.evalMatrix? X = some v) : Evaluates f X v := by
  induction f generalizing v with
  | var i => cases h; exact .var i
  | const a => cases h; exact .const a
  | add f g ihf ihg =>
      change (f.evalMatrix? X).bind (fun a =>
        (g.evalMatrix? X).bind (fun b => some (a + b))) = some v at h
      obtain ⟨a, ha, b, hb, hv⟩ : ∃ a, f.evalMatrix? X = some a ∧
          ∃ b, g.evalMatrix? X = some b ∧ a + b = v := by
        simpa only [Option.bind_eq_some_iff, Option.some.injEq] using h
      exact hv ▸ Formula.Eval.add (ihf ha) (ihg hb)
  | mul f g ihf ihg =>
      change (f.evalMatrix? X).bind (fun a =>
        (g.evalMatrix? X).bind (fun b => some (a * b))) = some v at h
      obtain ⟨a, ha, b, hb, hv⟩ : ∃ a, f.evalMatrix? X = some a ∧
          ∃ b, g.evalMatrix? X = some b ∧ a * b = v := by
        simpa only [Option.bind_eq_some_iff, Option.some.injEq] using h
      exact hv ▸ Formula.Eval.mul (ihf ha) (ihg hb)
  | inv f ih =>
      obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
      by_cases hd : a.det = 0
      · simp [hd] at hb
      · have hv : a.det⁻¹ • a.adjugate = v := by simpa [hd] using hb
        exact hv ▸ Formula.Eval.inv (ih ha) (matrix_inverse_left a hd) (matrix_inverse_right a hd)

lemma evalMatrix_complete {n d : ℕ} {f : Formula n} {X : Tuple n d}
    {v : Mat d} (h : Evaluates f X v) : f.evalMatrix? X = some v := by
  induction h with
  | var i => rfl
  | const a => rfl
  | add ha hb iha ihb => simp [evalMatrix?, iha, ihb]
  | mul ha hb iha ihb => simp [evalMatrix?, iha, ihb]
  | @inv f a b h hab hba ih =>
      have hu : IsUnit a := ⟨⟨a, b, hab, hba⟩, rfl⟩
      have hd : a.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det a).mp hu).ne_zero
      have hi : Evaluates (.inv f) X (a.det⁻¹ • a.adjugate) :=
        Formula.Eval.inv h (matrix_inverse_left a hd) (matrix_inverse_right a hd)
      have he := Formula.Eval.unique hi (Formula.Eval.inv h hab hba)
      simp [evalMatrix?, ih, hd, he]

lemma nonzero_admissible {n : ℕ} {f : Formula n} (hf : Nonzero f) : Admissible f := by
  obtain ⟨d, hd, X, v, he, _⟩ := hf
  exact ⟨d, hd, X, v, he⟩

lemma hits_nonzero_iff {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.size ≤ s) :
    Nonzero f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v := by
  have : NeZero H.dimension := ⟨H.dimension_pos.ne'⟩
  constructor
  · intro h
    exact hH f hf (nonzero_admissible h) h
  · rintro ⟨X, _, v, he, hu⟩
    exact ⟨H.dimension, H.dimension_pos, X, v, he, hu.ne_zero⟩

lemma admissible_nonzero_or_add_one {n : ℕ} (f : Formula n) (hf : Admissible f) :
    Nonzero f ∨ Nonzero (.add f (.const 1)) := by
  obtain ⟨d, hd, X, v, he⟩ := hf
  by_cases hv : v = 0
  · have : NeZero d := ⟨hd.ne'⟩
    right
    refine ⟨d, hd, X, v + 1, ?_, ?_⟩
    · simpa only [Evaluates, map_one] using Formula.Eval.add he (Formula.Eval.const 1)
    · simpa only [hv, zero_add] using (one_ne_zero : (1 : Mat d) ≠ 0)
  · exact Or.inl ⟨d, hd, X, v, he, hv⟩

lemma hits_admissible_iff {n s : ℕ} {H : Output n} (hH : Hits (s + 2) H)
    (f : Formula n) (hf : f.size ≤ s) :
    Admissible f ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v := by
  constructor
  · intro ha
    rcases admissible_nonzero_or_add_one f ha with hn | hn
    · obtain ⟨X, hX, v, he, _⟩ := hH f (by lia) ha hn
      exact ⟨X, hX, v, he⟩
    · have hsize : (Formula.add f (.const 1)).size ≤ s + 2 := by
        simpa only [Formula.size] using Nat.add_le_add_right (Nat.add_le_add_right hf 1) 1
      obtain ⟨X, hX, v, he, _⟩ := hH (.add f (.const 1)) hsize (nonzero_admissible hn) hn
      cases he with
      | add hleft _ => exact ⟨X, hX, _, hleft⟩
  · rintro ⟨X, _, v, he⟩
    exact ⟨H.dimension, H.dimension_pos, X, v, he⟩

lemma hits_admissible_inv_iff_nonzero {n s : ℕ} {H : Output n} (hH : Hits s H)
    (f : Formula n) (hf : f.size ≤ s) : Admissible (.inv f) ↔ Nonzero f := by
  constructor
  · rintro ⟨d, hd, X, v, he⟩
    have : NeZero d := ⟨hd.ne'⟩
    cases he with
    | @inv _ a _ he hab hba =>
        have hu : IsUnit a := ⟨⟨a, v, hab, hba⟩, rfl⟩
        exact ⟨d, hd, X, a, he, hu.ne_zero⟩
  · intro hn
    obtain ⟨X, _, v, he, hu⟩ := (hits_nonzero_iff hH f hf).mp hn
    obtain ⟨u, rfl⟩ := hu
    exact ⟨H.dimension, H.dimension_pos, X, ↑u⁻¹, Formula.Eval.inv he u.mul_inv u.inv_mul⟩

lemma admissibilityTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.admissibilityTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v := by
  simp only [admissibilityTest, List.any_eq_true, Option.isSome_iff_exists]
  constructor
  · rintro ⟨X, hX, v, hv⟩
    exact ⟨X, hX, v, evalMatrix_sound f X hv⟩
  · rintro ⟨X, hX, v, hv⟩
    exact ⟨X, hX, v, evalMatrix_complete hv⟩

lemma nonzeroTest_iff {n : ℕ} (H : Output n) (f : Formula n) :
    H.nonzeroTest f = true ↔ ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v := by
  simp only [nonzeroTest, List.any_eq_true, Option.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨X, hX, v, hv, hd⟩
    exact ⟨X, hX, v, evalMatrix_sound f X hv,
      (Matrix.isUnit_iff_isUnit_det v).mpr (isUnit_iff_ne_zero.mpr hd)⟩
  · rintro ⟨X, hX, v, hv, hu⟩
    exact ⟨X, hX, v, evalMatrix_complete hv,
      ((Matrix.isUnit_iff_isUnit_det v).mp hu).ne_zero⟩

lemma hits_admissibilityTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits (s + 2) H) (f : Formula n) (hf : f.size ≤ s) :
    H.admissibilityTest f = true ↔ Admissible f := by
  rw [admissibilityTest_iff H f, hits_admissible_iff hH f hf]

lemma hits_nonzeroTest_eq_true_iff {n s : ℕ} {H : Output n}
    (hH : Hits s H) (f : Formula n) (hf : f.size ≤ s) :
    H.nonzeroTest f = true ↔ Nonzero f := by
  rw [nonzeroTest_iff H f, hits_nonzero_iff hH f hf]


end Complexity.RationalHitting.Internal
