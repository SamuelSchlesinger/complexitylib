/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Blocks
import Mathlib.Tactic.Ring

/-!
# Multiplication increases modified degree by at most ordinary degree

The key step is multiplication by one input variable. Interpolation handles a
monomial that reaches the middle level, and majority is idempotent.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m r : ℕ}

theorem span_map_mem {I V W : Type*} [AddCommMonoid V] [Module (ZMod 2) V]
    [AddCommMonoid W] [Module (ZMod 2) W] (v : I → V) (L : V →ₗ[ZMod 2] W)
    (U : Submodule (ZMod 2) W) (h : ∀ i, L (v i) ∈ U)
    {f : V} (hf : f ∈ Submodule.span (ZMod 2) (Set.range v)) : L f ∈ U := by
  apply (show Submodule.span (ZMod 2) (Set.range v) ≤ U.comap L from ?_) hf
  exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)

theorem majority_mul_mem (W : Submodule (ZMod 2) (Finset (Fin (2 * m + 1)) → ZMod 2))
    (h : ∀ a : Low (Fin (2 * m + 1)) m, atomEval (a, true) ∈ W)
    (f : Finset (Fin (2 * m + 1)) → ZMod 2) :
    (fun x => majority x * f x) ∈ W := by
  obtain ⟨q, hq, r, hr, hf⟩ := majority_decomposition f
  let L : (Finset (Fin (2 * m + 1)) → ZMod 2) →ₗ[ZMod 2]
      (Finset (Fin (2 * m + 1)) → ZMod 2) :=
    { toFun := fun q x => majority x * q x
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_left_comm] }
  have heq : (fun x => majority x * f x) = L (q + r) := by
    ext x
    rw [hf]
    simp only [Pi.add_apply, mul_add, ← mul_assoc, majority_sq, L, LinearMap.coe_mk,
      AddHom.coe_mk]
  rw [heq]
  apply lowSpan_map_mem L W ?_ (Submodule.add_mem _ hq hr)
  intro a
  have heq : L (monomial a.val) = atomEval (a, true) := by
    ext x
    simp [L, atomEval, mul_comm]
  rw [heq]
  exact h a

theorem atom_variable_mem (a : Atom m) (j : Fin (2 * m + 1)) :
    (fun x => monomial {j} x * atomEval a x) ∈
      Submodule.span (ZMod 2)
        (Set.range fun b : {b : Atom m // atomWeight b ≤ atomWeight a + 1} =>
          atomEval b.val) := by
  classical
  rcases a with ⟨a, b⟩
  cases b
  · by_cases ha : a.val.card < m
    · let b : Atom m := (⟨insert j a.val, (card_insert_le j a.val).trans (by omega)⟩, false)
      apply Submodule.subset_span
      refine ⟨⟨b, ?_⟩, ?_⟩
      · exact card_insert_le j a.val
      · ext x
        simp only [b, atomEval, Bool.false_eq_true, ↓reduceIte, mul_one]
        rw [← monomial_union]
        simp
    · have heq : a.val.card = m := by have := a.property; omega
      apply (Submodule.span_mono (t := Set.range fun b :
          {b : Atom m // atomWeight b ≤ atomWeight (a, false) + 1} => atomEval b.val) ?_)
        (atom_spans _)
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, by simpa [atomWeight, heq] using atomWeight_le b⟩, rfl⟩
  · have heq : (fun x => monomial {j} x * atomEval (a, true) x) =
        fun x => majority x * (monomial {j} x * monomial a.val x) := by
      ext x
      simp only [atomEval, ↓reduceIte]
      ring
    rw [heq]
    apply majority_mul_mem
    intro b
    exact Submodule.subset_span ⟨⟨(b, true), by simp [atomWeight]⟩, rfl⟩

/-- Insert a function into one factor of a product generator. -/
def replaceFactor (a : Term k m) (i : Fin k) :
    (Finset (Fin (2 * m + 1)) → ZMod 2) →ₗ[ZMod 2] (BlockCube k m → ZMod 2) where
  toFun f x := f (x i) * ∏ j ∈ univ.erase i, atomEval (a j) (x j)
  map_add' := by intros; ext; simp [add_mul]
  map_smul' := by intros; ext; simp [mul_assoc]

theorem replaceFactor_atom (a : Term k m) (i : Fin k) (b : Atom m) :
    replaceFactor a i (atomEval b) = termEval (Function.update a i b) := by
  ext x
  rw [termEval, ← mul_prod_erase univ _ (mem_univ i)]
  simp only [replaceFactor, LinearMap.coe_mk, AddHom.coe_mk, Function.update_self]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (mem_erase.mp hj).1]

theorem weight_update (a : Term k m) (i : Fin k) (b : Atom m) :
    weight (Function.update a i b) =
      atomWeight b + ∑ j ∈ univ.erase i, atomWeight (a j) := by
  rw [weight, ← add_sum_erase univ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (mem_erase.mp hj).1]

theorem weight_eq (a : Term k m) (i : Fin k) :
    weight a = atomWeight (a i) + ∑ j ∈ univ.erase i, atomWeight (a j) :=
  (add_sum_erase univ _ (mem_univ i)).symm

theorem filtration_mono {s : ℕ} (h : r ≤ s) : filtration k m r ≤ filtration k m s := by
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨a.val, a.property.trans h⟩, rfl⟩

theorem term_mem (a : Term k m) {r : ℕ} (h : weight a ≤ r) :
    termEval a ∈ filtration k m r :=
  Submodule.subset_span ⟨⟨a, h⟩, rfl⟩

theorem term_variable_mem (a : Term k m) (i : Fin k) (j : Fin (2 * m + 1)) :
    (fun x => monomial {j} (x i) * termEval a x) ∈ filtration k m (weight a + 1) := by
  have heq : (fun x => monomial {j} (x i) * termEval a x) =
      replaceFactor a i (fun x => monomial {j} x * atomEval (a i) x) := by
    ext x
    simp only [replaceFactor, LinearMap.coe_mk, AddHom.coe_mk, termEval, mul_assoc]
    rw [mul_prod_erase univ (fun l => atomEval (a l) (x l)) (mem_univ i)]
  rw [heq]
  apply span_map_mem _ (replaceFactor a i) (filtration k m (weight a + 1)) ?_
    (atom_variable_mem (a i) j)
  intro b
  rw [replaceFactor_atom]
  apply term_mem
  rw [weight_update, weight_eq a i]
  have := b.property
  omega

/-- Multiplying by one variable increases the modified degree by at most one. -/
theorem variable_mul_mem {f : BlockCube k m → ZMod 2} (hf : f ∈ filtration k m r)
    (i : Fin k) (j : Fin (2 * m + 1)) :
    (fun x => monomial {j} (x i) * f x) ∈ filtration k m (r + 1) := by
  let L : (BlockCube k m → ZMod 2) →ₗ[ZMod 2] (BlockCube k m → ZMod 2) :=
    { toFun := fun f x => monomial {j} (x i) * f x
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp [mul_left_comm] }
  apply span_map_mem _ L (filtration k m (r + 1)) ?_ hf
  intro a
  exact filtration_mono (Nat.add_le_add_right a.property 1) (term_variable_mem a.val i j)

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
