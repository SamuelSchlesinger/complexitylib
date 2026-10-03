/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Internal.SecondMoment
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalization of the finite leftover-hash bound

The counting proof is normalized to the existing retained-seed test
probability. Restricting an input family along an injection preserves
universality, so the finite-type bound applies to every finite flat support.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem universalHashFamily_comp_injective {α β Seed Ω : Type*} [Fintype Seed]
    [Fintype Ω] {E : α → Seed → Ω} (universal : UniversalHashFamily E)
    (f : β → α) (injective : Function.Injective f) :
    UniversalHashFamily (fun x y => E (f x) y) := by
  intro x x' distinct
  exact universal (f x) (f x') (fun equal => distinct (injective equal))

theorem seededTestProb_sub_uniform_mul {α Seed Ω : Type*} [Fintype α]
    [Fintype Seed] [Fintype Ω] [Nonempty α] [Nonempty Seed] [Nonempty Ω]
    (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    (seededTestProb E T - uniformSeededTestProb T) *
        ((Fintype.card α : ℝ) * Fintype.card Seed * Fintype.card Ω) =
      ∑ z ∈ T, hashCenteredCount E z := by
  have source : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have seed : (Fintype.card Seed : ℝ) ≠ 0 := by positivity
  have output : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  rw [seededTestProb_eq_hashFiberCount, uniformSeededTestProb]
  simp only [hashCenteredCount, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem universalHashFamily_seededTestProb_sub_uniform_sq_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty α] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} (universal : UniversalHashFamily E) (T : Finset (Seed × Ω)) :
    (seededTestProb E T - uniformSeededTestProb T) ^ 2 ≤
      (Fintype.card Ω : ℝ) / (4 * Fintype.card α) := by
  have source : (0 : ℝ) < Fintype.card α := by positivity
  have seed : (0 : ℝ) < Fintype.card Seed := by positivity
  have output : (0 : ℝ) < Fintype.card Ω := by positivity
  have test := zero_sum_test_sq_le (hashCenteredCount E) (hashCenteredCount_sum E) T
  rw [Fintype.card_prod, Nat.cast_mul] at test
  have second := mul_le_mul_of_nonneg_left (hashCenteredCount_sq_sum_le universal)
    (show (0 : ℝ) ≤ (Fintype.card Seed : ℝ) * Fintype.card Ω by positivity)
  have bound := test.trans second
  rw [← seededTestProb_sub_uniform_mul E T] at bound
  apply (le_div_iff₀ (show (0 : ℝ) < 4 * Fintype.card α by positivity)).mpr
  apply (mul_le_mul_iff_right₀
    (show (0 : ℝ) < (Fintype.card α : ℝ) * (Fintype.card Seed : ℝ) ^ 2 *
      (Fintype.card Ω : ℝ) ^ 2 by positivity)).mp
  calc
    _ = 4 * ((seededTestProb E T - uniformSeededTestProb T) *
        ((Fintype.card α : ℝ) * Fintype.card Seed * Fintype.card Ω)) ^ 2 := by ring
    _ ≤ _ := bound
    _ = _ := by ring

theorem universalHashFamily_flat_test_sq_le {α Seed Ω : Type*} [Fintype Seed]
    [Fintype Ω] [Nonempty Seed] [Nonempty Ω] {E : α → Seed → Ω}
    (universal : UniversalHashFamily E) (P : Finset α) (nonempty : P.Nonempty)
    (T : Finset (Seed × Ω)) :
    (seededTestProb (fun x : P => E x.val) T - uniformSeededTestProb T) ^ 2 ≤
      (Fintype.card Ω : ℝ) / (4 * P.card) := by
  let : Nonempty P := ⟨⟨nonempty.choose, nonempty.choose_spec⟩⟩
  simpa only [Fintype.card_coe] using
    universalHashFamily_seededTestProb_sub_uniform_sq_le
      (universalHashFamily_comp_injective universal (fun x : P => x.val)
        Subtype.val_injective) T

theorem universalHashFamily_flatStrongSeededExtractor {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω] {E : α → Seed → Ω}
    (universal : UniversalHashFamily E) {K : Nat} {ε : ℝ} (positive : 0 < K)
    (error : 0 ≤ ε) (budget : (Fintype.card Ω : ℝ) ≤ 4 * ε ^ 2 * K) :
    FlatStrongSeededExtractor E K ε := by
  intro P nonempty size T
  have source : (0 : ℝ) < P.card := by exact_mod_cast positive.trans_le size
  have size' : (K : ℝ) ≤ P.card := by exact_mod_cast size
  have bound := universalHashFamily_flat_test_sq_le universal P nonempty T
  have error_sq : (Fintype.card Ω : ℝ) / (4 * P.card) ≤ ε ^ 2 := by
    apply (div_le_iff₀ (show (0 : ℝ) < 4 * P.card by positivity)).mpr
    calc
      (Fintype.card Ω : ℝ) ≤ 4 * ε ^ 2 * K := budget
      _ ≤ 4 * ε ^ 2 * P.card := mul_le_mul_of_nonneg_left size' (by positivity)
      _ = _ := by ring
  have square := bound.trans error_sq
  exact (sq_le_sq₀ (abs_nonneg _) error).mp (by simpa only [sq_abs] using square)

end Algebraic.Cutwidth.Extractor.Internal
