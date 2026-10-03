/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Finite probability identities for strong seeded extraction

Product tests forget some or all of the seed information. Counting their
source and seed pairs identifies the normalized contract with the existing
division-free output-test inequality. Empty sources contribute zero to that
inequality and need no probability normalization.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem uniformSeededTestProb_empty {Seed Ω : Type*} [Fintype Seed] [Fintype Ω] :
    uniformSeededTestProb (∅ : Finset (Seed × Ω)) = 0 := by
  simp [uniformSeededTestProb]

theorem uniformSeededTestProb_nonneg {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (T : Finset (Seed × Ω)) : 0 ≤ uniformSeededTestProb T := by
  unfold uniformSeededTestProb
  positivity

theorem uniformSeededTestProb_le_one {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (T : Finset (Seed × Ω)) : uniformSeededTestProb T ≤ 1 := by
  by_cases zero : (Fintype.card Seed : ℝ) * Fintype.card Ω = 0
  · simp [uniformSeededTestProb, zero]
  · have positive : (0 : ℝ) < (Fintype.card Seed : ℝ) * Fintype.card Ω :=
      lt_of_le_of_ne (by positivity) (Ne.symm zero)
    apply (div_le_one positive).mpr
    exact_mod_cast (by simpa only [Fintype.card_prod] using Finset.card_le_univ T)

theorem uniformSeededTestProb_product {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (S : Finset Seed) (T : Finset Ω) :
    uniformSeededTestProb (S.product T) =
      ((S.card : ℝ) / Fintype.card Seed) * ((T.card : ℝ) / Fintype.card Ω) := by
  rw [uniformSeededTestProb, Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul,
    div_mul_div_comm]

theorem uniformSeededTestProb_univ_product {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] (T : Finset Ω) :
    uniformSeededTestProb ((Finset.univ : Finset Seed).product T) =
      (T.card : ℝ) / Fintype.card Ω := by
  rw [uniformSeededTestProb_product, Finset.card_univ, div_self, one_mul]
  exact_mod_cast Fintype.card_ne_zero

theorem uniformSeededTestProb_univ {Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω] :
    uniformSeededTestProb (Finset.univ : Finset (Seed × Ω)) = 1 := by
  rw [uniformSeededTestProb, Finset.card_univ, Fintype.card_prod, Nat.cast_mul, div_self]
  exact mul_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Seed ≠ 0))
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0))

theorem seededTestProb_univ_product {α Seed Ω : Type*} [Fintype Seed]
    (E : α → Seed → Ω) (P : Finset α) (T : Finset Ω) :
    seededTestProb (fun x : P => E x.val) ((Finset.univ : Finset Seed).product T) =
      (∑ x ∈ P, (seedHits E T x : ℝ)) / ((P.card : ℝ) * Fintype.card Seed) := by
  unfold seededTestProb
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and,
    Fintype.card_coe]
  congr 1
  calc
    _ = ∑ x : P, (seedHits E T x.val : ℝ) := by
      rw [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [seedHits, Finset.card_filter]
    _ = ∑ x ∈ P, (seedHits E T x : ℝ) := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach P (fun x => (seedHits E T x : ℝ))

theorem strong_mono_threshold {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    {E : α → Seed → Ω} {K L : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (threshold : K ≤ L) :
    FlatStrongSeededExtractor E L ε :=
  fun P nonempty size => extract P nonempty (threshold.trans size)

theorem strong_mono_error {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    {E : α → Seed → Ω} {K : Nat} {ε δ : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (error : ε ≤ δ) :
    FlatStrongSeededExtractor E K δ :=
  fun P nonempty size T => (extract P nonempty size T).trans error

theorem strong_mono {α Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    {E : α → Seed → Ω} {K L : Nat} {ε δ : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (threshold : K ≤ L) (error : ε ≤ δ) :
    FlatStrongSeededExtractor E L δ :=
  strong_mono_error (strong_mono_threshold extract threshold) error

theorem flatSeededExtractor_of_strong {α Seed Ω : Type*}
    [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) : FlatSeededExtractor E K ε := by
  intro P size T
  by_cases nonempty : P.Nonempty
  · have hp : (0 : ℝ) < P.card := by exact_mod_cast nonempty.card_pos
    have hs : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
    have ho : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have normalized := extract P nonempty size ((Finset.univ : Finset Seed).product T)
    rw [seededTestProb_univ_product, uniformSeededTestProb_univ_product] at normalized
    have difference :
        (∑ x ∈ P, (seedHits E T x : ℝ)) / ((P.card : ℝ) * Fintype.card Seed) -
          (T.card : ℝ) / Fintype.card Ω =
        ((∑ x ∈ P, (seedHits E T x : ℝ)) * Fintype.card Ω -
          (P.card : ℝ) * Fintype.card Seed * T.card) /
            ((P.card : ℝ) * Fintype.card Seed * Fintype.card Ω) := by
      field_simp
    rw [difference, abs_div, abs_of_pos (mul_pos (mul_pos hp hs) ho)] at normalized
    have cleared := (div_le_iff₀ (mul_pos (mul_pos hp hs) ho)).mp normalized
    simpa only [mul_assoc] using cleared
  · have empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [empty]

end Algebraic.Cutwidth.Extractor.Internal
