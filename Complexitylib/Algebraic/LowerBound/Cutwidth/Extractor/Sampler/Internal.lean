/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting bad input fibres of a seeded extractor

If at least `K` inputs each hit a small test on more than a `2ε` fraction of
seeds, the uniform distribution on those inputs contradicts extraction.
Bounding each source point mass then gives sampling for arbitrary weak sources.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem card_badInputs_lt {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    (badInputs E T ε).card < K := by
  by_contra hn
  have hK : K ≤ (badInputs E T ε).card := by lia
  have hne : (badInputs E T ε).Nonempty :=
    Finset.card_pos.mp (positive.trans_le hK)
  have hseed : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hout : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hlower : (badInputs E T ε).card * (2 * ε * Fintype.card Seed) <
      ∑ x ∈ badInputs E T ε, (seedHits E T x : ℝ) := by
    simpa using Finset.sum_lt_sum_of_nonempty hne (fun x hx =>
      (Finset.mem_filter.mp hx).2)
  have hupper := (abs_le.mp (extract (badInputs E T ε) hK T)).2
  have hscale := mul_le_mul_of_nonneg_left small
    (mul_nonneg (Nat.cast_nonneg (badInputs E T ε).card) hseed.le)
  have hstrict := mul_lt_mul_of_pos_right hlower hout
  nlinarith

theorem sampler_of_flatSeededExtractor {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {L ε δ : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (source : 0 < L) (budget : (K : ℝ) ≤ δ * L) : Sampler E L ε δ := by
  intro T small p _ _ cap
  have hcard : ((badInputs E T ε).card : ℝ) < K := by
    exact_mod_cast card_badInputs_lt extract positive T small
  apply le_of_lt
  apply (mul_lt_mul_iff_right₀ source).mp
  calc
    L * (∑ x ∈ badInputs E T ε, p x) =
        ∑ x ∈ badInputs E T ε, L * p x := Finset.mul_sum ..
    _ ≤ ∑ _x ∈ badInputs E T ε, (1 : ℝ) :=
      Finset.sum_le_sum fun x _ => cap x
    _ = (badInputs E T ε).card := by simp
    _ < K := hcard
    _ ≤ L * δ := by simpa only [mul_comm] using budget

theorem card_badInputs_inter_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε δ : ℝ}
    (extract : FlatSeededExtractor E K ε) (positive : 0 < K)
    (P : Finset α) (budget : (K : ℝ) ≤ δ * P.card)
    (T : Finset Ω) (small : (T.card : ℝ) ≤ ε * Fintype.card Ω) :
    ((P ∩ badInputs E T ε).card : ℝ) ≤ δ * P.card := by
  have hcard : (P ∩ badInputs E T ε).card < K :=
    (Finset.card_le_card Finset.inter_subset_right).trans_lt
      (card_badInputs_lt extract positive T small)
  exact (by exact_mod_cast hcard : ((P ∩ badInputs E T ε).card : ℝ) < K).le.trans budget

theorem sampler_seedProjection {α Seed : Type*}
    [Fintype α] [Fintype Seed] [Nonempty Seed] {L ε : ℝ} (hε : 0 ≤ ε) :
    Sampler (fun (_ : α) (y : Seed) => y) L ε 0 := by
  intro T small p _ _ _
  have hseed : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hbad : badInputs (fun (_ : α) (y : Seed) => y) T ε = ∅ := by
    ext x
    simp only [badInputs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    have hits : seedHits (fun (_ : α) (y : Seed) => y) T x = T.card := by
      simp [seedHits]
    rw [hits]
    apply not_lt.mpr
    calc
      (T.card : ℝ) ≤ ε * Fintype.card Seed := small
      _ ≤ ε * Fintype.card Seed + ε * Fintype.card Seed :=
        le_add_of_nonneg_right (mul_nonneg hε hseed.le)
      _ = 2 * ε * Fintype.card Seed := by ring
  simp [hbad]

end Algebraic.Cutwidth.Extractor.Internal
