/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParameterBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseTailBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceMoment
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceProbability

/-!
# Unrestricted depth-three lower bound: hard slice parameters

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSliceParameters.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open Filter
open scoped Topology

namespace DepthThreeLowerBound

theorem sparseMomentBound_at_quarter (m b L h : ℕ) :
    sparseMomentBound m b L h ((2 : ℝ) ^ (-(m : ℝ) / 4)) =
      (Fintype.card (SparseTestCode (Fin m) b L) : ℝ) *
        ((2 * h : ℕ) : ℝ) ^ (2 * h) *
          (2 : ℝ) ^ (-((m : ℝ) * ((2 * h : ℕ) : ℝ)) / 4) := by
  have hbase : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℝ) := by simp
  have hratio : ((2 ^ m : ℕ) : ℝ) ^ h /
      (((2 : ℝ) ^ (-(m : ℝ) / 4)) * ((2 ^ m : ℕ) : ℝ)) ^ (2 * h) =
        (2 : ℝ) ^ (-((m : ℝ) * ((2 * h : ℕ) : ℝ)) / 4) := by
    rw [hbase, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have hcard : (Fintype.card (SparseTestCode (Fin m) b L) : ℝ) =
      ((((2 * m + 1) ^ b + 1) ^ L : ℕ) : ℝ) := by
    simp only [SparseTestCode.card_eq, Fintype.card_fin]
  unfold sparseMomentBound
  rw [← hcard, mul_div_assoc, hratio]
  ring

theorem sparseMomentBound_quarter_le (m b M h : ℕ) (hm : 0 < m) (hh : 0 < h)
    (hcond : (M : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (m : ℝ) + 1) / Real.log 2)) /
          ((2 * h : ℕ) : ℝ) + (Real.log ((2 * h : ℕ) : ℝ) / Real.log 2) /
            (m : ℝ) ≤ 1 / 8) :
    sparseMomentBound m b (M * m) h ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
      (2 : ℝ) ^ (-((m : ℝ) * ((2 * h : ℕ) : ℝ)) / 8) := by
  rw [sparseMomentBound_at_quarter]
  simpa only [Fintype.card_fin] using
    sparse_moment_union_le (V := Fin m) b M (2 * h)
      (by simpa only [Fintype.card_fin] using hm)
      (Nat.mul_pos (by decide) hh)
      (by simpa only [Fintype.card_fin] using hcond)

theorem exists_hashDimension_dominates (B : ℝ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
      (33 / 16 : ℝ) * (B * Real.sqrt (d : ℝ)) ≤ (hashDimension d : ℝ) := by
  have hg : ∀ᶠ x : ℝ in atTop, (33 / 16 : ℝ) * B ≤ x ^ (1 / 6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).eventually
      (eventually_ge_atTop ((33 / 16 : ℝ) * B))
  obtain ⟨R, hR⟩ := eventually_atTop.mp hg
  obtain ⟨D, hD⟩ := exists_nat_ge (max 1 R)
  have hDone : (1 : ℝ) ≤ (D : ℝ) := (le_max_left 1 R).trans hD
  refine ⟨D, by exact_mod_cast hDone, ?_⟩
  intro d hd
  have hDd : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one (hDone.trans hDd)
  have hpower := hR (d : ℝ) ((le_max_right 1 R).trans (hD.trans hDd))
  calc
    _ = ((33 / 16 : ℝ) * B) * Real.sqrt (d : ℝ) := by ring
    _ ≤ (d : ℝ) ^ (1 / 6 : ℝ) * Real.sqrt (d : ℝ) :=
      mul_le_mul_of_nonneg_right hpower (Real.sqrt_nonneg _)
    _ = (d : ℝ) ^ (2 / 3 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hdpos]
      norm_num
    _ ≤ (hashDimension d : ℝ) := hashDimension_rpow_lower d

theorem hard_slice_error_bound_eventually (b M : ℕ) (B : ℝ) (hB : 0 < B) :
    ∃ D : ℕ, 4096 ≤ D ∧ ∀ d : ℕ, D ≤ d → ∀ m h : ℕ,
      B * Real.sqrt (d : ℝ) / 2 ≤ (m : ℝ) →
      (m : ℝ) ≤ 2 * (B * Real.sqrt (d : ℝ)) →
      2 * h = independenceOrder d →
      (2 : ℝ) ^ ((m : ℝ) - (hashDimension d : ℝ)) +
        sparseMomentBound m b (M * m) h ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
          2 * (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := by
  obtain ⟨Ds, hDs, hSparse⟩ := uniform_sparse_condition (b : ℝ) (M : ℝ) B
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hB
  obtain ⟨Dr, hDr, hHash⟩ := exists_hashDimension_dominates B
  refine ⟨max 4096 (max Ds Dr), le_max_left _ _, ?_⟩
  intro d hd m h hmlo hmhi heven
  have hd4096 : 4096 ≤ d := (le_max_left _ _).trans hd
  have hds : Ds ≤ d := (le_max_left Ds Dr).trans ((le_max_right _ _).trans hd)
  have hdr : Dr ≤ d := (le_max_right Ds Dr).trans ((le_max_right _ _).trans hd)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hμ : 0 < B * Real.sqrt (d : ℝ) := mul_pos hB (Real.sqrt_pos.2 hdpos)
  have hmpos : 0 < m := by
    have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by linarith : 0 < B * Real.sqrt (d : ℝ) / 2) hmlo
    exact_mod_cast hmp
  have ht2 : 2 ≤ independenceOrder d := (independenceOrder_two_le_iff d).2 (by omega)
  have htone : (1 : ℝ) ≤ (independenceOrder d : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ independenceOrder d)
  have hh : 0 < h := by omega
  have hcond := hSparse (d : ℝ) (by exact_mod_cast hds)
    (m : ℝ) (independenceOrder d : ℝ) hmlo
    (by nlinarith [hmhi]) (half_rpow_le_independenceOrder d hd4096)
    (independenceOrder_rpow_le d) htone
  have hsparse : sparseMomentBound m b (M * m) h ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
      (2 : ℝ) ^ (-((m : ℝ) * (independenceOrder d : ℝ)) / 8) := by
    simpa only [heven] using sparseMomentBound_quarter_le m b M h hmpos hh
      (by simpa only [heven] using hcond)
  have htails := hard_slice_tail_bounds (B * Real.sqrt (d : ℝ)) (m : ℝ)
    (hashDimension d : ℝ) (independenceOrder d : ℝ) hμ.le hmlo hmhi (hHash d hdr) htone
  calc
    _ ≤ (2 : ℝ) ^ ((m : ℝ) - (hashDimension d : ℝ)) +
        (2 : ℝ) ^ (-((m : ℝ) * (independenceOrder d : ℝ)) / 8) :=
      add_le_add_right hsparse _
    _ ≤ (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) +
        (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := add_le_add htails.1 htails.2
    _ = _ := by ring

theorem hash_collision_ratio_eq (m r : ℕ) :
    (2 : ℝ) ^ m / (2 : ℝ) ^ r = (2 : ℝ) ^ ((m : ℝ) - (r : ℝ)) := by
  simpa only [Real.rpow_natCast] using
    (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) (m : ℝ) (r : ℝ)).symm

theorem actual_hard_slice_error_bound_eventually (b : ℕ) (hb : 1 ≤ b)
    (B : ℝ) (hB : 0 < B) :
    ∃ D : ℕ, 4096 ≤ D ∧ ∀ d : ℕ, D ≤ d → ∀ m h : ℕ,
      B * Real.sqrt (d : ℝ) / 2 ≤ (m : ℝ) →
      (m : ℝ) ≤ 2 * (B * Real.sqrt (d : ℝ)) →
      2 * h = independenceOrder d →
      (2 : ℝ) ^ m / (2 : ℝ) ^ hashDimension d +
        sparseMomentBound m b (hardSliceSparseConstant b hb * m) h
          ((2 : ℝ) ^ (-(m : ℝ) / 4)) ≤
            2 * (2 : ℝ) ^ (-(B * Real.sqrt (d : ℝ)) / 16) := by
  obtain ⟨D, hD, hbound⟩ :=
    hard_slice_error_bound_eventually b (hardSliceSparseConstant b hb) B hB
  refine ⟨D, hD, ?_⟩
  intro d hd m h hmlo hmhi heven
  rw [hash_collision_ratio_eq]
  exact hbound d hd m h hmlo hmhi heven

end DepthThreeLowerBound

end

end Complexity
