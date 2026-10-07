/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AsymptoticBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.ReversePathRecurrence
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Lean.Elab.Tactic.Omega

/-!
# Unrestricted depth-three lower bound: final parameter bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/FinalParameterBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

/-- The live-coordinate probability used by the final restriction parameters. -/
def liveProbability (B : ℝ) (d : ℕ) : ℝ := B / Real.sqrt (d : ℝ)

/-- The clause-width cutoff used in the final hard-slice bound. -/
def degreeCutoff (s : ℝ) (d : ℕ) : ℕ :=
  Nat.ceil (3 * (s + 1) * Real.sqrt (d : ℝ))

/-- The auxiliary scale used to bound the factorial contribution. -/
def factorialBase (B s : ℝ) : ℝ := 4 * B * (3 * (s + 1) + 1)

theorem liveProbability_pos (B : ℝ) (hB : 0 < B) (d : ℕ) (hd : 0 < d) :
    0 < liveProbability B d :=
  div_pos hB (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))

theorem liveProbability_mul_dimension (B : ℝ) (d : ℕ) (hd : 0 < d) :
    liveProbability B d * (d : ℝ) = B * Real.sqrt (d : ℝ) := by
  have hroot : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)).ne'
  unfold liveProbability
  calc
    B / Real.sqrt (d : ℝ) * (d : ℝ) =
        B / Real.sqrt (d : ℝ) * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg d)]
    _ = B * Real.sqrt (d : ℝ) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hroot]

theorem degreeCutoff_lower (s : ℝ) (d : ℕ) :
    3 * (s + 1) * Real.sqrt (d : ℝ) ≤ (degreeCutoff s d : ℝ) :=
  Nat.le_ceil _

theorem degreeCutoff_upper (s : ℝ) (hs : 0 ≤ s) (d : ℕ) (hd : 1 ≤ d) :
    (degreeCutoff s d : ℝ) ≤ (3 * (s + 1) + 1) * Real.sqrt (d : ℝ) := by
  have hroot : (1 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hnonneg : 0 ≤ 3 * (s + 1) * Real.sqrt (d : ℝ) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (degreeCutoff s d : ℝ) < 3 * (s + 1) * Real.sqrt (d : ℝ) + 1 at hceil
  nlinarith

theorem exists_liveProbability_threshold (B : ℝ) (hB : 0 < B) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
      0 < liveProbability B d ∧ liveProbability B d ≤ 1 / 2 := by
  obtain ⟨D, hD⟩ := exists_nat_ge (max (1 : ℝ) ((2 * B) ^ 2))
  have hDone : 1 ≤ D := by
    exact_mod_cast (le_max_left (1 : ℝ) ((2 * B) ^ 2)).trans hD
  refine ⟨D, hDone, ?_⟩
  intro d hd
  have hdone : 1 ≤ d := hDone.trans hd
  have hrootpos : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < d))
  have hsq : (2 * B) ^ 2 ≤ (d : ℝ) :=
    ((le_max_right (1 : ℝ) ((2 * B) ^ 2)).trans hD).trans (Nat.cast_le.mpr hd)
  have hroot : 2 * B ≤ Real.sqrt (d : ℝ) := Real.le_sqrt_of_sq_le hsq
  refine ⟨liveProbability_pos B hB d (by omega), ?_⟩
  change B / Real.sqrt (d : ℝ) ≤ 1 / 2
  apply (div_le_iff₀ hrootpos).mpr
  linarith

theorem scaled_cutoff_le_factorialBase (B s : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (d : ℕ) (hd : 1 ≤ d) (hp : liveProbability B d ≤ 1 / 2) :
    (2 * liveProbability B d / (1 - liveProbability B d)) *
      (degreeCutoff s d : ℝ) ≤ factorialBase B s := by
  have hrootpos : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < d))
  have hp0 : 0 ≤ liveProbability B d := div_nonneg hB (Real.sqrt_nonneg _)
  have hα : 2 * liveProbability B d / (1 - liveProbability B d) ≤
      4 * liveProbability B d := by
    calc
      2 * liveProbability B d / (1 - liveProbability B d) ≤
          2 * liveProbability B d / (1 / 2) :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
      _ = 4 * liveProbability B d := by ring
  calc
    (2 * liveProbability B d / (1 - liveProbability B d)) *
        (degreeCutoff s d : ℝ) ≤
      (4 * liveProbability B d) * (degreeCutoff s d : ℝ) :=
        mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)
    _ ≤ (4 * liveProbability B d) *
        ((3 * (s + 1) + 1) * Real.sqrt (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (degreeCutoff_upper s hs d hd) (by linarith)
    _ = factorialBase B s := by
      unfold liveProbability factorialBase
      field_simp [hrootpos.ne']

theorem reverseTheta_le_factorial_tail (α Q : ℝ) (hα : 0 ≤ α) (b k : ℕ)
    (hαk : α * (k : ℝ) ≤ Q) :
    reverseTheta α b k ≤
      ∑ ℓ ∈ Finset.Ico (b + 1) (k + 1), Q ^ ℓ / (ℓ.factorial : ℝ) := by
  have hset : (Finset.range (k + 1)).filter (fun ℓ => b < ℓ) =
      Finset.Ico (b + 1) (k + 1) := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  unfold reverseTheta
  rw [← Finset.sum_filter, hset]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  calc
    (k.choose ℓ : ℝ) * α ^ ℓ ≤
        ((k : ℝ) ^ ℓ / (ℓ.factorial : ℝ)) * α ^ ℓ :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div ℓ k) (pow_nonneg hα _)
    _ = (α * (k : ℝ)) ^ ℓ / (ℓ.factorial : ℝ) := by
      rw [mul_pow]
      ring
    _ ≤ Q ^ ℓ / (ℓ.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hα (Nat.cast_nonneg k)) hαk ℓ)
        (Nat.cast_nonneg _)

theorem exists_final_parameter_width (B s : ℝ) (hB : 0 < B) (hs : 0 ≤ s) :
    ∃ b : ℕ, 1 ≤ b ∧ ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℕ, D ≤ d →
      0 < liveProbability B d ∧ liveProbability B d ≤ 1 / 2 ∧
      reverseTheta (2 * liveProbability B d / (1 - liveProbability B d))
        b (degreeCutoff s d) ≤ 1 / 2 := by
  have hQ : 0 ≤ factorialBase B s :=
    mul_nonneg (mul_nonneg (by norm_num) hB.le) (by linarith)
  obtain ⟨b, hb, htail⟩ := exists_factorial_tail_width (factorialBase B s) hQ
  obtain ⟨D, hD, hprob⟩ := exists_liveProbability_threshold B hB
  refine ⟨b, hb, D, hD, ?_⟩
  intro d hd
  obtain ⟨hp0, hphalf⟩ := hprob d hd
  refine ⟨hp0, hphalf, ?_⟩
  have hα : 0 ≤ 2 * liveProbability B d / (1 - liveProbability B d) :=
    div_nonneg (by linarith) (by linarith)
  exact (reverseTheta_le_factorial_tail _ _ hα b (degreeCutoff s d)
    (scaled_cutoff_le_factorialBase B s hB.le hs d (hD.trans hd) hphalf)).trans
      (htail (degreeCutoff s d))

end DepthThreeLowerBound

end

end Complexity
