/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Model

/-!
# Gotsman--Linial: Statement

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/Statement.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

@[simp] theorem flip_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i x i = !(x i) := by
  simp [flip]

theorem flip_apply_ne {n : ℕ} (i : Fin n) (x : Cube n) (j : Fin n) (h : j ≠ i) :
    flip i x j = x j := by
  simp [flip, h]

@[simp] theorem flip_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

theorem flip_ne_self {n : ℕ} (i : Fin n) (x : Cube n) : flip i x ≠ x := by
  intro h
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hxi] at hi

theorem flip_injective_direction {n : ℕ} (x : Cube n) :
    Function.Injective (fun i : Fin n => flip i x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hij, hxi] at hi

theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) :=
  flip_flip i

theorem flip_bijective {n : ℕ} (i : Fin n) : Function.Bijective (flip i) :=
  (flip_involutive i).bijective

@[simp] theorem cubeCoord_flip_same {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord (flip i x) i = -cubeCoord x i := by
  cases hxi : x i <;> simp [cubeCoord, flip, hxi]

theorem cubeCoord_flip_ne {n : ℕ} (x : Cube n) (i j : Fin n) (h : j ≠ i) :
    cubeCoord (flip i x) j = cubeCoord x j := by
  simp [cubeCoord, flip, h]

theorem cubeCoord_cases {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord x i = 1 ∨ cubeCoord x i = -1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem cubeCoord_sq {n : ℕ} (x : Cube n) (i : Fin n) :
    (cubeCoord x i) ^ 2 = 1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem thresholdSign_zero : thresholdSign 0 = 1 := by
  simp [thresholdSign]

theorem thresholdSign_eq_one_iff (t : ℝ) : thresholdSign t = 1 ↔ 0 ≤ t := by
  by_cases h : 0 ≤ t
  · simp [thresholdSign, h]
  · simp [thresholdSign, h, show (-1 : ℝ) ≠ 1 by norm_num]

theorem thresholdSign_eq_neg_one_iff (t : ℝ) : thresholdSign t = -1 ↔ t < 0 := by
  by_cases h : 0 ≤ t
  · simp [thresholdSign, h, not_lt.mpr h, show (1 : ℝ) ≠ -1 by norm_num]
  · simp [thresholdSign, h, lt_of_not_ge h]

theorem thresholdSign_cases (t : ℝ) : thresholdSign t = 1 ∨ thresholdSign t = -1 := by
  unfold thresholdSign
  split <;> simp

@[simp] theorem thresholdSign_sq (t : ℝ) : thresholdSign t ^ 2 = 1 := by
  rcases thresholdSign_cases t with h | h <;> simp [h]

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

/-- The Boolean encoding represents every sign vector exactly once. -/
noncomputable def cubeEquivSignVectors (n : ℕ) :
    Cube n ≃ {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1} := by
  classical
  exact
    { toFun := fun x => ⟨cubeCoord x, cubeCoord_cases x⟩
      invFun := fun x i => decide (x.1 i = 1)
      left_inv := by
        intro x
        funext i
        cases hxi : x i <;> simp [cubeCoord, hxi, show (-1 : ℝ) ≠ 1 by norm_num]
      right_inv := by
        intro x
        apply Subtype.ext
        funext i
        rcases x.2 i with hxi | hxi <;>
          simp [cubeCoord, hxi, show (-1 : ℝ) ≠ 1 by norm_num] }

theorem averageSensitivity_eq_count {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f = (sensitiveEdgeCount f : ℝ) / (2 : ℝ) ^ n := by
  simp [averageSensitivity, sensitiveEdgeCount, Finset.sum_div]

theorem averageSensitivity_eq_uniform {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f =
      ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (Fintype.card (Cube n) : ℝ) := by
  simp [averageSensitivity]

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
