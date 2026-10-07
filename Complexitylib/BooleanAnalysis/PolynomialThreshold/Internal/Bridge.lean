/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Defs
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Main
public import Complexitylib.BooleanAnalysis.FourierExpansion

/-!
# Transport of the average-sensitivity bound

The source proof uses Boolean coordinates with `true` representing `+1`.
The equivalence below respects coordinate flips and uniform expectation, so
its average sensitivity agrees with the canonical Fourier total influence.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.PolynomialThreshold.Internal

open scoped BigOperators

/-- Translate the source's sign encoding to the library's additive binary cube. -/
def cubeEquiv (n : ℕ) : Cube n ≃ BooleanAnalysis.Cube n where
  toFun x i := if x i then 0 else 1
  invFun x i := decide (x i = 0)
  left_inv x := by
    funext i
    change decide ((if x i then (0 : ZMod 2) else 1) = 0) = x i
    cases x i <;> decide
  right_inv x := by
    funext i
    change (if decide (x i = 0) then (0 : ZMod 2) else 1) = x i
    generalize x i = z
    fin_cases z
    · change (if decide ((0 : ZMod 2) = 0) then (0 : ZMod 2) else 1) = 0
      decide
    · change (if decide ((1 : ZMod 2) = 0) then (0 : ZMod 2) else 1) = 1
      decide

theorem cubeEquiv_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    cubeEquiv n (flip i x) = flipCoord i (cubeEquiv n x) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [flipCoord_apply_same]
    cases hx : x i <;> simp [cubeEquiv, flip, hx]
    rfl
  · rw [flipCoord_apply_ne _ _ _ h]
    simp [cubeEquiv, flip, h]

theorem cubeEquiv_chi {n : ℕ} (x : Cube n) :
    (fun i => chi (cubeEquiv n x i)) = cubeCoord x := by
  funext i
  cases hx : x i <;> simp [cubeEquiv, chi, cubeCoord, hx]

theorem polynomialThreshold_cubeEquiv {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Cube n) :
    BooleanAnalysis.polynomialThreshold p (cubeEquiv n x) = polynomialThreshold p x := by
  change (if 0 ≤ MvPolynomial.eval _ p then (1 : ℝ) else -1) = _
  rw [cubeEquiv_chi]
  rfl

theorem totalInfluence_eq_averageSensitivity {n : ℕ} (f : BooleanFunction n)
    (hf : IsBooleanValued f) :
    totalInfluence f = averageSensitivity (fun x => f (cubeEquiv n x)) := by
  classical
  rw [totalInfluence_eq_sum_influence, averageSensitivity]
  apply Finset.sum_congr rfl
  intro i _
  rw [influence_boolean_eq_expect_sensitive i f hf]
  change (𝔼 x, if f x ≠ f (flipCoord i x) then (1 : ℝ) else 0) = _
  calc
    _ = 𝔼 x : Cube n,
        if f (cubeEquiv n x) ≠ f (cubeEquiv n (flip i x)) then (1 : ℝ) else 0 :=
      (Fintype.expect_equiv (cubeEquiv n) _ _ (fun x => by rw [cubeEquiv_flip])).symm
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [card_cube, Nat.cast_pow, Nat.cast_ofNat]
      congr 1
      simp only [sensitiveVertices, ← Finset.sum_boole]

theorem polynomialThreshold_isBooleanValued {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsBooleanValued (BooleanAnalysis.polynomialThreshold p) := by
  intro x
  change (if _ then (1 : ℝ) else -1) = 1 ∨ (if _ then (1 : ℝ) else -1) = -1
  split <;> simp

theorem totalInfluence_polynomialThreshold_le_of_multilinear {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    totalInfluence (BooleanAnalysis.polynomialThreshold p) ≤ 8 * d * Real.sqrt n := by
  rw [totalInfluence_eq_averageSensitivity _ (polynomialThreshold_isBooleanValued p)]
  simpa only [polynomialThreshold_cubeEquiv] using
    polynomialThreshold_averageSensitivity_le p hp hd

end Complexity.BooleanAnalysis.PolynomialThreshold.Internal
