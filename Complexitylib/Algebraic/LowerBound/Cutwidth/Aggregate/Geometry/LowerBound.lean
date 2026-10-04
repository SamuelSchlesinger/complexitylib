/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Bias
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine

/-!
# The finite pairing and entropy lower bound

The actual circuit messages have small fibres by dispersion. Averaging designated
primary-input pairs exposes biased coordinates; the resulting entropy saving
combines with the monochromatic affine restriction bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- The actual circuit's biased messages give an exact finite information bound. -/
theorem input_le_size_of_pair_entropy {n a K : ℕ} (c : Circuit signature n 1)
    (ha : 2 ≤ a) (han : a ≤ n) (hK : 0 < K)
    (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (large : 2 * K ≤ 2 ^ (n - a)) :
    (n : ℝ) ≤ (c.size : ℝ) + 1 + (n - a : ℕ) + Real.logb 2 K -
      (((a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1))) * multiCount c.program) *
        Entropy.bitSaving := by
  let J := {gate : Fin c.size // multiPrimary (c.program.lines gate) = true}
  have witnesses (j : J) : ∃ i ∈ primaryInputs (c.program.lines j.val),
      ∃ t ∈ primaryInputs (c.program.lines j.val), i ≠ t :=
    ((multiPrimary_iff_exists_pair _).mp j.property).2
  choose left hl right hr distinct using witnesses
  let embed : J ↪ Fin (c.size + 1) :=
    ⟨fun j => j.val.castSucc, fun _ _ h => Subtype.ext (Fin.castSucc_injective _ h)⟩
  have count : Fintype.card J = multiCount c.program := by
    rw [multiCount_eq_card_filter]
    exact Fintype.card_subtype _
  have bound := Entropy.input_le_bits_of_pair_summaries ha han hK free freeNot large
    embed left right distinct (circuitOneWaySummary c) (fun _ => true) (by
      intro U j hi hj
      have pair : SelectedPair (c.program.lines j.val) U :=
        ⟨((multiPrimary_iff_exists_pair _).mp j.property).1,
          left j, hl j, right j, hr j, distinct j, hi, hj⟩
      have bound := outputKey_quarter_of_selectedPair c.program U (c.outputs 0) j.val pair
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at bound
      convert bound using 1
      congr 2)
  simpa only [Fintype.card_fin, count, Nat.cast_add, Nat.cast_one] using bound

/-- Dispersion is preserved by complementing the output. -/
theorem disperse_not {n K : ℕ} {f : Cslib.BooleanFunction n}
    (disperse : FlatSumsetDisperser f K) : FlatSumsetDisperser (fun x => !(f x)) K := by
  intro P Q hP hQ b
  obtain ⟨x, hx, y, hy, h⟩ := disperse P Q hP hQ (!b)
  exact ⟨x, hx, y, hy, by simp only [h, Bool.not_not]⟩

/-- The finite entropy inequality for the standard logarithmic receiving side. -/
theorem input_le_size_of_entropy {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 3 ≤ n) :
    (n : ℝ) ≤ (c.size : ℝ) + 1 + (Nat.clog 2 K + 1 : ℕ) + Real.logb 2 K -
      (pairRetention n (Nat.clog 2 K) * multiCount c.program) * Entropy.bitSaving := by
  let k := Nat.clog 2 K
  let a := n - (k + 1)
  have ha : 2 ≤ a := by dsimp only [a, k]; lia
  have han : a ≤ n := Nat.sub_le _ _
  have complement : n - a = k + 1 := by dsimp only [a, k]; lia
  have large : 2 * K ≤ 2 ^ (n - a) := by
    rw [complement, Nat.pow_succ]
    have upper := Nat.le_pow_clog (by decide : 1 < 2) K
    dsimp only [k]
    lia
  have bound := input_le_size_of_pair_entropy c ha han hK disperse.rectangleFree
    (disperse_not disperse).rectangleFree large
  have cast_a : (a : ℝ) = n - k - 1 := by
    dsimp only [a]
    rw [Nat.cast_sub (by dsimp only [k]; lia), Nat.cast_add, Nat.cast_one]
    ring
  have ratio : (a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1)) = pairRetention n k := by
    rw [cast_a, pairRetention]
    ring
  rw [complement, ratio] at bound
  exact bound

/-- Affine pairing and biased gate messages give the stronger finite gate bound. -/
theorem size_lowerBound_of_sumsetDisperser {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 3 ≤ n) :
    let k := Nat.clog 2 K
    let d := Entropy.bitSaving * pairRetention n k
    (1 + 2 * d) * n - 2 * d * k - k - 2 - Real.logb 2 K ≤
      (1 + d) * c.size := by
  dsimp only
  have entropy := input_le_size_of_entropy c hK disperse range
  have affine := two_mul_input_le_size_add_multi c.program (c.outputs 0) disperse
  have affineReal : (2 : ℝ) * n ≤ c.size + multiCount c.program +
      2 * (Nat.clog 2 K : ℝ) := by exact_mod_cast affine
  have nonneg : 0 ≤ Entropy.bitSaving * pairRetention n (Nat.clog 2 K) :=
    mul_nonneg Entropy.bitSaving_pos.le (pairRetention_nonneg (by lia))
  have scaled := mul_le_mul_of_nonneg_left affineReal nonneg
  push_cast at entropy
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry
