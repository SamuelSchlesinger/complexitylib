/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Message
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Averaging
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.OneWay
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.LowerBound

/-!
# The finite joint-message circuit lower bound

Actual gate summaries receive a normalized joint weight. Retaining designated
primary pairs and bounding all message fibres gives an information inequality,
which combines with the existing paired affine restriction theorem.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- Joint counting improves the information bound for the actual sending side. -/
theorem sender_le_size_of_joint_messages {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card) :
    (1 - overlapPenalty) * U.card ≤ c.size + 1 + Real.logb 2 K -
      gateSaving * (Finset.univ.filter fun i : Fin c.size =>
        SelectedPair (c.program.lines i) U).card := by
  have bound := sender_card_le_of_weight_oneWay hK free freeNot U large
    (circuitOneWaySummary c U) (outputKeyWeightBound c.program U (c.outputs 0))
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have cost :
      (((c.size : ℝ) + 1) * Real.log 2 -
        (Finset.univ.filter fun i : Fin c.size => SelectedPair (c.program.lines i) U).card *
          (Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2) +
        U.card * (Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2)) / Real.log 2 =
      c.size + 1 - gateSaving *
        (Finset.univ.filter fun i : Fin c.size => SelectedPair (c.program.lines i) U).card +
        overlapPenalty * U.card := by
    unfold gateSaving overlapPenalty quarterEntropy
    field_simp
  rw [cost] at bound
  linarith

/-- Averaging retains the joint saving from a fraction of all multiple-primary gates. -/
theorem input_le_size_of_pair_entropy {n a K : ℕ} (c : Circuit signature n 1)
    (ha : 2 ≤ a) (han : a ≤ n) (hK : 0 < K)
    (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (large : 2 * K ≤ 2 ^ (n - a)) :
    (1 - overlapPenalty) * a ≤ c.size + 1 + Real.logb 2 K -
      gateSaving * (((a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1))) * multiCount c.program) := by
  obtain ⟨U, hU, retained⟩ := exists_subset_selectedPair_ratio c.program ha han
  have complement : Uᶜ.card = n - a := by
    have total : U.card + Uᶜ.card = n := by simp
    lia
  have bound := sender_le_size_of_joint_messages c hK free freeNot U
    (by simpa only [complement] using large)
  rw [hU] at bound
  have saving := mul_le_mul_of_nonneg_left retained gateSaving_pos.le
  linarith

/-- The logarithmic receiving side gives the exact finite joint information inequality. -/
theorem input_le_size_of_entropy {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 3 ≤ n) :
    (1 - overlapPenalty) * ((n : ℝ) - Nat.clog 2 K - 1) ≤
      c.size + 1 + Real.logb 2 K -
        gateSaving * (pairRetention n (Nat.clog 2 K) * multiCount c.program) := by
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
    (Geometry.disperse_not disperse).rectangleFree large
  have cast_a : (a : ℝ) = n - k - 1 := by
    dsimp only [a]
    rw [Nat.cast_sub (by dsimp only [k]; lia), Nat.cast_add, Nat.cast_one]
    ring
  have ratio : (a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1)) = pairRetention n k := by
    rw [cast_a, pairRetention]
    ring
  rw [ratio, cast_a] at bound
  exact bound

/-- The whole unbounded basis obeys the stronger finite pairing and joint-message bound. -/
theorem size_lowerBound_of_sumsetDisperser {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 3 ≤ n) :
    let k := Nat.clog 2 K
    let d := gateSaving * pairRetention n k
    (1 - overlapPenalty + 2 * d) * n - 2 * d * k -
      (1 - overlapPenalty) * (k + 1) - 1 - Real.logb 2 K ≤ (1 + d) * c.size := by
  dsimp only
  have entropy := input_le_size_of_entropy c hK disperse range
  have affine := two_mul_input_le_size_add_multi c.program (c.outputs 0) disperse
  have affineReal : (2 : ℝ) * n ≤ c.size + multiCount c.program +
      2 * (Nat.clog 2 K : ℝ) := by exact_mod_cast affine
  have nonneg : 0 ≤ gateSaving * pairRetention n (Nat.clog 2 K) :=
    mul_nonneg gateSaving_pos.le (pairRetention_nonneg (by lia))
  have scaled := mul_le_mul_of_nonneg_left affineReal nonneg
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
