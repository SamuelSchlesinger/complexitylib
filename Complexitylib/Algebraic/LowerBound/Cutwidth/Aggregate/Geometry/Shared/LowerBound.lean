/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.LowerBound
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedMessage
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedAveraging
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.OneWay
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Parameters

/-!
# The finite shared-control circuit lower bound

Actual narrow and wide conjunction messages receive their separate information
charges. A single averaged cut preserves a common triple fraction of both classes.
The old affine count and the new shared-control count eliminate both gate classes.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Shared

open Algebraic.Aggregate.Geometry
open scoped Classical

/-- The actual sending side receives separate narrow and wide message savings. -/
theorem sender_le_size_of_refined_messages {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (U : Finset (Fin n)) (large : 2 * K ≤ 2 ^ Uᶜ.card) :
    (1 - Joint.overlapPenalty) * U.card ≤ c.size + 1 + Real.logb 2 K -
      Joint.gateSaving * (Joint.retainedTwo c.program U).card -
      wideSaving * (Joint.retainedWide c.program U).card := by
  have bound := Joint.sender_card_le_of_weight_oneWay hK free freeNot U large
    (circuitOneWaySummary c U) (Joint.outputKeyRefinedWeightBound c.program U (c.outputs 0))
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have cost :
      (((c.size : ℝ) + 1) * Real.log 2 -
        (Joint.retainedTwo c.program U).card * (Real.binEntropy (1 / 4) - 1 / 2 * Real.log 2) -
        (Joint.retainedWide c.program U).card * (Real.log 2 - Real.binEntropy (1 / 8)) +
        U.card * (Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2)) / Real.log 2 =
      c.size + 1 - Joint.gateSaving * (Joint.retainedTwo c.program U).card -
        wideSaving * (Joint.retainedWide c.program U).card + Joint.overlapPenalty * U.card := by
    unfold Joint.gateSaving Joint.overlapPenalty Joint.quarterEntropy wideSaving wideEntropy
    field_simp
  rw [cost] at bound
  linarith

/-- One averaged cut retains the same triple fraction of both original gate classes. -/
theorem input_le_size_of_triple_entropy {n a K : ℕ} (c : Circuit signature n 1)
    (ha : 3 ≤ a) (han : a ≤ n) (hK : 0 < K)
    (free : RectangleFree (c.outputFunction interpretation 0) K)
    (freeNot : RectangleFree (fun x => !(c.outputFunction interpretation 0 x)) K)
    (large : 2 * K ≤ 2 ^ (n - a)) :
    (1 - Joint.overlapPenalty) * a ≤ c.size + 1 + Real.logb 2 K -
      Joint.tripleRetention n a *
        (Joint.gateSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
          wideSaving * (Joint.retainedWide c.program Finset.univ).card) := by
  obtain ⟨U, hU, retained⟩ := Joint.exists_subset_retained_weight c.program ha han
    Joint.gateSaving wideSaving Joint.gateSaving_pos.le wideSaving_pos.le
  have complement : Uᶜ.card = n - a := by
    have total : U.card + Uᶜ.card = n := by simp
    lia
  have bound := sender_le_size_of_refined_messages c hK free freeNot U
    (by simpa only [complement] using large)
  rw [hU] at bound
  linarith

/-- A logarithmic receiving side gives the finite refined information inequality. -/
theorem input_le_size_of_entropy {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n) :
    (1 - Joint.overlapPenalty) * ((n : ℝ) - Nat.clog 2 K - 1) ≤
      c.size + 1 + Real.logb 2 K - receiverRetention n (Nat.clog 2 K) *
        (Joint.gateSaving * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card +
          wideSaving * (Joint.retainedWide c.program Finset.univ).card) := by
  let k := Nat.clog 2 K
  let a := n - (k + 1)
  have ha : 3 ≤ a := by dsimp only [a, k]; lia
  have han : a ≤ n := Nat.sub_le _ _
  have complement : n - a = k + 1 := by dsimp only [a, k]; lia
  have large : 2 * K ≤ 2 ^ (n - a) := by
    rw [complement, Nat.pow_succ]
    have upper := Nat.le_pow_clog (by decide : 1 < 2) K
    dsimp only [k]
    lia
  have bound := input_le_size_of_triple_entropy c ha han hK disperse.rectangleFree
    (Geometry.disperse_not disperse).rectangleFree large
  have cast_a : (a : ℝ) = n - k - 1 := by
    dsimp only [a]
    rw [Nat.cast_sub (by dsimp only [k]; lia), Nat.cast_add, Nat.cast_one]
    ring
  have ratio : Joint.tripleRetention n a = receiverRetention n k := by
    unfold Joint.tripleRetention receiverRetention
    rw [cast_a]
    ring
  rw [ratio, cast_a] at bound
  exact bound

/-- The unrestricted signed basis satisfies the shared-control finite lower bound. -/
theorem size_lowerBound_of_sumsetDisperser {n K : ℕ} (c : Circuit signature n 1)
    (hK : 0 < K) (disperse : FlatSumsetDisperser (c.outputFunction interpretation 0) K)
    (range : Nat.clog 2 K + 4 ≤ n) :
    let k := Nat.clog 2 K
    let a := receiverRetention n k
    (1 - Joint.overlapPenalty) * ((n : ℝ) - k - 1) +
      a * (Joint.gateSaving / 2 + 3 * wideSaving / 2) * n -
      2 * a * wideSaving * k - 1 - Real.logb 2 K ≤ (1 + a * wideSaving) * c.size := by
  dsimp only
  have entropy := input_le_size_of_entropy c hK disperse range
  have old := two_mul_input_le_size_add_multi c.program (c.outputs 0) disperse
  have new := Algebraic.Aggregate.Geometry.Shared.seven_mul_input_add_two_mul_exactTwo_le
    c.program (c.outputs 0) disperse
  have oldReal : (2 : ℝ) * n ≤ c.size + multiCount c.program + 2 * Nat.clog 2 K := by
    exact_mod_cast old
  have newReal : (7 : ℝ) * n +
      2 * (Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card ≤
      4 * c.size + 4 * multiCount c.program + 8 * Nat.clog 2 K := by exact_mod_cast new
  have countReal :
      ((Algebraic.Aggregate.Geometry.Shared.exactTwo c.program).card : ℝ) +
        (Joint.retainedWide c.program Finset.univ).card = multiCount c.program := by
    exact_mod_cast Joint.exactTwo_add_retainedWide_univ c.program
  have alpha := receiverRetention_nonneg range
  have oldWeight : 0 ≤ receiverRetention n (Nat.clog 2 K) *
      (2 * Joint.gateSaving - wideSaving) :=
    mul_nonneg alpha (by linarith [wideSaving_lt_two_mul_gateSaving])
  have newWeight : 0 ≤ receiverRetention n (Nat.clog 2 K) *
      (wideSaving - Joint.gateSaving) / 2 := by
    exact div_nonneg (mul_nonneg alpha (sub_nonneg.mpr gateSaving_lt_wideSaving.le))
      (by norm_num)
  have scaledOld := mul_le_mul_of_nonneg_left oldReal oldWeight
  have scaledNew := mul_le_mul_of_nonneg_left newReal newWeight
  rw [← countReal] at scaledOld scaledNew
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Shared
