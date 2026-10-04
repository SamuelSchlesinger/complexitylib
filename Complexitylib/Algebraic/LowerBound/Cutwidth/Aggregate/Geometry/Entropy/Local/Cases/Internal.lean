/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Cases.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Empirical
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Numbers
public import Mathlib.Data.Fintype.Vector

/-!
# Finite truth-table proofs for conditional conjunction costs

All cases are checked by kernel reduction and exact logarithmic inequalities.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

namespace LocalCases

open scoped BigOperators

private theorem univ_bool_two : (Finset.univ : Finset (Fin 2 → Bool)) =
    {![false, false], ![false, true], ![true, false], ![true, true]} := by decide

private theorem univ_bool_three : (Finset.univ : Finset (Fin 3 → Bool)) =
    {![false, false, false], ![false, false, true], ![false, true, false],
      ![false, true, true], ![true, false, false], ![true, false, true],
      ![true, true, false], ![true, true, true]} := by decide

private theorem univ_bool_four : (Finset.univ : Finset (Fin 4 → Bool)) =
    {![false, false, false, false], ![false, false, false, true],
      ![false, false, true, false], ![false, false, true, true],
      ![false, true, false, false], ![false, true, false, true],
      ![false, true, true, false], ![false, true, true, true],
      ![true, false, false, false], ![true, false, false, true],
      ![true, false, true, false], ![true, false, true, true],
      ![true, true, false, false], ![true, true, false, true],
      ![true, true, true, false], ![true, true, true, true]} := by decide

/-- The seed table has exactly the quarter binary entropy. -/
theorem seed_cost (a b : Bool) :
    tableCost (pairBit (0 : Fin 2) 1 a b) (fun _ => ()) = Real.binEntropy (1 / 4) := by
  cases a <;> cases b <;>
    norm_num [tableCost, tableWeight, tableCount, univ_bool_two, pairBit,
      Finset.filter_insert, Finset.filter_singleton,
      binEntropy_quarter_eq, Real.log_div, Real.log_inv, show Real.log 4 =
        2 * Real.log 2 by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num,
          Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2] <;> ring


private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (2 : ℝ) 2

private theorem log_six : Real.log 6 = Real.log 2 + Real.log 3 := by
  simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)

private theorem log_eight : Real.log 8 = 3 * Real.log 2 := by
  simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (2 : ℝ) 3

private theorem log_nine : Real.log 9 = 2 * Real.log 3 := by
  simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (3 : ℝ) 2

set_option maxHeartbeats 1600000 in
/-- The shared-endpoint table costs at most three quarters of a bit. -/
theorem extension_cost (a b c d : Bool) :
    tableCost (pairBit (0 : Fin 3) 1 a b) (pairBit 0 2 c d) ≤ (3 / 4) * Real.log 2 := by
  have h₁ := extension_log_bound
  have h₂ := parallel_le_extension
  have h₃ := binEntropy_quarter_eq
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [tableCost, tableWeight, tableCount, univ_bool_three, pairBit,
      Finset.filter_insert, Finset.filter_singleton, Real.log_div, Real.log_inv, log_six] <;>
    linarith


set_option maxHeartbeats 800000 in
/-- The parallel-support table obeys the remaining-edge charge. -/
theorem parallel_cost (a b c d : Bool) :
    tableCost (pairBit (0 : Fin 2) 1 a b) (pairBit 0 1 c d) ≤
      (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h₁ := half_le_chord
  have h₂ := binEntropy_quarter_eq
  have h₃ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [tableCost, tableWeight, tableCount, univ_bool_two, pairBit,
      Finset.filter_insert, Finset.filter_singleton, Real.log_div, Real.log_inv] <;>
    linarith


set_option maxHeartbeats 6400000 in
/-- All signed triangle tables obey the remaining-edge charge. -/
theorem triangle_cost (a b c d e f : Bool) :
    tableCost (pairBit (0 : Fin 3) 1 a b)
      (fun x => (pairBit 0 2 c d x, pairBit 1 2 e f x)) ≤
        (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h₁ := triangle_log_bound
  have h₂ := triangle_first_log_bound
  have h₃ := triangle_second_log_bound
  have h₄ := half_le_chord
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    norm_num [tableCost, tableWeight, tableCount, univ_bool_three, pairBit,
      Finset.filter_insert, Finset.filter_singleton, Real.log_div, Real.log_inv, log_four] <;>
    linarith


set_option maxHeartbeats 12800000 in
/-- All signed four-vertex tables obey the remaining-edge charge. -/
theorem disjoint_cost (a b c d e f : Bool) :
    tableCost (pairBit (0 : Fin 4) 1 a b)
      (fun x => (pairBit 0 2 c d x, pairBit 1 3 e f x)) ≤
        (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h₁ := disjoint_first_log_bound
  have h₂ := disjoint_second_log_bound
  have h₃ := disjoint_third_log_bound
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    norm_num [tableCost, tableWeight, tableCount, univ_bool_four, pairBit,
      Finset.filter_insert, Finset.filter_singleton, Real.log_div, Real.log_inv,
      log_four, log_eight, log_nine] <;> linarith


end LocalCases

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
