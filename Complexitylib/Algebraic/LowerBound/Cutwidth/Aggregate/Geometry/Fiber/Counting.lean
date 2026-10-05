/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Internal
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Large fibers from disjoint conjunction summaries

Each disjoint signed conjunction has three majority assignments on its two
variables. After selecting all these majority outcomes, any remaining finite
message partitions a set of exactly `3 ^ |E| * 2 ^ (|V| - 2 * |E|)` inputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Entropy
open scoped BigOperators Classical

/-- The false endpoint is the left input of the selected conjunction. -/
@[simp] theorem endpoint_false {E V : Type*} (edge : E → SignedEdge V) (e : E) :
    endpoint edge (e, false) = (edge e).left := rfl

/-- The true endpoint is the right input of the selected conjunction. -/
@[simp] theorem endpoint_true {E V : Type*} (edge : E → SignedEdge V) (e : E) :
    endpoint edge (e, true) = (edge e).right := rfl

/-- Majority inputs make every selected signed conjunction false. -/
@[simp] theorem mem_majorityInputs {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (x : V → Bool) :
    x ∈ majorityInputs edge ↔ ∀ e, (edge e).eval x = false := by
  simp [majorityInputs]

/-- Disjoint signed pairs occupy exactly two distinct coordinates per edge. -/
theorem two_mul_card_le {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge)) :
    2 * Fintype.card E ≤ Fintype.card V := by
  simpa [Fintype.card_prod, Nat.mul_comm] using Fintype.card_le_of_injective _ disjoint

/-- All majority outcomes of disjoint signed conjunctions occur on this many inputs. -/
theorem card_majorityInputs {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge)) :
    (majorityInputs edge).card =
      3 ^ Fintype.card E * 2 ^ (Fintype.card V - 2 * Fintype.card E) :=
  Internal.card_majorityInputs edge disjoint

/-- A finite key with fibers of size at most `K` covers at most `|Y| * K` inputs. -/
theorem card_le_mul_of_fibers {X Y : Type*} [Fintype Y]
    (inputs : Finset X) (key : X → Y) {K : ℕ}
    (fibers : ∀ y, (inputs.filter fun x => key x = y).card ≤ K) :
    inputs.card ≤ Fintype.card Y * K := by
  classical
  have partition : inputs.card = ∑ y : Y, (inputs.filter fun x => key x = y).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (s := inputs) (t := Finset.univ) (f := key) (fun _ _ => Finset.mem_univ _)
  rw [partition]
  calc
    _ ≤ ∑ _y : Y, K := Finset.sum_le_sum fun y _ => fibers y
    _ = _ := by simp

/-- Restricting to majority outcomes leaves the same finite-key fiber bound. -/
theorem card_majorityInputs_le_mul_of_fibers {E V Y : Type*}
    [Fintype E] [Fintype V] [Fintype Y]
    (edge : E → SignedEdge V) (key : (V → Bool) → Y) {K : ℕ}
    (fibers : ∀ y, ((majorityInputs edge).filter fun x => key x = y).card ≤ K) :
    (majorityInputs edge).card ≤ Fintype.card Y * K :=
  card_le_mul_of_fibers _ key fibers

/-- Exact majority counting and a fiber cap bound the residual message alphabet. -/
theorem majority_product_le_of_fibers {E V Y : Type*}
    [Fintype E] [Fintype V] [Fintype Y]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (key : (V → Bool) → Y) {K : ℕ}
    (fibers : ∀ y, ((majorityInputs edge).filter fun x => key x = y).card ≤ K) :
    3 ^ Fintype.card E * 2 ^ (Fintype.card V - 2 * Fintype.card E) ≤
      Fintype.card Y * K := by
  rw [← card_majorityInputs edge disjoint]
  exact card_majorityInputs_le_mul_of_fibers edge key fibers

/-- The logarithmic count for an arbitrary finite residual message alphabet. -/
theorem log_card_le_of_fibers {E V Y : Type*}
    [Fintype E] [Fintype V] [Fintype Y]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (key : (V → Bool) → Y) {K : ℕ} (hK : 0 < K)
    (fibers : ∀ y, ((majorityInputs edge).filter fun x => key x = y).card ≤ K) :
    (Fintype.card V : ℝ) + (Real.logb 2 3 - 2) * Fintype.card E ≤
      Real.logb 2 (Fintype.card Y) + Real.logb 2 K := by
  let : Nonempty Y := ⟨key fun _ => false⟩
  have hY : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have count : (3 : ℝ) ^ Fintype.card E *
      2 ^ (Fintype.card V - 2 * Fintype.card E) ≤ (Fintype.card Y : ℝ) * K := by
    exact_mod_cast majority_product_le_of_fibers edge disjoint key fibers
  have logs := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by positivity) count
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_mul hY.ne' hKR.ne', Nat.cast_sub (two_mul_card_le edge disjoint),
    Nat.cast_mul, Nat.cast_ofNat] at logs
  nlinarith

/-- A residual Boolean key spends one bit per coordinate after majority selection. -/
theorem log_card_le_of_boolean_fibers {E V R : Type*}
    [Fintype E] [Fintype V] [Fintype R]
    (edge : E → SignedEdge V) (disjoint : Function.Injective (endpoint edge))
    (key : (V → Bool) → (R → Bool)) {K : ℕ} (hK : 0 < K)
    (fibers : ∀ y, ((majorityInputs edge).filter fun x => key x = y).card ≤ K) :
    (Fintype.card V : ℝ) + (Real.logb 2 3 - 2) * Fintype.card E ≤
      Fintype.card R + Real.logb 2 K := by
  classical
  have bound := log_card_le_of_fibers edge disjoint key hK (by
    intro y
    convert fibers y using 1
    congr 1
    ext x
    simp)
  simpa only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using bound

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
