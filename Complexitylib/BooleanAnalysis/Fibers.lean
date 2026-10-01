/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Fibers.Defs
public import Complexitylib.BooleanAnalysis.Fibers.Internal

/-!
# Korten's conditional-fiber entropy lemma

Lemma 4 of Oliver Korten, *Top-Down Lower Bounds for All Depths*,
ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.

For a nonempty cube subset `X`, conditioning on the coordinates outside `s`
does not increase its average uniform min-entropy deficit. The fiber is
represented on the selected-coordinate cube, and `card_coordinateFiber`
identifies it with the full-cube set of points agreeing outside `s`.

`coordinateFiber_good_probability` is the `63/64` consequence used in the
mirror-set argument. The uniform-mass API connects a deficit bound to the
pointwise probability bound required by the light-patterns lemma.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

/-- Uniform masses are nonnegative, including for the empty set. -/
theorem uniformMass_nonneg {α : Type*} [DecidableEq α] (X : Finset α) (x : α) :
    0 ≤ uniformMass X x := by
  unfold uniformMass
  split_ifs <;> positivity

/-- Uniform mass on a nonempty finite set sums to one. -/
theorem sum_uniformMass {α : Type*} [Fintype α] [DecidableEq α]
    {X : Finset α} (hX : X.Nonempty) : (∑ x, uniformMass X x) = 1 :=
  sum_uniformMass_internal hX

/-- Summing against uniform mass agrees with the finite-set expectation. -/
theorem sum_uniformMass_mul {α : Type*} [Fintype α] [DecidableEq α]
    (X : Finset α) (f : α → ℝ) : (∑ x, uniformMass X x * f x) = 𝔼 x ∈ X, f x :=
  sum_uniformMass_mul_internal X f

/-- The free-coordinate fiber counts exactly the full assignments in `X`
whose unselected coordinates agree with `x`. -/
theorem card_coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) :
    (coordinateFiber X s x).card =
      (X.filter fun y => (fun i : {i // s i ≠ true} => y i) =
        (fun i : {i // s i ≠ true} => x i)).card :=
  card_coordinateFiber_internal X s x

/-- Conditioning at a point of `X` leaves a nonempty fiber. -/
theorem coordinateFiber_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Finset (ι → Bool)} (s : ι → Bool) {x : ι → Bool} (hx : x ∈ X) :
    (coordinateFiber X s x).Nonempty := coordinateFiber_nonempty_internal s hx

/-- Uniform deficits are nonnegative. For the empty set this follows from
the documented real-logarithm convention. -/
theorem uniformDeficit_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) : 0 ≤ uniformDeficit X := uniformDeficit_nonneg_internal X

/-- A nonempty subset has cardinality `2^(dimension - deficit)`. -/
theorem card_eq_rpow_sub_uniformDeficit {ι : Type*} [Fintype ι]
    {X : Finset (ι → Bool)} (hX : X.Nonempty) :
    (X.card : ℝ) = (2 : ℝ) ^ ((Fintype.card ι : ℝ) - uniformDeficit X) :=
  card_eq_rpow_sub_uniformDeficit_internal hX

/-- A deficit bound is equivalent to the corresponding density lower bound
when the subset is nonempty. -/
theorem uniformDeficit_le_iff {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) {k : ℝ} : uniformDeficit X ≤ k ↔
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) ≤ X.card :=
  uniformDeficit_le_iff_internal hX

/-- A uniform deficit bound implies the light-patterns lemma's pointwise
probability-mass hypothesis. -/
theorem uniformMass_le_rpow {ι : Type*} [Fintype ι]
    {X : Finset (ι → Bool)} (hX : X.Nonempty) {k : ℝ} (hdef : uniformDeficit X ≤ k)
    (x : ι → Bool) : uniformMass X x ≤ (2 : ℝ) ^ (k - Fintype.card ι) :=
  uniformMass_le_rpow_internal hX hdef x

/-- Korten's entropy lemma (Lemma 4): conditioning on the unselected bits
does not increase the average deficit in the selected-coordinate cube. -/
theorem expect_uniformDeficit_coordinateFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool) :
    (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) ≤ uniformDeficit X :=
  expect_uniformDeficit_coordinateFiber_internal X hX s

/-- For every fixed set of free coordinates, a uniform point of `X` yields
a fiber of deficit at most `64*k` with probability at least `63/64`. -/
theorem coordinateFiber_good_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool)
    {k : ℝ} (hk : 0 < k) (hdef : uniformDeficit X ≤ k) :
    63 / 64 ≤ 𝔼 x ∈ X, if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then
      (1 : ℝ) else 0 :=
  coordinateFiber_good_probability_internal X hX s hk hdef

end Complexity.BooleanAnalysis
