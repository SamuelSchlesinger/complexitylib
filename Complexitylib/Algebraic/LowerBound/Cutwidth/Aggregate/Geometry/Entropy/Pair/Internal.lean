/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Pair.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Coordinates
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Cases.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Numbers
public import Mathlib.Data.Fintype.Vector

/-!
# Exact pair weights and their transport to dominated Boolean features

Compatible primary conjunctions use weights `(5/8, 1/8, 1/8, 1/8)`; incompatible
ones use `(1/2, 1/4, 1/4, 0)`. Both weights increase when a true feature is
turned false. Thus arbitrary additional gate predicates preserve the bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.PairInternal

open scoped BigOperators Classical

/-- Pair weights for compatible literals and for mutually exclusive conjunctions. -/
noncomputable def weight (disjoint : Bool) (y : Bool × Bool) : ℝ :=
  if disjoint then
    if y.1 then (if y.2 then 0 else 1 / 4) else (if y.2 then 1 / 4 else 1 / 2)
  else if y.1 || y.2 then 1 / 8 else 5 / 8

theorem weight_nonneg (disjoint : Bool) (y : Bool × Bool) : 0 ≤ weight disjoint y := by
  rcases y with ⟨a, b⟩
  cases disjoint <;> cases a <;> cases b <;> norm_num [weight]

theorem weight_mass (disjoint : Bool) : ∑ y, weight disjoint y = 1 := by
  cases disjoint <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, weight]

theorem weight_le (disjoint a b c d : Bool)
    (first : a = true → c = true) (second : b = true → d = true) :
    weight disjoint (c, d) ≤ weight disjoint (a, b) := by
  cases disjoint <;> cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [weight] at *

private theorem univ_bool_two : (Finset.univ : Finset (Fin 2 → Bool)) =
    {![false, false], ![false, true], ![true, false], ![true, true]} := by decide

private theorem univ_bool_three : (Finset.univ : Finset (Fin 3 → Bool)) =
    {![false, false, false], ![false, false, true], ![false, true, false],
      ![false, true, true], ![true, false, false], ![true, false, true],
      ![true, true, false], ![true, true, true]} := by decide

private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (2 : ℝ) 2

private theorem log_eight : Real.log 8 = 3 * Real.log 2 := by
  simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (2 : ℝ) 3

theorem disjoint_cost_le : (3 / 2) * Real.log 2 ≤ pairEntropyCost := by
  have bound : Real.log ((5 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 12) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at bound
  norm_num only [Nat.cast_ofNat] at bound
  unfold pairEntropyCost
  linarith

/-- Exact two-coordinate certificate, including equal and incompatible signed supports. -/
noncomputable def parallel (a b c d : Bool) :
    WeightBound (fun x : Fin 2 → Bool => (pairBit 0 1 a b x, pairBit 0 1 c d x))
      pairEntropyCost where
  weight := weight ((a != c) || (b != d))
  nonneg := weight_nonneg _
  mass := weight_mass _
  positive x := by
    cases a <;> cases b <;> cases c <;> cases d <;>
      cases h₀ : x 0 <;> cases h₁ : x 1 <;> norm_num [pairBit, weight, h₀, h₁]
  log_bound := by
    have bound := disjoint_cost_le
    have five : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    unfold pairEntropyCost at *
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [univ_bool_two, pairBit, weight, Real.log_div, Real.log_inv,
        log_four, log_eight] <;> linarith

/-- Exact three-coordinate certificate for a pair sharing its first coordinate. -/
noncomputable def shared (a b c d : Bool) :
    WeightBound (fun x : Fin 3 → Bool => (pairBit 0 1 a b x, pairBit 0 2 c d x))
      pairEntropyCost where
  weight := weight (a != c)
  nonneg := weight_nonneg _
  mass := weight_mass _
  positive x := by
    cases a <;> cases b <;> cases c <;> cases d <;>
      cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;>
        norm_num [pairBit, weight, h₀, h₁, h₂]
  log_bound := by
    have bound := disjoint_cost_le
    unfold pairEntropyCost at *
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [univ_bool_three, pairBit, weight, Real.log_div, Real.log_inv,
        log_four, log_eight] <;> linarith

/-- Lift the local pair certificates and permit arbitrary additional Boolean predicates. -/
noncomputable def dominatedSharedLeft {V : Type*} [Fintype V] [DecidableEq V]
    (e f : SignedEdge V) (left : e.left = f.left)
    (first second : (V → Bool) → Bool)
    (hfirst : ∀ x, first x = true → e.eval x = true)
    (hsecond : ∀ x, second x = true → f.eval x = true) :
    WeightBound (fun x => (first x, second x)) pairEntropyCost := by
  by_cases right : e.right = f.right
  · let bound := (parallel e.leftSign e.rightSign f.leftSign f.rightSign).precompCoordinates
      (pairCoordinates e.left e.right e.distinct)
    apply bound.ofPointwiseWeightLE
    intro x
    apply weight_le
    · simpa [SignedEdge.eval, pairBit, pairCoordinates, Function.comp_def] using hfirst x
    · simpa [SignedEdge.eval, pairBit, pairCoordinates, Function.comp_def, ← left, ← right]
        using hsecond x
  · have distinct : e.left ≠ f.right := by simpa only [left] using f.distinct
    let bound := (shared e.leftSign e.rightSign f.leftSign f.rightSign).precompCoordinates
      (tripleCoordinates e.left e.right f.right e.distinct distinct right)
    apply bound.ofPointwiseWeightLE
    intro x
    apply weight_le
    · simpa [SignedEdge.eval, pairBit, tripleCoordinates, Function.comp_def] using hfirst x
    · simpa [SignedEdge.eval, pairBit, tripleCoordinates, Function.comp_def, ← left]
        using hsecond x

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.PairInternal
