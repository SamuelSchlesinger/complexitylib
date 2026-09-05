/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection.Internal

/-!
# Approximate-selection round traces -- proof internals
-/


public section

namespace Complexity

namespace AntiChecker

theorem ApproximatesEveryRound.approximatesRoundsUpTo_internal
    {arity precision threshold : ℕ}
    {target : BitString arity → Bool}
    {estimator : List (BitString arity) → BitString arity → ℕ}
    (happrox : ApproximatesEveryRound precision target threshold estimator)
    (rounds : ℕ) :
    ApproximatesRoundsUpTo rounds precision target threshold estimator := by
  intro inputs _
  exact happrox inputs

theorem isEstimateSelectionTrace_nil_internal {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ) :
    IsEstimateSelectionTrace estimator [] := by
  trivial

theorem isEstimateSelectionTrace_cons_iff_internal {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (input : BitString arity) (inputs : List (BitString arity)) :
    IsEstimateSelectionTrace estimator (input :: inputs) ↔
      IsEstimateSelectionTrace estimator inputs ∧
        IsEstimateMinimizer (estimator inputs) input := by
  rfl

theorem exists_isEstimateSelectionTrace_length_internal {arity : ℕ}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (rounds : ℕ) :
    ∃ inputs : List (BitString arity),
      inputs.length = rounds ∧ IsEstimateSelectionTrace estimator inputs := by
  induction rounds with
  | zero => exact ⟨[], rfl, isEstimateSelectionTrace_nil_internal estimator⟩
  | succ rounds ih =>
      obtain ⟨inputs, hlength, htrace⟩ := ih
      obtain ⟨input, hminimum⟩ :=
        exists_isEstimateMinimizer_internal (estimator inputs)
      refine ⟨input :: inputs, ?_, htrace, hminimum⟩
      simp [hlength]

theorem IsEstimateSelectionTrace.isShrinkTrace_internal
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {estimator : List (BitString arity) → BitString arity → ℕ}
    {inputs : List (BitString arity)}
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesEveryRound precision target threshold estimator)
    (hgood :
      ∀ samplePrefix : List (BitString arity),
        HasShrinkExtension denominator target threshold samplePrefix)
    (htrace : IsEstimateSelectionTrace estimator inputs) :
    IsShrinkTrace (2 * denominator) target threshold inputs := by
  induction inputs with
  | nil => exact isShrinkTrace_nil_internal target
  | cons input inputs ih =>
      refine (isShrinkTrace_cons_iff_internal
        target input inputs).mpr ⟨ih htrace.1, ?_⟩
      exact htrace.2.isShrinkExtension_double_internal
        hprecision hdenominator hbound (happrox inputs) (hgood inputs)

theorem IsEstimateSelectionTrace.isShrinkTrace_of_length_le_internal
    {arity rounds precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    {estimator : List (BitString arity) → BitString arity → ℕ}
    {inputs : List (BitString arity)}
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesRoundsUpTo rounds precision target threshold estimator)
    (hgood :
      ∀ samplePrefix : List (BitString arity),
        HasShrinkExtension denominator target threshold samplePrefix)
    (htrace : IsEstimateSelectionTrace estimator inputs)
    (hlength : inputs.length ≤ rounds) :
    IsShrinkTrace (2 * denominator) target threshold inputs := by
  induction inputs with
  | nil => exact isShrinkTrace_nil_internal target
  | cons input inputs ih =>
      have htailLt : inputs.length < rounds := by
        exact hlength
      refine (isShrinkTrace_cons_iff_internal
        target input inputs).mpr ⟨ih htrace.1 htailLt.le, ?_⟩
      exact htrace.2.isShrinkExtension_double_internal
        hprecision hdenominator hbound (happrox inputs htailLt)
          (hgood inputs)

theorem exists_isShrinkTrace_length_of_approximatesEveryRound_internal
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (rounds : ℕ)
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesEveryRound precision target threshold estimator)
    (hgood :
      ∀ samplePrefix : List (BitString arity),
        HasShrinkExtension denominator target threshold samplePrefix) :
    ∃ inputs : List (BitString arity),
      inputs.length = rounds ∧
        IsShrinkTrace (2 * denominator) target threshold inputs := by
  obtain ⟨inputs, hlength, htrace⟩ :=
    exists_isEstimateSelectionTrace_length_internal estimator rounds
  exact ⟨inputs, hlength,
    htrace.isShrinkTrace_internal
      hprecision hdenominator hbound happrox hgood⟩

theorem exists_isShrinkTrace_length_of_approximatesRoundsUpTo_internal
    {arity precision denominator threshold : ℕ}
    {target : BitString arity → Bool}
    (estimator : List (BitString arity) → BitString arity → ℕ)
    (rounds : ℕ)
    (hprecision : 1 < precision)
    (hdenominator : 0 < denominator)
    (hbound : 4 * denominator ≤ precision + 3)
    (happrox :
      ApproximatesRoundsUpTo rounds precision target threshold estimator)
    (hgood :
      ∀ samplePrefix : List (BitString arity),
        HasShrinkExtension denominator target threshold samplePrefix) :
    ∃ inputs : List (BitString arity),
      inputs.length = rounds ∧
        IsShrinkTrace (2 * denominator) target threshold inputs := by
  obtain ⟨inputs, hlength, htrace⟩ :=
    exists_isEstimateSelectionTrace_length_internal estimator rounds
  exact ⟨inputs, hlength,
    htrace.isShrinkTrace_of_length_le_internal
      hprecision hdenominator hbound happrox hgood hlength.le⟩

end AntiChecker

end Complexity
