/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Efficient.Defs
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Efficient.Internal

/-!
# Efficient threshold search for logarithmic-gap MINKT

This module proves the algorithmic reverse direction of Hirahara's Fact 3.4.
If the one-bit characteristic string of a logarithmic-gap solver is in `FP`, an
explicit `t+1`-step unary sweep computes the corresponding numerical estimator
in `FP`. On canonical `(x,1^t)` inputs its output length is exactly the semantic
least-accepted-threshold estimator.
-/


public section

namespace Complexity

namespace GapMINKT

namespace Logarithmic

namespace Efficient

/-- The explicit unary threshold sweep preserves polynomial-time
computability. -/
theorem encodedTimeSearchEstimator_mem_FP (decide : List Bool → Bool)
    (hdecide : (fun bits => [decide bits]) ∈ FP) :
    encodedTimeSearchEstimator decide ∈ FP :=
  encodedTimeSearchEstimator_mem_FP_internal decide hdecide

/-- On canonical MINKT inputs, the threshold sweep returns the semantic
least-accepted threshold in exact unary form. -/
@[simp] theorem encodedTimeSearchEstimator_encode
    (decide : List Bool → Bool) (inst : MINKT.Instance) :
    encodedTimeSearchEstimator decide inst.encode =
      List.replicate (timeSearchEstimator decide inst) true :=
  encodedTimeSearchEstimator_encode_internal decide inst

/-- On canonical MINKT inputs, the unary sweep output has exactly the semantic
least-accepted threshold as its length. -/
theorem length_encodedTimeSearchEstimator_encode
    (decide : List Bool → Bool) (inst : MINKT.Instance) :
    (encodedTimeSearchEstimator decide inst.encode).length =
      timeSearchEstimator decide inst :=
  encodedTimeSearchEstimator_length_encode_internal decide inst

/-- The estimator represented by the executable unary sweep is extensionally
the semantic time-capped search estimator. -/
theorem executableEstimator_eq_timeSearchEstimator
    (decide : List Bool → Bool) :
    executableEstimator decide = timeSearchEstimator decide :=
  executableEstimator_eq_timeSearchEstimator_internal decide

/-- The numerical estimator represented by the threshold sweep satisfies the
Fact 3.4 sandwich at every finite source instance. -/
theorem executableEstimator_satisfiesBoundsAt {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (inst : MINKT.Instance)
    (hfinite : machine.timeBoundedKolmogorovComplexity
      inst.output inst.time ≠ ⊤) :
    (executableEstimator decide inst : WithTop ℕ) ≤
        machine.timeBoundedKolmogorovComplexity inst.output inst.time ∧
      machine.timeBoundedKolmogorovComplexity inst.output
          (parameters.transformedTime inst) ≤
        (executableEstimator decide inst +
          parameters.logarithmicSlack inst : ℕ) := by
  rw [executableEstimator_eq_timeSearchEstimator]
  exact timeSearchEstimator_satisfiesBoundsAt
    hwidening hsolve inst hfinite

/-- The executable estimator satisfies Fact 3.4 on any explicit domain where
the source-clock complexity is finite. -/
theorem executableEstimator_satisfiesBoundsOn {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    {eligible : MINKT.Instance → Prop}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (hfinite : ∀ inst, eligible inst →
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤) :
    (executableEstimator decide).SatisfiesBoundsOn
      machine parameters eligible := by
  rw [executableEstimator_eq_timeSearchEstimator]
  exact timeSearchEstimator_satisfiesBoundsOn
    hwidening hsolve hfinite

/-- Algorithmic reverse Fact 3.4 on the paper's exact `|x| <= t` domain.

The first conjunct is the concrete `FP` unary estimator implementation; the
second is its numerical sandwich on every eligible input. -/
theorem fp_and_satisfiesBoundsOn_lengthWithinTime {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    (hdecide : (fun bits => [decide bits]) ∈ FP)
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (hfinite : ∀ inst : MINKT.Instance, IsLengthWithinTime inst →
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤) :
    encodedTimeSearchEstimator decide ∈ FP ∧
      (executableEstimator decide).SatisfiesBoundsOn machine parameters
        IsLengthWithinTime := by
  exact ⟨encodedTimeSearchEstimator_mem_FP decide hdecide,
    executableEstimator_satisfiesBoundsOn hwidening hsolve hfinite⟩

/-- Generic efficient universality discharges source finiteness on a uniform
polynomial printer-clock domain. The returned coefficients depend only on the
universal machine: they are chosen before the clock parameters and the solver,
and for every widening clock and every `FP` solver of logarithmic GapMINKT,
every eligible `(x,1^t)` with the printer clock below `t` receives both the
executable `FP` estimator and the Fact 3.4 sandwich. -/
theorem fp_and_satisfiesBoundsOn_printerClock {tapes : ℕ}
    {machine : TM tapes} (huniversal : machine.IsEfficientlyUniversal) :
    ∃ coefficient exponent, ∀ {parameters : Parameters}
      (hwidening : parameters.IsWidening) {decide : List Bool → Bool},
      (fun bits => [decide bits]) ∈ FP →
      (problem machine parameters hwidening).SolvedBy decide →
      encodedTimeSearchEstimator decide ∈ FP ∧
        (executableEstimator decide).SatisfiesBoundsOn machine parameters
          (fun inst => coefficient *
            (2 * inst.output.length + 3) ^ exponent ≤ inst.time) := by
  obtain ⟨coefficient, exponent, h⟩ :=
    fp_and_satisfiesBoundsOn_printerClock_internal huniversal
  refine ⟨coefficient, exponent, ?_⟩
  intro parameters hwidening decide hdecide hsolve
  exact h hdecide (by simpa using hsolve.1) (by simpa using hsolve.2)

/-- Under global source finiteness, the executable estimator satisfies the
global Fact 3.4 sandwich. -/
theorem executableEstimator_satisfiesBounds {tapes : ℕ}
    {machine : TM tapes} {parameters : Parameters}
    (hwidening : parameters.IsWidening) {decide : List Bool → Bool}
    (hsolve : (problem machine parameters hwidening).SolvedBy decide)
    (hfinite : ∀ inst : MINKT.Instance,
      machine.timeBoundedKolmogorovComplexity inst.output inst.time ≠ ⊤) :
    (executableEstimator decide).SatisfiesBounds machine parameters := by
  rw [executableEstimator_eq_timeSearchEstimator]
  exact timeSearchEstimator_satisfiesBounds hwidening hsolve hfinite

end Efficient

end Logarithmic

end GapMINKT

end Complexity
