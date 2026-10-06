/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Defs
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Internal.Bounds

/-!
# Top-down lower bounds for majority

The two adjacent Hamming layers surrounding the strict-majority threshold
have logarithmic entropy deficit. Each point has at least half its coordinates
leading to the other layer by a single-bit flip. This gives bilateral density
limits at rate `16/n`, and Korten's improved mirror-set adversary applies.
The logarithmic initial deficit preserves the exponent `1/(d-1)`.

This extends the parity argument of Oliver Korten, *Top-Down Lower Bounds
for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/. The majority predicate is the
library's strict majority: ties are false, and both odd and even arities
are covered. The circuit basis is unbounded AND/OR with free input negations.
-/

public section

namespace Complexity.BooleanAnalysis

/-- Many single-bit neighbors give a density limit at a sparse sampling rate.
At least half the coordinates must flip the given point into `X`. -/
theorem isDensityLimit_of_many_neighbors {n : ℕ} (hn : 16 ≤ n)
    (X : Finset (Fin n → Bool)) (x s : Fin n → Bool) (hs : n ≤ 2 * popCount s)
    (hneighbor : ∀ i, s i = true → Function.update x i (!x i) ∈ X) :
    IsDensityLimit X (16 / n) 128 x :=
  isDensityLimit_of_many_neighbors_internal hn X x s hs hneighbor

/-- Both majority boundary layers are nonempty and have logarithmic entropy deficit. -/
theorem majority_layers_deficit {n : ℕ} (hn : 2 ≤ n) :
    ((weightLayer n (n / 2)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2)) ≤ majorityDeficitBound n) ∧
    ((weightLayer n (n / 2 + 1)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2 + 1)) ≤ majorityDeficitBound n) :=
  majority_layers_deficit_internal hn

/-- The majority boundary layers satisfy bilateral density limits at rate `16/n`. -/
theorem majority_layers_limits {n : ℕ} (hn : 16 ≤ n) :
    (∀ x ∈ weightLayer n (n / 2),
      IsDensityLimit (weightLayer n (n / 2 + 1)) (16 / n) (majorityDeficitBound n) x) ∧
    (∀ y ∈ weightLayer n (n / 2 + 1),
      IsDensityLimit (weightLayer n (n / 2)) (16 / n) (majorityDeficitBound n) y) :=
  majority_layers_limits_internal hn

end Complexity.BooleanAnalysis

namespace Complexity.KarchmerWigderson.RoundProtocol

open BooleanAnalysis

/-- Explicit finite obstruction for strict-majority protocols with at most `d+1` messages.
The logarithmic initial deficit appears additively alongside the per-message cost. -/
theorem not_solves_majority_finite {M : Type*} [Fintype M] [DecidableEq M] {n d : ℕ}
    (P : RoundProtocol (Fin n) M (d + 1)) {m : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 64 * (32768 * (194 : ℝ) ^ d * (m + majorityDeficitBound n)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW majority := not_solves_majority_finite_internal P hM hm hsize

end Complexity.KarchmerWigderson.RoundProtocol

universe u

namespace Complexity.KarchmerWigderson

/-- For every fixed number of rounds at least two, strict majority requires
per-message cost greater than `epsilon*n^(1/(rounds-1))` for sufficiently large `n`.
The constant and threshold depend only on the round bound. -/
theorem majority_communication_lower_bound (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {M : Type u} [Fintype M] [DecidableEq M] (m : ℝ), 0 ≤ m →
        (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m →
        m ≤ ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹) →
        ∀ P : RoundProtocol (Fin n) M rounds, ¬ P.SolvesKW majority :=
  majority_communication_lower_bound_internal rounds hrounds

end Complexity.KarchmerWigderson

namespace Complexity.Circuit

/-- Every sufficiently large strict-majority circuit of fixed depth at most `d ≥ 2`
has more than `2^(epsilon*n^(1/(d-1)))` input-wire occurrences.
Both odd and even input arities are covered, and per-input negations are free. -/
theorem majority_wire_lower_bound (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < c.totalFanIn :=
  majority_wire_lower_bound_internal rounds hrounds

/-- Every sufficiently large strict-majority circuit of fixed depth at most `d ≥ 2`
satisfies `2^(epsilon*n^(1/(d-1))) < 2 * (n + g)`, where `g` is the number of
internal gates. -/
theorem majority_gate_size_lower_bound (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < 2 * (n + g) :=
  majority_gate_size_lower_bound_internal rounds hrounds

/-- For any fixed depth bound `rounds` and polynomial parameters `k, C`, all
sufficiently large unbounded AND/OR circuits of depth at most `rounds`
computing strict majority require more than `C * n ^ k + C` internal gates. -/
theorem majority_superpolynomial_gates (rounds k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      C * n ^ k + C < g :=
  majority_superpolynomial_gates_internal rounds k C

end Complexity.Circuit
