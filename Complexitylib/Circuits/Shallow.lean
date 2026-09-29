/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Shallow.Defs
public import Complexitylib.Circuits.Shallow.Asymptotic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Optimal shallow-circuit upper bounds for symmetric functions

Theorem 1 of Victor Lecomte and Prasanna Ramakrishnan,
*Optimal Shallow Circuits for Majority*, arXiv:2609.34029v1 (2026):
for each fixed `d ≥ 2`, every symmetric function on `n` inputs has an
unbounded-fan-in AND/OR circuit of depth at most `d` and size
`2^{O(n^{1/(d-1)})}`. The constant is uniform over all symmetric functions.

The witnesses are native `Cslib.Circuits.Circuit`s. Gates have arbitrary
fan-in, size counts AND/OR gates, and negations occur only at primary inputs.
The construction is nonuniform. The integer-root bound also includes `n = 0`;
the real-exponent bound is stated for `n ≥ 1`.

This formalizes the paper's upper bound. Håstad's matching lower bound is
background to the optimality claim and is not reproved in this development.
Majority accepts ties, following the paper's convention.

## Reference

* Victor Lecomte and Prasanna Ramakrishnan,
  [Optimal Shallow Circuits for Majority](https://arxiv.org/abs/2609.34029),
  Sections 3 and 4, Theorems 1 and 2.
-/

public section

namespace Complexity.Shallow

/-- **Lecomte--Ramakrishnan, Theorem 1**, with an exact integer-root size bound,
including empty input and explicit restriction of negations to primary inputs. -/
theorem symmetric_upper_bound_nat (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℕ, ∀ (n : ℕ) (f : BitString n → Bool), Symmetric f →
      ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => f x) ∧
        c.depth ≤ d ∧ c.size ≤ 2 ^ (C * (Nat.nthRoot (d - 1) n + 1)) ∧
        InputNegationsOnly c := symmetric_circuit_bound_nat d hd

/-- **Lecomte--Ramakrishnan, Theorem 1.** One constant for each depth bounds
the size of circuits for every symmetric Boolean function. -/
theorem symmetric_upper_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ f : BitString n → Bool, Symmetric f →
      ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => f x) ∧
        c.depth ≤ d ∧ (c.size : ℝ) ≤
          (2 : ℝ) ^ (C * (n : ℝ) ^ (1 / ((d - 1 : ℕ) : ℝ))) ∧
        InputNegationsOnly c := symmetric_circuit_bound_real d hd

/-- **Lecomte--Ramakrishnan, Theorem 2.** Depth-three circuits for symmetric
functions have size at most `2^(C * sqrt n)`, uniformly over the function. -/
theorem symmetric_depth_three :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ f : BitString n → Bool, Symmetric f →
      ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => f x) ∧
        c.depth ≤ 3 ∧ (c.size : ℝ) ≤ (2 : ℝ) ^ (C * Real.sqrt n) ∧
        InputNegationsOnly c := by
  simpa [Real.sqrt_eq_rpow] using symmetric_upper_bound 3 (by omega)

/-- Majority has the paper's upper bound at every fixed depth at least two. -/
theorem majority_upper_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∃ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1,
        c.Computes Basis.unboundedAndOr.interpretation (fun x _ => majority x) ∧
        c.depth ≤ d ∧ (c.size : ℝ) ≤
          (2 : ℝ) ^ (C * (n : ℝ) ^ (1 / ((d - 1 : ℕ) : ℝ))) ∧
        InputNegationsOnly c := by
  obtain ⟨C, hC, h⟩ := symmetric_upper_bound d hd
  exact ⟨C, hC, fun n hn => h n hn majority (majority_symmetric n)⟩

end Complexity.Shallow
