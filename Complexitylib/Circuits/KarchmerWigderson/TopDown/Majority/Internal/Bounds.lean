/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Internal.Neighbors
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Internal.Arithmetic
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Adversary
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.GateBounds
import Mathlib.Tactic.Linarith

/-!
# Top-down communication, wire, and gate lower bounds for majority

Initialize the generalized bilateral density adversary with the two
majority boundary layers. Their logarithmic entropy loss is absorbed by
the power-law budget. The circuit-to-protocol translations then give the
wire bound, the exponential gate bound, and the superpolynomial gate bound
at every fixed depth for unbounded De Morgan circuits with free input
negations (via the shared glue in `TopDown.Internal.GateBounds`).

This extends the argument of Oliver Korten, *Top-Down Lower Bounds for
All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/. His Theorem 3 states the
parity case; the majority initialization is proved here.
-/

public section

namespace Complexity.KarchmerWigderson.RoundProtocol

open BooleanAnalysis Finset
open scoped Classical

variable {M : Type*} [Fintype M] [DecidableEq M]

theorem not_solves_majority_finite_internal {n d : ℕ} (P : RoundProtocol (Fin n) M (d + 1))
    {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m)
    (hsize : 64 * (32768 * (194 : ℝ) ^ d * (m + majorityDeficitBound n)) ^ d ≤ (n : ℝ)) :
    ¬ P.SolvesKW majority := by
  have hk := le_majorityDeficitBound_internal n
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + majorityDeficitBound n) := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (194 : ℝ) ^ d by positivity) hm]
  have hn64 : (64 : ℝ) ≤ n := by nlinarith [one_le_pow₀ (n := d) hC]
  have hn16 : 16 ≤ n := by exact_mod_cast (show (16 : ℝ) ≤ n by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  have ⟨hX, hY⟩ := majority_layers_deficit_internal (show 2 ≤ n by omega)
  have ⟨hleft, hright⟩ := majority_layers_limits_internal hn16
  have hbudget : (32768 * (194 : ℝ) ^ d * (m + majorityDeficitBound n)) ^ d * (16 / n) ≤ 1 / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hnpos).mpr
    nlinarith
  intro hsol
  apply P.not_solves_bilateral_density_with_deficit_internal hM hm (by linarith)
    (show (0 : ℝ) < 16 / n by positivity) hX.1 hY.1 hX.2 hY.2 hleft hright hbudget
  intro x hx y hy
  apply hsol x y
  · apply (majority_eq_false_iff x).mpr
    exact ((mem_filter.mp hx).2).le
  · apply (majority_eq_true_iff y).mpr
    have := (mem_filter.mp hy).2
    change popCount y = n / 2 + 1 at this
    omega

end Complexity.KarchmerWigderson.RoundProtocol

universe u

namespace Complexity.KarchmerWigderson

open BooleanAnalysis

theorem majority_communication_lower_bound_internal (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {M : Type u} [Fintype M] [DecidableEq M] (m : ℝ), 0 ≤ m →
        (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m →
        m ≤ ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹) →
        ∀ P : RoundProtocol (Fin n) M rounds, ¬ P.SolvesKW majority := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show rounds ≠ 0 by omega)
  have hd : 0 < d := by omega
  let ε : ℝ := 1 / (128 * (32768 * (194 : ℝ) ^ d))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨N, hN⟩ := majorityDeficitBound_eventually_le_internal
    (show (0 : ℝ) < (d : ℝ)⁻¹ by positivity) hε
  refine ⟨ε, hε, N, ?_⟩
  intro n hn M _ _ m hm hM hcost P
  apply P.not_solves_majority_finite_internal hM hm
  have hk := le_majorityDeficitBound_internal n
  apply finite_budget_with_deficit_of_cost_internal hd hm (by linarith)
  · simpa only [ε, Nat.succ_sub_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hcost
  · simpa only [ε, one_div, div_eq_mul_inv, mul_comm, one_mul] using hN n hn

end Complexity.KarchmerWigderson

namespace Complexity.Circuit

theorem majority_wire_lower_bound_internal (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < c.totalFanIn :=
  wire_lower_bound_of_communication_internal (fun _ => majority) rounds
    (KarchmerWigderson.majority_communication_lower_bound_internal.{0} rounds hrounds)

theorem majority_gate_size_lower_bound_internal (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < 2 * (n + g) :=
  gate_size_lower_bound_of_communication_internal (fun _ => majority) rounds
    (KarchmerWigderson.majority_communication_lower_bound_internal.{0} rounds hrounds)

theorem majority_superpolynomial_gates_internal (rounds k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      C * n ^ k + C < g :=
  superpolynomial_gates_of_gate_size_internal (fun _ => majority)
    majority_gate_size_lower_bound_internal rounds k C

end Complexity.Circuit
