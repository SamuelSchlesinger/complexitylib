/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Internal.Neighbors
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Internal.Arithmetic
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Adversary
public import Complexitylib.Circuits.KarchmerWigderson.Circuit
import Mathlib.Tactic.Linarith

/-!
# Top-down communication and wire lower bounds for majority

Initialize the generalized bilateral density adversary with the two
majority boundary layers. Their logarithmic entropy loss is absorbed by
the power-law budget. The circuit-to-protocol translation then gives the
wire bound for unbounded De Morgan circuits with free input negations.

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
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < c.totalFanIn := by
  obtain ⟨ε, hε, n0, hcomm⟩ :=
    KarchmerWigderson.majority_communication_lower_bound_internal.{0} rounds hrounds
  refine ⟨ε, hε, n0, ?_⟩
  intro n hn _ g c hdepth hcompute
  by_contra hsmall
  have hsize : (c.totalFanIn : ℝ) ≤ (2 : ℝ) ^
      (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) := le_of_not_gt hsmall
  obtain ⟨P, hP⟩ := exists_roundProtocol c rounds hdepth 0
  have hcost := hcomm n hn (M := Fin c.totalFanIn)
    (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹))
    (mul_nonneg hε.le (Real.rpow_nonneg (by positivity) _)) (by simpa using hsize) le_rfl P
  apply hcost
  have he : (fun x => c.eval x 0) = majority := funext hcompute
  rwa [he] at hP

theorem majority_gate_size_lower_bound_internal (rounds : ℕ) (hrounds : 2 ≤ rounds) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < 2 * (n + g) := by
  obtain ⟨ε, hε, n0, hcomm⟩ :=
    KarchmerWigderson.majority_communication_lower_bound_internal.{0} rounds hrounds
  refine ⟨ε, hε, n0, ?_⟩
  intro n hn _ g c hdepth hcompute
  by_contra hsmall
  have hsize : ((2 * (n + g) : ℕ) : ℝ) ≤ (2 : ℝ) ^
      (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) := by
    push_cast
    exact le_of_not_gt hsmall
  obtain ⟨P, hP⟩ := exists_roundProtocol_of_gates c rounds hdepth 0
  have hcost := hcomm n hn (M := Fin (2 * (n + g)))
    (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹))
    (mul_nonneg hε.le (Real.rpow_nonneg (by positivity) _)) (by simpa using hsize) le_rfl P
  apply hcost
  have he : (fun x => c.eval x 0) = majority := funext hcompute
  rwa [he] at hP

theorem eventually_poly_le_two_rpow_internal {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ((2 * (n + (C * n ^ k + C)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ r) := by
  have hDpos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
  obtain ⟨N, hN⟩ :=
    BooleanAnalysis.majorityDeficitBound_eventually_le_internal hr (div_pos hε hDpos)
  refine ⟨max N (4 * C + 2), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have hnC : 4 * C + 2 ≤ n := le_of_max_le_right hn
  have hn1 : 1 ≤ n := by omega
  have h1 : 1 ≤ n ^ k := Nat.one_le_pow k n hn1
  have h2 : n ≤ n ^ (k + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hn1 (show 1 ≤ k + 1 by omega)
  have h3 : n ^ k ≤ n ^ (k + 1) := Nat.pow_le_pow_right hn1 (Nat.le_succ k)
  have hnat : 2 * (n + (C * n ^ k + C)) ≤ n ^ (k + 2) := by
    calc 2 * (n + (C * n ^ k + C))
        = 2 * n + 2 * C * n ^ k + 2 * C * 1 := by ring
      _ ≤ 2 * n ^ (k + 1) + 2 * C * n ^ (k + 1) + 2 * C * n ^ (k + 1) := by nlinarith
      _ = (4 * C + 2) * n ^ (k + 1) := by ring
      _ ≤ n * n ^ (k + 1) := Nat.mul_le_mul_right _ hnC
      _ = n ^ (k + 2) := by ring
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hlog : Real.logb 2 (2 * ((n : ℝ) + 1)) ≤ BooleanAnalysis.majorityDeficitBound n := by
    unfold BooleanAnalysis.majorityDeficitBound
    linarith
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ (BooleanAnalysis.majorityDeficitBound n) := by
    calc (n : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
      _ = (2 : ℝ) ^ (Real.logb 2 (2 * ((n : ℝ) + 1))) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      _ ≤ (2 : ℝ) ^ (BooleanAnalysis.majorityDeficitBound n) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  have hdef := (le_div_iff₀ hDpos).mp
    (by simpa only [div_mul_eq_mul_div] using hN n hnN)
  calc ((2 * (n + (C * n ^ k + C)) : ℕ) : ℝ)
      ≤ ((n ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (n : ℝ) ^ (k + 2) := by push_cast; rfl
    _ ≤ ((2 : ℝ) ^ (BooleanAnalysis.majorityDeficitBound n)) ^ (k + 2) :=
      pow_le_pow_left₀ (by positivity) hn_le (k + 2)
    _ = (2 : ℝ) ^ (BooleanAnalysis.majorityDeficitBound n * (k + 2 : ℕ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ r) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hdef

theorem majority_superpolynomial_gates_internal (rounds k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = majority x) →
      C * n ^ k + C < g := by
  let r := max rounds 2
  have hr2 : 2 ≤ r := le_max_right rounds 2
  obtain ⟨ε, hε, n1, hgate⟩ := majority_gate_size_lower_bound_internal r hr2
  have hexp : (0 : ℝ) < ((r - 1 : ℕ) : ℝ)⁻¹ := by
    have : 0 < r - 1 := by omega
    positivity
  obtain ⟨n2, hpoly⟩ := eventually_poly_le_two_rpow_internal hexp hε k C
  refine ⟨max n1 n2, ?_⟩
  intro n hn _ g c hdepth hcompute
  by_contra hle
  have hg : g ≤ C * n ^ k + C := le_of_not_gt hle
  have hlow := hgate n (le_of_max_le_left hn) g c (hdepth.trans (le_max_left rounds 2)) hcompute
  have hup := hpoly n (le_of_max_le_right hn)
  have hcast : (2 : ℝ) * ((n : ℝ) + (g : ℝ)) ≤ ((2 * (n + (C * n ^ k + C)) : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * (n + g) ≤ 2 * (n + (C * n ^ k + C)) by omega)
  linarith

end Complexity.Circuit
