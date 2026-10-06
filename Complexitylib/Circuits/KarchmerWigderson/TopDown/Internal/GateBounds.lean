/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.Circuit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# From top-down communication bounds to circuit size bounds

Generic glue shared by the parity and majority top-down lower bounds. A
communication lower bound for `rounds`-message KW protocols whose per-message
cost is at most `ε * n^(1/(rounds-1))` yields

* a wire bound, via the `totalFanIn`-alphabet protocol of `exists_roundProtocol`;
* a gate bound `2^(ε * n^(1/(rounds-1))) < 2 * (n + g)`, via the
  `2 * (n + g)`-alphabet protocol of `exists_roundProtocol_of_gates`;
* a superpolynomial gate bound for every fixed depth, because every polynomial
  is eventually below `2^(ε * n^r)` for `r > 0`
  (`eventually_poly_le_two_rpow_internal`).
-/

public section

namespace Complexity.Circuit

open Filter Asymptotics

/-- Every polynomial bound of the shape `2 * (n + (C * n^k + C))` is eventually
at most `2^(ε * n^r)` when `r` and `ε` are positive. -/
theorem eventually_poly_le_two_rpow_internal {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ((2 * (n + (C * n ^ k + C)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ) ^ r) := by
  have hD : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < ε * Real.log 2 / ((k + 2 : ℕ) : ℝ) := by positivity
  have he : ∀ᶠ n : ℕ in atTop,
      ‖Real.log n‖ ≤ ε * Real.log 2 / ((k + 2 : ℕ) : ℝ) * ‖(n : ℝ) ^ r‖ :=
    tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hr).def hc)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
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
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hbound := hN n hnN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)]
    at hbound
  have hlog : ((k + 2 : ℕ) : ℝ) * Real.log n ≤ Real.log 2 * (ε * (n : ℝ) ^ r) := by
    have h := (le_abs_self _).trans hbound
    rw [div_mul_eq_mul_div, le_div_iff₀ hD] at h
    linarith
  calc ((2 * (n + (C * n ^ k + C)) : ℕ) : ℝ)
      ≤ ((n ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = Real.exp (((k + 2 : ℕ) : ℝ) * Real.log n) := by
      rw [Real.exp_nat_mul, Real.exp_log hnpos]
      norm_cast
    _ ≤ Real.exp (Real.log 2 * (ε * (n : ℝ) ^ r)) := Real.exp_le_exp.mpr hlog
    _ = (2 : ℝ) ^ (ε * (n : ℝ) ^ r) := (Real.rpow_def_of_pos (by norm_num) _).symm

/-- A top-down communication lower bound for a function family `f` gives the
corresponding exponential lower bound on input-wire occurrences. -/
theorem wire_lower_bound_of_communication_internal (f : ∀ n : ℕ, BitString n → Bool)
    (rounds : ℕ)
    (hcomm : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {M : Type} [Fintype M] [DecidableEq M] (m : ℝ), 0 ≤ m →
        (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m →
        m ≤ ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹) →
        ∀ P : KarchmerWigderson.RoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (f n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = f n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < c.totalFanIn := by
  obtain ⟨ε, hε, n0, hcomm⟩ := hcomm
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
  have he : (fun x => c.eval x 0) = f n := funext hcompute
  rwa [he] at hP

/-- A top-down communication lower bound for a function family `f` gives an
exponential lower bound on `2 * (n + g)`, where `g` is the number of internal
gates. -/
theorem gate_size_lower_bound_of_communication_internal (f : ∀ n : ℕ, BitString n → Bool)
    (rounds : ℕ)
    (hcomm : ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {M : Type} [Fintype M] [DecidableEq M] (m : ℝ), 0 ≤ m →
        (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m →
        m ≤ ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹) →
        ∀ P : KarchmerWigderson.RoundProtocol (Fin n) M rounds, ¬ P.SolvesKW (f n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = f n x) →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < 2 * (n + g) := by
  obtain ⟨ε, hε, n0, hcomm⟩ := hcomm
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
  have he : (fun x => c.eval x 0) = f n := funext hcompute
  rwa [he] at hP

/-- If a function family satisfies the exponential gate bound at every depth
`rounds ≥ 2`, then for every fixed depth and polynomial `C * n^k + C`, all
sufficiently large bounded-depth circuits computing it have more than
`C * n^k + C` internal gates. -/
theorem superpolynomial_gates_of_gate_size_internal (f : ∀ n : ℕ, BitString n → Bool)
    (hgate : ∀ rounds : ℕ, 2 ≤ rounds →
      ∃ ε : ℝ, 0 < ε ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
        (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
        (∀ x, c.eval x 0 = f n x) →
        (2 : ℝ) ^ (ε * (n : ℝ) ^ (((rounds - 1 : ℕ) : ℝ)⁻¹)) < 2 * (n + g))
    (rounds k C : ℕ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ [NeZero n] (g : ℕ)
      (c : Circuit Basis.unboundedAndOr n 1 g), c.depth ≤ rounds →
      (∀ x, c.eval x 0 = f n x) →
      C * n ^ k + C < g := by
  let r := max rounds 2
  have hr2 : 2 ≤ r := le_max_right rounds 2
  obtain ⟨ε, hε, n1, hgate⟩ := hgate r hr2
  have hexp : (0 : ℝ) < ((r - 1 : ℕ) : ℝ)⁻¹ := by
    have : 0 < r - 1 := by omega
    positivity
  obtain ⟨n2, hpoly⟩ := eventually_poly_le_two_rpow_internal hexp hε k C
  refine ⟨max n1 n2, ?_⟩
  intro n hn _ g c hdepth hcompute
  by_contra hle
  have hg : g ≤ C * n ^ k + C := le_of_not_gt hle
  have hlow := hgate n (le_of_max_le_left hn) g c
    (hdepth.trans (le_max_left rounds 2)) hcompute
  have hup := hpoly n (le_of_max_le_right hn)
  have hcast : (2 : ℝ) * ((n : ℝ) + (g : ℝ)) ≤ ((2 * (n + (C * n ^ k + C)) : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * (n + g) ≤ 2 * (n + (C * n ^ k + C)) by omega)
  linarith

end Complexity.Circuit
