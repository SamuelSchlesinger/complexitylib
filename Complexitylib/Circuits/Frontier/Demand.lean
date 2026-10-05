/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Demand and supply at the frontier

Every lower bound proved by the frontier method ends with the same comparison. On one side is
the *demand* of the problem: every layout of the graph of a circuit for it must, at some time,
have a frontier of about `n` edges, the information that must cross from the inputs read to
the inputs not yet read. On the other side is the *supply* of the layout hypothesis: the graph
of a circuit of size `s` has cycle rank about `s - n`, so it has a layout whose frontiers carry
at most about `A (s - n)` edges. Demand cannot exceed supply, so `n ≤ A (s - n)`, that is,
`s ≥ (1 + 1/A) n`.

`Frontier.eventually_lt_of_demand` makes this precise with every lower-order term in place. The
slack `η` of the layout hypothesis is chosen first, depending only on `A`, `ε`, and a constant
`κ` bounding the size of the graph; the constant `C` of the layout hypothesis and the error
`e(n) = o(n)` of the problem come afterwards.

## Main results

* `Frontier.eventually_lt_of_demand`: demand `n - o(n)` and supply `A (s - n + o(n)) + o(n)`
  force `s > (1 + 1/A - ε) n`.
* `Frontier.isLittleO_log_affine`: `log (α n + β) = o(n)`.
-/

@[expose] public section

namespace Complexity.Frontier

open Filter Asymptotics

/-- `log (α n + β) = o(n)` for constants `α ≥ 0` and `β ≥ 1`. -/
theorem isLittleO_log_affine {α β : ℝ} (hα : 0 ≤ α) (hβ : 1 ≤ β) :
    (fun n : ℕ => Real.log (α * n + β)) =o[atTop] fun n => (n : ℝ) := by
  have hlog : (fun n : ℕ => Real.log n) =o[atTop] fun n => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  refine IsLittleO.of_bound fun δ hδ => ?_
  filter_upwards [hlog.bound (show 0 < δ / 2 by positivity), eventually_ge_atTop 1,
    eventually_ge_atTop ⌈2 * Real.log (α + β) / δ⌉₊] with n hn hn1 hnC
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnC' : 2 * Real.log (α + β) / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnC)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hn ⊢
  rw [abs_of_nonneg (Real.log_nonneg (by nlinarith))]
  -- `log (α n + β) ≤ log ((α + β) n) = log (α + β) + log n`.
  have hle : Real.log (α * n + β) ≤ Real.log (α + β) + Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogn : Real.log n ≤ δ / 2 * n := (le_abs_self _).trans hn
  have hC : Real.log (α + β) ≤ δ / 2 * n := by
    have := (div_le_iff₀ hδ).mp hnC'
    linarith
  linarith

/-- **Demand and supply at the frontier.** Fix `A > 0`, `ε > 0`, and a constant `κ ≥ 0`. For every
small enough slack `η > 0`, every constant `C`, and every error `e(n) = o(n)`, for all large `n`
the following holds. If a graph with `v ≤ κ (n + s + 1)` vertices has a layout of width `w`
that is

* at least the demand: `n ≤ w + e(n) + κ log (v + 1)`, and
* at most the supply: `w ≤ (A + η) (s - n + e(n)) + η v + C`,

then `s > (1 + 1/A - ε) n`.

In applications, `s` is `(r - 1)` times the number of gates of a circuit of fan-in `r`, the
supply is the layout hypothesis applied to a graph of cycle rank at most `s - n + e(n)`, and the
demand is a counting argument for the problem. The slack is chosen before the layout hypothesis
provides `C`. -/
theorem eventually_lt_of_demand {A : ℝ} (hA : 0 < A) {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ η₀ > 0, ∀ η, 0 < η → η ≤ η₀ → ∀ (C : ℝ) (e : ℕ → ℝ), e =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n : ℕ in atTop, ∀ s v w : ℝ, 0 ≤ s → 0 ≤ v → v ≤ κ * (n + s + 1) →
        (n : ℝ) ≤ w + e n + κ * Real.log (v + 1) →
        w ≤ (A + η) * (s - n + e n) + η * v + C →
        (1 + 1 / A - ε) * n < s := by
  -- Spend the slack so that `η B ≤ A ε / 2`, where `B` collects the coefficients of `η n`.
  set B := 1 / A + κ * (2 + 1 / A) with hB_def
  have hB : 0 ≤ B := by positivity
  refine ⟨A * ε / (2 * (B + 1)), by positivity, fun η hη hηle C e he => ?_⟩
  have hηB : η * B ≤ A * ε / 2 := by
    have : A * ε / (2 * (B + 1)) * B ≤ A * ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [mul_pos hA hε]
    exact (mul_le_mul_of_nonneg_right hηle hB).trans this
  -- Each lower-order term is eventually at most `δ n`, with `δ = A ε / 10`.
  set δ := A * ε / 10 with hδ_def
  have hδ : 0 < δ := by positivity
  have hlog := isLittleO_log_affine (α := κ * (2 + 1 / A)) (β := κ + 1) (by positivity)
    (by linarith)
  filter_upwards [he.bound (show 0 < δ / (A + η + 1) by positivity),
    hlog.bound (show 0 < δ / (κ + 1) by positivity), eventually_ge_atTop 1,
    eventually_ge_atTop ⌈(|C| + η * κ) / δ⌉₊] with n hen hlogn hn1 hnC
  intro s v w hs hv hvκ hdemand hsupply
  by_contra! hsn
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hen hlogn
  -- The size of the circuit is at most `(1 + 1/A) n`, so the graph has `O(n)` vertices.
  have hεn : 0 ≤ ε * n := by positivity
  have hsA : s ≤ (1 + 1 / A) * n := by nlinarith
  have hv' : v ≤ κ * (2 + 1 / A) * n + κ := by
    have : κ * (n + s + 1) ≤ κ * ((2 + 1 / A) * n + 1) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hκ
    linarith
  -- The logarithmic term of the demand.
  have hL : κ * Real.log (v + 1) ≤ δ * n := by
    have hlog1 : Real.log (v + 1) ≤ Real.log (κ * (2 + 1 / A) * n + (κ + 1)) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log (v + 1) := Real.log_nonneg (by linarith)
    have h1 := (hlog1.trans (le_abs_self _)).trans hlogn
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ κ + 1)
    rw [← mul_assoc, mul_div_cancel₀ _ (by linarith : κ + 1 ≠ 0)] at h2
    have h3 : κ * Real.log (v + 1) ≤ (κ + 1) * Real.log (v + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hlog0
    linarith
  -- The error term of the problem.
  have hE : (A + η + 1) * |e n| ≤ δ * n := by
    have := mul_le_mul_of_nonneg_left hen (by linarith : 0 ≤ A + η + 1)
    rwa [← mul_assoc, mul_div_cancel₀ _ (by linarith : A + η + 1 ≠ 0)] at this
  -- The constants.
  have hC : |C| + η * κ ≤ δ * n := by
    have h := (Nat.le_ceil ((|C| + η * κ) / δ)).trans (show (⌈(|C| + η * κ) / δ⌉₊ : ℝ) ≤ n by
      exact_mod_cast hnC)
    have := (div_le_iff₀ hδ).mp h
    linarith
  -- Combine demand and supply.
  have hsupply' : (A + η) * (s - n) ≤ n + η / A * n - A * ε * n := by
    have h1 := mul_le_mul_of_nonneg_left (show s - n ≤ (1 / A - ε) * n by linarith)
      (by linarith : 0 ≤ A + η)
    have h2 : (A + η) * ((1 / A - ε) * n) = n + η / A * n - A * ε * n - η * (ε * n) := by
      field_simp; ring
    nlinarith [mul_nonneg hη.le hεn]
  have hηv : η * v ≤ η * κ * (2 + 1 / A) * n + η * κ := by
    have := mul_le_mul_of_nonneg_left hv' hη.le
    linarith [show η * (κ * (2 + 1 / A) * n + κ) = η * κ * (2 + 1 / A) * n + η * κ by ring]
  have he1 : (A + η) * e n + e n ≤ (A + η + 1) * |e n| := by
    have := mul_nonneg (by linarith : 0 ≤ A + η + 1) (sub_nonneg.mpr (le_abs_self (e n)))
    linarith [show (A + η + 1) * (|e n| - e n) = (A + η + 1) * |e n| - ((A + η) * e n + e n)
      by ring]
  have hexpand : (A + η) * (s - n + e n) = (A + η) * (s - n) + (A + η) * e n := by ring
  have hBn : η * B * n = η / A * n + η * κ * (2 + 1 / A) * n := by rw [hB_def]; ring
  have hηBn : η * B * n ≤ A * ε / 2 * n := mul_le_mul_of_nonneg_right hηB (by linarith)
  have hδn : δ * n = A * ε * n / 10 := by rw [hδ_def]; ring
  have hCle := le_abs_self C
  have hpos : 0 < A * ε * n := by positivity
  linarith

end Complexity.Frontier
