/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts
public import Complexitylib.Circuits.Frontier.LowerBound

/-!
# The unconditional lower bounds

Combining the main theorem (`Frontier.lowerBound_fanInTwo`) with the layout bounds of
`Frontier.Layouts` removes the layout hypothesis.

Let `S_n ⊆ U^n` be `K_n`-rectangle-free over a finite alphabet with at least two symbols, with
`log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit with fan-in at most two deciding `S_n`, over any basis on `U`, has more than

* `(L - ε) n` gates, with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`
  (`lowerBound_gaussian`), and in particular
* `(4 - ε) n` gates (`lowerBound_four`).

For every fixed fan-in `r ≥ 2`, the general-degree spanning-tree bound gives
`(r - 1) s > (2 - ε)n` (`lowerBound_all_fanIn`).

Constant gates are free: the bounds hold for the number of gates of positive arity
(`Cslib.Circuits.Circuit.innerSize`), and so for the size.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U]

/-- **The `(L - ε) n` lower bound**, with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem lowerBound_gaussian (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n < c.innerSize := by
  have h := lowerBound_fanInTwo two_mul_frontierCoefficient_pos
    layoutBound_gaussian S K hfree hK hdense hε
  rwa [Algebraic.Cutwidth.Gaussian.one_add_inv_two_mul_frontierCoefficient] at h

/-- **The `(4 - ε) n` lower bound.** -/
theorem lowerBound_four (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
        (4 - ε) * n < c.innerSize := by
  have h := lowerBound_fanInTwo (by norm_num) layoutBound_one_third S K hfree hK hdense hε
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-- **Every fixed fan-in.** The general-degree layout bound gives
`(r - 1) s > (2 - ε)n` for every fixed `r ≥ 2`. The Gaussian theorem is sharper at `r = 2`. -/
theorem lowerBound_all_fanIn {r : ℕ} (hr : 2 ≤ r)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → Decides c I Acc (S n) →
        (2 - ε) * n < (r - 1) * c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    lowerBound hr (by norm_num : (0 : ℝ) < 1) (layoutBound_one (r + 1))
      S K hfree hK hdense hε

end Complexity.Frontier
