/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts
public import Complexitylib.Circuits.Frontier.Ledger.LowerBound

/-!
# The unconditional lower bound with aggregate gates

Combining `Frontier.lowerBound_aggregate` with the layout bound for subcubic graphs: circuits of
fan-in two over any basis, together with `k = o(n)` gates of unbounded fan-in that aggregate in
a fixed finite commutative monoid, such as unbounded AND, OR, and parity, need more than
`(L - ε) n` ordinary inner gates to decide a dense rectangle-free set, with
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`.
-/

@[expose] public section

namespace Complexity.Frontier

open Cslib.Circuits Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U]

/-- **The `(L - ε) n` lower bound with aggregate gates.** -/
theorem lowerBound_aggregate_gaussian (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : ℕ → Prop) (T : Type) [CommMonoid T] [Finite T],
        (∀ g : Fin c.size, ¬ special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g : Fin c.size, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g : Fin c.size // special g} * Real.log (Nat.card T) ≤ β n →
        Decides c I Acc (S n) →
          (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
            (erase special c.program).innerGates.card := by
  filter_upwards [lowerBound_aggregate le_rfl (mul_pos two_pos Gaussian.gaussianCoefficient_pos)
    layoutBound_gaussian S K hfree hK hdense hβ hε] with n hn
  intro σ I Acc c special T _ _ hfan hagg hk hS
  have h := hn σ I Acc c special T hfan hagg hk hS
  rw [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h
  norm_num at h ⊢
  exact h

end Complexity.Frontier
