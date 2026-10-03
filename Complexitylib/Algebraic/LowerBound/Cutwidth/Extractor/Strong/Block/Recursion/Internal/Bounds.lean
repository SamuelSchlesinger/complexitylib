/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite block counts, seed cardinalities, and recursive error budgets

Each level doubles the number of blocks and adds one independent seed.
The exact product of seed cardinalities records their cost without charging
once per block. Summing the local errors gives an explicit geometric budget.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

theorem recursiveBlockCount_eq (t n : Nat) : recursiveBlockCount t n = 2 ^ n * t := by
  induction n with
  | zero => simp [recursiveBlockCount]
  | succ n ih => simp [recursiveBlockCount, ih, pow_succ, mul_assoc, mul_left_comm]

theorem recursiveSeeds_card (Earlier : Type u) (Fresh : Nat → Type u)
    [Fintype Earlier] [∀ i, Fintype (Fresh i)] (n : Nat) :
    Fintype.card (RecursiveSeeds Earlier Fresh n) =
      Fintype.card Earlier * ∏ i ∈ Finset.range n, Fintype.card (Fresh i) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, mul_one]
    exact Fintype.card_congr (Equiv.refl Earlier)
  | succ n ih =>
    change Fintype.card (RecursiveSeeds Earlier Fresh n × Fresh n) = _
    rw [Fintype.card_prod, ih, Finset.prod_range_succ]
    exact Nat.mul_assoc _ _ _

theorem recursiveSeeds_card_pow_two (Earlier : Type u) (Fresh : Nat → Type u)
    [Fintype Earlier] [∀ i, Fintype (Fresh i)] (n b₀ : Nat) (b : Nat → Nat)
    (first : Fintype.card Earlier = 2 ^ b₀)
    (fresh : ∀ i < n, Fintype.card (Fresh i) = 2 ^ b i) :
    Fintype.card (RecursiveSeeds Earlier Fresh n) = 2 ^ (b₀ + ∑ i ∈ Finset.range n, b i) := by
  rw [recursiveSeeds_card, first, pow_add]
  congr 1
  calc
    _ = ∏ i ∈ Finset.range n, 2 ^ b i :=
      Finset.prod_congr rfl (fun i hi => fresh i (Finset.mem_range.mp hi))
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem recursiveBlockError_succ (t : Nat) (ε : Nat → ℝ) (e : Nat → Nat) (n : Nat) :
    recursiveBlockError t ε e (n + 1) = recursiveBlockError t ε e n +
      (recursiveBlockCount t n : ℝ) * (ε n + ((2 : ℝ) ^ e n)⁻¹) := by
  exact Finset.sum_range_succ _ n

theorem recursiveBlockError_const (t n e : Nat) (ε : ℝ) :
    recursiveBlockError t (fun _ => ε) (fun _ => e) n =
      (t : ℝ) * ((2 : ℝ) ^ n - 1) * (ε + ((2 : ℝ) ^ e)⁻¹) := by
  induction n with
  | zero => simp [recursiveBlockError]
  | succ n ih =>
    rw [recursiveBlockError_succ, ih, recursiveBlockCount_eq]
    push_cast
    rw [pow_succ]
    ring

theorem recursiveBlockError_dyadic_total (h E : Nat) :
    ((2 : ℝ) ^ E)⁻¹ +
        recursiveBlockError 1 (fun _ => ((2 : ℝ) ^ E)⁻¹) (fun _ => E) h +
        (recursiveBlockCount 1 h : ℝ) * ((2 : ℝ) ^ E)⁻¹ =
      (3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹ := by
  rw [recursiveBlockError_const, recursiveBlockCount_eq]
  push_cast
  ring

theorem recursiveBlockError_dyadic_budget (h e : Nat) :
    (3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ (e + h + 2))⁻¹ ≤ ((2 : ℝ) ^ e)⁻¹ := by
  rw [← div_eq_mul_inv, ← one_div ((2 : ℝ) ^ e)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [one_mul, pow_add, pow_two]
  have ha : 0 ≤ (2 : ℝ) ^ e := by positivity
  have hab : 0 ≤ (2 : ℝ) ^ e * (2 : ℝ) ^ h := by positivity
  nlinarith

end Algebraic.Cutwidth.Extractor.Internal
