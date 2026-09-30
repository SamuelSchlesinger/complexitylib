/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.SparseFinite
public import Complexitylib.Circuits.SparseSynthesis.Internal.PartialFinite

/-!
# Bounds on the lower-order construction costs

An exponential gap absorbs the minterm tables, pattern banks, hash circuits,
and final collision repairs. Only the OR-per-chunk terms remain at leading
order.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

theorem two_pow_add_one_le (k : ℕ) : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  have : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
  omega

theorem hashBudget_le (p m : ℕ) (width : m ≤ 2 * p) :
    hashBudget (2 * p) m ≤ 32 * (p + 1) ^ 2 := by
  unfold hashBudget
  nlinarith [Nat.mul_le_mul_right (5 * (2 * p + 1) + 1) width]

theorem mintermBudget_le {p k l gap : ℕ} (width : k + l ≤ 2 * p)
    (columns : k ≤ gap) (rows : l ≤ gap) :
    (2 ^ k + 2 ^ l) * (2 * (k + l) + 1) ≤ (8 * p + 2) * 2 ^ gap := by
  have hk := Nat.pow_le_pow_right (by decide : 1 ≤ 2) columns
  have hl := Nat.pow_le_pow_right (by decide : 1 ≤ 2) rows
  calc
    _ ≤ (2 ^ gap + 2 ^ gap) * (4 * p + 1) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by ring

theorem sparseTableBudget_le {p k l K gap : ℕ} (width : k + l ≤ 2 * p)
    (columns : k ≤ gap) (rows : l ≤ gap) (bank : (k + 1) * K ≤ gap) (chunks : K ≤ p) :
    sparseTableBudget k l K (2 ^ p) ≤ 2 ^ p / K + 12 * (p + 1) * 2 ^ gap := by
  have minterms := mintermBudget_le width columns rows
  have patterns : (2 ^ k + 1) ^ K ≤ 2 ^ gap := by
    calc
      _ ≤ (2 ^ (k + 1)) ^ K := Nat.pow_le_pow_left (two_pow_add_one_le k) K
      _ ≤ 2 ^ gap := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) bank
  have hrows := Nat.pow_le_pow_right (by decide : 1 ≤ 2) rows
  have one : 1 ≤ 2 ^ gap := Nat.one_le_pow _ _ (by decide)
  unfold sparseTableBudget
  nlinarith [Nat.mul_le_mul_right (K + 1) patterns,
    Nat.mul_le_mul_right (2 ^ gap) chunks]

theorem partialTableBudget_le {p k l K gap : ℕ} (width : k + l ≤ 2 * p)
    (columns : k ≤ gap) (rows : l ≤ gap) (bank : 4 * k + 6 + K ≤ gap) :
    partialTableBudget k l K (2 ^ p) ≤ 2 ^ p / K + 10 * (p + 1) * 2 ^ gap := by
  have minterms := mintermBudget_le width columns rows
  have patterns : (2 ^ k + 1) ^ 3 * (4 * 2 ^ k + 1) * 2 ^ K ≤ 2 ^ gap := by
    have middle : 4 * 2 ^ k + 1 ≤ 2 ^ (k + 3) := by
      rw [pow_add]
      have : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
      norm_num
      omega
    calc
      _ ≤ (2 ^ (k + 1)) ^ 3 * 2 ^ (k + 3) * 2 ^ K := by gcongr; exact two_pow_add_one_le k
      _ = 2 ^ (4 * k + 6 + K) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ gap := Nat.pow_le_pow_right (by decide) bank
  have hrows := Nat.pow_le_pow_right (by decide : 1 ≤ 2) rows
  have one : 1 ≤ 2 ^ gap := Nat.one_le_pow _ _ (by decide)
  unfold partialTableBudget
  nlinarith

theorem residualBudget_le {p h a steps : ℕ} (hsmall : h ≤ p)
    (enough : p + h ≤ a * steps) : 2 ^ (2 * p) / (2 ^ a) ^ steps ≤ 2 ^ (p - h) := by
  rw [← pow_mul]
  calc
    _ ≤ 2 ^ (2 * p) / 2 ^ (p + h) := Nat.div_le_div_left
      (Nat.pow_le_pow_right (by decide) enough) (by positivity)
    _ = 2 ^ (p - h) := by rw [Nat.pow_div (by omega) (by decide)]; congr 1; omega

/-- A common bound for all auxiliary costs, with an exponential margin of `h` bits. -/
def synthesisError (p h : ℕ) : ℕ := 100 * (p + 1) ^ 3 * 2 ^ (p - h)

theorem sparseFiniteBudget_le {p h k l K a steps : ℕ}
    (hsmall : h ≤ p) (width : k + l ≤ 2 * p)
    (columns : k ≤ p - h) (rows : l ≤ p - h) (bank : (k + 1) * K ≤ p - h)
    (chunks : K ≤ p) (stages : steps ≤ p + 1) (enough : p + h ≤ a * steps) :
    sparseFiniteBudget (2 * p) k l K p a steps ≤ steps * (2 ^ p / K) + synthesisError p h := by
  have table := sparseTableBudget_le width columns rows bank chunks
  have hash := hashBudget_le p (k + l) width
  have residual := residualBudget_le hsmall enough
  have one : 1 ≤ 2 ^ (p - h) := Nat.one_le_pow _ _ (by decide)
  have polynomial : steps * (32 * (p + 1) ^ 2 + 12 * (p + 1) + 1) + (4 * p + 6) ≤
      100 * (p + 1) ^ 3 := by
    have bounded := Nat.mul_le_mul_right (32 * (p + 1) ^ 2 + 12 * (p + 1) + 1) stages
    nlinarith [Nat.zero_le (p ^ 3)]
  have cost : hashBudget (2 * p) (k + l) + sparseTableBudget k l K (2 ^ p) + 1 ≤
      2 ^ p / K + (32 * (p + 1) ^ 2 + 12 * (p + 1) + 1) * 2 ^ (p - h) := by
    have := Nat.mul_le_mul_left (32 * (p + 1) ^ 2) one
    nlinarith
  have patched := Nat.mul_le_mul_right (4 * p + 2) residual
  have all := Nat.mul_le_mul_left steps cost
  have last := Nat.mul_le_mul_right (2 ^ (p - h)) polynomial
  unfold sparseFiniteBudget synthesisError
  nlinarith

theorem partialFiniteBudget_le {p h k l K : ℕ}
    (hsmall : h ≤ p) (width : k + l ≤ 2 * p) (expanded : p + h ≤ k + l)
    (columns : k ≤ p - h) (rows : l ≤ p - h) (bank : 4 * k + 6 + K ≤ p - h) :
    partialFiniteBudget (2 * p) k l K (2 ^ p) ≤ 2 ^ p / K + synthesisError p h := by
  have table := partialTableBudget_le width columns rows bank
  have hash := hashBudget_le p (k + l) width
  have residual : 2 ^ p * 2 ^ p / 2 ^ (k + l) ≤ 2 ^ (p - h) := by
    rw [← pow_add, ← two_mul]
    calc
      _ ≤ 2 ^ (2 * p) / 2 ^ (p + h) := Nat.div_le_div_left
        (Nat.pow_le_pow_right (by decide) expanded) (by positivity)
      _ = _ := by rw [Nat.pow_div (by omega) (by decide)]; congr 1; omega
  have one : 1 ≤ 2 ^ (p - h) := Nat.one_le_pow _ _ (by decide)
  have polynomial : 32 * (p + 1) ^ 2 + 10 * (p + 1) + 4 * p + 7 ≤
      100 * (p + 1) ^ 3 := by nlinarith [Nat.zero_le (p ^ 3)]
  have hash' := Nat.mul_le_mul_left (32 * (p + 1) ^ 2) one
  have patched := Nat.mul_le_mul_right (4 * p + 2) residual
  have last := Nat.mul_le_mul_right (2 ^ (p - h)) polynomial
  unfold partialFiniteBudget synthesisError
  nlinarith

end Complexity.CircuitSparseSynthesis.Internal
