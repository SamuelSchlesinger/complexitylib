/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonLength
import Mathlib.Data.Nat.Log

/-!
# Barrington at the family level: `NC¹ ⊆` polynomial-size width-`5` branching programs

`Circuits/BarringtonLength.lean` proves the textbook per-formula bound
`barrington_representation_depth_four` (a formula of depth `d` compiles to a
width-`5` program of length `≤ 4^d`). This module lifts that to *families*: a
family of formulas of logarithmic depth
(`NC¹`) is computed, formula by formula, by a family of width-`5` permutation
branching programs of **polynomial** length. That is the class-level polynomial-size
direction of Barrington's characterization, in the nonuniform (per-length) setting.

The families here range over the same `ℕ → Bool` assignments the Barrington
development already uses, so `FormulaFamily.logDepth_polyLength_bp` follows by
applying the per-formula bound pointwise, together with the arithmetic fact that
`4^{c·log₂ n + c}` is bounded by a polynomial in `n`.

## Main definitions and results

- `FormulaFamily`, `FormulaFamily.LogDepth` — a family of Boolean formulas and the
  logarithmic-depth (`NC¹`) regime.
- `FormulaFamily.logDepth_polyLength_bp` — the family-level containment.
-/

open Equiv

namespace Complexity

/-- `4^{c·log₂ n + c} ≤ 4^c · (n+1)^{2c}`: the construction length for a
    depth-`(c·log₂ n + c)` formula is polynomial in `n`. -/
theorem pow4_poly (c n : ℕ) :
    4 ^ (c * Nat.log 2 n + c) ≤ 4 ^ c * (n + 1) ^ (2 * c) := by
  have hlog : 4 ^ Nat.log 2 n ≤ (n + 1) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · calc 4 ^ Nat.log 2 n
          ≤ n ^ 2 := pow_four_log_le n (by omega)
        _ ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc 4 ^ (c * Nat.log 2 n + c)
      = (4 ^ Nat.log 2 n) ^ c * 4 ^ c := by
        rw [pow_add, mul_comm c (Nat.log 2 n), pow_mul]
    _ ≤ ((n + 1) ^ 2) ^ c * 4 ^ c :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hlog c)
    _ = 4 ^ c * (n + 1) ^ (2 * c) := by rw [← pow_mul]; ring

/-- A family of Boolean formulas, one per input length. -/
def FormulaFamily := ℕ → BoolFormula

/-- A formula family has **logarithmic depth** if `depth (F n) ≤ c·log₂ n + c` for
    some constant `c` — the `NC¹` depth regime. -/
def FormulaFamily.LogDepth (F : FormulaFamily) : Prop :=
  ∃ c, ∀ n, (F n).depth ≤ c * Nat.log 2 n + c

/-- **Barrington, family level: `NC¹ ⊆` polynomial-size width-`5` branching
    programs.** A logarithmic-depth formula family is computed, formula by formula,
    by a family of width-`5` permutation branching programs whose length is bounded
    by a fixed polynomial `C·(n+1)^p` in the input length — with each program
    evaluating to a nonidentity `5`-cycle exactly when its formula is true. -/
theorem FormulaFamily.logDepth_polyLength_bp (F : FormulaFamily) (hF : F.LogDepth) :
    ∃ (R : ℕ → BP 5) (S : ℕ → Perm (Fin 5)) (C p : ℕ),
      (∀ n, S n ≠ 1) ∧
      (∀ n α, BP.eval α (R n) = if BoolFormula.eval α (F n) then S n else 1) ∧
      (∀ n, (R n).length ≤ C * (n + 1) ^ p) := by
  obtain ⟨c, hc⟩ := hF
  choose R S hS hev hlen using fun n =>
    barrington_representation_depth_four (F n)
  refine ⟨R, S, 4 ^ c, 2 * c, hS, hev, fun n => ?_⟩
  calc (R n).length ≤ 4 ^ (F n).depth := hlen n
    _ ≤ 4 ^ (c * Nat.log 2 n + c) :=
      Nat.pow_le_pow_right (by omega) (hc n)
    _ ≤ 4 ^ c * (n + 1) ^ (2 * c) := pow4_poly c n

/-- **Family-level Barrington, Boolean-decision form.** A logarithmic-depth formula
    family is *decided* by a family of polynomial-length width-`5` branching
    programs together with a family of query points: reading whether program `R n`
    moves point `x n` computes formula `F n`. -/
theorem FormulaFamily.logDepth_polyLength_decides (F : FormulaFamily) (hF : F.LogDepth) :
    ∃ (R : ℕ → BP 5) (x : ℕ → Fin 5) (C p : ℕ),
      (∀ n, (R n).length ≤ C * (n + 1) ^ p) ∧
      (∀ n α, ((BP.eval α (R n)) (x n) ≠ x n) ↔ BoolFormula.eval α (F n) = true) := by
  obtain ⟨R, S, C, p, hS, hev, hlen⟩ := F.logDepth_polyLength_bp hF
  have hmove : ∀ n, ∃ y, S n y ≠ y := fun n => by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hS n (Equiv.ext h)
  choose x hx using hmove
  refine ⟨R, x, C, p, hlen, fun n α => ?_⟩
  rw [hev n α]
  cases hev' : BoolFormula.eval α (F n)
  · simp
  · simp [hx n]

end Complexity
