/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Hierarchy.Family
public import Complexitylib.Algebraic.CircuitFamily.Growth
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial circuit size hierarchy

For arbitrary real exponents `1 ≤ a < b`, nonuniform `SIZE(n^a)` is a strict
subset of `SIZE(n^b)`. These classes allow multiplicative constants and
finitely many exceptional widths. Floors convert real powers to natural
gate budgets; `mem_polynomialSize_iff` gives the usual real-valued formulation.

The proof first establishes the exact finite interpolation theorem, then
absorbs its `2 * n` overhead in the gap between distinct real powers. It
asserts existence of nonuniform function families, without a uniform circuit
construction or an explicit hard function.
-/

@[expose] public section

namespace Algebraic.DeMorgan

open Filter

/-- Natural gate budget obtained by flooring a real power of the input width. -/
noncomputable def polynomialBudget (degree : Real) (n : Nat) : Nat :=
  ⌊(n : Real) ^ degree⌋₊

/-- Natural exponents recover ordinary natural-power budgets exactly. -/
@[simp] theorem polynomialBudget_natCast (degree : Nat) :
    polynomialBudget (degree : Real) = fun n => n ^ degree := by
  funext n
  simp only [polynomialBudget, Real.rpow_natCast, ← Nat.cast_pow, Nat.floor_natCast]

/-- The nonuniform class `SIZE(n^degree)`, including constant factors. -/
def polynomialSize (degree : Real) : Set FunctionFamily :=
  sizeClass (polynomialBudget degree)

/-- The floored definition agrees with the usual real-valued `O(n^degree)`
bound, for every nonnegative real degree. -/
theorem mem_polynomialSize_iff (family : FunctionFamily) {degree : Real}
    (nonnegative : 0 ≤ degree) :
    family ∈ polynomialSize degree ↔
      ∃ constant : Real, ∀ᶠ n in atTop,
        (complexity (family n) : Real) ≤ constant * (n : Real) ^ degree := by
  constructor
  · rintro ⟨constant, bounded⟩
    refine ⟨constant, ?_⟩
    filter_upwards [bounded] with n hn
    have castBound : (complexity (family n) : Real) ≤
        constant * (polynomialBudget degree n : Real) := by exact_mod_cast hn
    exact castBound.trans (mul_le_mul_of_nonneg_left
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) degree)) (Nat.cast_nonneg constant))
  · rintro ⟨constant, bounded⟩
    refine ⟨2 * ⌈constant⌉₊, ?_⟩
    filter_upwards [bounded, eventually_ge_atTop 1] with n hn positive
    have base : (1 : Real) ≤ n := by exact_mod_cast positive
    have powerOne : (1 : Real) ≤ (n : Real) ^ degree := Real.one_le_rpow base nonnegative
    have floorOne : 1 ≤ polynomialBudget degree n := (Nat.one_le_floor_iff _).mpr powerOne
    have powerBound : (n : Real) ^ degree ≤ 2 * (polynomialBudget degree n : Real) := by
      have floorLower := Nat.lt_floor_add_one ((n : Real) ^ degree)
      have castOne : (1 : Real) ≤ polynomialBudget degree n := by exact_mod_cast floorOne
      dsimp [polynomialBudget] at *
      linarith
    have rounded : constant ≤ (⌈constant⌉₊ : Real) := Nat.le_ceil constant
    have castBound : (complexity (family n) : Real) ≤
        (2 * ⌈constant⌉₊ : Nat) * (polynomialBudget degree n : Real) := by
      calc
        (complexity (family n) : Real) ≤ constant * (n : Real) ^ degree := hn
        _ ≤ (⌈constant⌉₊ : Real) * (n : Real) ^ degree :=
          mul_le_mul_of_nonneg_right rounded (Real.rpow_nonneg (Nat.cast_nonneg n) degree)
        _ ≤ (⌈constant⌉₊ : Real) * (2 * (polynomialBudget degree n : Real)) :=
          mul_le_mul_of_nonneg_left powerBound (Nat.cast_nonneg _)
        _ = _ := by push_cast; ring
    exact_mod_cast castBound

/-- Every fixed real power is eventually below the Shannon gate budget. -/
theorem polynomialBudget_eventually_le_shannon (degree : Real) :
    ∀ᶠ n in atTop, polynomialBudget degree n ≤ 2 ^ n / n := by
  obtain ⟨ceiling, above⟩ := exists_nat_ge degree
  have exponential := Circuit.Resource.eventually_const_mul_pow_le_two_pow 1 (ceiling + 1)
  filter_upwards [exponential, eventually_ge_atTop 1] with n hn positive
  have base : (1 : Real) ≤ n := by exact_mod_cast positive
  have powerBound : (n : Real) ^ degree ≤ (n : Real) ^ ceiling := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le base above
  have floorBound : polynomialBudget degree n ≤ n ^ ceiling := by
    apply Nat.floor_le_of_le
    exact_mod_cast powerBound
  apply (Nat.le_div_iff_mul_le (by omega : 0 < n)).mpr
  calc
    polynomialBudget degree n * n ≤ n ^ ceiling * n := Nat.mul_le_mul_right n floorBound
    _ = n ^ (ceiling + 1) := (pow_succ _ _).symm
    _ ≤ 2 ^ n := by simpa using hn

/-- The gap between distinct real powers above the linear scale absorbs the
exact `2 * n` interpolation overhead and every fixed lower-size coefficient. -/
theorem polynomialBudget_gap {a b : Real} (linear : 1 ≤ a) (separated : a < b)
    (constant : Nat) :
    ∀ᶠ n in atTop,
      constant * polynomialBudget a n + 2 * n + 1 ≤ polynomialBudget b n := by
  have growth : Tendsto (fun n : Nat => (n : Real) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr separated)).comp tendsto_natCast_atTop_atTop
  filter_upwards [growth.eventually (eventually_ge_atTop (constant + 3 : Real)),
    eventually_ge_atTop 1] with n hn positive
  have base : (1 : Real) ≤ n := by exact_mod_cast positive
  have basePositive : (0 : Real) < n := by linarith
  have linearBound : (n : Real) ≤ (n : Real) ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le base linear
  have oneBound : (1 : Real) ≤ (n : Real) ^ a := base.trans linearBound
  have floorBound : (polynomialBudget a n : Real) ≤ (n : Real) ^ a :=
    Nat.floor_le (Real.rpow_nonneg basePositive.le a)
  apply (Nat.le_floor_iff (Real.rpow_nonneg basePositive.le b)).mpr
  calc
    ((constant * polynomialBudget a n + 2 * n + 1 : Nat) : Real) =
        constant * (polynomialBudget a n : Real) + 2 * (n : Real) + 1 := by push_cast; rfl
    _ ≤ constant * (n : Real) ^ a + 2 * (n : Real) ^ a + (n : Real) ^ a := by gcongr
    _ = (constant + 3 : Real) * (n : Real) ^ a := by ring
    _ ≤ (n : Real) ^ (b - a) * (n : Real) ^ a :=
      mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg basePositive.le a)
    _ = (n : Real) ^ b := by rw [← Real.rpow_add basePositive]; congr 1; ring

/-- Circuit size hierarchy for arbitrary real polynomial exponents:
`SIZE(n^a)` is strictly contained in `SIZE(n^b)` whenever `1 ≤ a < b`. -/
theorem polynomialSize_ssubset {a b : Real} (linear : 1 ≤ a) (separated : a < b) :
    polynomialSize a ⊂ polynomialSize b :=
  sizeClass_ssubset_of_gap (polynomialBudget a) (polynomialBudget b)
    (polynomialBudget_eventually_le_shannon b) (polynomialBudget_gap linear separated)

/-- Natural-power specialization of the circuit size hierarchy. -/
theorem sizeClass_pow_ssubset {a b : Nat} (linear : 1 ≤ a) (separated : a < b) :
    sizeClass (fun n => n ^ a) ⊂ sizeClass (fun n => n ^ b) := by
  have hierarchy := polynomialSize_ssubset (by exact_mod_cast linear : (1 : Real) ≤ a)
    (by exact_mod_cast separated : (a : Real) < b)
  simpa only [polynomialSize, polynomialBudget_natCast] using hierarchy

end Algebraic.DeMorgan
