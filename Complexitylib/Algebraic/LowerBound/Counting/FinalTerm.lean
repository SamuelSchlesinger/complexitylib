/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.Arity
public import Complexitylib.Algebraic.LowerBound.Counting.Sharp
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Final-term envelope for sharp circuit counting

The exact sharp budget is a sum of factorial-divided terms. This file bounds
that sum by its final real-valued term, without yet invoking Stirling.
-/

@[expose] public section

namespace Algebraic

/-- Real-valued envelope obtained by replacing every summand of the sharp
budget by its final factorial-divided term. -/
noncomputable def _root_.Cslib.Circuits.Signature.finalTerm
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Real :=
  (G + 1) *
    (σ.lineCount (n + G) : Real) ^ G * (n + G : Real) ^ m /
      (G.factorial : Real)

export Cslib.Circuits (Signature.finalTerm)

/-- The tail of a factorial is bounded by replacing every factor by the final
index. -/
theorem Nat.factorial_le_factorial_mul_pow
    {g G : Nat}
    (bounded : g ≤ G) :
    G.factorial ≤ g.factorial * G ^ (G - g) := by
  induction G with
  | zero =>
      have : g = 0 := Nat.eq_zero_of_le_zero bounded
      subst g
      simp
  | succ G ih =>
      by_cases last : g = G + 1
      · subst g
        simp
      · have prior : g ≤ G := by omega
        calc
          (G + 1).factorial = (G + 1) * G.factorial := by
            rw [Nat.factorial_succ]
          _ ≤ (G + 1) * (g.factorial * G ^ (G - g)) :=
            Nat.mul_le_mul_left _ (ih prior)
          _ ≤ (G + 1) *
              (g.factorial * (G + 1) ^ (G - g)) := by
            gcongr
            exact Nat.le_succ G
          _ = g.factorial * (G + 1) ^ ((G + 1) - g) := by
            rw [show (G + 1) - g = (G - g) + 1 by omega, pow_succ]
            ac_rfl

/-- Real-valued global form of the factorial-improved count. It bounds every
summand by the final one whenever the final line count is at least `G`. -/
theorem _root_.Cslib.Circuits.Signature.sharpBudget_cast_le_finalTerm
    (σ : Signature) [Fintype σ.Op]
    {n m G : Nat}
    (enoughLines : G ≤ σ.lineCount (n + G)) :
    (σ.sharpBudget n m G : Real) ≤
      σ.finalTerm n m G := by
  unfold Signature.finalTerm
  let base := σ.lineCount (n + G)
  have termBound (g : Nat) (bounded : g ≤ G) :
      (σ.sharpCount n g m : Real) ≤
        ((base : Real) ^ G * (n + G : Real) ^ m) /
          (G.factorial : Real) := by
    have lineBound : σ.lineCount (n + g) ≤ base := by
      apply Signature.lineCount_mono σ
      omega
    have wireBound : n + g ≤ n + G := Nat.add_le_add_left bounded n
    have factorialBound : G.factorial ≤ g.factorial * base ^ (G - g) :=
      (Nat.factorial_le_factorial_mul_pow bounded).trans <|
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left enoughLines _)
    calc
      (σ.sharpCount n g m : Real) ≤
          (σ.lineCount (n + g) ^ g * (n + g) ^ m : Nat) /
            (g.factorial : Real) := by
        exact Nat.cast_div_le
      _ ≤ ((base : Real) ^ g * (n + G : Real) ^ m) /
          (g.factorial : Real) := by
        apply div_le_div_of_nonneg_right
        · norm_cast
          exact Nat.mul_le_mul (Nat.pow_le_pow_left lineBound g)
            (Nat.pow_le_pow_left wireBound m)
        · exact Nat.cast_nonneg _
      _ ≤ ((base : Real) ^ G * (n + G : Real) ^ m) /
          (G.factorial : Real) := by
        rw [div_le_div_iff₀
          (by exact_mod_cast Nat.factorial_pos g : (0 : Real) < g.factorial)
          (by exact_mod_cast Nat.factorial_pos G : (0 : Real) < G.factorial)]
        have castFactorialBound :
            (G.factorial : Real) ≤
              (g.factorial : Real) * (base : Real) ^ (G - g) := by
          rw [← Nat.cast_pow, ← Nat.cast_mul]
          exact_mod_cast factorialBound
        calc
          ((base : Real) ^ g * (n + G : Real) ^ m) * G.factorial ≤
              ((base : Real) ^ g * (n + G : Real) ^ m) *
                (g.factorial * base ^ (G - g)) := by
            exact mul_le_mul_of_nonneg_left castFactorialBound
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg base) _)
                (pow_nonneg
                  (add_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg G)) _))
          _ = ((base : Real) ^ G * (n + G : Real) ^ m) * g.factorial := by
            calc
              ((base : Real) ^ g * (n + G : Real) ^ m) *
                    ((g.factorial : Real) * base ^ (G - g)) =
                  (((base : Real) ^ g * base ^ (G - g)) *
                    (n + G : Real) ^ m) * g.factorial := by ring
              _ = ((base : Real) ^ (g + (G - g)) *
                    (n + G : Real) ^ m) * g.factorial := by
                rw [pow_add]
              _ = ((base : Real) ^ G * (n + G : Real) ^ m) *
                    g.factorial := by
                rw [Nat.add_sub_of_le bounded]
  unfold Signature.sharpBudget
  rw [Nat.cast_sum]
  calc
    (∑ g ∈ Finset.range (G + 1), (σ.sharpCount n g m : Real)) ≤
        ∑ _g ∈ Finset.range (G + 1),
          ((base : Real) ^ G * (n + G : Real) ^ m) /
            (G.factorial : Real) := by
      exact Finset.sum_le_sum fun g present =>
        termBound g (Nat.le_of_lt_succ (Finset.mem_range.mp present))
    _ = (G + 1) * (base : Real) ^ G * (n + G : Real) ^ m /
        (G.factorial : Real) := by
      simp
      ring

export Cslib.Circuits (Signature.sharpBudget_cast_le_finalTerm)

/-- Real-valued final-term bound on the number of functions computed with at
most `G` gates. -/
theorem _root_.Cslib.Circuits.Circuit.card_functionsAtMost_cast_le_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {n m G : Nat}
    (enoughLines : G ≤ σ.lineCount (n + G)) :
    ((Circuit.functionsAtMost interpretation n m G).card : Real) ≤
      σ.finalTerm n m G := by
  calc
    ((Circuit.functionsAtMost interpretation n m G).card : Real) ≤
        (σ.sharpBudget n m G : Real) := by
      exact_mod_cast Circuit.card_functionsAtMost_le_sharpBudget
        interpretation n m G
    _ ≤ _ := σ.sharpBudget_cast_le_finalTerm enoughLines

export Cslib.Circuits (Circuit.card_functionsAtMost_cast_le_finalTerm)

/-- A finite family exceeding the real-valued final-term envelope contains a
function requiring more than `G` gates. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_in_family_of_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (family : Finset (Target U n m))
    (enoughLines : G ≤ σ.lineCount (n + G))
    (large : σ.finalTerm n m G < family.card) :
    ∃ target ∈ family,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_in_family_sharp interpretation family
  have castBound : (σ.sharpBudget n m G : Real) < (family.card : Real) :=
    (σ.sharpBudget_cast_le_finalTerm enoughLines).trans_lt large
  exact_mod_cast castBound

export Cslib.Circuits (Circuit.exists_hard_in_family_of_finalTerm)

/-- Full-function-space Shannon theorem using the real-valued final-term
envelope. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_of_finalTerm
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (enoughLines : G ≤ σ.lineCount (n + G))
    (large : σ.finalTerm n m G < (Target.count U n m : Real)) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_sharp interpretation
  have castBound : (σ.sharpBudget n m G : Real) <
      (Target.count U n m : Real) :=
    (σ.sharpBudget_cast_le_finalTerm enoughLines).trans_lt large
  exact_mod_cast castBound

export Cslib.Circuits (Circuit.exists_hard_of_finalTerm)

end Algebraic
