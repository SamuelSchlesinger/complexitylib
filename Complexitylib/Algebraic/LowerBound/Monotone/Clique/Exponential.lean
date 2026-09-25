/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.LowerBound
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.Positivity

/-!
# An explicit exponential lower bound for monotone CLIQUE circuits

We instantiate the finite approximation dichotomy with

* width `w`,
* clique size `w^4`,
* vertex count `w^20`, and
* `w^2` sunflower petals.

For every `w ≥ 16`, a binary, constant-free monotone shared circuit computing
this CLIQUE function has more than `w^w` gates.  Taking `w = 2^t` gives the
closed form `2^(t * 2^t)` gates on `2^(20*t)` vertices.

This is an explicit finite specialization of Razborov's monotone
approximation method (1985).
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace Exponential

/-- Scaling the ambient set by `q` scales every factor in a descending
factorial by at least `q`. -/
theorem pow_mul_descFactorial_le
    (q k d : Nat)
    (qPositive : 1 ≤ q)
    (d_le_k : d ≤ k) :
    q ^ d * k.descFactorial d ≤
      (q * k).descFactorial d := by
  induction d with
  | zero => simp
  | succ d inductionHypothesis =>
      have d_le_k' : d ≤ k := by omega
      have factorBound : q * (k - d) ≤ q * k - d := by
        rw [Nat.mul_sub_left_distrib]
        exact Nat.sub_le_sub_left
          (Nat.le_mul_of_pos_left d (by omega : 0 < q)) (q * k)
      rw [pow_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
      calc
        q ^ d * q * ((k - d) * k.descFactorial d) =
            (q * (k - d)) * (q ^ d * k.descFactorial d) := by
          ac_rfl
        _ ≤ (q * k - d) * (q * k).descFactorial d :=
          Nat.mul_le_mul factorBound (inductionHypothesis d_le_k')

/-- Binomial coefficients inherit the descending-factorial scaling bound. -/
theorem pow_mul_choose_le_choose_mul
    (q k d : Nat)
    (qPositive : 1 ≤ q)
    (d_le_k : d ≤ k) :
    q ^ d * Nat.choose k d ≤ Nat.choose (q * k) d := by
  have descending := pow_mul_descFactorial_le q k d qPositive d_le_k
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at descending
  apply Nat.le_of_mul_le_mul_left (c := d.factorial)
  · simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using descending
  · exact Nat.factorial_pos d

/-- A `d`-set occurs in at most a `q^-d` fraction of the `k`-sets of a
`q*k`-element universe, stated without division. -/
theorem pow_mul_containing_choose_le
    (q k d : Nat)
    (qPositive : 1 ≤ q)
    (d_le_k : d ≤ k) :
    q ^ d * Nat.choose (q * k - d) (k - d) ≤
      Nat.choose (q * k) k := by
  have scaled := pow_mul_choose_le_choose_mul q k d qPositive d_le_k
  have chooseIdentity := Nat.choose_mul (n := q * k) d_le_k
  have multiplied :
      (q ^ d * Nat.choose k d) *
          Nat.choose (q * k - d) (k - d) ≤
        Nat.choose (q * k) d *
          Nat.choose (q * k - d) (k - d) :=
    Nat.mul_le_mul_right _ scaled
  rw [← chooseIdentity] at multiplied
  have rearranged :
      Nat.choose k d *
          (q ^ d * Nat.choose (q * k - d) (k - d)) ≤
        Nat.choose k d * Nat.choose (q * k) k := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using multiplied
  exact Nat.le_of_mul_le_mul_left rearranged (Nat.choose_pos d_le_k)

/-- Strict form used by the positive approximation budget. -/
theorem mul_containing_choose_lt
    (q k d budget : Nat)
    (qPositive : 1 ≤ q)
    (d_le_k : d ≤ k)
    (budgetSmall : budget < q ^ d) :
    budget * Nat.choose (q * k - d) (k - d) <
      Nat.choose (q * k) k := by
  have k_le_qk : k ≤ q * k := Nat.le_mul_of_pos_left k (by omega)
  have remaining : k - d ≤ q * k - d :=
    Nat.sub_le_sub_right k_le_qk d
  have capPositive : 0 < Nat.choose (q * k - d) (k - d) :=
    Nat.choose_pos remaining
  exact (Nat.mul_lt_mul_of_pos_right budgetSmall capPositive).trans_le
    (pow_mul_containing_choose_le q k d qPositive d_le_k)

/-- The elementary sunflower bound at `w^2` petals is at most `w^(4w)`. -/
theorem sunflower_bound_le_pow
    (w : Nat)
    (two_le : 2 ≤ w) :
    Sunflower.bound (w ^ 2) w ≤ w ^ (4 * w) := by
  have factorialBound : w.factorial ≤ w ^ w := Nat.factorial_le_pow w
  have successorBound : w + 1 ≤ w ^ 2 := by
    calc
      w + 1 ≤ w + w := Nat.add_le_add_left (by omega) w
      _ = 2 * w := by omega
      _ ≤ w * w := Nat.mul_le_mul_right w two_le
      _ = w ^ 2 := by simp [pow_two]
  have petalBaseBound : w ^ 2 - 1 ≤ w ^ 2 := Nat.sub_le _ _
  calc
    Sunflower.bound (w ^ 2) w =
        (w + 1) * ((w ^ 2 - 1) ^ w * w.factorial) := rfl
    _ ≤ w ^ 2 * ((w ^ 2) ^ w * w ^ w) := by
      gcongr
    _ = w ^ (3 * w + 2) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ w ^ (4 * w) :=
      Nat.pow_le_pow_right (by omega) (by omega)

/-- The chosen vertex count factors as `w^16 * w^4`. -/
private theorem vertexCount_factorization (w : Nat) :
    w ^ 16 * w ^ 4 = w ^ 20 := by
  rw [← pow_add]

private theorem width_succ_le_cliqueSize
    (w : Nat)
    (two_le : 2 ≤ w) :
    w + 1 ≤ w ^ 4 := by
  have successorSquare : w + 1 ≤ w ^ 2 := by
    calc
      w + 1 ≤ w + w := Nat.add_le_add_left (by omega) w
      _ = 2 * w := by omega
      _ ≤ w * w := Nat.mul_le_mul_right w two_le
      _ = w ^ 2 := by simp [pow_two]
  exact successorSquare.trans <| by
    rw [show w ^ 4 = w ^ 2 * w ^ 2 by ring]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) 2)

/-- The positive truncation budget is strictly smaller than the number of
minimal positive clique graphs. -/
theorem positive_budget
    (w : Nat)
    (sixteen_le : 16 ≤ w) :
    LowerBound.positiveGateCap (w ^ 20) (w ^ 4) (w ^ 2) w * w ^ w <
      Nat.choose (w ^ 20) (w ^ 4) := by
  let familyBound := Sunflower.bound (w ^ 2) w
  have two_le : 2 ≤ w := by omega
  have familyBound_le : familyBound ≤ w ^ (4 * w) :=
    sunflower_bound_le_pow w two_le
  have squaredBound : familyBound ^ 2 * w ^ w ≤ w ^ (9 * w) := by
    calc
      familyBound ^ 2 * w ^ w ≤ (w ^ (4 * w)) ^ 2 * w ^ w := by
        gcongr
      _ = w ^ (9 * w) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
  have budgetSmall : familyBound ^ 2 * w ^ w <
      (w ^ 16) ^ (w + 1) := by
    apply squaredBound.trans_lt
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have amplified := mul_containing_choose_lt
    (w ^ 16) (w ^ 4) (w + 1) (familyBound ^ 2 * w ^ w)
    (one_le_pow₀ (by omega : 1 ≤ w))
    (width_succ_le_cliqueSize w two_le)
    budgetSmall
  rw [vertexCount_factorization] at amplified
  simpa [LowerBound.positiveGateCap, Positive.errorCap, familyBound,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using amplified

private theorem colors_large
    (w : Nat)
    (two_le : 2 ≤ w) :
    2 * w ^ 2 ≤ w ^ 4 - 1 := by
  apply Nat.le_sub_of_add_le
  calc
    2 * w ^ 2 + 1 ≤ 3 * w ^ 2 := by
      have : 1 ≤ w ^ 2 := one_le_pow₀ (by omega : 1 ≤ w)
      omega
    _ ≤ w ^ 2 * w ^ 2 := by
      exact Nat.mul_le_mul_right (w ^ 2) (by
        have squareFour : 4 ≤ w ^ 2 :=
          Nat.pow_le_pow_left two_le 2
        omega)
    _ = w ^ 4 := by ring

private theorem cube_le_fourth_sub_one
    (w : Nat)
    (two_le : 2 ≤ w) :
    w ^ 3 ≤ w ^ 4 - 1 := by
  apply Nat.le_sub_of_add_le
  calc
    w ^ 3 + 1 ≤ 2 * w ^ 3 := by
      have : 1 ≤ w ^ 3 := one_le_pow₀ (by omega : 1 ≤ w)
      omega
    _ ≤ w * w ^ 3 := Nat.mul_le_mul_right (w ^ 3) two_le
    _ = w ^ 4 := by ring

/-- The negative plucking budget is also strictly below the full coloring
space for the chosen parameters. -/
theorem negative_budget
    (w : Nat)
    (sixteen_le : 16 ≤ w) :
    2 * LowerBound.negativeGateCap
        (w ^ 20) (w ^ 4 - 1) (w ^ 2) w * w ^ w <
      (w ^ 4 - 1) ^ (w ^ 20) := by
  let familyBound := Sunflower.bound (w ^ 2) w
  let coarseBound := w ^ (4 * w)
  let colors := w ^ 4 - 1
  have two_le : 2 ≤ w := by omega
  have familyBound_le : familyBound ≤ coarseBound :=
    sunflower_bound_le_pow w two_le
  have coarsePositive : 0 < coarseBound := pow_pos (by omega) _
  have coarse_le_square : coarseBound ≤ coarseBound ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left _ coarsePositive
  have familySumBound : 2 * familyBound + familyBound ^ 2 ≤
      3 * coarseBound ^ 2 := by
    calc
      2 * familyBound + familyBound ^ 2 ≤
          2 * coarseBound + coarseBound ^ 2 := by gcongr
      _ ≤ 2 * (coarseBound ^ 2) + coarseBound ^ 2 := by gcongr
      _ = 3 * coarseBound ^ 2 := by omega
  have six_le_cube : 6 ≤ w ^ 3 := by
    have sixteen_le_cube : 16 ≤ w ^ 3 := by
      calc
        16 ≤ w := sixteen_le
        _ ≤ w ^ 3 := by
          rw [show w ^ 3 = w * w ^ 2 by ring]
          simpa [Nat.mul_comm] using
            Nat.le_mul_of_pos_left (n := w ^ 2) w (pow_pos (by omega) 2)
    omega
  have coefficientBound :
      2 * (2 * familyBound + familyBound ^ 2) * w ^ w *
          (w ^ 2) ^ (w ^ 2) ≤
        w ^ (2 * w ^ 2 + 9 * w + 3) := by
    calc
      2 * (2 * familyBound + familyBound ^ 2) * w ^ w *
          (w ^ 2) ^ (w ^ 2) ≤
          2 * (3 * coarseBound ^ 2) * w ^ w *
            (w ^ 2) ^ (w ^ 2) := by gcongr
      _ = 6 * coarseBound ^ 2 * w ^ w * (w ^ 2) ^ (w ^ 2) := by
        ring
      _ ≤ w ^ 3 * coarseBound ^ 2 * w ^ w *
          (w ^ 2) ^ (w ^ 2) := by gcongr
      _ = w ^ (2 * w ^ 2 + 9 * w + 3) := by
        simp only [coarseBound]
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
  have exponent_lt : 2 * w ^ 2 + 9 * w + 3 < 3 * w ^ 2 := by
    have sixteen_mul_le : 16 * w ≤ w * w :=
      Nat.mul_le_mul_right w sixteen_le
    rw [pow_two]
    omega
  have coefficient_lt_colors :
      2 * (2 * familyBound + familyBound ^ 2) * w ^ w *
          (w ^ 2) ^ (w ^ 2) < colors ^ (w ^ 2) := by
    apply coefficientBound.trans_lt
    apply (Nat.pow_lt_pow_right (by omega) exponent_lt).trans_le
    rw [pow_mul]
    exact Nat.pow_le_pow_left
      (cube_le_fourth_sub_one w two_le) (w ^ 2)
  have petals_le_vertices : w ^ 2 ≤ w ^ 20 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have tailPositive : 0 < colors ^ (w ^ 20 - w ^ 2) := by
    apply pow_pos
    exact (cube_le_fourth_sub_one w two_le).trans_lt' (pow_pos (by omega) 3)
  calc
    2 * LowerBound.negativeGateCap
        (w ^ 20) (w ^ 4 - 1) (w ^ 2) w * w ^ w =
        (2 * (2 * familyBound + familyBound ^ 2) * w ^ w *
          (w ^ 2) ^ (w ^ 2)) * colors ^ (w ^ 20 - w ^ 2) := by
      simp only [LowerBound.negativeGateCap, Negative.pluckErrorCap,
        familyBound, colors]
      ac_rfl
    _ < colors ^ (w ^ 2) * colors ^ (w ^ 20 - w ^ 2) :=
      Nat.mul_lt_mul_of_pos_right coefficient_lt_colors tailPositive
    _ = colors ^ (w ^ 20) := by
      rw [← pow_add]
      congr 1
      omega

/-- Explicit exponential lower bound in the width parameter for binary,
constant-free monotone shared circuits. -/
theorem powSelf_lt_circuitSize
    (w : Nat)
    (sixteen_le : 16 ≤ w)
    (circuit : Circuit AndOr.signature (edgeCount (w ^ 20)) g 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function (w ^ 20) (w ^ 4) assignment) :
    w ^ w < circuit.size := by
  have two_le : 2 ≤ w := by omega
  exact LowerBound.sizeBound_lt_circuitSize
    (w ^ 20) (w ^ 4) (w ^ 2) w (w ^ w)
    (pow_pos (by omega) 20)
    (pow_pos (by omega) 4)
    (by
      have : 4 ≤ w ^ 2 := Nat.pow_le_pow_left two_le 2
      omega)
    two_le
    (width_succ_le_cliqueSize w two_le)
    (colors_large w two_le)
    (positive_budget w sixteen_le)
    (negative_budget w sixteen_le)
    circuit computes

/-- Closed power-of-two specialization.  On `N = 2^(20t)` vertices, the
`2^(4t)`-CLIQUE function needs more than `2^(t*2^t)` monotone gates. -/
theorem twoPow_lt_circuitSize
    (t : Nat)
    (four_le : 4 ≤ t)
    (circuit : Circuit AndOr.signature (edgeCount ((2 ^ t) ^ 20)) g 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function ((2 ^ t) ^ 20) ((2 ^ t) ^ 4) assignment) :
    2 ^ (t * 2 ^ t) < circuit.size := by
  have sixteen_le : 16 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) four_le
  simpa [pow_mul] using
    powSelf_lt_circuitSize (w := 2 ^ t) sixteen_le circuit computes

end Exponential
end Clique
end Monotone
end Algebraic
