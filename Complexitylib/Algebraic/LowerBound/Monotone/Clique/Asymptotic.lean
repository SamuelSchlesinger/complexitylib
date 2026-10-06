/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Essential
public import Complexitylib.Algebraic.LowerBound.Monotone.Clique.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.IntervalCases

/-!
# A `2^√k` lower bound for monotone CLIQUE circuits

We instantiate the finite approximation dichotomy of `LowerBound.lean` for
every admissible pair of a vertex count `n` and a clique size `k`, not only
along the special family of `Exponential.lean`.

For a width `w` we use `w^2` sunflower petals.  Writing
`F = Sunflower.bound (w^2) w ≤ (w + 1) * w^(3w)`, the two budgets become:

* positive: when `64 * w^6 * k ≤ n`, the ratio between the number of
  `k`-sets of vertices and the number of those containing a fixed
  `(w+1)`-set is at least `(64 * w^6)^(w+1)`, which exceeds `F^2 * 64^w`;
* negative: when `4 * w^2 ≤ k - 1`, a fixed `w^2`-petal sunflower is plucked
  wrongly by at most a `4^-(w^2)` fraction of the colorings, and
  `6 * F^2 * 64^w < 4^(w^2)` once `w ≥ 16`.

So every circuit computing `k`-CLIQUE has more than `64^w = 2^(6w)` gates
(`sixtyFourPow_lt_circuitSize`).  Choosing `w = ⌊√(k-1)⌋ / 2` handles
`1025 ≤ k` (`twoPow_two_mul_sqrt_lt_circuitSize_of_large`).  Smaller clique
sizes are covered by `Essential.lean`: for `2 ≤ k ≤ 1024` every edge variable
is essential, which already forces `(n / 2)^2 - 1` gates, and for `k ≤ 1` no
constant-free circuit computes `k`-CLIQUE at all.

Together: for every `k` with `k^4 ≤ n` (that is, `k ≤ n^(1/4)`), every
binary, constant-free monotone shared circuit computing `k`-CLIQUE on `n`
vertices has more than `2^(2⌊√k⌋)` gates (`twoPow_two_mul_sqrt_lt_circuitSize`)
and hence more than `2^√k` gates (`rpow_sqrt_lt_circuitSize`).  This is the
`2^(ε√k)` bound of Razborov (1985) and Alon–Boppana (1987), in the form of
Arora–Barak Theorem 14.7, with `ε = 1`, in the circuit model of the imported
library (every AND and OR gate has fan-in two and is counted).
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique
namespace Asymptotic

/-- A `d`-subset of a `k`-set lies in at most a `q^-d` fraction of the
`k`-subsets of an `n`-set when `q * k ≤ n`, stated without division. -/
theorem pow_mul_choose_sub_le_choose
    (q n k d : Nat)
    (qPositive : 1 ≤ q)
    (d_le_k : d ≤ k)
    (verticesLarge : q * k ≤ n) :
    q ^ d * Nat.choose (n - d) (k - d) ≤ Nat.choose n k := by
  have scaled : q ^ d * Nat.choose k d ≤ Nat.choose n d :=
    (Exponential.pow_mul_choose_le_choose_mul q k d qPositive d_le_k).trans
      (Nat.choose_le_choose d verticesLarge)
  have multiplied :
      (q ^ d * Nat.choose k d) * Nat.choose (n - d) (k - d) ≤
        Nat.choose n d * Nat.choose (n - d) (k - d) :=
    Nat.mul_le_mul_right _ scaled
  rw [← Nat.choose_mul (n := n) d_le_k] at multiplied
  have rearranged :
      Nat.choose k d * (q ^ d * Nat.choose (n - d) (k - d)) ≤
        Nat.choose k d * Nat.choose n k := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using multiplied
  exact Nat.le_of_mul_le_mul_left rearranged (Nat.choose_pos d_le_k)

/-- The elementary sunflower bound at `w^2` petals is at most
`(w + 1) * w^(3w)`. -/
theorem sunflower_bound_le (w : Nat) :
    Sunflower.bound (w ^ 2) w ≤ (w + 1) * w ^ (3 * w) := by
  have factorialBound : w.factorial ≤ w ^ w := Nat.factorial_le_pow w
  have petalBaseBound : w ^ 2 - 1 ≤ w ^ 2 := Nat.sub_le _ _
  calc
    Sunflower.bound (w ^ 2) w =
        (w + 1) * ((w ^ 2 - 1) ^ w * w.factorial) := rfl
    _ ≤ (w + 1) * ((w ^ 2) ^ w * w ^ w) := by
      gcongr
    _ = (w + 1) * w ^ (3 * w) := by
      rw [← pow_mul, ← pow_add]
      congr 2
      ring

/-- A sixth power is eventually dominated by `4^w`. -/
theorem mul_pow_six_le_four_pow
    (w : Nat)
    (sixteen_le : 16 ≤ w) :
    128 * w ^ 6 ≤ 4 ^ w := by
  induction w, sixteen_le using Nat.le_induction with
  | base => norm_num
  | succ w sixteen_le inductionHypothesis =>
      have step : 16 * (w + 1) ≤ 17 * w := by omega
      have powered := Nat.pow_le_pow_left step 6
      rw [mul_pow, mul_pow] at powered
      have successorBound : (w + 1) ^ 6 ≤ 4 * w ^ 6 := by
        norm_num at powered
        omega
      rw [pow_succ 4 w]
      omega

/-- A quadratic is eventually dominated by `2^w`. -/
theorem six_mul_succ_sq_lt_two_pow
    (w : Nat)
    (sixteen_le : 16 ≤ w) :
    6 * (w + 1) ^ 2 < 2 ^ w := by
  induction w, sixteen_le using Nat.le_induction with
  | base => norm_num
  | succ w sixteen_le inductionHypothesis =>
      have successorBound : (w + 1 + 1) ^ 2 ≤ 2 * (w + 1) ^ 2 := by
        nlinarith
      rw [pow_succ 2 w]
      omega

/-- The positive truncation budget at width `w`, `w^2` petals, and size
bound `64^w` is below the number of minimal positive clique graphs. -/
theorem positive_budget
    (n k w : Nat)
    (one_le : 1 ≤ w)
    (width_succ_le_k : w + 1 ≤ k)
    (verticesLarge : 64 * w ^ 6 * k ≤ n) :
    LowerBound.positiveGateCap n k (w ^ 2) w * 64 ^ w <
      Nat.choose n k := by
  let familyBound := Sunflower.bound (w ^ 2) w
  let ratio := 64 * w ^ 6
  have familyBound_le : familyBound ≤ (w + 1) * w ^ (3 * w) :=
    sunflower_bound_le w
  have ratioPositive : 0 < ratio := by
    simp only [ratio]
    positivity
  have successorSmall : (w + 1) ^ 2 < ratio := by
    have : 1 ≤ w ^ 6 := one_le_pow₀ one_le
    have : (w + 1) ^ 2 ≤ 4 * w ^ 6 := by
      calc
        (w + 1) ^ 2 ≤ (2 * w) ^ 2 := by gcongr; omega
        _ = 4 * w ^ 2 := by ring
        _ ≤ 4 * w ^ 6 := by gcongr; omega
    omega
  have budgetSmall : familyBound ^ 2 * 64 ^ w < ratio ^ (w + 1) := by
    calc
      familyBound ^ 2 * 64 ^ w ≤ ((w + 1) * w ^ (3 * w)) ^ 2 * 64 ^ w := by
        gcongr
      _ = (w + 1) ^ 2 * ratio ^ w := by
        simp only [ratio]
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          show 3 * w * 2 = 6 * w by ring]
        ring
      _ < ratio * ratio ^ w :=
        Nat.mul_lt_mul_of_pos_right successorSmall (pow_pos ratioPositive w)
      _ = ratio ^ (w + 1) := by ring
  have containing := pow_mul_choose_sub_le_choose ratio n k (w + 1)
    ratioPositive width_succ_le_k verticesLarge
  have k_le_n : k ≤ n := by
    calc
      k ≤ 64 * w ^ 6 * k := Nat.le_mul_of_pos_left k ratioPositive
      _ ≤ n := verticesLarge
  have remainingPositive : 0 < Nat.choose (n - (w + 1)) (k - (w + 1)) :=
    Nat.choose_pos (Nat.sub_le_sub_right k_le_n _)
  calc
    LowerBound.positiveGateCap n k (w ^ 2) w * 64 ^ w =
        (familyBound ^ 2 * 64 ^ w) *
          Nat.choose (n - (w + 1)) (k - (w + 1)) := by
      simp only [LowerBound.positiveGateCap, Positive.errorCap, familyBound]
      ring
    _ < ratio ^ (w + 1) * Nat.choose (n - (w + 1)) (k - (w + 1)) :=
      Nat.mul_lt_mul_of_pos_right budgetSmall remainingPositive
    _ ≤ Nat.choose n k := containing

/-- The negative plucking budget at width `w`, `w^2` petals, and size bound
`64^w` is below the number of colorings with `k - 1` colors. -/
theorem negative_budget
    (n k w : Nat)
    (sixteen_le : 16 ≤ w)
    (widthSmall : 4 * w ^ 2 ≤ k - 1)
    (petals_le_n : w ^ 2 ≤ n) :
    2 * LowerBound.negativeGateCap n (k - 1) (w ^ 2) w * 64 ^ w <
      (k - 1) ^ n := by
  let familyBound := Sunflower.bound (w ^ 2) w
  let colors := k - 1
  let petals := w ^ 2
  have familyBound_le : familyBound ≤ (w + 1) * w ^ (3 * w) :=
    sunflower_bound_le w
  have familySum : 2 * familyBound + familyBound ^ 2 ≤ 3 * familyBound ^ 2 := by
    have : familyBound ≤ familyBound ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have core : 6 * familyBound ^ 2 * 64 ^ w < 4 ^ petals := by
    have exponential := mul_pow_six_le_four_pow w sixteen_le
    have quadratic := six_mul_succ_sq_lt_two_pow w sixteen_le
    calc
      6 * familyBound ^ 2 * 64 ^ w ≤
          6 * ((w + 1) * w ^ (3 * w)) ^ 2 * 64 ^ w := by
        gcongr
      _ = 6 * (w + 1) ^ 2 * (64 * w ^ 6) ^ w := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          show 3 * w * 2 = 6 * w by ring]
        ring
      _ < 2 ^ w * (64 * w ^ 6) ^ w := by
        apply Nat.mul_lt_mul_of_pos_right quadratic
        exact pow_pos (by positivity) w
      _ = (128 * w ^ 6) ^ w := by
        rw [← mul_pow]
        ring_nf
      _ ≤ (4 ^ w) ^ w := Nat.pow_le_pow_left exponential w
      _ = 4 ^ petals := by
        simp only [petals]
        rw [← pow_mul, pow_two]
  have colorsLarge : (4 * w ^ 2) ^ petals ≤ colors ^ petals :=
    Nat.pow_le_pow_left widthSmall petals
  have tailPositive : 0 < (w ^ 2) ^ petals * colors ^ (n - petals) := by
    apply Nat.mul_pos
    · exact pow_pos (pow_pos (by omega) 2) _
    · apply pow_pos
      have : 4 ≤ 4 * w ^ 2 := by
        have : 1 ≤ w ^ 2 := one_le_pow₀ (by omega)
        omega
      exact lt_of_lt_of_le (by norm_num) (this.trans widthSmall)
  calc
    2 * LowerBound.negativeGateCap n (k - 1) (w ^ 2) w * 64 ^ w =
        2 * (2 * familyBound + familyBound ^ 2) * 64 ^ w *
          ((w ^ 2) ^ petals * colors ^ (n - petals)) := by
      simp only [LowerBound.negativeGateCap, Negative.pluckErrorCap,
        familyBound, colors, petals]
      ring
    _ ≤ 6 * familyBound ^ 2 * 64 ^ w *
          ((w ^ 2) ^ petals * colors ^ (n - petals)) := by
      have coefficient : 2 * (2 * familyBound + familyBound ^ 2) ≤
          6 * familyBound ^ 2 := by
        omega
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ coefficient)
    _ < 4 ^ petals * ((w ^ 2) ^ petals * colors ^ (n - petals)) :=
      Nat.mul_lt_mul_of_pos_right core tailPositive
    _ = (4 * w ^ 2) ^ petals * colors ^ (n - petals) := by
      rw [mul_pow]
      ring
    _ ≤ colors ^ petals * colors ^ (n - petals) := by
      gcongr
    _ = (k - 1) ^ n := by
      rw [← pow_add]
      congr 1
      omega

/-- Every binary, constant-free monotone shared circuit computing `k`-CLIQUE
on `n` vertices has more than `64^w` gates, for every width `w ≥ 16` with
`4 * w^2 ≤ k - 1` and `64 * w^6 * k ≤ n`. -/
theorem sixtyFourPow_lt_circuitSize
    (n k w : Nat)
    (sixteen_le : 16 ≤ w)
    (widthSmall : 4 * w ^ 2 ≤ k - 1)
    (verticesLarge : 64 * w ^ 6 * k ≤ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    64 ^ w < circuit.size := by
  have squareLarge : 256 ≤ w ^ 2 := by
    simpa using Nat.pow_le_pow_left sixteen_le 2
  have widthLe : w ≤ w ^ 2 := Nat.le_self_pow (by norm_num) w
  have k_le_n : k ≤ n := by
    have : 0 < 64 * w ^ 6 := by positivity
    calc
      k ≤ 64 * w ^ 6 * k := Nat.le_mul_of_pos_left k this
      _ ≤ n := verticesLarge
  exact LowerBound.sizeBound_lt_circuitSize
    n k (w ^ 2) w (64 ^ w)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
    (positive_budget n k w (by omega) (by omega) verticesLarge)
    (negative_budget n k w sixteen_le widthSmall (by omega))
    circuit computes

/-- The approximation bound for large cliques: for `1025 ≤ k` and
`k^4 ≤ n`, every binary, constant-free monotone shared circuit computing
`k`-CLIQUE on `n` vertices has more than `2^(2⌊√k⌋)` gates. -/
theorem twoPow_two_mul_sqrt_lt_circuitSize_of_large
    (n k : Nat)
    (cliqueLarge : 1025 ≤ k)
    (verticesLarge : k ^ 4 ≤ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    2 ^ (2 * Nat.sqrt k) < circuit.size := by
  let root := Nat.sqrt (k - 1)
  let w := root / 2
  have rootLarge : 32 ≤ root := Nat.le_sqrt.2 (by omega)
  have rootSquare : root ^ 2 ≤ k - 1 := Nat.sqrt_le' (k - 1)
  have sqrtSmall : Nat.sqrt k ≤ root + 1 := by
    have : Nat.sqrt k < root + 2 := by
      rw [Nat.sqrt_lt']
      have successor : k - 1 < (root + 1) ^ 2 := Nat.lt_succ_sqrt' (k - 1)
      have : (root + 1) ^ 2 + 1 ≤ (root + 2) ^ 2 := by nlinarith
      omega
    omega
  have widthSmall : 4 * w ^ 2 ≤ k - 1 := by
    calc
      4 * w ^ 2 = (2 * w) ^ 2 := by ring
      _ ≤ root ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ k - 1 := rootSquare
  have verticesLarge' : 64 * w ^ 6 * k ≤ n := by
    calc
      64 * w ^ 6 * k = (4 * w ^ 2) ^ 3 * k := by ring
      _ ≤ k ^ 3 * k := by gcongr; omega
      _ = k ^ 4 := by ring
      _ ≤ n := verticesLarge
  have bound := sixtyFourPow_lt_circuitSize n k w (by omega) widthSmall
    verticesLarge' circuit computes
  calc
    2 ^ (2 * Nat.sqrt k) ≤ 2 ^ (6 * w) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 64 ^ w := by rw [pow_mul]; norm_num
    _ < circuit.size := bound

/-- For `2 ≤ k ≤ 1024`, the edge count of `k^4` vertices exceeds
`4^⌊√k⌋ + 1`. -/
theorem fourPow_sqrt_add_two_le
    (k : Nat)
    (two_le : 2 ≤ k)
    (k_le : k ≤ 1024) :
    4 ^ Nat.sqrt k + 2 ≤ (k ^ 4 / 2) ^ 2 := by
  have monotone : ∀ base, base ≤ k →
      (base ^ 4 / 2) ^ 2 ≤ (k ^ 4 / 2) ^ 2 := fun base below =>
    Nat.pow_le_pow_left (Nat.div_le_div_right (Nat.pow_le_pow_left below 4)) 2
  have sqrtSmall : Nat.sqrt k ≤ 32 := by
    have : Nat.sqrt k < 33 := Nat.sqrt_lt'.2 (by omega)
    omega
  have sqrtPositive : 1 ≤ Nat.sqrt k := Nat.le_sqrt.2 (by omega)
  have squareBelow : Nat.sqrt k ^ 2 ≤ k := Nat.sqrt_le' k
  generalize Nat.sqrt k = root at sqrtSmall sqrtPositive squareBelow ⊢
  interval_cases root
  · exact le_trans (by norm_num) (monotone 2 two_le)
  all_goals exact le_trans (by norm_num) (monotone _ squareBelow)

/-- **Monotone CLIQUE lower bound.**  For every `k` with `k^4 ≤ n`, that is
`k ≤ n^(1/4)`, every binary, constant-free monotone shared circuit computing
`k`-CLIQUE on `n` vertices has more than `2^(2⌊√k⌋)` gates.  For `k ≤ 1` no
such circuit exists. -/
theorem twoPow_two_mul_sqrt_lt_circuitSize
    (n k : Nat)
    (verticesLarge : k ^ 4 ≤ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    2 ^ (2 * Nat.sqrt k) < circuit.size := by
  have k_le_n : k ≤ n := (Nat.le_self_pow (by norm_num) k).trans verticesLarge
  rcases Nat.lt_or_ge k 2 with small | two_le
  · exact absurd computes (not_computes_of_le_one (by omega) k_le_n circuit)
  rcases Nat.lt_or_ge k 1025 with medium | large
  · have edges := edgeCount_le_succ_size two_le k_le_n circuit computes
    have pairs := sq_half_le_edgeCount n
    have arithmetic := fourPow_sqrt_add_two_le k two_le (by omega)
    have scaled : (k ^ 4 / 2) ^ 2 ≤ (n / 2) ^ 2 :=
      Nat.pow_le_pow_left (Nat.div_le_div_right verticesLarge) 2
    rw [pow_mul]
    norm_num
    omega
  · exact twoPow_two_mul_sqrt_lt_circuitSize_of_large n k large verticesLarge
      circuit computes

/-- **Monotone CLIQUE lower bound, real form.**  For every `k ≤ n^(1/4)`,
every binary, constant-free monotone shared circuit computing `k`-CLIQUE on
`n` vertices has more than `2^√k` gates. -/
theorem rpow_sqrt_lt_circuitSize
    (n k : Nat)
    (verticesLarge : k ^ 4 ≤ n)
    (circuit : Circuit AndOr.signature (edgeCount n) 1)
    (computes : ∀ assignment,
      circuit.eval AndOr.boolInterpretation assignment 0 =
        function n k assignment) :
    (2 : ℝ) ^ Real.sqrt k < circuit.size := by
  have k_le_n : k ≤ n := (Nat.le_self_pow (by norm_num) k).trans verticesLarge
  rcases Nat.lt_or_ge k 2 with small | two_le
  · exact absurd computes (not_computes_of_le_one (by omega) k_le_n circuit)
  have natural := twoPow_two_mul_sqrt_lt_circuitSize n k verticesLarge
    circuit computes
  have sqrtPositive : 1 ≤ Nat.sqrt k := Nat.le_sqrt.2 (by omega)
  have exponentBound : Real.sqrt k ≤ ((2 * Nat.sqrt k : Nat) : ℝ) := by
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := k)
    have : (1 : ℝ) ≤ Nat.sqrt k := by exact_mod_cast sqrtPositive
    push_cast
    linarith
  calc
    (2 : ℝ) ^ Real.sqrt k ≤ (2 : ℝ) ^ ((2 * Nat.sqrt k : Nat) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) exponentBound
    _ = ((2 ^ (2 * Nat.sqrt k) : Nat) : ℝ) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    _ < circuit.size := by exact_mod_cast natural

end Asymptotic
end Clique
end Monotone
end Algebraic
