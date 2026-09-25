/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.Arity
public import Complexitylib.Algebraic.LowerBound.Counting.AlmostAll
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Closed-form Shannon counting lower bounds

This file turns the exact factorial-improved census into the familiar
coefficient-one Shannon lower bound. For a fixed finite basis of maximum arity
`r ≥ 2` over a `q`-element universe, almost every `m`-output function requires
more than `⌊m qⁿ / ((r - 1) n)⌋` internal gates.

The proof keeps the exact budget. For any fixed shift `t`, the denominator `n`
eventually puts that budget below `q ^ (n - t)`; choosing `t` large absorbs all
basis-dependent constants while retaining leading coefficient one.
-/

@[expose] public section

namespace Algebraic

/-! ## Stirling reduction -/

/-- Logarithmic exponent obtained from the factorial-improved final term after
retaining the leading part of Stirling's lower bound. -/
noncomputable def _root_.Cslib.Circuits.Signature.stirlingExponent
    (σ : Signature) [Fintype σ.Op]
    (n m G : Nat) : Real :=
  Real.log (G + 1) +
    G * Real.log (σ.lineCount (n + G)) +
      m * Real.log (n + G) -
      ((G : Real) * Real.log G - G)

export Cslib.Circuits (Signature.stirlingExponent)

namespace Shannon

/-- Logarithm of the number `q ^ (m * q ^ n)` of `m`-output functions on
`n` inputs over a `q`-element universe, when `q` is positive. -/
noncomputable def logTargetCount (q n m : Nat) : Real :=
  ((m * q ^ n : Nat) : Real) * Real.log q

end Shannon

/-- The part of Stirling's lower bound responsible for the sharp leading
constant. -/
theorem Nat.cast_mul_log_sub_le_log_factorial
    {G : Nat}
    (positive : 0 < G) :
    (G : Real) * Real.log G - G ≤ Real.log G.factorial := by
  have stirling := Stirling.le_log_factorial_stirling
    (n := G) (Nat.ne_of_gt positive)
  refine le_trans ?_ stirling
  have logNonnegative : 0 ≤ Real.log (G : Real) :=
    Real.log_nonneg (by exact_mod_cast positive)
  have piNonnegative : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.two_le_pi])
  linarith

/-- Exponential envelope obtained by inserting the leading part of Stirling's
lower bound into the factorial-improved final term. -/
theorem _root_.Cslib.Circuits.Signature.finalTerm_le_exp_stirling
    (σ : Signature) [Fintype σ.Op]
    {n m G : Nat}
    (positive : 0 < G)
    (linesPositive : 0 < σ.lineCount (n + G)) :
    σ.finalTerm n m G ≤ Real.exp (σ.stirlingExponent n m G) := by
  unfold Signature.finalTerm Signature.stirlingExponent
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  norm_cast
  have stirling := Nat.cast_mul_log_sub_le_log_factorial positive
  linarith

export Cslib.Circuits (Signature.finalTerm_le_exp_stirling)

/-- Logarithmic finite form of the sharp Shannon criterion. Its left side has
leading contribution `(r - 1) * G * n * log q` for an `r`-ary signature over
a `q`-element universe. -/
theorem _root_.Cslib.Circuits.Circuit.exists_hard_of_stirlingLog
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (universeNontrivial : 1 < Fintype.card U)
    (gatePositive : 0 < G)
    (enoughLines : G ≤ σ.lineCount (n + G))
    (linesPositive : 0 < σ.lineCount (n + G))
    (large : σ.stirlingExponent n m G <
      Shannon.logTargetCount (Fintype.card U) n m) :
    ∃ target : Target U n m,
      Circuit.GateHard interpretation G target := by
  apply Circuit.exists_hard_of_finalTerm interpretation enoughLines
  apply (σ.finalTerm_le_exp_stirling gatePositive linesPositive).trans_lt
  have exponentBound := Real.exp_lt_exp.mpr large
  unfold Shannon.logTargetCount at exponentBound
  rw [Real.exp_nat_mul, Real.exp_log (by
    exact_mod_cast Nat.zero_lt_of_lt universeNontrivial)] at exponentBound
  calc
    Real.exp (σ.stirlingExponent n m G) <
        (Fintype.card U : Real) ^ (m * Fintype.card U ^ n) := exponentBound
    _ = (Target.count U n m : Real) := by
      rw [Target.count_eq, Nat.card_eq_fintype_card]
      norm_cast

/-! ## Gate-budget estimates -/

export Cslib.Circuits (Circuit.exists_hard_of_stirlingLog)

namespace Shannon

/-- Internal-gate budget at the sharp Shannon scale. Natural-number division
implements the floor; its value at `n = 0` is irrelevant to eventual results. -/
def gateBudget (q r m n : Nat) : Nat :=
  m * q ^ n / ((r - 1) * n)

@[simp] theorem gateBudget_two_two_one (n : Nat) :
    gateBudget 2 2 1 n = 2 ^ n / n := by
  simp [gateBudget]

/-! ### Elementary exponential growth estimates -/

private theorem eventually_const_mul_le_pow
    {q : Nat} (hq : 2 ≤ q) (c : Nat) :
    ∀ᶠ n in Filter.atTop, c * n ≤ q ^ n := by
  apply Filter.eventually_atTop.2
  refine ⟨2 * c, fun n hn => ?_⟩
  have hc : c ≤ 2 ^ c := by
    exact (by omega : c ≤ 2 * c).trans (Nat.mul_le_pow (by decide) c)
  have hnsub : n ≤ 2 * (n - c) := by omega
  calc
    c * n ≤ 2 ^ c * n := Nat.mul_le_mul_right n hc
    _ ≤ 2 ^ c * 2 ^ (n - c) :=
      Nat.mul_le_mul_left _
        (hnsub.trans (Nat.mul_le_pow (by decide) (n - c)))
    _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
    _ ≤ q ^ n := Nat.pow_le_pow_left hq n

private theorem square_le_two_pow
    {n : Nat} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ']

private theorem eventually_const_mul_square_le_pow
    {q : Nat} (hq : 2 ≤ q) (c : Nat) :
    ∀ᶠ n in Filter.atTop, c * n ^ 2 ≤ q ^ n := by
  apply Filter.eventually_atTop.2
  refine ⟨2 * (c + 2) + 4, fun n hn => ?_⟩
  have hc : c ≤ 2 ^ c := by
    exact (by omega : c ≤ 2 * c).trans (Nat.mul_le_pow (by decide) c)
  have hshift : c + 2 ≤ n := by omega
  have hdouble : n ≤ 2 * (n - (c + 2)) := by omega
  have hsquare : (n - (c + 2)) ^ 2 ≤ 2 ^ (n - (c + 2)) :=
    square_le_two_pow (by omega)
  calc
    c * n ^ 2 ≤ 2 ^ c * n ^ 2 := Nat.mul_le_mul_right _ hc
    _ ≤ 2 ^ c * (2 * (n - (c + 2))) ^ 2 := by
      gcongr
    _ = 2 ^ c * 4 * (n - (c + 2)) ^ 2 := by ring
    _ ≤ 2 ^ c * 4 * 2 ^ (n - (c + 2)) := by
      gcongr
    _ = 2 ^ n := by
      rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add,
        Nat.add_sub_of_le hshift]
    _ ≤ q ^ n := Nat.pow_le_pow_left hq n

/-! ### Gate-budget arithmetic -/

private theorem eventually_le_gateBudget
    {q r m : Nat}
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hm : 0 < m) (K : Nat) :
    ∀ᶠ n in Filter.atTop, K ≤ gateBudget q r m n := by
  have growth := eventually_const_mul_le_pow hq (K * (r - 1))
  filter_upwards [growth, Filter.eventually_ge_atTop 1] with n hn hnone
  rw [gateBudget, Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) hnone)]
  calc
    K * ((r - 1) * n) = (K * (r - 1)) * n := by ac_rfl
    _ ≤ q ^ n := hn
    _ ≤ m * q ^ n := Nat.le_mul_of_pos_left _ hm

private theorem gateBudget_mul_le
    (q r m n : Nat) :
    (r - 1) * n * gateBudget q r m n ≤ m * q ^ n := by
  simpa only [gateBudget] using
    Nat.mul_div_le (m * q ^ n) ((r - 1) * n)

private theorem gateBudget_le_shifted_pow
    {q r m n t : Nat}
    (htn : t ≤ n)
    (large : m * q ^ t ≤ (r - 1) * n) :
    gateBudget q r m n ≤ q ^ (n - t) := by
  apply Nat.div_le_of_le_mul
  calc
    m * q ^ n = (m * q ^ t) * q ^ (n - t) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le htn]
    _ ≤ ((r - 1) * n) * q ^ (n - t) :=
      Nat.mul_le_mul_right _ large

private theorem eventually_inputs_lt_gateBudget
    {q r m : Nat}
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hm : 0 < m) :
    ∀ᶠ n in Filter.atTop, n + 1 ≤ gateBudget q r m n := by
  have growth :=
    eventually_const_mul_square_le_pow hq (2 * (r - 1))
  filter_upwards [growth, Filter.eventually_ge_atTop 1] with n hn hnone
  rw [gateBudget, Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) hnone)]
  calc
    (n + 1) * ((r - 1) * n) ≤
        (2 * n) * ((r - 1) * n) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 2 * (r - 1) * n ^ 2 := by ring
    _ ≤ q ^ n := hn
    _ ≤ m * q ^ n := Nat.le_mul_of_pos_left _ hm

end Shannon

/-! ## Bounding the Stirling exponent -/

private theorem _root_.Cslib.Circuits.Signature.log_lineCount_le_maximumArity
    {σ : Signature} [Fintype σ.Op]
    {r n G : Nat}
    (maximum : σ.HasMaximumArity r)
    (hr : 2 ≤ r)
    (gatePositive : 0 < G)
    (inputsSmall : n + 1 ≤ G) :
    Real.log (σ.lineCount (n + G)) ≤
      Real.log (Fintype.card σ.Op) +
        r * (Real.log 2 + Real.log G) := by
  have opNonempty : Nonempty σ.Op := by
    obtain ⟨op, _⟩ := maximum.attained
    exact ⟨op⟩
  have opCountPositive : 0 < Fintype.card σ.Op :=
    Fintype.card_pos_iff.mpr opNonempty
  have enoughLines : G ≤ σ.lineCount (n + G) := by
    calc
      G ≤ n + G := by omega
      _ ≤ σ.lineCount (n + G) :=
        maximum.wires_le_lineCount (by omega) (n + G)
  have linesPositive : 0 < σ.lineCount (n + G) :=
    gatePositive.trans_le enoughLines
  have wiresBound : n + G + 1 ≤ 2 * G := by omega
  have lineBound :
      σ.lineCount (n + G) ≤
        Fintype.card σ.Op * (2 * G) ^ r := by
    calc
      σ.lineCount (n + G) ≤
          Fintype.card σ.Op * (n + G + 1) ^ r :=
        σ.lineCount_le_card_mul_pow maximum.arity_le (n + G)
      _ ≤ Fintype.card σ.Op * (2 * G) ^ r := by
        gcongr
  have castBound :
      (σ.lineCount (n + G) : Real) ≤
        (Fintype.card σ.Op : Real) * (2 * G : Nat) ^ r := by
    exact_mod_cast lineBound
  calc
    Real.log (σ.lineCount (n + G)) ≤
        Real.log ((Fintype.card σ.Op : Real) * (2 * G : Nat) ^ r) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show (0 : Real) < σ.lineCount (n + G) by exact_mod_cast linesPositive)
        (show (0 : Real) <
          (Fintype.card σ.Op : Real) * (2 * G : Nat) ^ r by positivity)
        castBound
    _ = Real.log (Fintype.card σ.Op) +
        r * (Real.log 2 + Real.log G) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [Real.log_mul (by norm_num)
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt gatePositive))]

namespace Shannon

private noncomputable def overhead (σ : Signature) [Fintype σ.Op]
    (r m : Nat) : Real :=
  (m + 1) *
      (Real.log (Fintype.card σ.Op) + r * Real.log 2) +
    m * r + 3

private theorem stirlingExponent_le
    {σ : Signature} [Fintype σ.Op]
    {r n m G : Nat}
    (maximum : σ.HasMaximumArity r)
    (hr : 2 ≤ r)
    (gatePositive : 0 < G)
    (inputsSmall : n + 1 ≤ G) :
    σ.stirlingExponent n m G ≤
      (r - 1 : Nat) * G * Real.log G +
        overhead σ r m * G := by
  let c : Real :=
    Real.log (Fintype.card σ.Op) + r * Real.log 2
  have cNonnegative : 0 ≤ c := by
    dsimp [c]
    positivity
  have lineLog : Real.log (σ.lineCount (n + G)) ≤
      c + r * Real.log G := by
    calc
      Real.log (σ.lineCount (n + G)) ≤
          Real.log (Fintype.card σ.Op) +
            r * (Real.log 2 + Real.log G) :=
        Cslib.Circuits.Signature.log_lineCount_le_maximumArity
          maximum hr gatePositive inputsSmall
      _ = c + r * Real.log G := by
        dsimp [c]
        ring
  have exponentNonnegative : (0 : Real) ≤ G + m := by positivity
  have lineContribution :=
    mul_le_mul_of_nonneg_left lineLog exponentNonnegative
  have wiresLeLines : n + G ≤ σ.lineCount (n + G) :=
    maximum.wires_le_lineCount (by omega) (n + G)
  have wiresPositive : 0 < n + G := by omega
  have linesPositive : 0 < σ.lineCount (n + G) :=
    wiresPositive.trans_le wiresLeLines
  have wireLog : Real.log (n + G) ≤
      Real.log (σ.lineCount (n + G)) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by
        simpa only [Set.mem_Ioi] using
          add_pos_of_nonneg_of_pos (Nat.cast_nonneg n)
            (by exact_mod_cast gatePositive : (0 : Real) < G))
      (by
        have positive : (0 : Real) < σ.lineCount (n + G) := by
          exact_mod_cast linesPositive
        simpa only [Set.mem_Ioi] using positive)
      (by exact_mod_cast wiresLeLines)
  have combinedContribution :
      (G : Real) * Real.log (σ.lineCount (n + G)) +
          (m : Real) * Real.log (n + G) ≤
        ((G : Real) + m) * (c + r * Real.log G) := by
    calc
      (G : Real) * Real.log (σ.lineCount (n + G)) +
            (m : Real) * Real.log (n + G) ≤
          (G : Real) * Real.log (σ.lineCount (n + G)) +
            (m : Real) * Real.log (σ.lineCount (n + G)) := by
        gcongr
      _ = ((G : Real) + m) * Real.log (σ.lineCount (n + G)) := by ring
      _ ≤ ((G : Real) + m) * (c + r * Real.log G) := lineContribution
  have logGate : Real.log G ≤ G :=
    Real.log_le_self (by positivity)
  have extraLog :
      (m : Real) * r * Real.log G ≤ (m : Real) * r * G :=
    mul_le_mul_of_nonneg_left logGate (by positivity)
  have logGateSucc : Real.log (G + 1) ≤ G + 1 :=
    Real.log_le_self (by positivity)
  have gateOne : (1 : Real) ≤ G := by exact_mod_cast gatePositive
  have constantAbsorption :
      (m : Real) * c + 1 ≤ ((m : Real) * c + 1) * G := by
    calc
      (m : Real) * c + 1 = ((m : Real) * c + 1) * 1 := by ring
      _ ≤ ((m : Real) * c + 1) * G :=
        mul_le_mul_of_nonneg_left gateOne (by positivity)
  unfold Signature.stirlingExponent
  dsimp only [overhead]
  rw [Nat.cast_sub (by omega : 1 ≤ r)]
  norm_num only [Nat.cast_one]
  calc
    Real.log (G + 1) +
          G * Real.log (σ.lineCount (n + G)) +
          m * Real.log (n + G) -
            (G * Real.log G - G) ≤
        (G + 1) + (G + m) * (c + r * Real.log G) -
          (G * Real.log G - G) := by
      linarith
    _ = (r - 1) * G * Real.log G + c * G + m * c +
          m * r * Real.log G + 2 * G + 1 := by ring
    _ ≤ (r - 1) * G * Real.log G + c * G + m * c +
          m * r * G + 2 * G + 1 := by
      linarith
    _ ≤ (r - 1) * G * Real.log G +
          ((m + 1) * c + m * r + 3) * G := by
      linarith
    _ = (r - 1) * G * Real.log G +
          ((m + 1) *
              (Real.log (Fintype.card σ.Op) + r * Real.log 2) +
            m * r + 3) * G := by
      rfl

private theorem eventually_stirlingExponent_le_target_sub_budget
    {σ : Signature} [Fintype σ.Op]
    {q r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (hq : 2 ≤ q)
    (hr : 2 ≤ r)
    (hm : 0 < m) :
    ∀ᶠ n in Filter.atTop,
      σ.stirlingExponent n m (gateBudget q r m n) ≤
        Shannon.logTargetCount q n m - gateBudget q r m n := by
  have qOne : (1 : Real) < q := by exact_mod_cast (by omega : 1 < q)
  have logQPositive : 0 < Real.log q := Real.log_pos qOne
  have arityGapPositive : 0 < (r - 1 : Nat) := by omega
  have coefficientPositive :
      0 < ((r - 1 : Nat) : Real) * Real.log q := by positivity
  let H := overhead σ r m
  obtain ⟨t, ht⟩ :=
    exists_nat_gt ((H + 1) /
      (((r - 1 : Nat) : Real) * Real.log q))
  have gap : H + 1 <
      ((r - 1 : Nat) : Real) * t * Real.log q := by
    have divided := (div_lt_iff₀ coefficientPositive).mp ht
    nlinarith
  have gatePositive := eventually_le_gateBudget hq hr hm 1
  have inputsSmall := eventually_inputs_lt_gateBudget hq hr hm
  filter_upwards [gatePositive, inputsSmall,
      Filter.eventually_ge_atTop t,
      Filter.eventually_ge_atTop (m * q ^ t)] with
      n gateOne inputsBelow htn hnlarge
  let G := gateBudget q r m n
  have GPositive : 0 < G := by dsimp only [G]; omega
  have shiftedLarge : m * q ^ t ≤ (r - 1) * n := by
    exact hnlarge.trans (Nat.le_mul_of_pos_left n arityGapPositive)
  have GUpperNat : G ≤ q ^ (n - t) := by
    exact gateBudget_le_shifted_pow htn shiftedLarge
  have GUpper : (G : Real) ≤ (q : Real) ^ (n - t) := by
    exact_mod_cast GUpperNat
  have logGUpper : Real.log G ≤ (n - t : Nat) * Real.log q := by
    calc
      Real.log G ≤ Real.log ((q : Real) ^ (n - t)) :=
        Real.strictMonoOn_log.monotoneOn
          (show (0 : Real) < G by exact_mod_cast GPositive)
          (show (0 : Real) < (q : Real) ^ (n - t) by positivity)
          GUpper
      _ = (n - t : Nat) * Real.log q := Real.log_pow _ _
  have productBoundNat : (r - 1) * n * G ≤ m * q ^ n := by
    simpa only [G] using gateBudget_mul_le q r m n
  have productBound :
      (((r - 1) * n * G : Nat) : Real) * Real.log q ≤
        ((m * q ^ n : Nat) : Real) * Real.log q :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast productBoundNat)
      logQPositive.le
  have leadingBound :
      ((r - 1 : Nat) : Real) * G * Real.log G ≤
        ((m * q ^ n : Nat) : Real) * Real.log q -
          (((r - 1 : Nat) : Real) * t * Real.log q) * G := by
    have logContribution := mul_le_mul_of_nonneg_left logGUpper
      (mul_nonneg (Nat.cast_nonneg (r - 1)) (Nat.cast_nonneg G))
    calc
      ((r - 1 : Nat) : Real) * G * Real.log G ≤
          ((r - 1 : Nat) : Real) * G *
            ((n - t : Nat) * Real.log q) := logContribution
      _ = (((r - 1) * n * G : Nat) : Real) * Real.log q -
          (((r - 1 : Nat) : Real) * t * Real.log q) * G := by
        rw [Nat.cast_sub htn]
        push_cast
        ring
      _ ≤ ((m * q ^ n : Nat) : Real) * Real.log q -
          (((r - 1 : Nat) : Real) * t * Real.log q) * G :=
        sub_le_sub_right productBound _
  have exponentBound := stirlingExponent_le
    (m := m) maximum hr GPositive inputsBelow
  unfold Signature.stirlingExponent at exponentBound
  change
    Real.log (G + 1) +
          G * Real.log (σ.lineCount (n + G)) +
          m * Real.log (n + G) -
          (G * Real.log G - G) ≤
      ((m * q ^ n : Nat) : Real) * Real.log q - G
  have gapTimesGate :
      (overhead σ r m + 1) * (G : Real) ≤
        (((r - 1 : Nat) : Real) * t * Real.log q) * G := by
    dsimp only [H] at gap
    exact mul_le_mul_of_nonneg_right gap.le (Nat.cast_nonneg _)
  nlinarith

/-! ### Negligibility of the final term -/

private theorem eventually_mul_finalTerm_le_fullSpace
    {σ : Signature} [Fintype σ.Op]
    {q r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (hq : 2 ≤ q)
    (hr : 2 ≤ r)
    (hm : 0 < m)
    (K : Nat) :
    ∀ᶠ n in Filter.atTop,
      (K : Real) * σ.finalTerm n m (gateBudget q r m n) ≤
        (q : Real) ^ (m * q ^ n) := by
  have exponentBound :=
    eventually_stirlingExponent_le_target_sub_budget maximum hq hr hm
  have gateLarge := eventually_le_gateBudget hq hr hm (max K 1)
  filter_upwards [exponentBound, gateLarge] with n bounded hgate
  let G := gateBudget q r m n
  have GPositive : 0 < G := by dsimp only [G]; omega
  have KBound : K ≤ G := by dsimp only [G]; omega
  have enoughLines : G ≤ σ.lineCount (n + G) :=
    (Nat.le_add_left G n).trans
      (maximum.wires_le_lineCount (by omega) (n + G))
  have linesPositive : 0 < σ.lineCount (n + G) :=
    GPositive.trans_le enoughLines
  have finalTermBound :=
    σ.finalTerm_le_exp_stirling (m := m) GPositive linesPositive
  have KExp : (K : Real) ≤ Real.exp G := by
    calc
      (K : Real) ≤ G := by exact_mod_cast KBound
      _ ≤ G + 1 := by linarith
      _ ≤ Real.exp G := Real.add_one_le_exp _
  let A := σ.stirlingExponent n m G
  change
    (K : Real) * σ.finalTerm n m G ≤
      (q : Real) ^ (m * q ^ n)
  change σ.finalTerm n m G ≤ Real.exp A at finalTermBound
  change A ≤ Shannon.logTargetCount q n m - G at bounded
  calc
    (K : Real) * σ.finalTerm n m G ≤ (K : Real) * Real.exp A :=
      mul_le_mul_of_nonneg_left finalTermBound (Nat.cast_nonneg K)
    _ ≤ Real.exp G * Real.exp A :=
      mul_le_mul_of_nonneg_right KExp (Real.exp_pos A).le
    _ = Real.exp (G + A) := (Real.exp_add G A).symm
    _ ≤ Real.exp (Shannon.logTargetCount q n m) := by
      rw [Real.exp_le_exp]
      linarith
    _ = (q : Real) ^ (m * q ^ n) := by
      unfold Shannon.logTargetCount
      rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (by omega : 0 < q))]

end Shannon

/-! ## Closed-form density theorems -/

/-- Closed-form Shannon theorem for an arbitrary fixed finite basis. At the
exact budget `⌊m |U|ⁿ / ((r - 1) n)⌋`, the easy functions form an
asymptotically negligible fraction of the full function space. -/
theorem _root_.Cslib.Circuits.Circuit.asymptoticallyAlmostAllHard_shannon
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (universeNontrivial : 2 ≤ Fintype.card U)
    (arityAtLeastTwo : 2 ≤ r)
    (outputsPositive : 0 < m) :
    Circuit.AsymptoticallyAlmostAllHard
      interpretation m
      (Circuit.fullFamily U m)
      (Shannon.gateBudget (Fintype.card U) r m) := by
  apply Circuit.asymptoticallyAlmostAllHard_of_finalTerm
  · exact Filter.Eventually.of_forall fun n =>
      (Nat.le_add_left (Shannon.gateBudget (Fintype.card U) r m n) n).trans
        (maximum.wires_le_lineCount (by omega)
          (n + Shannon.gateBudget (Fintype.card U) r m n))
  · intro K
    have bounded := Shannon.eventually_mul_finalTerm_le_fullSpace
      maximum universeNontrivial arityAtLeastTwo outputsPositive K
    filter_upwards [bounded] with n hn
    calc
      (K : Real) * σ.finalTerm n m
            (Shannon.gateBudget (Fintype.card U) r m n) ≤
          (Fintype.card U : Real) ^
            (m * Fintype.card U ^ n) := hn
      _ = ((Circuit.fullFamily U m n).card : Real) := by
        rw [Circuit.card_fullFamily, Target.count_eq,
          Nat.card_eq_fintype_card]
        norm_cast

export Cslib.Circuits (Circuit.asymptoticallyAlmostAllHard_shannon)

/-- Conventional density form of the closed Shannon theorem. -/
theorem _root_.Cslib.Circuits.Circuit.tendsto_easyDensity_zero_shannon
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    {r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (universeNontrivial : 2 ≤ Fintype.card U)
    (arityAtLeastTwo : 2 ≤ r)
    (outputsPositive : 0 < m) :
    Filter.Tendsto
      (fun n =>
        Circuit.easyDensity interpretation
          (Circuit.fullFamily U m n)
          (Shannon.gateBudget (Fintype.card U) r m n))
      Filter.atTop (nhds 0) := by
  apply (Circuit.asymptoticallyAlmostAllHard_shannon interpretation
    maximum universeNontrivial arityAtLeastTwo outputsPositive).tendsto_easyDensity_zero
  exact Filter.Eventually.of_forall fun n => by
    rw [Circuit.card_fullFamily, Target.count_eq,
      Nat.card_eq_fintype_card]
    positivity

export Cslib.Circuits (Circuit.tendsto_easyDensity_zero_shannon)

/-- Boolean specialization of the closed Shannon theorem. For a binary basis
and one output, `Shannon.gateBudget_two_two_one` identifies the budget with
`2 ^ n / n`. -/
theorem _root_.Cslib.Circuits.Circuit.tendsto_boolean_easyDensity_zero_shannon
    [Fintype σ.Op]
    (interpretation : Interpretation σ Bool)
    {r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (arityAtLeastTwo : 2 ≤ r)
    (outputsPositive : 0 < m) :
    Filter.Tendsto
      (fun n =>
        Circuit.easyDensity interpretation
          (Circuit.fullFamily Bool m n)
          (Shannon.gateBudget 2 r m n))
      Filter.atTop (nhds 0) := by
  simpa only [Fintype.card_bool] using
    Circuit.tendsto_easyDensity_zero_shannon interpretation maximum
      (by simp) arityAtLeastTwo outputsPositive

export Cslib.Circuits (Circuit.tendsto_boolean_easyDensity_zero_shannon)

/-- Finite-field specialization of the closed Shannon theorem. -/
theorem _root_.Cslib.Circuits.Circuit.tendsto_finiteField_easyDensity_zero_shannon
    {K : Type u} [Field K] [Fintype K]
    [Fintype σ.Op]
    (interpretation : Interpretation σ K)
    {r m : Nat}
    (maximum : σ.HasMaximumArity r)
    (arityAtLeastTwo : 2 ≤ r)
    (outputsPositive : 0 < m) :
    Filter.Tendsto
      (fun n =>
        Circuit.easyDensity interpretation
          (Circuit.fullFamily K m n)
          (Shannon.gateBudget (Fintype.card K) r m n))
      Filter.atTop (nhds 0) :=
  Circuit.tendsto_easyDensity_zero_shannon interpretation maximum
    Fintype.one_lt_card arityAtLeastTwo outputsPositive

export Cslib.Circuits (Circuit.tendsto_finiteField_easyDensity_zero_shannon)

end Algebraic
