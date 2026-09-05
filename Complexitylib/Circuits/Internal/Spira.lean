/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Formula
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Spira formula balancing -- proof internals

This file implements the separator-subformula argument behind Spira's
balancing theorem. The construction is kept internal; the public surface
states only the existence of an equivalent shallow, polynomial-size formula.
-/


public section

namespace Complexity
namespace BoolFormula

/-- A Boolean-formula context with one distinguished hole. -/
private inductive Context where
  | hole
  | neg (context : Context)
  | conjLeft (context : Context) (right : BoolFormula)
  | conjRight (left : BoolFormula) (context : Context)
  | disjLeft (context : Context) (right : BoolFormula)
  | disjRight (left : BoolFormula) (context : Context)

namespace Context

/-- Fill the unique hole of a formula context. -/
private def plug : Context → BoolFormula → BoolFormula
  | .hole, formula => formula
  | .neg context, formula => .neg (context.plug formula)
  | .conjLeft context right, formula =>
      .conj (context.plug formula) right
  | .conjRight left context, formula =>
      .conj left (context.plug formula)
  | .disjLeft context right, formula =>
      .disj (context.plug formula) right
  | .disjRight left context, formula =>
      .disj left (context.plug formula)

/-- The number of nodes in a context outside its hole. -/
private def size : Context → ℕ
  | .hole => 0
  | .neg context => context.size + 1
  | .conjLeft context right => context.size + right.size + 1
  | .conjRight left context => left.size + context.size + 1
  | .disjLeft context right => context.size + right.size + 1
  | .disjRight left context => left.size + context.size + 1

private theorem size_plug (context : Context) (formula : BoolFormula) :
    (context.plug formula).size = context.size + formula.size := by
  induction context with
  | hole => simp [plug, Context.size]
  | neg context ih =>
      simp [plug, Context.size, BoolFormula.size, ih]
      omega
  | conjLeft context right ih =>
      simp [plug, Context.size, BoolFormula.size, ih]
      omega
  | conjRight left context ih =>
      simp [plug, Context.size, BoolFormula.size, ih]
      omega
  | disjLeft context right ih =>
      simp [plug, Context.size, BoolFormula.size, ih]
      omega
  | disjRight left context ih =>
      simp [plug, Context.size, BoolFormula.size, ih]
      omega

private theorem eval_plug_shannon (context : Context)
    (formula : BoolFormula) (assignment : ℕ → Bool) :
    eval assignment (context.plug formula) =
      eval assignment
        (.disj
          (.conj formula (context.plug .tru))
          (.conj (.neg formula) (context.plug .fls))) := by
  cases hformula : eval assignment formula <;>
    induction context <;> simp_all [plug, eval]

end Context

/-- Select a subformula with size in `[threshold, 2 * threshold)` whenever the
input formula is at least `threshold`. The context component records the
selected occurrence, so plugging the selected subformula reconstructs the
original formula exactly. -/
private def splitAt : BoolFormula → ℕ → Context × BoolFormula
  | formula@(.var _), _ => (.hole, formula)
  | .tru, _ => (.hole, .tru)
  | .fls, _ => (.hole, .fls)
  | formula@(.neg child), threshold =>
      if formula.size < 2 * threshold then
        (.hole, formula)
      else
        let split := splitAt child threshold
        (.neg split.1, split.2)
  | formula@(.conj left right), threshold =>
      if formula.size < 2 * threshold then
        (.hole, formula)
      else if threshold ≤ left.size then
        let split := splitAt left threshold
        (.conjLeft split.1 right, split.2)
      else
        let split := splitAt right threshold
        (.conjRight left split.1, split.2)
  | formula@(.disj left right), threshold =>
      if formula.size < 2 * threshold then
        (.hole, formula)
      else if threshold ≤ left.size then
        let split := splitAt left threshold
        (.disjLeft split.1 right, split.2)
      else
        let split := splitAt right threshold
        (.disjRight left split.1, split.2)

private theorem splitAt_plug (formula : BoolFormula) (threshold : ℕ) :
    (splitAt formula threshold).1.plug
      (splitAt formula threshold).2 = formula := by
  induction formula with
  | var i => rfl
  | tru => rfl
  | fls => rfl
  | neg child ih =>
    simp only [splitAt]
    split
    · rfl
    · simp only [Context.plug, ih]
  | conj left right ihleft ihright =>
    simp only [splitAt]
    split
    · rfl
    · split
      · simp only [Context.plug, ihleft]
      · simp only [Context.plug, ihright]
  | disj left right ihleft ihright =>
    simp only [splitAt]
    split
    · rfl
    · split
      · simp only [Context.plug, ihleft]
      · simp only [Context.plug, ihright]

private theorem splitAt_size_bounds (formula : BoolFormula) (threshold : ℕ)
    (hthreshold : 1 ≤ threshold) (hformula : threshold ≤ formula.size) :
    threshold ≤ (splitAt formula threshold).2.size ∧
      (splitAt formula threshold).2.size < 2 * threshold := by
  induction formula with
  | var i =>
    simpa only [splitAt, BoolFormula.size] using
      And.intro hformula (by omega : (1 : ℕ) < 2 * threshold)
  | tru =>
    simpa only [splitAt, BoolFormula.size] using
      And.intro hformula (by omega : (1 : ℕ) < 2 * threshold)
  | fls =>
    simpa only [splitAt, BoolFormula.size] using
      And.intro hformula (by omega : (1 : ℕ) < 2 * threshold)
  | neg child ih =>
    simp only [splitAt]
    split
    · exact ⟨hformula, by assumption⟩
    · apply ih
      simp only [BoolFormula.size] at *
      omega
  | conj left right ihleft ihright =>
    simp only [splitAt]
    split
    · exact ⟨hformula, by assumption⟩
    · split
      · apply ihleft
        assumption
      · apply ihright
        simp only [BoolFormula.size] at *
        omega
  | disj left right ihleft ihright =>
    simp only [splitAt]
    split
    · exact ⟨hformula, by assumption⟩
    · split
      · apply ihleft
        assumption
      · apply ihright
        simp only [BoolFormula.size] at *
        omega

/-- The canonical quarter-size separator used by the balancing recursion. -/
private def spiraSplit (formula : BoolFormula) : Context × BoolFormula :=
  splitAt formula ((formula.size + 3) / 4)

private theorem spiraSplit_plug (formula : BoolFormula) :
    (spiraSplit formula).1.plug (spiraSplit formula).2 = formula :=
  splitAt_plug formula _

private theorem spiraSplit_subformula_contract (formula : BoolFormula)
    (hlarge : 16 ≤ formula.size) :
    16 * (spiraSplit formula).2.size ≤ 13 * formula.size := by
  have hthreshold : 1 ≤ (formula.size + 3) / 4 := by omega
  have hthreshold_le : (formula.size + 3) / 4 ≤ formula.size := by
    omega
  obtain ⟨_, hupper⟩ :=
    splitAt_size_bounds formula _ hthreshold hthreshold_le
  change 16 * (splitAt formula ((formula.size + 3) / 4)).2.size ≤
    13 * formula.size
  omega

private theorem spiraSplit_true_contract (formula : BoolFormula)
    (hlarge : 16 ≤ formula.size) :
    16 * ((spiraSplit formula).1.plug .tru).size ≤
      13 * formula.size := by
  have hthreshold : 1 ≤ (formula.size + 3) / 4 := by omega
  have hthreshold_le : (formula.size + 3) / 4 ≤ formula.size := by
    omega
  obtain ⟨hlower, _⟩ :=
    splitAt_size_bounds formula _ hthreshold hthreshold_le
  have hplug := congrArg BoolFormula.size (spiraSplit_plug formula)
  simp only [spiraSplit, Context.size_plug, BoolFormula.size] at hplug ⊢
  omega

private theorem spiraSplit_false_contract (formula : BoolFormula)
    (hlarge : 16 ≤ formula.size) :
    16 * ((spiraSplit formula).1.plug .fls).size ≤
      13 * formula.size := by
  have htrue := spiraSplit_true_contract formula hlarge
  rw [Context.size_plug] at htrue ⊢
  simp only [BoolFormula.size] at htrue ⊢
  exact htrue

/-- The logarithmic potential that pays for one balancing layer whenever a
separator contracts size by the factor `13 / 16`. -/
private def spiraRank (formula : BoolFormula) : ℕ :=
  Nat.clog 2 (formula.size ^ 4)

private theorem clog_two_mul {number : ℕ} (hpositive : 0 < number) :
    Nat.clog 2 (2 * number) = Nat.clog 2 number + 1 := by
  rw [Nat.clog_of_one_lt (by omega) (by omega)]
  congr 2
  omega

private theorem spiraRank_contract {child parent : BoolFormula}
    (hcontract : 16 * child.size ≤ 13 * parent.size) :
    spiraRank child + 1 ≤ spiraRank parent := by
  simp only [spiraRank]
  rw [← clog_two_mul (by
    have := one_le_size child
    positivity : 0 < child.size ^ 4)]
  apply Nat.clog_mono_right
  have hpower := Nat.pow_le_pow_left hcontract 4
  norm_num [Nat.mul_pow] at hpower ⊢
  omega

private theorem spiraSplit_subformula_lt (formula : BoolFormula)
    (hlarge : 16 ≤ formula.size) :
    (spiraSplit formula).2.size < formula.size := by
  have hcontract := spiraSplit_subformula_contract formula hlarge
  omega

private theorem spiraSplit_true_lt (formula : BoolFormula)
    (hlarge : 16 ≤ formula.size) :
    ((spiraSplit formula).1.plug .tru).size < formula.size := by
  have hcontract := spiraSplit_true_contract formula hlarge
  omega

private theorem spiraSplit_false_lt (formula : BoolFormula)
    (hlarge : 16 ≤ formula.size) :
    ((spiraSplit formula).1.plug .fls).size < formula.size := by
  have hcontract := spiraSplit_false_contract formula hlarge
  omega

/-- The deterministic balancing construction used to witness Spira's
theorem. Large formulas are expanded around a quarter-size separator; small
formulas are left unchanged. -/
private def spiraBalance (formula : BoolFormula) : BoolFormula :=
  if 16 ≤ formula.size then
    let split := spiraSplit formula
    let balancedSubformula := spiraBalance split.2
    let balancedTrue := spiraBalance (split.1.plug .tru)
    let balancedFalse := spiraBalance (split.1.plug .fls)
    .disj
      (.conj balancedSubformula balancedTrue)
      (.conj (.neg balancedSubformula) balancedFalse)
  else
    formula
termination_by formula.size
decreasing_by
  · apply spiraSplit_subformula_lt
    assumption
  · apply spiraSplit_true_lt
    assumption
  · apply spiraSplit_false_lt
    assumption

private theorem spiraBalance_eval (formula : BoolFormula)
    (assignment : ℕ → Bool) :
    eval assignment (spiraBalance formula) = eval assignment formula := by
  fun_induction spiraBalance formula with
  | case1 formula hlarge split balancedSubformula balancedTrue
      balancedFalse ihSubformula ihTrue ihFalse =>
    simp only [balancedSubformula, balancedTrue, balancedFalse, split,
      eval, ihSubformula, ihTrue, ihFalse]
    simpa only [spiraSplit_plug, eval] using
      (Context.eval_plug_shannon (spiraSplit formula).1
        (spiraSplit formula).2 assignment).symm
  | case2 formula hsmall =>
    rfl

private theorem spiraBalance_depth (formula : BoolFormula) :
    (spiraBalance formula).depth ≤ 15 + 3 * spiraRank formula := by
  fun_induction spiraBalance formula with
  | case1 formula hlarge split balancedSubformula balancedTrue
      balancedFalse ihSubformula ihTrue ihFalse =>
    simp only [split] at ihSubformula ihTrue ihFalse
    have hrSubformula :
        spiraRank (spiraSplit formula).2 + 1 ≤ spiraRank formula :=
      spiraRank_contract
        (spiraSplit_subformula_contract formula hlarge)
    have hrTrue :
        spiraRank ((spiraSplit formula).1.plug .tru) + 1 ≤
          spiraRank formula :=
      spiraRank_contract (spiraSplit_true_contract formula hlarge)
    have hrFalse :
        spiraRank ((spiraSplit formula).1.plug .fls) + 1 ≤
          spiraRank formula :=
      spiraRank_contract (spiraSplit_false_contract formula hlarge)
    have hdSubformula :
        (spiraBalance (spiraSplit formula).2).depth + 3 ≤
          15 + 3 * spiraRank formula := by
      omega
    have hdTrue :
        (spiraBalance ((spiraSplit formula).1.plug .tru)).depth + 3 ≤
          15 + 3 * spiraRank formula := by
      omega
    have hdFalse :
        (spiraBalance ((spiraSplit formula).1.plug .fls)).depth + 3 ≤
          15 + 3 * spiraRank formula := by
      omega
    simp only [balancedSubformula, balancedTrue, balancedFalse, split]
    simp only [depth]
    rw [max_add]
    apply max_le
    · have hmax := max_le hdSubformula hdTrue
      rw [← max_add] at hmax
      omega
    · rw [max_add, max_add]
      apply max_le <;> omega
  | case2 formula hsmall =>
    have hdepth := depth_le_size formula
    omega

private theorem spiraBalance_size (formula : BoolFormula) :
    (spiraBalance formula).size + 4 ≤
      20 * 4 ^ spiraRank formula := by
  fun_induction spiraBalance formula with
  | case1 formula hlarge split balancedSubformula balancedTrue
      balancedFalse ihSubformula ihTrue ihFalse =>
    simp only [split] at ihSubformula ihTrue ihFalse
    have hrSubformula :
        spiraRank (spiraSplit formula).2 + 1 ≤ spiraRank formula :=
      spiraRank_contract
        (spiraSplit_subformula_contract formula hlarge)
    have hrTrue :
        spiraRank ((spiraSplit formula).1.plug .tru) + 1 ≤
          spiraRank formula :=
      spiraRank_contract (spiraSplit_true_contract formula hlarge)
    have hrFalse :
        spiraRank ((spiraSplit formula).1.plug .fls) + 1 ≤
          spiraRank formula :=
      spiraRank_contract (spiraSplit_false_contract formula hlarge)
    have hsSubformula :
        4 * ((spiraBalance (spiraSplit formula).2).size + 4) ≤
          20 * 4 ^ spiraRank formula := by
      calc
        4 * ((spiraBalance (spiraSplit formula).2).size + 4)
            ≤ 4 * (20 * 4 ^ spiraRank (spiraSplit formula).2) :=
          Nat.mul_le_mul_left 4 ihSubformula
        _ = 20 * 4 ^
            (spiraRank (spiraSplit formula).2 + 1) := by
          rw [Nat.pow_succ]
          ring
        _ ≤ 20 * 4 ^ spiraRank formula :=
          Nat.mul_le_mul_left 20
            (Nat.pow_le_pow_right (by omega) hrSubformula)
    have hsTrue :
        4 *
            ((spiraBalance
              ((spiraSplit formula).1.plug .tru)).size + 4) ≤
          20 * 4 ^ spiraRank formula := by
      calc
        4 *
              ((spiraBalance
                ((spiraSplit formula).1.plug .tru)).size + 4)
            ≤ 4 * (20 * 4 ^
                spiraRank ((spiraSplit formula).1.plug .tru)) :=
          Nat.mul_le_mul_left 4 ihTrue
        _ = 20 * 4 ^
            (spiraRank ((spiraSplit formula).1.plug .tru) + 1) := by
          rw [Nat.pow_succ]
          ring
        _ ≤ 20 * 4 ^ spiraRank formula :=
          Nat.mul_le_mul_left 20
            (Nat.pow_le_pow_right (by omega) hrTrue)
    have hsFalse :
        4 *
            ((spiraBalance
              ((spiraSplit formula).1.plug .fls)).size + 4) ≤
          20 * 4 ^ spiraRank formula := by
      calc
        4 *
              ((spiraBalance
                ((spiraSplit formula).1.plug .fls)).size + 4)
            ≤ 4 * (20 * 4 ^
                spiraRank ((spiraSplit formula).1.plug .fls)) :=
          Nat.mul_le_mul_left 4 ihFalse
        _ = 20 * 4 ^
            (spiraRank ((spiraSplit formula).1.plug .fls) + 1) := by
          rw [Nat.pow_succ]
          ring
        _ ≤ 20 * 4 ^ spiraRank formula :=
          Nat.mul_le_mul_left 20
            (Nat.pow_le_pow_right (by omega) hrFalse)
    simp only [balancedSubformula, balancedTrue, balancedFalse, split,
      size]
    omega
  | case2 formula hsmall =>
    have hpow : 1 ≤ 4 ^ spiraRank formula :=
      Nat.one_le_pow (spiraRank formula) 4 (by omega)
    omega

private theorem spiraRank_le_four_clog (formula : BoolFormula) :
    spiraRank formula ≤ 4 * Nat.clog 2 formula.size := by
  simp only [spiraRank]
  apply Nat.clog_le_of_le_pow
  calc
    formula.size ^ 4 ≤ (2 ^ Nat.clog 2 formula.size) ^ 4 :=
      Nat.pow_le_pow_left
        (Nat.le_pow_clog Nat.one_lt_two formula.size) 4
    _ = 2 ^ (4 * Nat.clog 2 formula.size) := by
      rw [← Nat.pow_mul]
      congr 1
      omega

private theorem two_pow_clog_lt_two_mul {number : ℕ}
    (hpositive : 0 < number) :
    2 ^ Nat.clog 2 number < 2 * number := by
  by_cases hone : number = 1
  · simp [hone]
  · have hone_lt : 1 < number := by omega
    have hpower :=
      Nat.pow_pred_clog_lt_self Nat.one_lt_two hone_lt
    have hclog :=
      Nat.clog_pos Nat.one_lt_two hone_lt
    rw [← Nat.succ_pred_eq_of_pos hclog, Nat.pow_succ,
      Nat.mul_two]
    omega

private theorem spiraBalance_depth_logarithmic (formula : BoolFormula) :
    (spiraBalance formula).depth ≤
      15 + 12 * Nat.clog 2 formula.size := by
  have hdepth := spiraBalance_depth formula
  have hrank := spiraRank_le_four_clog formula
  omega

private theorem spiraBalance_size_polynomial (formula : BoolFormula) :
    (spiraBalance formula).size + 4 ≤ 80 * formula.size ^ 8 := by
  refine (spiraBalance_size formula).trans ?_
  have hpositive : 0 < formula.size ^ 4 := by
    have := one_le_size formula
    positivity
  have hclog :
      2 ^ spiraRank formula < 2 * formula.size ^ 4 := by
    simpa only [spiraRank] using
      two_pow_clog_lt_two_mul hpositive
  have hpower :
      (2 ^ spiraRank formula) ^ 2 ≤
        (2 * formula.size ^ 4) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_of_lt hclog) 2
  calc
    20 * 4 ^ spiraRank formula =
        20 * (2 ^ spiraRank formula) ^ 2 := by
      congr 1
      calc
        4 ^ spiraRank formula =
            (2 ^ 2) ^ spiraRank formula := by norm_num
        _ = 2 ^ (2 * spiraRank formula) :=
          (Nat.pow_mul 2 2 (spiraRank formula)).symm
        _ = 2 ^ (spiraRank formula * 2) := by
          rw [Nat.mul_comm]
        _ = (2 ^ spiraRank formula) ^ 2 :=
          Nat.pow_mul 2 (spiraRank formula) 2
    _ ≤ 20 * (2 * formula.size ^ 4) ^ 2 :=
      Nat.mul_le_mul_left 20 hpower
    _ = 80 * formula.size ^ 8 := by ring

theorem exists_spira_balanced_internal (formula : BoolFormula) :
    ∃ balanced : BoolFormula,
      (∀ assignment, eval assignment balanced = eval assignment formula) ∧
      balanced.depth ≤ 15 + 12 * Nat.clog 2 formula.size ∧
      balanced.size + 4 ≤ 80 * formula.size ^ 8 :=
  ⟨spiraBalance formula, spiraBalance_eval formula,
    spiraBalance_depth_logarithmic formula,
    spiraBalance_size_polynomial formula⟩

end BoolFormula
end Complexity
