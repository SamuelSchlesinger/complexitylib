/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Threshold.Defs
public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.BasisHom.Defs
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Threshold circuits -- proof internals
-/


public section

namespace Complexity

private theorem countP_eq_arity_iff (n : ℕ)
    (inputs : Fin n → Bool) :
    Fin.countP inputs = n ↔
      ∀ index, inputs index = true := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.countP_succ, Fin.forall_fin_succ]
      cases hvalue : inputs 0 with
      | false =>
          have hnat : false.toNat = 0 := rfl
          rw [hnat]
          simp only [zero_add, Bool.false_eq_true, false_and,
            iff_false]
          exact Nat.ne_of_lt (Nat.lt_succ_of_le
            (Fin.countP_le
              (fun index : Fin n => inputs index.succ)))
      | true =>
          have hnat : true.toNat = 1 := rfl
          rw [hnat, Nat.add_comm n 1]
          simp only [true_and, Nat.add_left_cancel_iff]
          exact ih (fun index : Fin n => inputs index.succ)

private theorem countP_pos_iff (n : ℕ)
    (inputs : Fin n → Bool) :
    0 < Fin.countP inputs ↔
      ∃ index, inputs index = true := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.countP_succ, Fin.exists_fin_succ]
      cases hvalue : inputs 0 with
      | false =>
          have hnat : false.toNat = 0 := rfl
          rw [hnat]
          simp only [zero_add, Bool.false_eq_true, false_or]
          exact ih (fun index : Fin n => inputs index.succ)
      | true =>
          have hnat : true.toNat = 1 := rfl
          rw [hnat]
          simp only [true_or, iff_true]
          omega

private theorem foldl_and_eq (n : ℕ) (accumulator : Bool)
    (inputs : Fin n → Bool) :
    Fin.foldl n
        (fun value index => value && inputs index) accumulator =
      (accumulator && AndOrOp.eval .and n inputs) := by
  induction n generalizing accumulator with
  | zero =>
      simp [AndOrOp.eval, Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ, ih]
      have heval :
          AndOrOp.eval .and (n + 1) inputs =
            (inputs 0 &&
              AndOrOp.eval .and n
                (fun index => inputs index.succ)) := by
        simp only [AndOrOp.eval, Fin.foldl_succ]
        rw [ih]
        rfl
      rw [heval]
      cases accumulator <;> cases inputs 0 <;> rfl

private theorem foldl_or_eq (n : ℕ) (accumulator : Bool)
    (inputs : Fin n → Bool) :
    Fin.foldl n
        (fun value index => value || inputs index) accumulator =
      (accumulator || AndOrOp.eval .or n inputs) := by
  induction n generalizing accumulator with
  | zero =>
      simp [AndOrOp.eval, Fin.foldl_zero]
  | succ n ih =>
      rw [Fin.foldl_succ, ih]
      have heval :
          AndOrOp.eval .or (n + 1) inputs =
            (inputs 0 ||
              AndOrOp.eval .or n
                (fun index => inputs index.succ)) := by
        simp only [AndOrOp.eval, Fin.foldl_succ]
        rw [ih]
        rfl
      rw [heval]
      cases accumulator <;> cases inputs 0 <;> rfl

private theorem and_eval_eq_true_iff (n : ℕ)
    (inputs : Fin n → Bool) :
    AndOrOp.eval .and n inputs = true ↔
      ∀ index, inputs index = true := by
  induction n with
  | zero =>
      simp [AndOrOp.eval, Fin.foldl_zero]
  | succ n ih =>
      have heval :
          AndOrOp.eval .and (n + 1) inputs =
            (inputs 0 &&
              AndOrOp.eval .and n
                (fun index => inputs index.succ)) := by
        simp only [AndOrOp.eval, Fin.foldl_succ]
        rw [foldl_and_eq]
        rfl
      rw [heval, Bool.and_eq_true, ih, Fin.forall_fin_succ]

private theorem or_eval_eq_true_iff (n : ℕ)
    (inputs : Fin n → Bool) :
    AndOrOp.eval .or n inputs = true ↔
      ∃ index, inputs index = true := by
  induction n with
  | zero =>
      simp [AndOrOp.eval, Fin.foldl_zero]
  | succ n ih =>
      have heval :
          AndOrOp.eval .or (n + 1) inputs =
            (inputs 0 ||
              AndOrOp.eval .or n
                (fun index => inputs index.succ)) := by
        simp only [AndOrOp.eval, Fin.foldl_succ]
        rw [foldl_or_eq]
        rfl
      rw [heval, Bool.or_eq_true, ih, Fin.exists_fin_succ]

theorem trueCount_le_arity_internal (inputs : BitString n) :
    ThresholdOp.trueCount inputs ≤ n :=
  Fin.countP_le inputs

theorem eval_conjunction_internal (n : ℕ)
    (inputs : BitString n) :
    (ThresholdOp.conjunction n).eval n inputs =
      AndOrOp.eval .and n inputs := by
  rw [Bool.eq_iff_iff]
  unfold ThresholdOp.eval ThresholdOp.conjunction ThresholdOp.trueCount
  simp only [decide_eq_true_eq, and_eval_eq_true_iff]
  have hcount := Fin.countP_le inputs
  rw [show n ≤ Fin.countP inputs ↔
      Fin.countP inputs = n by omega]
  exact countP_eq_arity_iff n inputs

theorem eval_disjunction_internal (n : ℕ)
    (inputs : BitString n) :
    ThresholdOp.disjunction.eval n inputs =
      AndOrOp.eval .or n inputs := by
  rw [Bool.eq_iff_iff]
  unfold ThresholdOp.eval ThresholdOp.disjunction ThresholdOp.trueCount
  simp only [decide_eq_true_eq, or_eval_eq_true_iff]
  rw [show 1 ≤ Fin.countP inputs ↔
      0 < Fin.countP inputs by omega]
  exact countP_pos_iff n inputs

theorem eval_majority_internal (n : ℕ)
    (inputs : BitString n) :
    (ThresholdOp.majority n).eval n inputs =
      decide (n / 2 < Fin.countP inputs) := by
  rw [Bool.eq_iff_iff]
  unfold ThresholdOp.eval ThresholdOp.majority ThresholdOp.trueCount
  simp only [decide_eq_true_eq]
  omega

theorem eval_zero_internal (n : ℕ) (inputs : BitString n) :
    (ThresholdOp.mk 0).eval n inputs = true := by
  simp [ThresholdOp.eval, ThresholdOp.trueCount]

theorem eval_of_arity_lt_internal {cutoff n : ℕ}
    (hcutoff : n < cutoff) (inputs : BitString n) :
    (ThresholdOp.mk cutoff).eval n inputs = false := by
  unfold ThresholdOp.eval ThresholdOp.trueCount
  simp only [decide_eq_false_iff_not]
  have hcount := Fin.countP_le inputs
  omega

/-- Proof-internal exact embedding of unbounded AND/OR into threshold gates. -/
def Basis.andOrToThresholdHomInternal :
    Basis.Hom Basis.unboundedAndOr Basis.threshold where
  mapOp op n :=
    match op with
    | .and => ThresholdOp.conjunction n
    | .or => ThresholdOp.disjunction
  mapArity := by
    intro op n _
    trivial
  eval_map := by
    intro op n arityOk inputs
    cases op with
    | and =>
        exact eval_conjunction_internal n inputs
    | or =>
        exact eval_disjunction_internal n inputs

end Complexity
