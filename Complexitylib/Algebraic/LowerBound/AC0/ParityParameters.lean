/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerSchedule

/-!
# Concrete switching parameters for parity depth reduction

This module records a simple source-faithful choice of parameters. For target
tree depth `t >= 1`, use

* tree bounds `1, t, t, ...`,
* restriction probabilities `1/10, 1/(10t), 1/(10t), ...`, and
* retained ratios `1/20, 1/(20t), 1/(20t), ...`.

In every round the switching base `5 * p_i * t_i` is exactly `1/2`, while the
retained ratio is half of `p_i`. Hence every charged failure bound is

`S * (1/2)^(t+1)`,

and the single sufficient smallness condition is that this be below the
minimum ratio `1/(20t)`. Constants are intentionally conservative so exact
first-moment slack remains visible; optimizing them is not mathematically
important for the lower-bound exponent.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace ParityParameters

open scoped ENNReal

/-- Width one before any switching step, then the common target depth `t`. -/
def treeBound (t : Nat) : Nat → Nat
  | 0 => 1
  | _ + 1 => t

/-- Constant first-round restriction probability, followed by probability
inversely proportional to the common tree depth. -/
noncomputable def probability (t : Nat) : Nat → NNReal
  | 0 => 1 / 10
  | _ + 1 => 1 / (10 * (t : NNReal))

/-- Keep half of the expected live fraction available as failure slack. -/
noncomputable def retentionRatio (t : Nat) : Nat → NNReal
  | 0 => 1 / 20
  | _ + 1 => 1 / (20 * (t : NNReal))

/-- The smallest retained ratio occurring in the schedule. -/
noncomputable def minimumRatio (t : Nat) : NNReal :=
  1 / (20 * (t : NNReal))

@[simp] theorem treeBound_zero (t : Nat) :
    treeBound t 0 = 1 := rfl

@[simp] theorem treeBound_succ (t level : Nat) :
    treeBound t (level + 1) = t := by
  simp [treeBound]

/-- Every scheduled restriction parameter is a probability. -/
theorem probability_le_one
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    probability t level ≤ 1 := by
  cases level with
  | zero =>
      simp only [probability]
      rw [div_le_one (by norm_num)]
      norm_num
  | succ level =>
      simp only [probability]
      rw [div_le_one (by positivity)]
      have oneLeT : (1 : NNReal) ≤ (t : NNReal) := by
        exact_mod_cast oneLe
      calc
        (1 : NNReal) ≤ t := oneLeT
        _ ≤ 10 * t := by
          simpa using mul_le_mul_left
            (show (1 : NNReal) ≤ 10 by norm_num) t

/-- The scheduled tree allowance is monotone. -/
theorem treeBound_mono
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    treeBound t level ≤ treeBound t (level + 1) := by
  cases level with
  | zero => simpa [treeBound] using oneLe
  | succ level => simp [treeBound]

/-- Exact switching base, first proved in the finite nonnegative reals. -/
theorem five_mul_probability_mul_treeBound_nnreal
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    (5 : NNReal) * probability t level * (treeBound t level : NNReal) =
      1 / 2 := by
  cases level with
  | zero => norm_num [probability, treeBound]
  | succ level =>
      simp only [probability, treeBound]
      have tNe : (t : NNReal) ≠ 0 := by
        norm_cast
        omega
      field_simp
      norm_num

/-- Exact switching base in the extended nonnegative reals used by finite
probabilities. -/
theorem five_mul_probability_mul_treeBound
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    (5 : ENNReal) * (probability t level : ENNReal) *
        (treeBound t level : ENNReal) = 1 / 2 := by
  have casted := congrArg (fun value : NNReal => (value : ENNReal))
    (five_mul_probability_mul_treeBound_nnreal t oneLe level)
  simpa [ENNReal.coe_mul, ENNReal.coe_div, ENNReal.coe_natCast,
    ENNReal.coe_ofNat] using casted

/-- The retention ratio is exactly half the restriction probability. -/
theorem retention_twice_eq_probability_nnreal
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    retentionRatio t level + retentionRatio t level =
      probability t level := by
  cases level with
  | zero => norm_num [retentionRatio, probability]
  | succ level =>
      simp only [retentionRatio, probability]
      have tNe : (t : NNReal) ≠ 0 := by
        norm_cast
        omega
      field_simp
      norm_num

/-- The half-probability identity after coercion to exact finite
probabilities. -/
theorem retention_twice_eq_probability
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    (retentionRatio t level : ENNReal) +
        (retentionRatio t level : ENNReal) =
      (probability t level : ENNReal) := by
  have casted := congrArg (fun value : NNReal => (value : ENNReal))
    (retention_twice_eq_probability_nnreal t oneLe level)
  simpa [ENNReal.coe_add, ENNReal.coe_div, ENNReal.coe_natCast,
    ENNReal.coe_ofNat] using casted

/-- The later-round ratio is no larger than the first-round ratio. -/
theorem minimumRatio_le
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    minimumRatio t ≤ retentionRatio t level := by
  cases level with
  | zero =>
      simp only [minimumRatio, retentionRatio]
      apply one_div_le_one_div_of_le (by norm_num)
      have oneLeT : (1 : NNReal) ≤ (t : NNReal) := by
        exact_mod_cast oneLe
      simpa using mul_le_mul_right oneLeT (20 : NNReal)
  | succ level => rfl

/-- Common charged switching failure bound for every round. -/
noncomputable def switchingFailure
    (program : Algebraic.Program signature n g)
    (t : Nat) : ENNReal :=
  (program.cost andOrCost : ENNReal) * ((1 / 2 : ENNReal) ^ (t + 1))

/-- Every concrete round has the same charged failure bound. -/
theorem layerFailure_eq
    (program : Algebraic.Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    Program.layerFailureBoundOfBounds program (probability t level)
        (treeBound t level) (treeBound t (level + 1)) =
      switchingFailure program t := by
  unfold Program.layerFailureBoundOfBounds switchingFailure
  rw [treeBound_succ]
  rw [five_mul_probability_mul_treeBound t oneLe level]

/-- One uniform small-failure hypothesis supplies the probability slack for
every concrete round. -/
theorem layer_slack
    (program : Algebraic.Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat)
    (small : switchingFailure program t < (minimumRatio t : ENNReal)) :
    Program.layerFailureBoundOfBounds program (probability t level)
          (treeBound t level) (treeBound t (level + 1)) +
        (retentionRatio t level : ENNReal) <
      (probability t level : ENNReal) := by
  rw [layerFailure_eq program t oneLe level]
  rw [← retention_twice_eq_probability t oneLe level]
  apply ENNReal.add_lt_add_right ENNReal.coe_ne_top
  exact small.trans_le <| by
    exact_mod_cast minimumRatio_le t oneLe level

end ParityParameters
end AC0
end Algebraic
